import Lean
import KannoSoe.Signature.V2
import KannoSoe.Signature.Interpenetration
import KannoSoe.Meta.Examples
import KannoSoe.Meta.InterpenetrationExamples

/-!
# Audit: signature and example modules

This standalone audit is intentionally not imported by the library. Run it
from the repository root with:

    lake env lean KannoSoe/Meta/Audit.lean

For each target module, the audit parses its source to find review-sensitive
constructs, then checks every environment declaration attributed to the
module, including private and compiler-generated declarations. It reports
declared axioms, opaque/unsafe/partial declarations, and every transitive
kernel axiom dependency.

The exact module-level trust boundaries are:

* KannoSoe.Signature.V2: propext, plus the known private partial helper
  generated for Being.rawOfComponents.
* KannoSoe.Signature.Interpenetration: propext.
* KannoSoe.Meta.Examples: propext and Quot.sound.
* KannoSoe.Meta.InterpenetrationExamples: propext.

In particular, sorry and admit (which elaborate through sorryAx), declared
axioms, and classical choice are rejected.
-/

open Lean Elab Command

private structure ModuleAuditConfig where
  moduleName : String
  sourcePath : System.FilePath
  allowedAxioms : List String
  expectedPartials : List String := []

private structure SourceMarker where
  text : String
  pos : String.Pos.Raw

private def auditStringLt (a b : String) : Bool :=
  a < b

private def auditNameLt (a b : Name) : Bool :=
  auditStringLt a.toString b.toString

private def auditRenderStrings (items : List String) : String :=
  "[" ++ String.intercalate ", "
    ((items.toArray.qsort auditStringLt).toList) ++ "]"

private def auditRenderNames (names : List Name) : String :=
  auditRenderStrings (names.map Name.toString)

private def auditDottedName (value : String) : Name :=
  value.splitOn "." |>.foldl
    (fun name part => Name.str name part) Name.anonymous

private def auditAtomMarker? (value : String) : Option String :=
  if ["sorry", "admit", "axiom", "axioms", "opaque", "unsafe",
      "partial", "noncomputable", "classical", "extern",
      "implemented_by"].contains value then
    some value
  else
    none

private def auditIdentMarker? (value : Name) : Option String :=
  let value := value.toString
  if value == "propext" || value == "Quot.sound" ||
      value == "Classical" || value.startsWith "Classical." then
    some value
  else
    none

private partial def collectSourceMarkers : Syntax → Array SourceMarker
  | .missing => #[]
  | .atom info value =>
      match auditAtomMarker? value, info.getPos? with
      | some text, some pos => #[{ text, pos }]
      | _, _ => #[]
  | .ident info _ value _ =>
      match auditIdentMarker? value, info.getPos? with
      | some text, some pos => #[{ text, pos }]
      | _, _ => #[]
  | .node _ _ args =>
      args.foldl
        (fun found arg => found ++ collectSourceMarkers arg) #[]

private def auditModule
    (env : Environment) (config : ModuleAuditConfig) : CommandElabM Unit := do
  let moduleName := auditDottedName config.moduleName
  let some moduleIdx := env.getModuleIdx? moduleName
    | throwError "unknown imported module {moduleName}"

  let source ← IO.FS.readFile config.sourcePath
  let syntaxTree ← Parser.testParseFile env config.sourcePath
  let fileMap := FileMap.ofString source
  let sourceMarkers := collectSourceMarkers syntaxTree

  let mut declarationCount := 0
  let mut directAxioms : Array Name := #[]
  let mut opaques : Array Name := #[]
  let mut unsafes : Array Name := #[]
  let mut partials : Array Name := #[]
  let mut dependencies : Array (Name × List Name) := #[]
  let mut seenAxioms : Array String := #[]
  let mut failures : Array String := #[]

  for (name, info) in env.constants do
    if env.getModuleIdxFor? name == some moduleIdx then
      declarationCount := declarationCount + 1
      if info.isAxiom then
        directAxioms := directAxioms.push name
        failures := failures.push s!"declared axiom: {name}"
      if info matches .opaqueInfo _ then
        opaques := opaques.push name
        failures := failures.push s!"opaque declaration: {name}"
      if info.isUnsafe then
        unsafes := unsafes.push name
        failures := failures.push s!"unsafe declaration: {name}"
      if info.isPartial then
        partials := partials.push name
        unless config.expectedPartials.contains name.toString do
          failures := failures.push s!"unexpected partial declaration: {name}"

      let occurs := (← Lean.collectAxioms name).toList
      unless occurs.isEmpty do
        dependencies := dependencies.push (name, occurs)
      for axiomName in occurs do
        let axiomName := axiomName.toString
        unless seenAxioms.contains axiomName do
          seenAxioms := seenAxioms.push axiomName
      let unexpected := occurs.filter
        (fun axiomName => !config.allowedAxioms.contains axiomName.toString)
      unless unexpected.isEmpty do
        failures := failures.push (
          s!"{name}: unexpected axiom dependencies " ++
            auditRenderNames unexpected)

  for expected in config.expectedPartials do
    unless partials.any (fun name => name.toString == expected) do
      failures := failures.push s!"expected partial declaration absent: {expected}"

  for allowed in config.allowedAxioms do
    unless seenAxioms.contains allowed do
      failures := failures.push s!"expected axiom dependency absent: {allowed}"

  for marker in sourceMarkers do
    let pos := fileMap.toPosition marker.pos
    failures := failures.push (
      s!"source review marker at " ++
        s!"{config.sourcePath}:{pos.line}:{pos.column + 1}: {marker.text}")

  logInfo m!"source review markers for {moduleName}: {sourceMarkers.size}"
  for marker in sourceMarkers do
    let pos := fileMap.toPosition marker.pos
    logInfo
      m!"  {config.sourcePath}:{pos.line}:{pos.column + 1}: {marker.text}"

  let summary : String :=
    s!"module {moduleName}: {declarationCount} declarations; " ++
      s!"{directAxioms.size} declared axioms; {opaques.size} opaque; " ++
      s!"{unsafes.size} unsafe; {partials.size} partial"
  logInfo summary

  unless directAxioms.isEmpty do
    logInfo "declared axioms:"
    for name in directAxioms.qsort auditNameLt do
      logInfo m!"  {name}"

  unless opaques.isEmpty do
    logInfo "opaque declarations:"
    for name in opaques.qsort auditNameLt do
      logInfo m!"  {name}"

  unless unsafes.isEmpty do
    logInfo "unsafe declarations:"
    for name in unsafes.qsort auditNameLt do
      logInfo m!"  {name}"

  unless partials.isEmpty do
    logInfo "partial declarations:"
    for name in partials.qsort auditNameLt do
      logInfo m!"  {name}"

  let axiomSummary : String :=
    s!"module axiom set for {moduleName}: " ++
      auditRenderStrings seenAxioms.toList
  logInfo axiomSummary
  logInfo m!"declarations with axiom dependencies for {moduleName}:"
  for (name, occurs) in dependencies.qsort
      (fun a b => auditNameLt a.1 b.1) do
    logInfo m!"  {name}: {auditRenderNames occurs}"

  unless failures.isEmpty do
    let details := failures.foldl
      (fun result failure => result ++ "\n- " ++ failure) ""
    throwError m!"module audit failed for {moduleName}:{details}"

  logInfo m!"module audit passed: {moduleName}"

elab "#audit_signature_and_examples" : command => do
  let env ← getEnv
  let auditPath := System.FilePath.mk (← read).fileName
  let some auditDir := auditPath.parent
    | throwError "cannot determine the audit file's parent directory"
  let some packageDir := auditDir.parent
    | throwError "cannot determine the KannoSoe source directory"

  let configs : List ModuleAuditConfig := [
    { moduleName := "KannoSoe.Signature.V2"
      sourcePath := packageDir / "Signature" / "V2.lean"
      allowedAxioms := ["propext"]
      expectedPartials :=
        ["_private.KannoSoe.Signature.V2.0.Being.rawOfComponents._unsafe_rec"] },
    { moduleName := "KannoSoe.Signature.Interpenetration"
      sourcePath := packageDir / "Signature" / "Interpenetration.lean"
      allowedAxioms := ["propext"] },
    { moduleName := "KannoSoe.Meta.Examples"
      sourcePath := auditDir / "Examples.lean"
      allowedAxioms := ["propext", "Quot.sound"] },
    { moduleName := "KannoSoe.Meta.InterpenetrationExamples"
      sourcePath := auditDir / "InterpenetrationExamples.lean"
      allowedAxioms := ["propext"] }
  ]

  for config in configs do
    auditModule env config

#audit_signature_and_examples
