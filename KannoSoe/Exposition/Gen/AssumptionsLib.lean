import KannoSoe.Exposition.Registry
import KannoSoe.Meta.AssumptionLedger

namespace KannoSoe

namespace AssumptionsGen

def renderAnchor (anchor : AssumptionAnchor) : String :=
  "`" ++ anchor.name.toString ++ "` (" ++ anchor.status.label ++ ")"

def renderAnchorList (anchors : List AssumptionAnchor) : String :=
  match anchors with
  | [] => "None."
  | names => Exposition.joinComma (names.map renderAnchor)

def anchorsForLayer (layer : AnchorLayer) (entry : AssumptionEntry) :
    List AssumptionAnchor :=
  entry.anchors.filter (fun anchor => anchor.layer == layer)

def renderEntry (entry : AssumptionEntry) : String :=
  let signatureAnchors := anchorsForLayer .signature entry
  let downstreamAnchors := anchorsForLayer .downstream entry
  let note :=
    match entry.note with
    | none => ""
    | some text => "\n\n> Note: " ++ text
  let downstream :=
    match downstreamAnchors with
    | [] => ""
    | anchors =>
        "\n\n**Downstream elaboration:** " ++ renderAnchorList anchors
  "### " ++ entry.«section».key ++ "." ++ toString entry.number ++ " " ++
    Exposition.markdownEscape entry.title ++ "\n\n" ++
    entry.statement ++ "\n\n" ++
    "**Checked anchors (Signature):** " ++ renderAnchorList signatureAnchors ++
    downstream ++ note

def renderSection (sec : AssumptionSection) : String :=
  "## " ++ sec.key ++ ". " ++ sec.label ++ "\n\n" ++
    String.intercalate "\n\n"
      ((assumptionSectionEntries sec).map renderEntry)

def renderAxiomNames (names : List Lean.Name) : String :=
  match names with
  | [] => "None"
  | names => Exposition.joinComma (names.map (fun name => "`" ++ name.toString ++ "`"))

def renderAxiomAuditEntry (entry : AxiomAuditEntry) : String :=
  "| `" ++ entry.name.toString ++ "` | " ++ renderAxiomNames entry.allowed ++ " |"

def renderAxiomAudit : String :=
  "## Axiom audit\n\n" ++
    "`#verify_axiom_audit` compares each declaration's collected axiom set " ++
    "with this allowlist during every build.\n\n" ++
    "| Declaration | Allowed axioms |\n|---|---|\n" ++
    String.intercalate "\n" (axiomAuditLedger.map renderAxiomAuditEntry)

def assumptionsBody : String :=
  "# Assumptions\n\n" ++
    "Generated from `KannoSoe/Meta/AssumptionLedger.lean` by " ++
    "`lake exe exposition_gen`. `KannoSoe/Meta/AxiomAudit.lean` holds the " ++
    "compile-checked axiom ledger; statement prose is canonical here.\n\n" ++
    String.intercalate "\n\n"
      [ renderSection .asserted,
        renderSection .declined,
        renderSection .convenience,
        renderAxiomAudit ] ++ "\n"

end AssumptionsGen

def assumptionsDoc : Exposition.Doc :=
  { id := Exposition.assumptionsRef.id
    title := Exposition.assumptionsRef.title
    output := Exposition.assumptionsRef.output
    source := "KannoSoe/Meta/AssumptionLedger.lean"
    summary := Exposition.assumptionsRef.summary
    blocks := [.raw AssumptionsGen.assumptionsBody] }

def renderAssumptions : String :=
  Exposition.renderDoc assumptionsDoc

end KannoSoe
