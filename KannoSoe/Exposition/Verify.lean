import Lean
import KannoSoe.Exposition.Registry
import KannoSoe.Exposition.Glossary

namespace KannoSoe.Exposition

def isEmptyList {α : Type} : List α -> Bool
  | [] => true
  | _ => false

def claimFailures (docId : DocId) (claim : Claim) : List String :=
  match claim.status with
  | .checked =>
      if isEmptyList claim.anchors then
        [docId ++ ": checked claim has no anchors"]
      else
        []
  | .proseBound reason =>
      if reason = "" then
        [docId ++ ": prose-bound claim has no reason"]
      else
        []

def xrefFailures (docIds : List DocId) (doc : Doc) : List String :=
  doc.xrefs.filterMap (fun target =>
    if docIds.contains target then
      none
    else
      some (doc.id ++ ": unknown xref target " ++ target))

def termFailures (terms : List String) (doc : Doc) : List String :=
  doc.terms.filterMap (fun term =>
    if terms.contains term then
      none
    else
      some (doc.id ++ ": glossary term not found: " ++ term))

def structuralFailures (docs : List Doc) (terms : List String) : List String :=
  let docIds := docs.map (fun doc => doc.id)
  docs.flatMap (fun doc =>
    doc.claims.flatMap (claimFailures doc.id) ++
    xrefFailures docIds doc ++
    termFailures terms doc)

def residueFailures (docIds : List DocId) (entries : List ResidueEntry) : List String :=
  entries.filterMap (fun entry =>
    if docIds.contains entry.locus then
      none
    else
      some (entry.id ++ ": unknown residue locus " ++ entry.locus))

open Lean Elab Command Meta

syntax (name := verifyExpositionAnchors) "#verify_exposition_anchors" : command

unsafe def evalAllDocs : Term.TermElabM (List Doc) := do
  evalExpr (List Doc)
    (mkApp (mkConst ``List [Level.zero]) (mkConst ``Doc))
    (mkConst ``allDocs)

@[command_elab verifyExpositionAnchors] unsafe def elabVerifyExpositionAnchors :
    CommandElab := fun _stx => do
  let docs <- liftTermElabM evalAllDocs
  let env <- getEnv
  let mut failures : Array String := #[]
  for failure in structuralFailures docs KannoSoe.glossaryTerms do
    failures := failures.push failure
  for failure in residueFailures registryIds residueLedger do
    failures := failures.push failure
  for doc in docs do
    for anchor in doc.anchors do
      unless env.contains anchor do
        failures := failures.push s!"{doc.id}: missing exposition anchor {anchor}"
  unless failures.isEmpty do
    let details := failures.foldl (fun acc item => acc ++ "\n" ++ item) ""
    throwError m!"exposition verification failed:{details}"

#verify_exposition_anchors

end KannoSoe.Exposition
