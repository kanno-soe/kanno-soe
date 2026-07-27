import KannoSoe.Exposition.Basic
import KannoSoe.Signature
import KannoSoe.Identification.Ownership
import KannoSoe.Meta.Invariance

namespace KannoSoe.Exposition

structure ThesisClause where
  id : String
  text : String
  status : ClaimStatus
  anchors : List Lean.Name := []
deriving Repr

def thesisClauses : List ThesisClause := [
  { id := "diachronicToField"
    text := "Everything diachronic belongs to the field"
    status := .checked
    anchors := [``Config] },
  { id := "indexEnactedNotStored"
    text := "every index is enacted and nothing indexed is stored"
    status := .checked
    anchors := [``Grid.index, ``Grid.rePitch_forgets,
      ``Grid.relabel_rePitch, ``Grid.no_natural_agent_recovery_from_config] },
  { id := "karmaNamesLoop"
    text := "karma names this loop"
    status := .checked
    anchors := [``Grid.DirectedConvention.KsmdOwnershipFace] },
  { id := "namingEarnedByFit"
    text := "and the naming is earned by fit"
    status := .proseBound "fit to the traditional offices is argued in exposition"
    anchors := [``Grid.DirectedConvention.KsmdReportFace,
      ``Grid.DirectedConvention.KsmdOwnershipFace] }
]

def thesisSentence : String :=
  "Everything diachronic belongs to the field; every index is enacted and nothing indexed is stored; karma names this loop, and the naming is earned by fit"

def thesisRender : String :=
  "**" ++ thesisSentence ++ "** — the tradition's uses of karmic ownership (cetanā, reception, remorse, absolution, dedication) discharge natively at act-time."

example : thesisSentence =
    "Everything diachronic belongs to the field; every index is enacted and nothing indexed is stored; karma names this loop, and the naming is earned by fit" := rfl

end KannoSoe.Exposition
