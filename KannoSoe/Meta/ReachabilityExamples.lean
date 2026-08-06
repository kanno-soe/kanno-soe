import KannoSoe.Signature.Rules

/-!
# Reachability examples

This small finite system records that every component of an elaborated mutual
dependence is available to ordinary reachability, including a component in the
middle of the displayed chain.
-/

namespace ReachabilityExamples

inductive Designatum where
  | x
  | a
  | μ
  | b
  | unrelated
  deriving DecidableEq, Repr

open Designatum

abbrev elaboration : Elaboration Designatum :=
  Elaboration.ofRules [
    { source := x, components := [[a], [μ], [b]] }
  ]

/-- A source may enter a middle component of its elaborated body. -/
theorem middle_reachable : elaboration.Reaches x μ := by
  rw [← Elaboration.Rules.mem_reachSet_iff]
  decide

/-- The same fact is available through the verified `Joinable` decision. -/
theorem middle_joinable : elaboration.Joinable x μ := by decide

/-- A designatum absent from every rule remains unrelated. -/
theorem unrelated_not_joinable : ¬elaboration.Joinable x unrelated := by
  decide

/-- Reversing every displayed alternative does not change base reach. -/
theorem reversal_closure_same_reach :
    (Elaboration.reversalClosure elaboration).Reaches = elaboration.Reaches :=
  Elaboration.reaches_reversalClosure elaboration

end ReachabilityExamples
