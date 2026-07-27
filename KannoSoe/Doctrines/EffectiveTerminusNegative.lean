/-
================================================================================
  KannoSoe.Doctrines.EffectiveTerminusNegative
  Actual-run underdetermination of effective termination
================================================================================

The standing predicate is intentionally stronger than any actual-run transcript
that omits the delivery register. Replacing only `conditions` can leave every
mounted response and share unchanged while flipping `KsmdEffectiveTerminus`.

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import KannoSoe.Doctrines.Shusho
import KannoSoe.Doctrines.SraddhaNegative

namespace KannoSoe

namespace EffectiveTerminusNegative

open Grid
open Grid.DirectedConvention

abbrev baseGrid :
    CoreReadings SraddhaNegative.CaseDesignatum Nat :=
  SraddhaNegative.zeroEffectGrid

abbrev sealedGrid :
    CoreReadings SraddhaNegative.CaseDesignatum Nat :=
  baseGrid.withConditions (fun _ _ => False)

def addedDelivery
    (deed reception : SraddhaNegative.CaseDesignatum) : Prop :=
  deed = .sraddhaOccurrence ∧ reception = .receiverOccurrence

abbrev openedGrid :
    CoreReadings SraddhaNegative.CaseDesignatum Nat :=
  sealedGrid.withConditions addedDelivery

def b : SraddhaNegative.CaseDesignatum :=
  .sraddha

def liveBefore : Config Nat :=
  SraddhaNegative.liveBefore

def deed : sealedGrid.Weld :=
  ⟨.sraddhaOccurrence, True.intro⟩

def reception : sealedGrid.Weld :=
  ⟨.receiverOccurrence, True.intro⟩

theorem sealed_responsiveTerminus :
    sealedGrid.ResponsiveTerminus b :=
  SraddhaNegative.sraddha_responsiveTerminus

theorem sealed_undelivered :
    ∀ (deed reception : sealedGrid.Weld),
      deed.agent = b →
        ¬ Grid.DirectedConvention.DeliveredTo
          sealedGrid deed reception := by
  intro deed reception _hdeed hdel
  exact hdel

theorem sealed_ksmdEffectiveTerminus :
    KsmdEffectiveTerminus sealedGrid b :=
  ksmdEffectiveTerminus_of_responsiveTerminus_of_undelivered
    sealedGrid sealed_responsiveTerminus sealed_undelivered

theorem opened_delivered :
    Grid.DirectedConvention.DeliveredTo openedGrid deed reception := by
  exact ⟨rfl, rfl⟩

theorem opened_liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency :=
  SraddhaNegative.liveBefore_not_atBot

theorem opened_not_hasShareDropLanding :
    ¬ HasShareDropLanding openedGrid liveBefore deed := by
  rintro ⟨received, hland⟩
  have hreceiver :
      received.1 = SraddhaNegative.CaseDesignatum.receiverOccurrence :=
    hland.left.left.right
  have hdrop : Strict (openedGrid.share received) liveBefore.tendency :=
    hland.right
  rcases received with ⟨d, hd⟩
  change d = SraddhaNegative.CaseDesignatum.receiverOccurrence at hreceiver
  subst d
  change Strict (1 : Nat) 1 at hdrop
  exact strict_irrefl (1 : Nat) hdrop

theorem opened_not_ksmdEffectiveTerminus :
    ¬ KsmdEffectiveTerminus openedGrid b := by
  intro hstanding
  exact opened_not_hasShareDropLanding
    (hstanding.right liveBefore deed reception rfl
      opened_liveBefore_not_atBot opened_delivered)

/-- The actual-run transcript used by this collision: response function plus
    grade/share data, deliberately excluding the delivery relation. -/
abbrev RunData : Type :=
  (SraddhaNegative.CaseDesignatum ->
      SraddhaNegative.CaseDesignatum ->
        Option SraddhaNegative.CaseDesignatum) ×
    (SraddhaNegative.CaseDesignatum -> Nat)

def sealedRunData : RunData :=
  (sealedGrid.respondsTo, sealedGrid.grade)

def openedRunData : RunData :=
  (openedGrid.respondsTo, openedGrid.grade)

theorem runData_agrees :
    sealedRunData = openedRunData :=
  rfl

theorem actual_iff_agrees (w : sealedGrid.Weld) :
    sealedGrid.Actual w ↔ openedGrid.Actual w :=
  Iff.rfl

theorem share_agrees (w : sealedGrid.Weld) :
    sealedGrid.share w = openedGrid.share w :=
  rfl

theorem respondsTo_agrees
    (being cue : SraddhaNegative.CaseDesignatum) :
    sealedGrid.respondsTo being cue = openedGrid.respondsTo being cue :=
  rfl

theorem effectiveTerminus_collision :
    sealedRunData = openedRunData ∧
      KsmdEffectiveTerminus sealedGrid b ∧
        ¬ KsmdEffectiveTerminus openedGrid b :=
  ⟨runData_agrees, sealed_ksmdEffectiveTerminus,
    opened_not_ksmdEffectiveTerminus⟩

/-- No Boolean estimator from this actual-run transcript can recover the
    effective-terminus predicate across the collision. -/
theorem no_effectiveTerminus_recovery_from_run :
    ¬ ∃ estimate : RunData -> Bool,
        estimate sealedRunData = true ∧
          estimate openedRunData = false := by
  rintro ⟨estimate, hsealed, hopened⟩
  have hsame : estimate sealedRunData = estimate openedRunData :=
    congrArg estimate runData_agrees
  have htruefalse : true = false := by
    calc
      true = estimate sealedRunData := hsealed.symm
      _ = estimate openedRunData := hsame
      _ = false := hopened
  cases htruefalse

theorem actual_run_data_underdetermines_effectiveTerminus :
    KsmdEffectiveTerminus sealedGrid b ∧
      ¬ KsmdEffectiveTerminus openedGrid b ∧
        sealedRunData = openedRunData ∧
          ¬ ∃ estimate : RunData -> Bool,
            estimate sealedRunData = true ∧
              estimate openedRunData = false :=
  ⟨sealed_ksmdEffectiveTerminus, opened_not_ksmdEffectiveTerminus,
    runData_agrees, no_effectiveTerminus_recovery_from_run⟩

end EffectiveTerminusNegative

end KannoSoe
