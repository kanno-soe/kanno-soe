/-
================================================================================
  KannoSoe.Doctrines.SraddhaNegative
  Negative witnesses for the sraddha conditional
================================================================================

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import KannoSoe.Doctrines.Sraddha

namespace KannoSoe
/- ==============================================================================
   Negative witnesses: both antecedents matter
============================================================================== -/

namespace SraddhaNegative

open Grid.DirectedConvention

inductive CaseDesignatum
  | sraddha
  | receiver
  | call
  | response
  | sraddhaOccurrence
  | receiverOccurrence
  deriving DecidableEq

def occurrenceReading : OccurrenceReading CaseDesignatum where
  occurrence
    | .sraddhaOccurrence | .receiverOccurrence => True
    | _ => False
  isBeing
    | .sraddha | .receiver => True
    | _ => False
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .sraddhaOccurrence => .sraddha
    | .receiverOccurrence => .receiver
    | d => d
  call
    | .sraddhaOccurrence | .receiverOccurrence => .call
    | d => d
  response
    | .sraddhaOccurrence | .receiverOccurrence => .response
    | d => d

/-- A responsive terminus whose delivered deed has no share-drop landing for
    the receiver's live prior tendency. -/
def zeroEffectGrid : CoreReadings CaseDesignatum Nat where
  occurrence := occurrenceReading
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .sraddha, .call | .receiver, .call => some .response
      | _, _ => none
  }
  placement := {
    grade := fun d =>
      match d with
      | .receiverOccurrence => 1
      | _ => 0
  }
  conditioning := {
    conditions := fun deed reception =>
      deed = .sraddhaOccurrence ∧ reception = .receiverOccurrence
  }

def liveBefore : Config Nat :=
  { tendency := 1 }

def poleBefore : Config Nat :=
  { tendency := 0 }

def deed : zeroEffectGrid.Weld :=
  ⟨.sraddhaOccurrence, True.intro⟩

def reception : zeroEffectGrid.Weld :=
  ⟨.receiverOccurrence, True.intro⟩

theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 0 h

theorem poleBefore_atBot :
    AtBot poleBefore.tendency :=
  Nat.le_refl 0

theorem reception_actual :
    zeroEffectGrid.Actual reception :=
  rfl

theorem delivered :
    Grid.DirectedConvention.DeliveredTo zeroEffectGrid deed reception :=
  ⟨rfl, rfl⟩

theorem reception_hasSelfPoleIndex :
    zeroEffectGrid.HasSelfPoleIndex reception := by
  intro hbot
  exact Nat.not_succ_le_zero 0 hbot

theorem aversionContext :
    KsmdAversionContext zeroEffectGrid liveBefore reception :=
  { liveBefore := liveBefore_not_atBot
    clenchMismatch := ⟨reception_actual, reception_hasSelfPoleIndex⟩ }

theorem sraddha_responsiveTerminus :
    zeroEffectGrid.ResponsiveTerminus CaseDesignatum.sraddha := by
  constructor
  · intro c hc
    change c = CaseDesignatum.call at hc
    subst c
    exact ⟨CaseDesignatum.response, rfl⟩
  · rintro ⟨d, hd⟩ _hactual hagent
    change occurrenceReading.occurrence d at hd
    change occurrenceReading.agent d = CaseDesignatum.sraddha at hagent
    change AtBot (zeroEffectGrid.placement.grade d)
    cases d with
    | sraddha | receiver | call | response =>
        change False at hd
        contradiction
    | receiverOccurrence =>
        change CaseDesignatum.receiver = CaseDesignatum.sraddha at hagent
        contradiction
    | sraddhaOccurrence =>
        exact Nat.le_refl 0

theorem not_hasShareDropLanding_liveBefore :
    ¬ HasShareDropLanding zeroEffectGrid liveBefore deed := by
  rintro ⟨received, hland⟩
  have hreceiver :
      received.1 = CaseDesignatum.receiverOccurrence :=
    hland.left.left.right
  have hdrop : Strict (zeroEffectGrid.share received) liveBefore.tendency :=
    hland.right
  rcases received with ⟨d, hd⟩
  change d = CaseDesignatum.receiverOccurrence at hreceiver
  subst d
  change Strict (1 : Nat) 1 at hdrop
  exact strict_irrefl (1 : Nat) hdrop

theorem not_ksmdEffectiveTerminus :
    ¬ KsmdEffectiveTerminus zeroEffectGrid CaseDesignatum.sraddha := by
  intro hfaith
  exact not_hasShareDropLanding_liveBefore
    (hfaith.right liveBefore deed reception rfl liveBefore_not_atBot delivered)

/-- Dropping the faith conjunct leaves delivery and aversion insufficient. -/
theorem drop_faith_antecedent_fails :
    zeroEffectGrid.ResponsiveTerminus CaseDesignatum.sraddha ∧
      Grid.DirectedConvention.DeliveredTo zeroEffectGrid deed reception ∧
      KsmdAversionContext zeroEffectGrid liveBefore reception ∧
      ¬ HasShareDropLanding zeroEffectGrid liveBefore deed :=
  ⟨sraddha_responsiveTerminus, delivered, aversionContext,
    not_hasShareDropLanding_liveBefore⟩

theorem not_hasShareDropLanding_poleBefore :
    ¬ HasShareDropLanding zeroEffectGrid poleBefore deed :=
  no_ksmd_path_at_pole zeroEffectGrid poleBefore_atBot deed

/-- Dropping the aversion conjunct leaves a pole-prior case where no
    share-drop landing is constructible. -/
theorem drop_aversion_antecedent_fails :
    AtBot poleBefore.tendency ∧
      Grid.DirectedConvention.DeliveredTo zeroEffectGrid deed reception ∧
      ¬ KsmdAversionContext zeroEffectGrid poleBefore reception ∧
      ¬ HasShareDropLanding zeroEffectGrid poleBefore deed :=
  ⟨poleBefore_atBot, delivered,
    no_ksmd_aversion_context_at_pole zeroEffectGrid poleBefore_atBot reception,
    not_hasShareDropLanding_poleBefore⟩

end SraddhaNegative

/- ==============================================================================
   Sraddha orthogonality countermodel
============================================================================== -/

namespace OrthogonalityNegative

open Grid.DirectedConvention

/-- The same zero-effectiveness witness used by `SraddhaNegative`: a responsive
    terminus whose delivered deed does not land as a share-drop for the live
    receiver context. -/
abbrev zeroEffectGrid :
    CoreReadings SraddhaNegative.CaseDesignatum Nat :=
  SraddhaNegative.zeroEffectGrid

theorem responsiveTerminus_with_no_shareDropLanding :
    zeroEffectGrid.ResponsiveTerminus
        SraddhaNegative.CaseDesignatum.sraddha ∧
      ¬ HasShareDropLanding zeroEffectGrid SraddhaNegative.liveBefore SraddhaNegative.deed :=
  ⟨SraddhaNegative.sraddha_responsiveTerminus,
    SraddhaNegative.not_hasShareDropLanding_liveBefore⟩

theorem terminus_not_ksmdEffectiveTerminus :
    zeroEffectGrid.Terminus SraddhaNegative.CaseDesignatum.sraddha ∧
      ¬ KsmdEffectiveTerminus zeroEffectGrid
        SraddhaNegative.CaseDesignatum.sraddha :=
  ⟨SraddhaNegative.sraddha_responsiveTerminus.right,
    SraddhaNegative.not_ksmdEffectiveTerminus⟩

/-- `KsmdEffectiveTerminus` is strictly stronger than terminus typing: it
    implies terminus, and this concrete responsive terminus still fails the
    shortfall-closure conjunct. -/
theorem ksmdEffectiveTerminus_stronger_than_terminus :
    (KsmdEffectiveTerminus zeroEffectGrid
          SraddhaNegative.CaseDesignatum.sraddha →
        zeroEffectGrid.Terminus SraddhaNegative.CaseDesignatum.sraddha) ∧
      zeroEffectGrid.Terminus SraddhaNegative.CaseDesignatum.sraddha ∧
      ¬ KsmdEffectiveTerminus zeroEffectGrid
        SraddhaNegative.CaseDesignatum.sraddha := by
  constructor
  · intro h
    exact (responsiveTerminus_of_ksmdEffectiveTerminus zeroEffectGrid h).right
  · exact terminus_not_ksmdEffectiveTerminus

end OrthogonalityNegative

end KannoSoe
