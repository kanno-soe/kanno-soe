/-
================================================================================
  KannoSoe.Doctrines.FactorsNegative
  Supplied factor boundaries and order underdetermination
================================================================================
-/

import KannoSoe.Doctrines.Factors

namespace KannoSoe

namespace FactorsNegative

open Grid

inductive CaseDesignatum
  | being
  | first
  | second
  | response
  | firstOccurrence
  | secondOccurrence

def occurrenceReading : OccurrenceReading CaseDesignatum where
  occurrence d := d = .firstOccurrence ∨ d = .secondOccurrence
  isBeing d := d = .being
  isCall
    | .first | .second => True
    | _ => False
  isResponse d := d = .response
  agent
    | .firstOccurrence | .secondOccurrence => .being
    | d => d
  call
    | .firstOccurrence => .first
    | .secondOccurrence => .second
    | d => d
  response
    | .firstOccurrence | .secondOccurrence => .response
    | d => d

def grid : CoreReadings CaseDesignatum Nat where
  occurrence := occurrenceReading
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .being, .first | .being, .second => some .response
      | _, _ => none
  }
  placement := {
    grade := fun d =>
      match d with
      | .firstOccurrence => 1
      | _ => 0
  }
  conditioning := {
    conditions := fun _ _ => True
  }

def reading : grid.DoorReading where
  door w := match w.call with | .first => .speech | _ => .body

def firstWeld : grid.Weld := ⟨.firstOccurrence, Or.inl rfl⟩
def secondWeld : grid.Weld := ⟨.secondOccurrence, Or.inr rfl⟩

def firstViewReading : grid.FetterReading where
  provocationClass f w :=
    match f with
    | .identityView => w.call = .first
    | .ritesGrasp => w.call = .second
    | _ => False

def secondViewReading : grid.FetterReading where
  provocationClass f w :=
    match f with
    | .identityView => w.call = .second
    | .ritesGrasp => w.call = .first
    | _ => False

theorem speech_class_activated :
    PathFactor.blockerClass reading firstViewReading .speech firstWeld :=
  rfl

theorem conduct_class_inert (w : grid.Weld) :
    ¬ PathFactor.blockerClass reading firstViewReading .conduct w :=
  fun h => h

theorem first_view_held :
    grid.FactorHeld reading CaseDesignatum.being
      firstViewReading .view [firstWeld] := by
  refine ⟨firstWeld, by simp, rfl, rfl, Or.inl rfl, ?_⟩
  dsimp [Grid.HasSelfPoleIndex, Grid.share, grid, firstWeld, AtBot, shareBot]
  show ¬ (1 : Nat) ≤ 0
  decide

theorem second_view_released :
    grid.FactorReleased reading CaseDesignatum.being
      secondViewReading .view := by
  rintro ⟨d, hd⟩ _hactual _hagent hclass
  rcases hclass with hclass | hclass
  · change d = CaseDesignatum.firstOccurrence ∨
      d = CaseDesignatum.secondOccurrence at hd
    change occurrenceReading.call d = CaseDesignatum.second at hclass
    rcases hd with rfl | rfl
    · contradiction
    · exact Nat.le_refl 0
  · cases hclass

abbrev GridData : Type :=
  (CaseDesignatum → CaseDesignatum → Option CaseDesignatum) ×
    (CaseDesignatum → Nat)

def gridData : GridData := (grid.respondsTo, grid.grade)

def firstViewBoundary (w : grid.Weld) : Prop := w.call = .first
def secondViewBoundary (w : grid.Weld) : Prop := w.call = .second

/-- The same grid data supports incompatible factor boundaries, so a seen
    hold/release classification remains reading-relative. -/
theorem no_hold_conceit_boundary_recovery :
    ¬ ∃ recover : GridData → grid.Weld → Prop,
      recover gridData = firstViewBoundary ∧
        recover gridData = secondViewBoundary := by
  rintro ⟨recover, hfirst, hsecond⟩
  have hyes : recover gridData firstWeld := by rw [hfirst]; rfl
  have hno : ¬ recover gridData firstWeld := by
    rw [hsecond]
    intro h
    cases h
  exact hno hyes

/-- Swapping the supplied view and rites classes reverses their displayed
    factor order without changing the underlying grid. -/
theorem factor_order_underdetermined :
    firstViewReading.provocationClass Fetter.identityView firstWeld ∧
      secondViewReading.provocationClass Fetter.ritesGrasp firstWeld ∧
      firstViewReading.provocationClass Fetter.ritesGrasp secondWeld ∧
      secondViewReading.provocationClass Fetter.identityView secondWeld :=
  ⟨rfl, rfl, rfl, rfl⟩

end FactorsNegative

end KannoSoe
