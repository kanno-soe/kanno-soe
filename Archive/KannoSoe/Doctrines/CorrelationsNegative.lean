/-
================================================================================
  KannoSoe.Doctrines.CorrelationsNegative
  Negative witnesses for Bulls, ranks, and stage-coarsenings
================================================================================
-/

import KannoSoe.Doctrines.Correlations

namespace KannoSoe

namespace CorrelationsNegative

open Grid.DirectedConvention
open Grid.DirectedConvention.BeingConvention

/- ==============================================================================
   Bull 9 without Bull 10
============================================================================== -/

inductive SolitaryDesignatum
  | solo
  | other
  | call
  | response
  | soloOccurrence
  | otherOccurrence
  deriving DecidableEq

def solitaryOccurrence : OccurrenceReading SolitaryDesignatum where
  occurrence
    | .soloOccurrence | .otherOccurrence => True
    | _ => False
  isBeing
    | .solo | .other => True
    | _ => False
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .soloOccurrence => .solo
    | .otherOccurrence => .other
    | d => d
  call
    | .soloOccurrence | .otherOccurrence => .call
    | d => d
  response
    | .soloOccurrence | .otherOccurrence => .response
    | d => d

/-- A pole responder in a world where delivery never crosses fibers. -/
def solitaryGrid : CoreReadings SolitaryDesignatum Nat where
  occurrence := solitaryOccurrence
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .solo, .call | .other, .call => some .response
      | _, _ => none
  }
  placement := {
    grade := fun _ => 0
  }
  conditioning := {
    conditions := fun deed reception =>
      solitaryOccurrence.agent deed = solitaryOccurrence.agent reception
  }

def identityCoarsening :
    BeingCoarsening solitaryGrid SolitaryDesignatum where
  proj := id

def solitarySentience : solitaryGrid.SentienceReading :=
  Grid.SentienceReading.allSentient solitaryGrid

theorem solo_bullNine :
    solitaryGrid.KsmdBullNine SolitaryDesignatum.solo := by
  constructor
  · intro c hc
    change c = SolitaryDesignatum.call at hc
    subst c
    exact ⟨SolitaryDesignatum.response, rfl⟩
  · intro _w _hactual _hagent
    exact Nat.le_refl 0

theorem solo_not_bullTen :
    ¬ solitaryGrid.KsmdBullTen solitarySentience identityCoarsening
      SolitaryDesignatum.solo := by
  intro h
  rcases h.right with
    ⟨deed, reception, _hdeed, _hactual, hnotSame, _hsentient, hdel⟩
  exact hnotSame hdel

/-- A pratyekabuddha-shaped witness: Bull 9 can hold while Bull 10 fails. -/
theorem pratyekabuddha_countermodel :
    solitaryGrid.KsmdBullNine SolitaryDesignatum.solo ∧
      ¬ solitaryGrid.KsmdBullTen solitarySentience identityCoarsening
        SolitaryDesignatum.solo :=
  ⟨solo_bullNine, solo_not_bullTen⟩

/- ==============================================================================
   No grid-carried recovery of a unique stage boundary
============================================================================== -/

inductive StageDesignatum
  | fineFalse
  | fineTrue
  | call
  | response
  | falseOccurrence
  | trueOccurrence
  deriving DecidableEq

def stageOccurrence : OccurrenceReading StageDesignatum where
  occurrence
    | .falseOccurrence | .trueOccurrence => True
    | _ => False
  isBeing
    | .fineFalse | .fineTrue => True
    | _ => False
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .falseOccurrence => .fineFalse
    | .trueOccurrence => .fineTrue
    | d => d
  call
    | .falseOccurrence | .trueOccurrence => .call
    | d => d
  response
    | .falseOccurrence | .trueOccurrence => .response
    | d => d

/-- Two fine tags with identical grid data, as in the being-boundary witness. -/
def stageGrid : CoreReadings StageDesignatum Nat where
  occurrence := stageOccurrence
  response := {
    respondsTo := fun _ _ => some .response
  }
  placement := {
    grade := fun _ => 0
  }
  conditioning := {
    conditions := fun _ _ => True
  }

def stageMerge : stageGrid.StageScheme Unit where
  proj _ := ()

def stageSplit : stageGrid.StageScheme StageDesignatum where
  proj := id

theorem stageMerge_same_fiber :
    stageMerge.SameFiber
      StageDesignatum.fineFalse StageDesignatum.fineTrue :=
  rfl

theorem stageSplit_not_same_fiber :
    ¬ stageSplit.SameFiber
      StageDesignatum.fineFalse StageDesignatum.fineTrue := by
  intro h
  cases h

abbrev W := stageGrid.Weld

abbrev GridData : Type :=
  (StageDesignatum → StageDesignatum → Option StageDesignatum) ×
    (StageDesignatum → Nat) ×
      (W → W → Prop)

def gridData : GridData :=
  (stageGrid.respondsTo, stageGrid.grade, stageGrid.conditions)

def mergedBoundary (_p _q : StageDesignatum) : Prop := True

def splitBoundary (p q : StageDesignatum) : Prop := p = q

/-- The same grid data supports a merge and a split stage-coarsening. Holding
    either boundary as recovered from the grid is the uniform freeze. -/
theorem no_stage_boundary_recovery :
    ¬ ∃ recover : GridData → StageDesignatum → StageDesignatum → Prop,
        recover gridData = mergedBoundary ∧
        recover gridData = splitBoundary := by
  rintro ⟨recover, hmerge, hsplit⟩
  have hmerged :
      recover gridData .fineFalse .fineTrue := by
    rw [hmerge]
    exact True.intro
  have hsplitNot : ¬ recover gridData .fineFalse .fineTrue := by
    rw [hsplit]
    intro h
    cases h
  exact hsplitNot hmerged

end CorrelationsNegative

end KannoSoe
