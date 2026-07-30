/-
================================================================================
  KannoSoe.Doctrines.OtherPowerNegative
  Negative witnesses for regime/share polemics
================================================================================

The positive module types same-agent and cross-agent delivery as regimes over
the same act grammar. This sibling keeps the no-polemic clause honest: neither
regime determines reception share, and reception share does not recover the
regime.
-/

import KannoSoe.Doctrines.OtherPower

namespace KannoSoe

namespace OtherPowerNegative

open Grid.DirectedConvention

inductive Designatum
  | source
  | receiver
  | live
  | pole
  | response
  | sourceLiveOccurrence
  | sourcePoleOccurrence
  | receiverLiveOccurrence
  | receiverPoleOccurrence
deriving DecidableEq

namespace Being
abbrev source : Designatum := .source
abbrev receiver : Designatum := .receiver
end Being

namespace Call
abbrev live : Designatum := .live
abbrev pole : Designatum := .pole
end Call

namespace Response
abbrev response : Designatum := .response
end Response

def regimeOccurrence : OccurrenceReading Designatum where
  occurrence d :=
    d = .sourceLiveOccurrence ∨ d = .sourcePoleOccurrence ∨
      d = .receiverLiveOccurrence ∨ d = .receiverPoleOccurrence
  isBeing d := d = .source ∨ d = .receiver
  isCall d := d = .live ∨ d = .pole
  isResponse d := d = .response
  agent d :=
    match d with
    | .sourceLiveOccurrence | .sourcePoleOccurrence => .source
    | .receiverLiveOccurrence | .receiverPoleOccurrence => .receiver
    | _ => d
  call d :=
    match d with
    | .sourceLiveOccurrence | .receiverLiveOccurrence => .live
    | .sourcePoleOccurrence | .receiverPoleOccurrence => .pole
    | _ => d
  response d :=
    match d with
    | .sourceLiveOccurrence | .sourcePoleOccurrence
    | .receiverLiveOccurrence | .receiverPoleOccurrence => .response
    | _ => d

/-- Delivery is total; reception share is controlled only by the call. -/
def regimeShareGrid : CoreReadings Designatum Nat where
  occurrence := regimeOccurrence
  response := {
    respondsTo := fun b c =>
      if (b = .source ∨ b = .receiver) ∧ (c = .live ∨ c = .pole)
      then some .response
      else none
  }
  placement := {
    grade := fun d =>
      match d with
      | .sourceLiveOccurrence | .receiverLiveOccurrence => 1
      | _ => 0
  }
  conditioning := { conditions := fun _ _ => True }

def sameLiveDeed : regimeShareGrid.Weld :=
  ⟨.sourceLiveOccurrence, Or.inl rfl⟩

def sameLiveReception : regimeShareGrid.Weld :=
  sameLiveDeed

def samePoleReception : regimeShareGrid.Weld :=
  ⟨.sourcePoleOccurrence, Or.inr (Or.inl rfl)⟩

def crossLiveDeed : regimeShareGrid.Weld :=
  sameLiveDeed

def crossLiveReception : regimeShareGrid.Weld :=
  ⟨.receiverLiveOccurrence, Or.inr (Or.inr (Or.inl rfl))⟩

def crossPoleReception : regimeShareGrid.Weld :=
  ⟨.receiverPoleOccurrence, Or.inr (Or.inr (Or.inr rfl))⟩

theorem sameLiveLine :
    SameAgentDelivery regimeShareGrid sameLiveDeed sameLiveReception :=
  ⟨True.intro, rfl⟩

theorem samePoleLine :
    SameAgentDelivery regimeShareGrid sameLiveDeed samePoleReception :=
  ⟨True.intro, rfl⟩

theorem crossLiveLine :
    CrossAgentDelivery regimeShareGrid crossLiveDeed crossLiveReception := by
  constructor
  · exact True.intro
  · intro h
    cases h

theorem crossPoleLine :
    CrossAgentDelivery regimeShareGrid crossLiveDeed crossPoleReception := by
  constructor
  · exact True.intro
  · intro h
    cases h

/-- Cross-agent delivery and same-agent delivery each allow a live-share
    reception and a pole-class reception. The regime by itself therefore does
    not type the reception's share. -/
theorem regime_does_not_determine_share :
    (∃ deed reception,
      SameAgentDelivery regimeShareGrid deed reception ∧
        regimeShareGrid.Actual reception ∧
        ¬ AtBot (regimeShareGrid.share reception)) ∧
    (∃ deed reception,
      SameAgentDelivery regimeShareGrid deed reception ∧
        regimeShareGrid.Actual reception ∧
        AtBot (regimeShareGrid.share reception)) ∧
    (∃ deed reception,
      CrossAgentDelivery regimeShareGrid deed reception ∧
        regimeShareGrid.Actual reception ∧
        ¬ AtBot (regimeShareGrid.share reception)) ∧
    (∃ deed reception,
      CrossAgentDelivery regimeShareGrid deed reception ∧
        regimeShareGrid.Actual reception ∧
        AtBot (regimeShareGrid.share reception)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨sameLiveDeed, sameLiveReception, sameLiveLine, rfl, ?_⟩
    intro hbot
    exact Nat.not_succ_le_zero 0 hbot
  · refine ⟨sameLiveDeed, samePoleReception, samePoleLine, rfl, ?_⟩
    exact Nat.le_refl 0
  · refine ⟨crossLiveDeed, crossLiveReception, crossLiveLine, rfl, ?_⟩
    intro hbot
    exact Nat.not_succ_le_zero 0 hbot
  · refine ⟨crossLiveDeed, crossPoleReception, crossPoleLine, rfl, ?_⟩
    exact Nat.le_refl 0

/-- Equal reception share is compatible with both regimes, so the share value
    cannot recover whether the line was same-agent or cross-agent. -/
theorem share_does_not_determine_regime :
    ∃ sameDeed sameReception crossDeed crossReception,
      SameAgentDelivery regimeShareGrid sameDeed sameReception ∧
        CrossAgentDelivery regimeShareGrid crossDeed crossReception ∧
        regimeShareGrid.Actual sameReception ∧
        regimeShareGrid.Actual crossReception ∧
        regimeShareGrid.share sameReception =
          regimeShareGrid.share crossReception := by
  refine ⟨sameLiveDeed, sameLiveReception,
    crossLiveDeed, crossLiveReception, ?_⟩
  exact ⟨sameLiveLine, crossLiveLine, rfl, rfl, rfl⟩

end OtherPowerNegative

end KannoSoe
