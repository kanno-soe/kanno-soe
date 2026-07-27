/-
================================================================================
  KannoSoe.Signature.Models
  Concrete one-carrier reading packages
================================================================================
-/

import KannoSoe.Signature.BeingConvention

namespace KannoSoe

section Preview

instance : PreorderBot Nat where
  le       := Nat.le
  le_refl  := Nat.le_refl
  le_trans := fun h1 h2 => Nat.le_trans h1 h2
  bot      := 0
  bot_le   := Nat.zero_le

/- --------------------------------------------------------------------------
   Clock case
-------------------------------------------------------------------------- -/

/-- One carrier for the clock display. -/
inductive ClockCase
  | rigid
  | adaptive
  | present
  | absent
  | chime
  | adaptivePresentOccurrence
  deriving DecidableEq

namespace Clock
abbrev rigid : ClockCase := .rigid
abbrev adaptive : ClockCase := .adaptive
end Clock

namespace Listener
abbrev present : ClockCase := .present
abbrev absent : ClockCase := .absent
end Listener

namespace Chime
abbrev chime : ClockCase := .chime
end Chime

def clockOccurrence : OccurrenceReading ClockCase where
  occurrence d := d = .adaptivePresentOccurrence
  isBeing d := d = .rigid ∨ d = .adaptive
  isCall d := d = .present ∨ d = .absent
  isResponse d := d = .chime
  agent
    | .adaptivePresentOccurrence => .adaptive
    | d => d
  call
    | .adaptivePresentOccurrence => .present
    | d => d
  response
    | .adaptivePresentOccurrence => .chime
    | d => d

def clockRespondsTo : RespondsToReading ClockCase where
  respondsTo b c :=
    match b, c with
    | .adaptive, .present => some .chime
    | _, _ => none

def clockPlacement : PlacementReading ClockCase Nat where
  grade _ := 0

def clockConditioning : ConditionsReading ClockCase where
  conditions _ _ := False

def clockGrid : CoreReadings ClockCase Nat where
  occurrence := clockOccurrence
  response := clockRespondsTo
  placement := clockPlacement
  conditioning := clockConditioning

def clockAdaptivePresent : clockGrid.Weld :=
  ⟨.adaptivePresentOccurrence, rfl⟩

theorem adaptive_is_terminus : clockGrid.Terminus Clock.adaptive := by
  intro w _hactual _hagent
  exact Nat.le_refl 0

theorem rigid_terminus_vacuous :
    clockGrid.Terminus Clock.rigid ∧
      ¬ clockGrid.ActualAgentInhabited Clock.rigid := by
  constructor
  · intro w _hactual _hagent
    exact Nat.le_refl 0
  · rintro ⟨w, _hactual, hagent⟩
    rcases w with ⟨d, hd⟩
    change clockOccurrence.agent d = Clock.rigid at hagent
    change clockOccurrence.occurrence d at hd
    subst d
    cases hagent

theorem adaptive_liveTerminus : clockGrid.LiveTerminus Clock.adaptive :=
  ⟨⟨clockAdaptivePresent, rfl, rfl⟩, adaptive_is_terminus⟩

theorem clock_pole_readings_split :
    clockGrid.StoneAct
        (Grid.SentienceReading.allInsentient clockGrid)
        clockAdaptivePresent ∧
      clockGrid.TerminusAct
        (Grid.SentienceReading.allSentient clockGrid)
        clockAdaptivePresent := by
  have hsplit := clockGrid.actual_weld_readings_split
    clockAdaptivePresent rfl
  have hbot : AtBot (clockGrid.share clockAdaptivePresent) :=
    clockGrid.atBot_of_terminus_response adaptive_is_terminus rfl
  exact ⟨⟨hsplit.right, hbot⟩, ⟨hsplit.left, hbot⟩⟩

/- --------------------------------------------------------------------------
   Inhabited sentience/share square
-------------------------------------------------------------------------- -/

inductive SquareCase
  | agent
  | ordinary
  | terminus
  | insentientAppropriation
  | stone
  | response
  | ordinaryOccurrence
  | terminusOccurrence
  | insentientAppropriationOccurrence
  | stoneOccurrence
  deriving DecidableEq

abbrev SquareCall := SquareCase

def squareOccurrenceOfCall : SquareCase → SquareCase
  | .ordinary => .ordinaryOccurrence
  | .terminus => .terminusOccurrence
  | .insentientAppropriation => .insentientAppropriationOccurrence
  | .stone => .stoneOccurrence
  | _ => .ordinaryOccurrence

def squareCallOfOccurrence : SquareCase → SquareCase
  | .ordinaryOccurrence => .ordinary
  | .terminusOccurrence => .terminus
  | .insentientAppropriationOccurrence => .insentientAppropriation
  | .stoneOccurrence => .stone
  | d => d

def squareOccurrence : OccurrenceReading SquareCase where
  occurrence
    | .ordinaryOccurrence
    | .terminusOccurrence
    | .insentientAppropriationOccurrence
    | .stoneOccurrence => True
    | _ => False
  isBeing d := d = .agent
  isCall d :=
    d = .ordinary ∨ d = .terminus ∨
      d = .insentientAppropriation ∨ d = .stone
  isResponse d := d = .response
  agent
    | .ordinaryOccurrence
    | .terminusOccurrence
    | .insentientAppropriationOccurrence
    | .stoneOccurrence => .agent
    | d => d
  call := squareCallOfOccurrence
  response
    | .ordinaryOccurrence
    | .terminusOccurrence
    | .insentientAppropriationOccurrence
    | .stoneOccurrence => .response
    | d => d

def sentienceSquareGrid : CoreReadings SquareCase Nat where
  occurrence := squareOccurrence
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .agent, .ordinary
      | .agent, .terminus
      | .agent, .insentientAppropriation
      | .agent, .stone => some .response
      | _, _ => none
  }
  placement := {
    grade := fun d =>
      match d with
      | .ordinaryOccurrence | .insentientAppropriationOccurrence => 1
      | _ => 0
  }
  conditioning := { conditions := fun _ _ => True }

def sentienceSquareReading : sentienceSquareGrid.SentienceReading where
  sentient d :=
    match d with
    | .ordinaryOccurrence | .terminusOccurrence => True
    | _ => False

def squareWeld (c : SquareCall) : sentienceSquareGrid.Weld := by
  refine ⟨squareOccurrenceOfCall c, ?_⟩
  cases c <;> trivial

theorem square_ordinary :
    sentienceSquareGrid.OrdinaryAct sentienceSquareReading
      (squareWeld .ordinary) := by
  refine ⟨⟨rfl, True.intro⟩, ?_⟩
  exact Nat.not_succ_le_zero 0

theorem square_terminus :
    sentienceSquareGrid.TerminusAct sentienceSquareReading
      (squareWeld .terminus) :=
  ⟨⟨rfl, True.intro⟩, Nat.le_refl 0⟩

theorem square_insentientAppropriation :
    sentienceSquareGrid.InsentientAppropriation sentienceSquareReading
      (squareWeld .insentientAppropriation) := by
  refine ⟨⟨rfl, fun h => h⟩, ?_⟩
  exact Nat.not_succ_le_zero 0

theorem square_stone :
    sentienceSquareGrid.StoneAct sentienceSquareReading
      (squareWeld .stone) :=
  ⟨⟨rfl, fun h => h⟩, Nat.le_refl 0⟩

theorem sentience_share_square_inhabited :
    (∃ w, sentienceSquareGrid.OrdinaryAct sentienceSquareReading w) ∧
      (∃ w, sentienceSquareGrid.TerminusAct sentienceSquareReading w) ∧
      (∃ w, sentienceSquareGrid.InsentientAppropriation
        sentienceSquareReading w) ∧
      (∃ w, sentienceSquareGrid.StoneAct sentienceSquareReading w) :=
  ⟨⟨squareWeld .ordinary, square_ordinary⟩,
   ⟨squareWeld .terminus, square_terminus⟩,
   ⟨squareWeld .insentientAppropriation, square_insentientAppropriation⟩,
   ⟨squareWeld .stone, square_stone⟩⟩

/- --------------------------------------------------------------------------
   Register clock
-------------------------------------------------------------------------- -/

inductive RegisterCase
  | register (n : Nat)
  | tick
  | result (n : Nat)
  | occurrence (n : Nat)
  deriving DecidableEq

def registerOccurrence : OccurrenceReading RegisterCase where
  occurrence
    | .occurrence _ => True
    | _ => False
  isBeing
    | .register _ => True
    | _ => False
  isCall d := d = .tick
  isResponse
    | .result _ => True
    | _ => False
  agent
    | .occurrence n => .register n
    | d => d
  call
    | .occurrence _ => .tick
    | d => d
  response
    | .occurrence n => .result (n + 1)
    | d => d

def registerClockGrid : CoreReadings RegisterCase Nat where
  occurrence := registerOccurrence
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .register n, .tick => some (.result (n + 1))
      | _, _ => none
  }
  placement := {
    grade := fun d =>
      match d with
      | .occurrence n => n
      | _ => 0
  }
  conditioning := {
    conditions := fun deed reception =>
      match deed, reception with
      | .occurrence n, .occurrence m => m = n + 1
      | _, _ => False
  }

def registerWeld (n : Nat) : registerClockGrid.Weld :=
  ⟨.occurrence n, True.intro⟩

def registerClockCoarsening :
    Grid.DirectedConvention.BeingConvention.BeingCoarsening
      registerClockGrid Unit where
  proj _ := ()

theorem registerClock_macro_actualFiberInhabited :
    registerClockCoarsening.ActualFiberInhabited () :=
  ⟨registerWeld 0, rfl, rfl⟩

theorem registerClock_macro_not_sentientTag_insentient :
    ¬ registerClockCoarsening.SentientTag
        (Grid.SentienceReading.allInsentient registerClockGrid) () :=
  registerClockCoarsening.allInsentient_not_sentientTag ()

theorem registerClock_macro_not_stoneTag_insentient :
    ¬ registerClockCoarsening.StoneTag
        (Grid.SentienceReading.allInsentient registerClockGrid) () := by
  intro hstone
  have hbot := (hstone.right (registerWeld 2) rfl rfl).right
  exact (by decide : ¬ (2 : Nat) ≤ 0) hbot

theorem registerClock_macro_patchy :
    registerClockCoarsening.Patchy () := by
  constructor
  · intro hpole
    have hbot := hpole (registerWeld 2) rfl rfl
    exact (by decide : ¬ (2 : Nat) ≤ 0) hbot
  · intro hselfApt
    have hlive := hselfApt (registerWeld 0) rfl rfl
    exact hlive (Nat.le_refl 0)

theorem registerClock_macro_selfConditioning :
    registerClockCoarsening.SelfConditioningTag () := by
  refine ⟨registerWeld 0, registerWeld 1, rfl, rfl, rfl, ?_⟩
  rfl

theorem registerClock_insentient_proficient :
    ¬ registerClockCoarsening.SentientTag
        (Grid.SentienceReading.allInsentient registerClockGrid) () ∧
      registerClockCoarsening.ActualFiberInhabited () ∧
      registerClockCoarsening.SelfConditioningTag () ∧
      registerClockCoarsening.Patchy () :=
  ⟨registerClock_macro_not_sentientTag_insentient,
    registerClock_macro_actualFiberInhabited,
    registerClock_macro_selfConditioning,
    registerClock_macro_patchy⟩

theorem registerClock_rung_readings_split :
    registerClockGrid.InsentientAppropriation
        (Grid.SentienceReading.allInsentient registerClockGrid)
        (registerWeld 2) ∧
      registerClockGrid.OrdinaryAct
        (Grid.SentienceReading.allSentient registerClockGrid)
        (registerWeld 2) := by
  have hsplit := registerClockGrid.actual_weld_readings_split
    (registerWeld 2) rfl
  have hlive : registerClockGrid.HasSelfPoleIndex (registerWeld 2) := by
    exact (by decide : ¬ (2 : Nat) ≤ 0)
  exact ⟨⟨hsplit.right, hlive⟩, ⟨hsplit.left, hlive⟩⟩

/- --------------------------------------------------------------------------
   Source and receiver
-------------------------------------------------------------------------- -/

inductive SourceReceiverCase
  | clock
  | receiver
  | call
  | response
  | clockOccurrence
  | receiverOccurrence
  deriving DecidableEq

abbrev SourceReceiver := SourceReceiverCase

namespace SourceReceiver
abbrev clock : SourceReceiverCase := .clock
abbrev receiver : SourceReceiverCase := .receiver
end SourceReceiver

def sourceReceiverOccurrence : OccurrenceReading SourceReceiverCase where
  occurrence
    | .clockOccurrence | .receiverOccurrence => True
    | _ => False
  isBeing d := d = .clock ∨ d = .receiver
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .clockOccurrence => .clock
    | .receiverOccurrence => .receiver
    | d => d
  call
    | .clockOccurrence | .receiverOccurrence => .call
    | d => d
  response
    | .clockOccurrence | .receiverOccurrence => .response
    | d => d

def sourceReceiverGrid : CoreReadings SourceReceiverCase Nat where
  occurrence := sourceReceiverOccurrence
  response := {
    respondsTo := fun b c =>
      if (b = .clock ∨ b = .receiver) ∧ c = .call
      then some .response
      else none
  }
  placement := {
    grade := fun d =>
      match d with
      | .receiverOccurrence => 1
      | _ => 0
  }
  conditioning := {
    conditions := fun deed reception =>
      deed = .clockOccurrence ∧ reception = .receiverOccurrence
  }

def sourceReceiverCoarsening :
    Grid.DirectedConvention.BeingConvention.BeingCoarsening
      sourceReceiverGrid SourceReceiver :=
  Grid.DirectedConvention.BeingConvention.BeingCoarsening.id sourceReceiverGrid

def sourceReceiverReading : sourceReceiverGrid.SentienceReading where
  sentient d := d = .receiverOccurrence

def sourceReceiverDeed : sourceReceiverGrid.Weld :=
  ⟨.clockOccurrence, True.intro⟩

def sourceReceiverReception : sourceReceiverGrid.Weld :=
  ⟨.receiverOccurrence, True.intro⟩

def sourceReceiverBefore : Config Nat := { tendency := 5 }

theorem insentient_source_shareDropLanding :
    ¬ sourceReceiverCoarsening.SentientTag sourceReceiverReading
        SourceReceiver.clock ∧
      sourceReceiverCoarsening.SentientTag sourceReceiverReading
        SourceReceiver.receiver ∧
      Grid.DirectedConvention.LandsWithShareDrop sourceReceiverGrid
        sourceReceiverBefore sourceReceiverDeed sourceReceiverReception := by
  constructor
  · rintro ⟨w, ⟨_hactual, hmarked⟩, hfiber⟩
    rcases w with ⟨d, hd⟩
    change d = SourceReceiverCase.receiverOccurrence at hmarked
    subst d
    cases hfiber
  · constructor
    · exact ⟨sourceReceiverReception, ⟨rfl, rfl⟩, rfl⟩
    · refine ⟨⟨?_, rfl⟩, ?_⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨(by decide : (1 : Nat) ≤ 5),
          (by decide : ¬ (5 : Nat) ≤ 1)⟩

/- --------------------------------------------------------------------------
   Backsliding
-------------------------------------------------------------------------- -/

inductive BackslideCase
  | agent
  | gentle
  | harsh
  | response
  | gentleOccurrence
  | harshOccurrence
  deriving DecidableEq

abbrev Cue := BackslideCase

def backslideOccurrence : OccurrenceReading BackslideCase where
  occurrence
    | .gentleOccurrence | .harshOccurrence => True
    | _ => False
  isBeing d := d = .agent
  isCall d := d = .gentle ∨ d = .harsh
  isResponse d := d = .response
  agent
    | .gentleOccurrence | .harshOccurrence => .agent
    | d => d
  call
    | .gentleOccurrence => .gentle
    | .harshOccurrence => .harsh
    | d => d
  response
    | .gentleOccurrence | .harshOccurrence => .response
    | d => d

def backslideGrid : CoreReadings BackslideCase Nat where
  occurrence := backslideOccurrence
  response := {
    respondsTo := fun b c =>
      if b = .agent ∧ (c = .gentle ∨ c = .harsh)
      then some .response
      else none
  }
  placement := {
    grade := fun d =>
      match d with
      | .harshOccurrence => 5
      | _ => 0
  }
  conditioning := { conditions := fun _ _ => True }

def backslideWeld (c : Cue) : backslideGrid.Weld := by
  cases c with
  | gentle => exact ⟨.gentleOccurrence, True.intro⟩
  | harsh => exact ⟨.harshOccurrence, True.intro⟩
  | _ => exact ⟨.gentleOccurrence, True.intro⟩

/- --------------------------------------------------------------------------
   Placement and share collisions
-------------------------------------------------------------------------- -/

inductive GradingCollisionCase
  | left
  | right
  | call
  | response
  | leftOccurrence
  | rightOccurrence
  deriving DecidableEq

abbrev GradingCollisionBeing := GradingCollisionCase

def gradingCollisionOccurrence : OccurrenceReading GradingCollisionCase where
  occurrence
    | .leftOccurrence | .rightOccurrence => True
    | _ => False
  isBeing d := d = .left ∨ d = .right
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .leftOccurrence => .left
    | .rightOccurrence => .right
    | d => d
  call
    | .leftOccurrence | .rightOccurrence => .call
    | d => d
  response
    | .leftOccurrence | .rightOccurrence => .response
    | d => d

def gradingCollisionGrid : CoreReadings GradingCollisionCase Nat where
  occurrence := gradingCollisionOccurrence
  response := {
    respondsTo := fun b c =>
      if (b = .left ∨ b = .right) ∧ c = .call
      then some .response
      else none
  }
  placement := {
    grade := fun d =>
      match d with
      | .leftOccurrence => 5
      | _ => 0
  }
  conditioning := { conditions := fun _ _ => True }

def gradingCollisionLeft : gradingCollisionGrid.Weld :=
  ⟨.leftOccurrence, True.intro⟩

def gradingCollisionRight : gradingCollisionGrid.Weld :=
  ⟨.rightOccurrence, True.intro⟩

inductive ShareCollisionCase
  | left
  | right
  | call
  | response
  | leftOccurrence
  | rightOccurrence
  deriving DecidableEq

abbrev ShareCollisionBeing := ShareCollisionCase

def shareCollisionOccurrence : OccurrenceReading ShareCollisionCase where
  occurrence
    | .leftOccurrence | .rightOccurrence => True
    | _ => False
  isBeing d := d = .left ∨ d = .right
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .leftOccurrence => .left
    | .rightOccurrence => .right
    | d => d
  call
    | .leftOccurrence | .rightOccurrence => .call
    | d => d
  response
    | .leftOccurrence | .rightOccurrence => .response
    | d => d

def shareCollisionGrid : CoreReadings ShareCollisionCase Nat where
  occurrence := shareCollisionOccurrence
  response := {
    respondsTo := fun b c =>
      if (b = .left ∨ b = .right) ∧ c = .call
      then some .response
      else none
  }
  placement := {
    grade := fun d =>
      match d with
      | .leftOccurrence | .rightOccurrence => 3
      | _ => 0
  }
  conditioning := { conditions := fun _ _ => True }

def shareCollisionLeft : shareCollisionGrid.Weld :=
  ⟨.leftOccurrence, True.intro⟩

def shareCollisionRight : shareCollisionGrid.Weld :=
  ⟨.rightOccurrence, True.intro⟩

end Preview

end KannoSoe
