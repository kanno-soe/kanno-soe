/-
================================================================================
  KannoSoe.Doctrines.OtherPower
  Other-power as delivery-regime, not a second act grammar
================================================================================

Reception is a deed either way. Tariki names a delivery-regime, not a second
act-grammar: Dogen's passive "being verified" reading is modeled by ordinary
reception-welds whose delivery line is supplied from elsewhere. No theorem in
this module ranks self-power and other-power against one another; that
no-polemic clause is part of the model design.

The checked surface uses only existing predicates: `Actual`, `share`,
`conditions`/`DeliveredTo`, `ResponseInvariant`, and `HasShareDropLanding`.
-/

import KannoSoe.Consequences.Basic

namespace KannoSoe

namespace Grid
namespace DirectedConvention

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

omit [PreorderBot Contrib] in
/-- Changing only the delivery relation does not change the reception's grade,
    share, or actuality. The sower's identity is delivery data; reception
    typing reads the weld itself. -/
theorem reception_typing_ignores_sower
    (conditions₁ conditions₂ : Designatum -> Designatum -> Prop)
    (reception : G.Weld) :
    (G.withConditions conditions₁).grade
        reception.val =
      (G.withConditions conditions₂).grade
        reception.val ∧
    (G.withConditions conditions₁).share reception =
      (G.withConditions conditions₂).share reception ∧
    ((G.withConditions conditions₁).Actual reception ↔
      (G.withConditions conditions₂).Actual reception) :=
  ⟨G.grade_independent_of_conditions conditions₁ conditions₂
      reception.val,
    G.share_independent_of_conditions conditions₁ conditions₂ reception,
    Iff.rfl⟩

omit [PreorderBot Contrib] in
/-- Same-agent lines and cross-agent lines both fill the ordinary reach-back
    relation once the model supplies the delivery line. The actuality
    hypothesis records that the reception is a deed; the conclusion is just the
    shared first conjunct of the two delivery-regime predicates. -/
theorem ksmdReachBack_filled_either_regime
    {deed reception : G.Weld} (_hactual : G.Actual reception) :
    (SameAgentDelivery G deed reception →
        KsmdReachBackFull G deed reception) ∧
      (CrossAgentDelivery G deed reception →
        KsmdReachBackFull G deed reception) :=
  ⟨fun h => h.left, fun h => h.left⟩

/-- Other-power line: a cross-agent delivery line read in KannoSoe vocabulary. -/
abbrev KsmdTarikiLine (deed reception : G.Weld) : Prop :=
  CrossAgentDelivery G deed reception

/-- Self-power line: a same-agent delivery line read in KannoSoe vocabulary. -/
abbrev KsmdJirikiLine (deed reception : G.Weld) : Prop :=
  SameAgentDelivery G deed reception

end DirectedConvention
end Grid

/- ==============================================================================
   Tariki perfected limit model
============================================================================== -/

namespace TarikiCase

open Grid
open Grid.DirectedConvention

inductive Designatum
  | invoker
  | name
  | heard
  | chime
  | receive
  | nameOccurrence
  | invokerOccurrence
deriving DecidableEq

namespace Being
abbrev invoker : Designatum := .invoker
abbrev name : Designatum := .name
end Being

namespace Call
abbrev heard : Designatum := .heard
end Call

namespace Response
abbrev chime : Designatum := .chime
abbrev receive : Designatum := .receive
end Response

def tarikiOccurrence : OccurrenceReading Designatum where
  occurrence d := d = .nameOccurrence ∨ d = .invokerOccurrence
  isBeing d := d = .name ∨ d = .invoker
  isCall d := d = .heard
  isResponse d := d = .chime ∨ d = .receive
  agent d :=
    match d with
    | .nameOccurrence => .name
    | .invokerOccurrence => .invoker
    | _ => d
  call d :=
    match d with
    | .nameOccurrence | .invokerOccurrence => .heard
    | _ => d
  response d :=
    match d with
    | .nameOccurrence => .chime
    | .invokerOccurrence => .receive
    | _ => d

/-- A two-being model: the name chimes independent of the call, the invoker
    receives, and delivery sends the name's weld to every invoker reception.
    This checks grammar only; it asserts no Pure Land doctrine and no ranking
    of regimes. -/
def tarikiGrid : CoreReadings Designatum Nat where
  occurrence := tarikiOccurrence
  response := {
    respondsTo := fun b _ =>
      match b with
      | .name => some .chime
      | .invoker => some .receive
      | _ => none
  }
  placement := {
    grade := fun d =>
      match d with
      | .invokerOccurrence => 1
      | _ => 0
  }
  conditioning := {
    conditions := fun deed reception =>
      deed = .nameOccurrence ∧ reception = .invokerOccurrence
  }

def liveBefore : Config Nat :=
  { tendency := 2 }

/-- The fixed call-source weld. Its call is still carried by the weld; a
    quotation severed from its call would be quotable, never gradeable. -/
def nameWeld : tarikiGrid.Weld :=
  ⟨.nameOccurrence, Or.inl rfl⟩

def invokerReception : tarikiGrid.Weld :=
  ⟨.invokerOccurrence, Or.inr rfl⟩

theorem nameWeld_actual :
    tarikiGrid.Actual nameWeld :=
  rfl

theorem invokerReception_actual :
    tarikiGrid.Actual invokerReception :=
  rfl

theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 1 h

theorem name_responseInvariant :
    tarikiGrid.ResponseInvariant Being.name := by
  intro c₁ c₂ r₁ r₂ h₁ h₂
  change some .chime = some r₁ at h₁
  change some .chime = some r₂ at h₂
  exact Option.some.inj (h₁.symm.trans h₂)

theorem name_actualAgentInhabited :
    tarikiGrid.ActualAgentInhabited Being.name :=
  ⟨nameWeld, rfl, rfl⟩

theorem name_share_bot
    (w : tarikiGrid.Weld) (hagent : w.agent = Being.name) :
    tarikiGrid.share w = 0 := by
  rcases w with ⟨d, hd⟩
  change d = .nameOccurrence ∨ d = .invokerOccurrence at hd
  rcases hd with rfl | rfl
  · rfl
  · cases hagent

theorem name_object_axis_entire
    (reception : tarikiGrid.Weld) (hagent : reception.agent = Being.invoker) :
    Grid.DirectedConvention.DeliveredTo tarikiGrid nameWeld reception :=
  by
    rcases reception with ⟨d, hd⟩
    change d = .nameOccurrence ∨ d = .invokerOccurrence at hd
    rcases hd with rfl | rfl
    · cases hagent
    · change
        Designatum.nameOccurrence = Designatum.nameOccurrence ∧
          Designatum.invokerOccurrence = Designatum.invokerOccurrence
      exact ⟨rfl, rfl⟩

/-- The fixed-call source lands at every actual invoker reception as a
    share-drop from `liveBefore`. This is the effective corner opposite
    `OrthogonalityNegative`: non-adaptivity does not by itself decide
    effectiveness. -/
theorem universal_fixed_call_lands_without_reading
    (reception : tarikiGrid.Weld)
    (hagent : reception.agent = Being.invoker)
    (hactual : tarikiGrid.Actual reception) :
    HasShareDropLanding tarikiGrid liveBefore nameWeld := by
  refine ⟨reception,
    ⟨⟨name_object_axis_entire reception hagent, hactual⟩, ?_⟩⟩
  rcases reception with ⟨d, hd⟩
  change d = .nameOccurrence ∨ d = .invokerOccurrence at hd
  rcases hd with rfl | rfl
  · cases hagent
  · constructor
    · show (1 : Nat) ≤ 2
      decide
    · show ¬ (2 : Nat) ≤ 1
      decide

theorem name_to_invoker_tarikiLine :
    KsmdTarikiLine tarikiGrid nameWeld invokerReception := by
  constructor
  · exact name_object_axis_entire invokerReception rfl
  · intro h
    cases h

theorem fixed_call_landing_witness :
    HasShareDropLanding tarikiGrid liveBefore nameWeld :=
  universal_fixed_call_lands_without_reading
    invokerReception rfl invokerReception_actual

/-- The invoker's reception is an ordinary actual deed with ordinary live
    share, even though the delivery-regime is cross-agent. -/
theorem invoker_reception_is_deed :
    tarikiGrid.Actual invokerReception ∧
      tarikiGrid.share invokerReception = 1 ∧
        tarikiGrid.HasSelfPoleIndex invokerReception := by
  constructor
  · exact invokerReception_actual
  · constructor
    · rfl
    · intro hbot
      exact Nat.not_succ_le_zero 0 hbot

end TarikiCase

end KannoSoe
