import KannoSoe.Signature.Readings
import KannoSoe.Signature.Grid
import KannoSoe.Signature.SentienceConvention
import KannoSoe.Signature.BeingConvention
import KannoSoe.Signature.DirectionConvention
import KannoSoe.Signature.Models
import KannoSoe.Signature.Claims

/-!
Input-side assumption pins for the `Signature` layer.

This file is the compile-time tripwire for the system's input surface.
-/

namespace KannoSoe

namespace AssumptionLocalWitnesses

inductive DirectionCase
  | agent
  | falseCall
  | trueCall
  | response
  | falseOccurrence
  | trueOccurrence
  deriving DecidableEq

def directionOccurrence : OccurrenceReading DirectionCase where
  occurrence
    | .falseOccurrence | .trueOccurrence => True
    | _ => False
  isBeing d := d = .agent
  isCall d := d = .falseCall ∨ d = .trueCall
  isResponse d := d = .response
  agent
    | .falseOccurrence | .trueOccurrence => .agent
    | d => d
  call
    | .falseOccurrence => .falseCall
    | .trueOccurrence => .trueCall
    | d => d
  response
    | .falseOccurrence | .trueOccurrence => .response
    | d => d

abbrev DirectionW := directionOccurrence.Weld

def directionFalse : DirectionW := ⟨.falseOccurrence, True.intro⟩
def directionTrue : DirectionW := ⟨.trueOccurrence, True.intro⟩

def directionResponse : RespondsToReading DirectionCase where
  respondsTo b c :=
    match b, c with
    | .agent, .falseCall | .agent, .trueCall => some .response
    | _, _ => none

def directionPlacement : PlacementReading DirectionCase Nat where
  grade _ := 0

def directionForwardGrid : CoreReadings DirectionCase Nat where
  occurrence := directionOccurrence
  response := directionResponse
  placement := directionPlacement
  conditioning := {
    conditions := fun d₁ d₂ =>
      d₁ = .falseOccurrence ∧ d₂ = .trueOccurrence
  }

def directionBackwardGrid : CoreReadings DirectionCase Nat where
  occurrence := directionOccurrence
  response := directionResponse
  placement := directionPlacement
  conditioning := {
    conditions := fun d₁ d₂ =>
      d₁ = .trueOccurrence ∧ d₂ = .falseOccurrence
  }

theorem direction_conditionsEither_agrees (w₁ w₂ : DirectionW) :
    directionForwardGrid.ConditionsEither w₁ w₂ ↔
      directionBackwardGrid.ConditionsEither w₁ w₂ :=
  ⟨fun h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                   (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩),
   fun h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                   (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)⟩

theorem direction_conditions_disagree :
    directionForwardGrid.conditions directionFalse directionTrue ∧
      ¬ directionBackwardGrid.conditions directionFalse directionTrue := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro h
    cases h.left

theorem no_direction_recovery_from_conditionsEither :
    ¬ ∃ recover : (DirectionW → DirectionW → Prop) →
        (DirectionW → DirectionW → Prop),
        recover directionForwardGrid.ConditionsEither =
          directionForwardGrid.conditions ∧
        recover directionBackwardGrid.ConditionsEither =
          directionBackwardGrid.conditions := by
  rintro ⟨recover, hf, hb⟩
  have hsame :
      directionForwardGrid.ConditionsEither =
        directionBackwardGrid.ConditionsEither := by
    funext w₁ w₂
    exact propext (direction_conditionsEither_agrees w₁ w₂)
  have hcond :
      directionForwardGrid.conditions =
        directionBackwardGrid.conditions := by
    rw [← hf, hsame, hb]
  exact direction_conditions_disagree.right
    (hcond ▸ direction_conditions_disagree.left)

open Grid.DirectedConvention.BeingConvention

def partitionOccurrence : OccurrenceReading Bool where
  occurrence _ := True
  isBeing _ := True
  isCall _ := True
  isResponse _ := True
  agent := id
  call := id
  response := id

def partitionGrid : CoreReadings Bool Nat where
  occurrence := partitionOccurrence
  response := { respondsTo := fun _ c => some c }
  placement := { grade := fun _ => 0 }
  conditioning := { conditions := fun _ _ => True }

def partitionMerge : BeingCoarsening partitionGrid Unit where
  proj _ := ()

def partitionSplit : BeingCoarsening partitionGrid Bool where
  proj := id

theorem partition_merge_split_disagree :
    partitionMerge.SameFiber false true ∧
      ¬ partitionSplit.SameFiber false true := by
  constructor
  · rfl
  · intro h
    cases h

theorem nat_preorderBot_has_no_top :
    ¬ ∃ t : Nat, ∀ x : Nat, x ≼ t := by
  rintro ⟨t, htop⟩
  exact Nat.not_succ_le_self t (htop (Nat.succ t))

theorem signature_self_line_permitted :
    ∃ w : backslideGrid.Weld,
      Grid.DirectedConvention.LandsAt backslideGrid w w := by
  exact ⟨backslideWeld .gentle, True.intro, rfl⟩

end AssumptionLocalWitnesses

namespace InteriorDirectionNegative

inductive InteriorCase
  | agent
  | low
  | high
  | occurrence
  deriving DecidableEq

def occurrenceReading : OccurrenceReading InteriorCase where
  occurrence d := d = .occurrence
  isBeing d := d = .agent
  isCall d := d = .low
  isResponse d := d = .high
  agent
    | .occurrence => .agent
    | d => d
  call
    | .occurrence => .low
    | d => d
  response
    | .occurrence => .high
    | d => d

abbrev W := occurrenceReading.Weld

def callThenResponse : W := ⟨.occurrence, rfl⟩

def unorderedCRContent (_w : W) : Prop := True

def callResponseReading (w : W) : Prop :=
  w.call = .low

def responseCallReading (w : W) : Prop :=
  w.response = .low

theorem transposeCR_involutive :
    occurrenceReading.transposeCR.transposeCR = occurrenceReading :=
  OccurrenceReading.transposeCR_transposeCR occurrenceReading

theorem unorderedCRContent_transpose_invariant :
    unorderedCRContent callThenResponse ↔
      unorderedCRContent callThenResponse.transposeCR :=
  Iff.rfl

theorem transpose_swaps_readings :
    callThenResponse.transposeCR.call = callThenResponse.response :=
  rfl

theorem call_response_readings_disagree :
    callResponseReading callThenResponse ∧
      ¬ responseCallReading callThenResponse := by
  constructor
  · rfl
  · intro h
    cases h

theorem no_interior_direction_recovery :
    ¬ ∃ recover : (W → Prop) → W → Prop,
        recover unorderedCRContent = callResponseReading ∧
        recover unorderedCRContent = responseCallReading := by
  rintro ⟨recover, hcall, hresponse⟩
  have hcallHolds : recover unorderedCRContent callThenResponse := by
    rw [hcall]
    exact call_response_readings_disagree.left
  have hresponseNot : ¬ recover unorderedCRContent callThenResponse := by
    rw [hresponse]
    exact call_response_readings_disagree.right
  exact hresponseNot hcallHolds

end InteriorDirectionNegative

section AssumptionAnchors

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/- A.1 One carrier; occurrence and roles are readings. -/
#check OccurrenceReading -- proof
#check OccurrenceReading.Weld -- proof
#check RespondsToReading -- proof
#check PlacementReading -- proof
#check ConditionsReading -- proof
#check CoreReadings -- convenience
#check Grid.index -- proof
#check Grid.share -- proof
#check Grid.no_agent_recovery_of_field_collision -- witness
example (w : G.Weld) : G.index w = w.agent := rfl -- proof
example (w : G.Weld) :
    G.share w = G.grade w.1 := rfl -- proof

/- A.2 Nothing self-indexed is stored. -/
#check Config -- proof
#check Config.tendency -- proof
#check Grid.rePitch -- proof
example (c : Config Contrib) : c = ⟨c.tendency⟩ := rfl -- proof
example (before before' : Config Contrib) (received : G.Weld) :
    G.rePitch before received = G.rePitch before' received := rfl -- proof
example (before : Config Contrib) (received : G.Weld) :
    (G.rePitch before received).tendency = G.share received := rfl -- proof

/- A.3 Self-pole index as live share. -/
#check Grid.HasSelfPoleIndex -- proof
#check Grid.selfPoleIndex_eq_agent_of_hasSelfPoleIndex -- proof
#check Grid.no_self_pole_index_of_atBot -- proof
example (w : G.Weld) :
    G.HasSelfPoleIndex w ↔ ¬ AtBot (G.share w) := Iff.rfl -- proof

/- A.4 Sentience and share are orthogonal per occurrence. -/
#check SentienceReading -- proof
#check Grid.SentienceReading -- compatibility
#check Grid.SentientAct -- proof
#check Grid.InsentientAct -- proof
#check Grid.OrdinaryAct -- proof
#check Grid.TerminusAct -- proof
#check Grid.InsentientAppropriation -- proof
#check Grid.StoneAct -- proof
#check sentience_share_square_inhabited -- witness

/- A.5 Self-lines are permitted. -/
#check Grid.conditions -- proof
#check Grid.DirectedConvention.DeliveredTo -- proof
#check Grid.DirectedConvention.LandsAt -- proof
#check AssumptionLocalWitnesses.signature_self_line_permitted -- witness

/- B.1 Direction is supplied by readings. -/
#check ConditionsReading.transpose -- witness
#check OccurrenceReading.transposeCR -- witness
#check OccurrenceReading.Weld.transposeCR -- witness
#check Grid.ConditionsEither -- proof
#check Grid.conditionsEither_symm -- proof
#check Grid.transpose -- witness
#check Grid.transpose_conditionsEither_iff -- witness
#check AssumptionLocalWitnesses.no_direction_recovery_from_conditionsEither -- witness
#check InteriorDirectionNegative.no_interior_direction_recovery -- witness

/- B.2 No PreorderTop. -/
#check PreorderBot -- proof
#check AtBot -- proof
#check AssumptionLocalWitnesses.nat_preorderBot_has_no_top -- witness

/- B.3 No privileged person-partition. -/
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening -- proof
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber -- proof
#check Grid.DirectedConvention.BeingConvention.BeingCoarsening.SameFiber -- proof
#check AssumptionLocalWitnesses.partition_merge_split_disagree -- witness

/- B.4 Direction resolution is display, not signature furniture. -/
#check Grid.DirectedConvention.DirectionCoarsening -- proof
#check Grid.DirectedConvention.DirectionCoarsening.SameTick -- proof
#check Grid.DirectedConvention.DirectionCoarsening.ResolutionBounded -- proof

/- B.5 Contribution values are display, not operational tokens. -/
#check Grid.share_eq_grade_check -- proof
#check AtBot -- proof
#check OrderEq -- proof
#check Grid.Terminus -- proof

/- B.11 No sentience recovery from the other readings. -/
#check Grid.actual_weld_readings_split -- proof
#check Grid.no_sentience_recovery -- witness
#check Grid.SentienceReading.allSentient -- witness
#check Grid.SentienceReading.allInsentient -- witness

/- C.1 Hand-rolled order classes. -/
#check Preorder -- proof
#check PreorderBot -- proof
#check shareBot -- proof
#check shareBot_le -- proof

/- C.4 Model witnesses are illustrative. -/
#check clockGrid -- witness
#check registerClockGrid -- witness
#check registerClock_insentient_proficient -- witness
#check clock_pole_readings_split -- witness
#check registerClock_rung_readings_split -- witness
#check rigid_terminus_vacuous -- witness
#check adaptive_liveTerminus -- witness
#check sentience_share_square_inhabited -- witness
#check registerClock_macro_selfConditioning -- witness

end AssumptionAnchors

end KannoSoe
