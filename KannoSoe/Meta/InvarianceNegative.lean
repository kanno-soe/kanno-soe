/-
================================================================================
  KannoSoe.Meta.InvarianceNegative
  Countermodels for invariance and recovery claims
================================================================================

Reading and motivation: Identification/Commentary.lean, C.3.
-/

import KannoSoe.Meta.Invariance

namespace KannoSoe

/- ==========================================================================
   Equality with a chosen bottom token does not transport
============================================================================ -/

namespace InvarianceNegative

inductive TwoBottom
  | chosen
  | other

instance : PreorderBot TwoBottom where
  le := fun _ _ => True
  le_refl := fun _ => True.intro
  le_trans := fun _ _ => True.intro
  bot := .chosen
  bot_le := fun _ => True.intro

instance : PreorderBot Unit where
  le := fun _ _ => True
  le_refl := fun _ => True.intro
  le_trans := fun _ _ => True.intro
  bot := ()
  bot_le := fun _ => True.intro

def mergeToUnit : DisplayReparam TwoBottom Unit where
  toFun _ := ()
  le_iff _ _ := ⟨fun _ => True.intro, fun _ => True.intro⟩
  atBot_bot := True.intro

def unitOccurrence : OccurrenceReading Unit where
  occurrence _ := True
  isBeing _ := True
  isCall _ := True
  isResponse _ := True
  agent := id
  call := id
  response := id

def twoBottomGrid : CoreReadings Unit TwoBottom where
  occurrence := unitOccurrence
  response := { respondsTo := fun _ _ => some () }
  placement := { grade := fun _ => .other }
  conditioning := { conditions := fun _ _ => False }

def twoBottomWeld : twoBottomGrid.Weld :=
  ⟨(), True.intro⟩

/-- The retired equality-token terminus, retained only as a counterexample.
    The system predicate uses the pole-class `AtBot`. -/
def OldEqTerminus {Designatum Contrib : Type} [PreorderBot Contrib]
    (G : CoreReadings Designatum Contrib) (b : Designatum) : Prop :=
  ∀ w : G.Weld, G.Actual w → w.agent = b → G.share w = shareBot

theorem twoBottomGrid_terminus : twoBottomGrid.Terminus () := by
  intro _w _hactual _hagent
  exact True.intro

theorem not_oldEqTerminus_twoBottomGrid :
    ¬ OldEqTerminus twoBottomGrid () := by
  intro h
  have hbad : TwoBottom.other = TwoBottom.chosen :=
    h twoBottomWeld rfl rfl
  cases hbad

theorem oldEqTerminus_map_mergeToUnit :
    OldEqTerminus (twoBottomGrid.map mergeToUnit) () := by
  intro _w _hactual _hagent
  rfl

/-- Pole-class terminus transports, whereas equality with one selected bottom
    representative does not. -/
theorem oldEqTerminus_not_invariant :
    ((twoBottomGrid.map mergeToUnit).Terminus () ↔
        twoBottomGrid.Terminus ()) ∧
      OldEqTerminus (twoBottomGrid.map mergeToUnit) () ∧
      ¬ OldEqTerminus twoBottomGrid () :=
  ⟨Grid.map_terminus_iff twoBottomGrid mergeToUnit (),
    oldEqTerminus_map_mergeToUnit,
    not_oldEqTerminus_twoBottomGrid⟩

end InvarianceNegative

/- ==========================================================================
   Configuration leak witnesses: honest limits of non-storage
============================================================================ -/

namespace ConfigLeakWitness

/-- In the register clock, re-pitching exposes the received occurrence's
    register number. This is a model-specific information-flow fact, not a
    typed agent field stored in `Config`. -/
theorem registerClock_config_recovers_agent :
    ∀ (before : Config Nat) (n : Nat),
      (registerClockGrid.rePitch before (registerWeld n)).tendency = n := by
  intro _before _n
  rfl

/-- A share collision prevents uniform recovery of the acting designatum from
    the re-pitched configuration, even when recovery is requested only for
    actual occurrence-generated welds. -/
theorem no_agent_recovery_from_config_of_share_collision :
    ¬ ∃ recover : Config Nat → ShareCollisionCase,
        ∀ (before : Config Nat) (w : shareCollisionGrid.Weld),
          shareCollisionGrid.Actual w →
            recover (shareCollisionGrid.rePitch before w) = w.agent := by
  rintro ⟨recover, correct⟩
  let before : Config Nat := { tendency := 0 }
  have hleft := correct before shareCollisionLeft (by rfl)
  have hright := correct before shareCollisionRight (by rfl)
  have hcfg :
      shareCollisionGrid.rePitch before shareCollisionLeft =
        shareCollisionGrid.rePitch before shareCollisionRight := by
    rfl
  rw [hcfg] at hleft
  have hagents : ShareCollisionCase.left = ShareCollisionCase.right :=
    hleft.symm.trans hright
  cases hagents

end ConfigLeakWitness

/- ==========================================================================
   Direction is not recoverable from symmetric conditioning
============================================================================ -/

namespace DirectionNegative

inductive DirectionCase
  | agent
  | callFalse
  | callTrue
  | response
  | occurrenceFalse
  | occurrenceTrue
  deriving DecidableEq

def directionOccurrence : OccurrenceReading DirectionCase where
  occurrence
    | .occurrenceFalse | .occurrenceTrue => True
    | _ => False
  isBeing d := d = .agent
  isCall d := d = .callFalse ∨ d = .callTrue
  isResponse d := d = .response
  agent
    | .occurrenceFalse | .occurrenceTrue => .agent
    | d => d
  call
    | .occurrenceFalse => .callFalse
    | .occurrenceTrue => .callTrue
    | d => d
  response
    | .occurrenceFalse | .occurrenceTrue => .response
    | d => d

abbrev W := directionOccurrence.Weld

def wFalse : W := ⟨.occurrenceFalse, True.intro⟩
def wTrue : W := ⟨.occurrenceTrue, True.intro⟩

def forwardGrid : CoreReadings DirectionCase Nat where
  occurrence := directionOccurrence
  response := {
    respondsTo := fun b c =>
      if b = .agent ∧ (c = .callFalse ∨ c = .callTrue)
      then some .response
      else none
  }
  placement := { grade := fun _ => 0 }
  conditioning := {
    conditions := fun d₁ d₂ =>
      d₁ = .occurrenceFalse ∧ d₂ = .occurrenceTrue
  }

def backwardGrid : CoreReadings DirectionCase Nat where
  occurrence := directionOccurrence
  response := forwardGrid.response
  placement := forwardGrid.placement
  conditioning := {
    conditions := fun d₁ d₂ =>
      d₁ = .occurrenceTrue ∧ d₂ = .occurrenceFalse
  }

theorem conditionsEither_agrees (w₁ w₂ : W) :
    forwardGrid.ConditionsEither w₁ w₂ ↔
      backwardGrid.ConditionsEither w₁ w₂ :=
  ⟨fun h => h.elim
      (fun ⟨h₁, h₂⟩ => Or.inr ⟨h₂, h₁⟩)
      (fun ⟨h₁, h₂⟩ => Or.inl ⟨h₂, h₁⟩),
   fun h => h.elim
      (fun ⟨h₁, h₂⟩ => Or.inr ⟨h₂, h₁⟩)
      (fun ⟨h₁, h₂⟩ => Or.inl ⟨h₂, h₁⟩)⟩

theorem conditions_disagree :
    forwardGrid.conditions wFalse wTrue ∧
      ¬ backwardGrid.conditions wFalse wTrue := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro h
    cases h.left

theorem no_direction_recovery_from_conditionsEither :
    ¬ ∃ recover : (W → W → Prop) → (W → W → Prop),
        recover forwardGrid.ConditionsEither = forwardGrid.conditions ∧
        recover backwardGrid.ConditionsEither = backwardGrid.conditions := by
  rintro ⟨recover, hf, hb⟩
  have hsame :
      forwardGrid.ConditionsEither = backwardGrid.ConditionsEither := by
    funext w₁ w₂
    exact propext (conditionsEither_agrees w₁ w₂)
  have hcond : forwardGrid.conditions = backwardGrid.conditions := by
    rw [← hf, hsame, hb]
  exact conditions_disagree.right (hcond ▸ conditions_disagree.left)

theorem not_strict_twoBottom
    (a b : InvarianceNegative.TwoBottom) : ¬ Strict a b :=
  no_strict_of_all_orderEq
    (fun _ _ => ⟨True.intro, True.intro⟩) a b

end DirectionNegative

namespace DirectionCoarseningWitness

/-- The one-point carrier is direction-void. The proof deliberately uses the
    legal display collapse retained by the positive transport API. -/
theorem unit_directionVoid_via_mergeToUnit : DirectionVoid Unit :=
  DisplayReparam.directionVoid_of_surjective
    InvarianceNegative.mergeToUnit
    (fun b => ⟨InvarianceNegative.TwoBottom.chosen, by cases b; rfl⟩)
    DirectionNegative.not_strict_twoBottom

/-- Two occurrence events are enough for a resolution witness; their
    agent/call/response readings are immaterial to the clock claim. -/
inductive ResolutionEvent
  | low
  | high
  deriving DecidableEq

def resolutionOccurrence : OccurrenceReading ResolutionEvent where
  occurrence _ := True
  isBeing _ := True
  isCall _ := True
  isResponse _ := True
  agent := id
  call := id
  response := id

def resolutionGrid : CoreReadings ResolutionEvent Nat where
  occurrence := resolutionOccurrence
  response := { respondsTo := fun b _ => some b }
  placement := {
    grade
      | .low => 0
      | .high => 1
  }
  conditioning := { conditions := fun _ _ => False }

def resolutionLow : resolutionGrid.Weld :=
  ⟨.low, True.intro⟩

def resolutionHigh : resolutionGrid.Weld :=
  ⟨.high, True.intro⟩

def oneTick : Grid.DirectedConvention.DirectionCoarsening resolutionGrid Unit where
  tick _ := ()

def eventTick :
    Grid.DirectedConvention.DirectionCoarsening resolutionGrid ResolutionEvent where
  tick w := w.1

theorem oneTick_not_resolutionBounded :
    ¬ oneTick.ResolutionBounded := by
  intro h
  have heq := h resolutionLow resolutionHigh rfl
  change OrderEq (0 : Nat) 1 at heq
  exact Nat.not_succ_le_zero 0 heq.right

theorem eventTick_resolutionBounded :
    eventTick.ResolutionBounded := by
  intro w₁ w₂ hsame
  have hweld : w₁ = w₂ := Subtype.ext hsame
  subst w₂
  exact orderEq_refl _

/-- Resolution-boundedness belongs to the supplied clock: the same two-event
    grid supports both a lawful resolving clock and a lawful over-coarse clock
    that fails the bound. -/
theorem twoResolution_directionCoarsening_independence :
    eventTick.ResolutionBounded ∧ ¬ oneTick.ResolutionBounded :=
  ⟨eventTick_resolutionBounded, oneTick_not_resolutionBounded⟩

/-- The register clock's macro actuality and internal-delivery witnesses do
    not consume either a clock choice or a resolution-boundedness proof.  This
    dependency certificate is distinct from the two-clock counterexample
    above. -/
theorem registerClock_directionCoarsening_independence :
    (∀ {Tick : Type}
        (_ρ : Grid.DirectedConvention.DirectionCoarsening registerClockGrid Tick),
        registerClockCoarsening.ActualFiberInhabited () ∧
          registerClockCoarsening.SelfConditioningTag ()) ∧
      (∀ {Tick : Type}
        (ρ : Grid.DirectedConvention.DirectionCoarsening registerClockGrid Tick),
        ρ.ResolutionBounded →
          registerClockCoarsening.ActualFiberInhabited () ∧
            registerClockCoarsening.SelfConditioningTag ()) := by
  constructor
  · intro _Tick _ρ
    exact ⟨registerClock_macro_actualFiberInhabited,
      registerClock_macro_selfConditioning⟩
  · intro _Tick _ρ _hbounded
    exact ⟨registerClock_macro_actualFiberInhabited,
      registerClock_macro_selfConditioning⟩

end DirectionCoarseningWitness

/- ==========================================================================
   Content-row countermodels
============================================================================ -/

namespace ContentNegative

open Grid
open Grid.DirectedConvention.BeingConvention.GridConvention

/- --------------------------------------------------------------------------
   A selected but unrealized occurrence
-------------------------------------------------------------------------- -/

inductive HypotheticalCase
  | agent
  | call
  | response
  | hypothetical
  deriving DecidableEq

def hypotheticalOccurrence : OccurrenceReading HypotheticalCase where
  occurrence d := d = .hypothetical
  isBeing d := d = .agent
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .hypothetical => .agent
    | d => d
  call
    | .hypothetical => .call
    | d => d
  response
    | .hypothetical => .response
    | d => d

def hypotheticalGrid : CoreReadings HypotheticalCase Nat where
  occurrence := hypotheticalOccurrence
  response := { respondsTo := fun _ _ => none }
  placement := { grade := fun _ => 0 }
  conditioning := { conditions := fun _ _ => False }

def hypotheticalWeld : hypotheticalGrid.Weld :=
  ⟨.hypothetical, rfl⟩

theorem hypotheticalGrid_no_actual :
    ¬ ∃ w : hypotheticalGrid.Weld, hypotheticalGrid.Actual w := by
  rintro ⟨⟨d, hd⟩, hactual⟩
  change d = HypotheticalCase.hypothetical at hd
  subst d
  change (none : Option HypotheticalCase) = some .response at hactual
  cases hactual

theorem hypotheticalGrid_no_liveTier
    (t : Grid.Tier hypotheticalGrid) :
    ¬ Grid.Tier.hasLiveShare hypotheticalGrid t := by
  cases t with
  | floor =>
      intro h
      exact h
  | actTime _w =>
      intro hlive
      exact hlive (Nat.le_refl 0)

theorem hypotheticalWeld_not_live :
    ¬ hypotheticalGrid.HasSelfPoleIndex hypotheticalWeld :=
  hypotheticalGrid_no_liveTier (.actTime hypotheticalWeld)

/-- An unrealized occurrence makes the beings-denial true at its non-live
    act-time. -/
theorem contentBeingsRow_not_fused_hypothetical :
    ¬ (contentBeingsRow hypotheticalGrid).Fused (.actTime hypotheticalWeld) := by
  apply contentLayerRow_not_fused_of_nonlive_denial
    (G := hypotheticalGrid) .beings hypotheticalWeld hypotheticalWeld_not_live
  dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
  exact hypotheticalGrid_no_actual

theorem contentBeingsRow_not_obeys_hypothetical :
    ¬ (contentBeingsRow hypotheticalGrid).ObeysSeparateFuse := by
  intro h
  exact contentBeingsRow_not_fused_hypothetical
    (hypotheticalGrid.fused_of_obeysSeparateFuse h (.actTime hypotheticalWeld))

/-- The same unrealized occurrence supplies an act-time while the model has no
    live tier anywhere, exposing the grid-lens row's required hypothesis. -/
theorem contentGridLensRow_not_fused_hypothetical :
    ¬ (contentGridLensRow hypotheticalGrid).Fused
      (.actTime hypotheticalWeld) := by
  apply contentLayerRow_not_fused_of_nonlive_denial
    (G := hypotheticalGrid) .gridLens hypotheticalWeld hypotheticalWeld_not_live
  dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
  exact hypotheticalGrid_no_liveTier

theorem contentGridLensRow_not_obeys_hypothetical :
    ¬ (contentGridLensRow hypotheticalGrid).ObeysSeparateFuse := by
  intro h
  exact contentGridLensRow_not_fused_hypothetical
    (hypotheticalGrid.fused_of_obeysSeparateFuse h (.actTime hypotheticalWeld))

/-- Weld-grain content needs actuality just as beings content does. -/
theorem contentWeldRow_not_fused_hypothetical :
    ¬ (contentWeldRow hypotheticalGrid).Fused (.actTime hypotheticalWeld) := by
  apply contentLayerRow_not_fused_of_nonlive_denial
    (G := hypotheticalGrid) .weldGrain hypotheticalWeld hypotheticalWeld_not_live
  dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
  exact hypotheticalGrid_no_actual

theorem contentWeldRow_not_obeys_hypothetical :
    ¬ (contentWeldRow hypotheticalGrid).ObeysSeparateFuse := by
  intro h
  exact contentWeldRow_not_fused_hypothetical
    (hypotheticalGrid.fused_of_obeysSeparateFuse h (.actTime hypotheticalWeld))

/- --------------------------------------------------------------------------
   Actual but fixed response across two distinct calls
-------------------------------------------------------------------------- -/

inductive FixedResponseCase
  | agent
  | firstCall
  | secondCall
  | response
  | firstOccurrence
  | secondOccurrence
  deriving DecidableEq

def fixedResponseOccurrence : OccurrenceReading FixedResponseCase where
  occurrence d := d = .firstOccurrence ∨ d = .secondOccurrence
  isBeing d := d = .agent
  isCall d := d = .firstCall ∨ d = .secondCall
  isResponse d := d = .response
  agent
    | .firstOccurrence | .secondOccurrence => .agent
    | d => d
  call
    | .firstOccurrence => .firstCall
    | .secondOccurrence => .secondCall
    | d => d
  response
    | .firstOccurrence | .secondOccurrence => .response
    | d => d

def fixedResponseReading : RespondsToReading FixedResponseCase where
  respondsTo
    | .agent, .firstCall => some .response
    | .agent, .secondCall => some .response
    | _, _ => none

def fixedResponseGrid : CoreReadings FixedResponseCase Nat where
  occurrence := fixedResponseOccurrence
  response := fixedResponseReading
  placement := { grade := fun _ => 0 }
  conditioning := { conditions := fun _ _ => False }

def fixedResponseFirst : fixedResponseGrid.Weld :=
  ⟨.firstOccurrence, Or.inl rfl⟩

def fixedResponseSecond : fixedResponseGrid.Weld :=
  ⟨.secondOccurrence, Or.inr rfl⟩

theorem fixedResponseFirst_actual :
    fixedResponseGrid.Actual fixedResponseFirst :=
  rfl

theorem fixedResponseSecond_actual :
    fixedResponseGrid.Actual fixedResponseSecond :=
  rfl

theorem fixedResponse_eq_of_some
    {b c r : FixedResponseCase}
    (h : fixedResponseReading.respondsTo b c = some r) :
    r = .response := by
  cases b <;> cases c <;>
    simp [fixedResponseReading] at h ⊢ <;>
    exact h.symm

/-- Response invariance is substantive here: two distinct calls are mounted,
    and both return the same response. -/
theorem fixedResponseGrid_no_variation :
    ∀ b : FixedResponseCase,
      ¬ fixedResponseGrid.ResponseVariesWithCall b := by
  intro b
  rintro ⟨c₁, c₂, r₁, r₂, h₁, h₂, hne⟩
  have hr₁ := fixedResponse_eq_of_some h₁
  have hr₂ := fixedResponse_eq_of_some h₂
  exact hne (hr₁.trans hr₂.symm)

theorem fixedResponseFirst_not_live :
    ¬ fixedResponseGrid.HasSelfPoleIndex fixedResponseFirst := by
  intro hlive
  exact hlive (Nat.le_refl 0)

theorem contentIntraWeldArrowRow_not_fused_fixedResponse :
    ¬ (contentIntraWeldArrowRow fixedResponseGrid).Fused
      (.actTime fixedResponseFirst) := by
  apply contentLayerRow_not_fused_of_nonlive_denial
    (G := fixedResponseGrid) .intraWeldArrow fixedResponseFirst
      fixedResponseFirst_not_live
  dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
  exact fixedResponseGrid_no_variation

theorem contentIntraWeldArrowRow_not_obeys_fixedResponse :
    ¬ (contentIntraWeldArrowRow fixedResponseGrid).ObeysSeparateFuse := by
  intro h
  exact contentIntraWeldArrowRow_not_fused_fixedResponse
    (fixedResponseGrid.fused_of_obeysSeparateFuse h (.actTime fixedResponseFirst))

/- --------------------------------------------------------------------------
   Direction denial at a non-live occurrence
-------------------------------------------------------------------------- -/

theorem contentBeforeAfterRow_not_fused_twoBottom :
    ¬ (contentBeforeAfterRow InvarianceNegative.twoBottomGrid).Fused
      (.actTime InvarianceNegative.twoBottomWeld) := by
  apply contentLayerRow_not_fused_of_nonlive_denial
    (G := InvarianceNegative.twoBottomGrid) .directedTime
      InvarianceNegative.twoBottomWeld
  · intro hlive
    exact hlive True.intro
  · dsimp [contentLayerLanguage, Grid.ClaimLanguage.TrueAt]
    exact DirectionNegative.not_strict_twoBottom

theorem contentBeforeAfterRow_not_obeys_twoBottom :
    ¬ (contentBeforeAfterRow InvarianceNegative.twoBottomGrid).ObeysSeparateFuse := by
  intro h
  exact contentBeforeAfterRow_not_fused_twoBottom
    (InvarianceNegative.twoBottomGrid.fused_of_obeysSeparateFuse h
      (.actTime InvarianceNegative.twoBottomWeld))

end ContentNegative

/- ==========================================================================
   Being-boundary freedom: a coarsening is a supplied reading
============================================================================ -/

namespace BeingNegative

open Grid.DirectedConvention.BeingConvention

def twoBeingOccurrence : OccurrenceReading Bool where
  occurrence _ := True
  isBeing _ := True
  isCall _ := True
  isResponse _ := True
  agent := id
  call := id
  response := id

def twoBeingGrid : CoreReadings Bool Nat where
  occurrence := twoBeingOccurrence
  response := { respondsTo := fun b _ => some b }
  placement := { grade := fun _ => 0 }
  conditioning := { conditions := fun _ _ => True }

def κmerge : BeingCoarsening twoBeingGrid Unit where
  proj _ := ()

def κsplit : BeingCoarsening twoBeingGrid Bool where
  proj := id

theorem merge_same_fiber :
    BeingCoarsening.SameFiber κmerge false true :=
  rfl

theorem split_not_same_fiber :
    ¬ BeingCoarsening.SameFiber κsplit false true := by
  intro h
  cases h

abbrev GridData := CoreReadings Bool Nat

def gridData : GridData := twoBeingGrid
def mergeBoundary (_p _q : Bool) : Prop := True
def splitBoundary (p q : Bool) : Prop := p = q

theorem no_partition_recovery :
    ¬ ∃ recover : GridData → Bool → Bool → Prop,
        recover gridData = mergeBoundary ∧
        recover gridData = splitBoundary := by
  rintro ⟨recover, hmerge, hsplit⟩
  have hmerged : recover gridData false true := by
    rw [hmerge]
    exact True.intro
  have hsplitNot : ¬ recover gridData false true := by
    rw [hsplit]
    intro h
    cases h
  exact hsplitNot hmerged

end BeingNegative

/- ==========================================================================
   Coverage countermodels
============================================================================ -/

namespace CoverageNegative

open Grid.DirectedConvention

def embedIntoNat : DisplayReparam Unit Nat where
  toFun _ := 0
  le_iff _ _ := ⟨fun _ => Nat.le_refl 0, fun _ => True.intro⟩
  atBot_bot := Nat.le_refl 0

theorem embedIntoNat_not_surjective (u : Unit) :
    embedIntoNat.toFun u ≠ 1 := by
  intro h
  cases h

theorem directionVoid_unit : DirectionVoid Unit :=
  no_strict_of_all_orderEq (fun _ _ => ⟨True.intro, True.intro⟩)

theorem strict_zero_one : Strict (0 : Nat) 1 :=
  ⟨Nat.zero_le 1, fun h => Nat.not_succ_le_zero 0 h⟩

theorem not_directionVoid_nat : ¬ DirectionVoid Nat :=
  fun h => h 0 1 strict_zero_one

theorem directionVoid_needs_coverage :
    (∀ u : Unit, embedIntoNat.toFun u ≠ 1) ∧
      DirectionVoid Unit ∧ ¬ DirectionVoid Nat :=
  ⟨embedIntoNat_not_surjective, directionVoid_unit, not_directionVoid_nat⟩

inductive PhantomCase
  | agent
  | call
  | responseTrue
  | responseFalse
  | deed
  | reception
  deriving DecidableEq

def phantomOccurrence : OccurrenceReading PhantomCase where
  occurrence
    | .deed | .reception => True
    | _ => False
  isBeing d := d = .agent
  isCall d := d = .call
  isResponse d := d = .responseTrue ∨ d = .responseFalse
  agent
    | .deed | .reception => .agent
    | d => d
  call
    | .deed | .reception => .call
    | d => d
  response
    | .deed => .responseTrue
    | .reception => .responseFalse
    | d => d

def phantomGrid : CoreReadings PhantomCase Unit where
  occurrence := phantomOccurrence
  response := {
    respondsTo := fun b c =>
      if b = .agent ∧ c = .call then some .responseTrue else none
  }
  placement := { grade := fun _ => () }
  conditioning := {
    conditions := fun d₁ d₂ =>
      d₁ = .deed ∧ d₂ = .reception
  }

def phantomDeed : phantomGrid.Weld :=
  ⟨.deed, True.intro⟩

def phantomReception : phantomGrid.Weld :=
  ⟨.reception, True.intro⟩

theorem phantom_responsiveTerminus :
    phantomGrid.ResponsiveTerminus .agent := by
  constructor
  · intro c hcall
    have hc : c = PhantomCase.call := hcall
    subst c
    exact ⟨.responseTrue, rfl⟩
  · intro _w _hactual _hagent
    exact True.intro

theorem phantom_ksmdEffectiveTerminus :
    KsmdEffectiveTerminus phantomGrid .agent := by
  constructor
  · exact phantom_responsiveTerminus
  · intro before _deed _reception _hdeed hlive
    exact False.elim (hlive True.intro)

theorem not_ksmdEffectiveTerminus_map :
    ¬ KsmdEffectiveTerminus (phantomGrid.map embedIntoNat)
      .agent := by
  intro h
  let liveBefore : Config Nat := { tendency := 1 }
  have hlive : ¬ AtBot liveBefore.tendency := by
    intro hbot
    exact Nat.not_succ_le_zero 0 hbot
  have hdel :
      Grid.DirectedConvention.DeliveredTo
        (phantomGrid.map embedIntoNat)
        phantomDeed phantomReception := by
    exact ⟨rfl, rfl⟩
  have hlanding :
      Grid.DirectedConvention.HasShareDropLanding
        (phantomGrid.map embedIntoNat)
        liveBefore phantomDeed :=
    h.right liveBefore phantomDeed phantomReception rfl hlive hdel
  rcases hlanding with
    ⟨reception, ⟨⟨hcondition, hactual⟩, _hdrop⟩⟩
  have hreception : reception.1 = PhantomCase.reception :=
    hcondition.right
  rcases reception with ⟨d, hd⟩
  change d = PhantomCase.reception at hreception
  subst d
  change some PhantomCase.responseTrue =
    some PhantomCase.responseFalse at hactual
  cases hactual

theorem ksmdEffectiveTerminus_needs_coverage :
    KsmdEffectiveTerminus phantomGrid .agent ∧
      ¬ KsmdEffectiveTerminus (phantomGrid.map embedIntoNat)
        .agent :=
  ⟨phantom_ksmdEffectiveTerminus, not_ksmdEffectiveTerminus_map⟩

end CoverageNegative

/- ==========================================================================
   Weld-boundary freedom: occurrence segmentation is supplied
============================================================================ -/

namespace WeldNegative

structure WeldSegmentation
    (G : CoreReadings Bool Nat) (Macro : Type) where
  proj : G.Weld → Macro

namespace WeldSegmentation

variable {G : CoreReadings Bool Nat} {Macro : Type}
variable (σ : WeldSegmentation G Macro)

def SamePairing (p q : G.Weld) : Prop := σ.proj p = σ.proj q

end WeldSegmentation

def twoWeldOccurrence : OccurrenceReading Bool where
  occurrence _ := True
  isBeing _ := True
  isCall _ := True
  isResponse _ := True
  agent _ := false
  call := id
  response := id

def twoWeldGrid : CoreReadings Bool Nat where
  occurrence := twoWeldOccurrence
  response := { respondsTo := fun _ c => some c }
  placement := { grade := fun _ => 0 }
  conditioning := { conditions := fun _ _ => True }

def wFalse : twoWeldGrid.Weld := ⟨false, True.intro⟩
def wTrue : twoWeldGrid.Weld := ⟨true, True.intro⟩

def σmerge : WeldSegmentation twoWeldGrid Unit where
  proj _ := ()

def σsplit : WeldSegmentation twoWeldGrid Bool where
  proj w := w.call

theorem merge_same_pairing :
    WeldSegmentation.SamePairing σmerge wFalse wTrue :=
  rfl

theorem split_not_same_pairing :
    ¬ WeldSegmentation.SamePairing σsplit wFalse wTrue := by
  intro h
  cases h

abbrev W := twoWeldGrid.Weld
abbrev GridData := CoreReadings Bool Nat

def gridData : GridData := twoWeldGrid
def mergedPairing (_p _q : W) : Prop := True
def splitPairing (p q : W) : Prop := p.call = q.call

theorem no_weld_boundary_recovery :
    ¬ ∃ recover : GridData → W → W → Prop,
        recover gridData = mergedPairing ∧
        recover gridData = splitPairing := by
  rintro ⟨recover, hmerge, hsplit⟩
  have hmerged : recover gridData wFalse wTrue := by
    rw [hmerge]
    exact True.intro
  have hsplitNot : ¬ recover gridData wFalse wTrue := by
    rw [hsplit]
    intro h
    cases h
  exact hsplitNot hmerged

end WeldNegative

/- ==========================================================================
   Doer/deed priority freedom: priority is a supplied reading
============================================================================ -/

namespace DoerDeedNegative

abbrev W := WeldNegative.W
abbrev GridData := WeldNegative.GridData

def gridData : GridData := WeldNegative.gridData
def beingPriorReading (_b : Bool) (_deed : W) : Prop := True
def mutualReading (_b : Bool) (_deed : W) : Prop := False

theorem priority_readings_disagree :
    beingPriorReading false WeldNegative.wFalse ∧
      ¬ mutualReading false WeldNegative.wFalse := by
  constructor
  · exact True.intro
  · intro h
    exact h

theorem no_priority_recovery :
    ¬ ∃ recover : GridData → Bool → W → Prop,
        recover gridData = beingPriorReading ∧
        recover gridData = mutualReading := by
  rintro ⟨recover, hprior, hmutual⟩
  have hPrior : recover gridData false WeldNegative.wFalse := by
    rw [hprior]
    exact priority_readings_disagree.left
  have hMutualNot :
      ¬ recover gridData false WeldNegative.wFalse := by
    rw [hmutual]
    exact priority_readings_disagree.right
  exact hMutualNot hPrior

end DoerDeedNegative

end KannoSoe
