/-
================================================================================
  KannoSoe.Consequences.Basic
  Checked consequences of the signature layer
================================================================================

This module proves consequences of the primitive definitions: order facts,
function/share facts, re-pitch facts, delivery and landing projections, pair
projections, and tier diagnostics.

Reading and motivation: Identification/Commentary.lean, C.2.
-/

import KannoSoe.Signature

namespace KannoSoe

section Preorder

variable {α : Type} [Preorder α]

/-- Incomparability is symmetric. -/
theorem incomparable_symm {a b : α} (h : Incomparable a b) :
    Incomparable b a :=
  ⟨h.right, h.left⟩

/-- Incomparability rules out the left-to-right comparison. -/
theorem not_le_of_incomparable {a b : α} (h : Incomparable a b) :
    ¬ a ≼ b :=
  h.left

/-- Incomparability rules out the right-to-left comparison. -/
theorem not_ge_of_incomparable {a b : α} (h : Incomparable a b) :
    ¬ b ≼ a :=
  h.right

end Preorder

namespace Grid

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/

omit [PreorderBot Contrib] in
/-- The share projection is exactly the grade recorded for the weld. -/
@[simp]
theorem share_eq_grade (w : G.Weld) :
    G.share w = G.grade w.1 :=
  rfl

omit [PreorderBot Contrib] in
/-- An actual weld witnesses response-function at its own call. -/
theorem mountsAt_of_actual (w : G.Weld) (h : G.Actual w) :
    G.MountsAt w.agent w.call :=
  ⟨w.response, h⟩

omit [PreorderBot Contrib] in
/-- An actual weld supplies the occurrence-form non-vacuity witness for its
    agent. -/
theorem actualAgentInhabited_of_actual (w : G.Weld) (h : G.Actual w) :
    G.ActualAgentInhabited w.agent :=
  ⟨w, h, rfl⟩

omit [PreorderBot Contrib] in
/-- Mounting at a call is exactly the existence of an actual weld with that
    agent and call.  Function talk is thereby kept per occurrence. -/
theorem mountsAt_iff_exists_actual (b : Designatum) (c : Designatum)
    (hrealize : ∀ r, G.respondsTo b c = some r →
      ∃ w : G.Weld, G.Actual w ∧ w.agent = b ∧ w.call = c) :
    G.MountsAt b c ↔
      ∃ w : G.Weld, G.Actual w ∧ w.agent = b ∧ w.call = c := by
  constructor
  · rintro ⟨r, hresp⟩
    exact hrealize r hresp
  · rintro ⟨w, hactual, hagent, hcall⟩
    subst hagent
    subst hcall
    exact ⟨w.response, hactual⟩

omit [PreorderBot Contrib] in
theorem respondsToEveryCall_of_no_call
    (h : ∀ c, ¬ G.occurrence.isCall c) (b : Designatum) :
    G.RespondsToEveryCall b :=
  fun c hcall => False.elim (h c hcall)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem atPoleClass_of_terminus (b : Designatum) (hterm : G.Terminus b) :
    G.AtPoleClass b :=
  hterm

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
omit [PreorderBot Contrib] in
theorem rePitch_tendency_eq_share
    (before : Config Contrib) (received : G.Weld) :
    (G.rePitch before received).tendency = G.share received :=
  rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem isShareDrop_iff_rePitch_tendency_drop
    (before : Config Contrib) (received : G.Weld) :
    G.IsShareDrop before received ↔
      ((G.rePitch before received).tendency ≼ before.tendency ∧
        ¬ (before.tendency ≼ (G.rePitch before received).tendency)) :=
  Iff.rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem rePitch_tendency_le_before_of_shareDrop
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsShareDrop before received) :
    (G.rePitch before received).tendency ≼ before.tendency :=
  h.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem not_before_le_rePitch_tendency_of_shareDrop
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsShareDrop before received) :
    ¬ (before.tendency ≼ (G.rePitch before received).tendency) :=
  h.right

/-- A terminus response re-pitches the carried tendency into the pole-class. -/
theorem rePitch_tendency_atBot_of_terminus_response
    (before : Config Contrib) {w : G.Weld}
    (hterm : G.Terminus w.agent) (hactual : G.Actual w) :
    AtBot (G.rePitch before w).tendency :=
  G.atBot_of_terminus_response hterm hactual

/- ==============================================================================
   Conditions-free grade checks
============================================================================== -/

/-- Replace only the conditioning reading. Response and placement readings are
    left untouched. -/
def withConditions (conditions' : Designatum → Designatum → Prop) :
    CoreReadings Designatum Contrib where
  occurrence := G.occurrence
  response := G.response
  placement := G.placement
  conditioning := { conditions := conditions' }

omit [PreorderBot Contrib] in
@[simp]
theorem withConditions_respondsTo
    (conditions' : Designatum → Designatum → Prop)
    (b : Designatum) (c : Designatum) :
    (withConditions G conditions').respondsTo b c = G.respondsTo b c :=
  rfl

omit [PreorderBot Contrib] in
@[simp]
theorem withConditions_grade
    (conditions' : Designatum → Designatum → Prop)
    (d : Designatum) :
    (withConditions G conditions').grade d = G.grade d :=
  rfl

omit [PreorderBot Contrib] in
@[simp]
theorem withConditions_share
    (conditions' : Designatum → Designatum → Prop) (w : G.Weld) :
    (withConditions G conditions').share w = G.share w :=
  rfl

omit [PreorderBot Contrib] in
@[simp]
theorem withConditions_actual_iff
    (conditions' : Designatum → Designatum → Prop) (w : G.Weld) :
    (withConditions G conditions').Actual w ↔ G.Actual w :=
  Iff.rfl

omit [PreorderBot Contrib] in
/-- Changing only `conditions` cannot change the grade assigned to a mounted
    response. This is the formal anchor for the cetana correlation at
    signature level: grade is blind to downstream delivery facts. -/
theorem grade_independent_of_conditions
    (conditions₁ conditions₂ : Designatum → Designatum → Prop)
    (d : Designatum) :
    (withConditions G conditions₁).grade d =
      (withConditions G conditions₂).grade d :=
  rfl

omit [PreorderBot Contrib] in
/-- The same cetana anchor at the weld/share projection: what is graded is the
    weld's agent-call-response composition, not the later delivery relation. -/
theorem share_independent_of_conditions
    (conditions₁ conditions₂ : Designatum → Designatum → Prop) (w : G.Weld) :
    (withConditions G conditions₁).share w =
      (withConditions G conditions₂).share w :=
  rfl

/- ==============================================================================
   Response-function replacement as countermodel tooling
============================================================================== -/

/-- Replace only the response function of a grid. Grade and delivery data are
    left untouched.  This is countermodel tooling; no doctrinal reading is
    attached to the `none` region it may create. -/
def withRespondsTo (respondsTo' : Designatum -> Designatum -> Option Designatum) :
    CoreReadings Designatum Contrib where
  occurrence := G.occurrence
  response := { respondsTo := respondsTo' }
  placement := G.placement
  conditioning := G.conditioning

omit [PreorderBot Contrib] in
@[simp]
theorem withRespondsTo_grade
    (respondsTo' : Designatum -> Designatum -> Option Designatum)
    (d : Designatum) :
    (withRespondsTo G respondsTo').grade d = G.grade d :=
  rfl

omit [PreorderBot Contrib] in
@[simp]
theorem withRespondsTo_share
    (respondsTo' : Designatum -> Designatum -> Option Designatum) (w : G.Weld) :
    (withRespondsTo G respondsTo').share w = G.share w :=
  rfl

omit [PreorderBot Contrib] in
@[simp]
theorem withRespondsTo_conditions
    (respondsTo' : Designatum -> Designatum -> Option Designatum) :
    (withRespondsTo G respondsTo').conditions = G.conditions :=
  rfl

/- ==============================================================================
   Accumulation: `rePitch` has no history register
============================================================================== -/

omit [PreorderBot Contrib] in
/-- The post-reception configuration ignores the prior configuration and reads
    only the received weld's share. -/
theorem rePitch_forgets
    (before₁ before₂ : Config Contrib) (received : G.Weld) :
    G.rePitch before₁ received = G.rePitch before₂ received :=
  rfl

omit [PreorderBot Contrib] in
/-- Any run-valued score that factors through the post-reception `Config` is
    constant across histories that share their final reception. -/
theorem accumulated_attainment_constant_of_same_final
    {α : Type} (score : Config Contrib -> α)
    (before₁ before₂ : Config Contrib) (received : G.Weld) :
    score (G.rePitch before₁ received) =
      score (G.rePitch before₂ received) :=
  congrArg score (rePitch_forgets G before₁ before₂ received)

/- ==============================================================================
   The environs lens
============================================================================== -/

namespace DirectedConvention

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem environsLine_of_shareDropLine
    {before : Config Contrib} {b : Designatum} {deed reception : G.Weld}
    (h : ShareDropLine G before b deed reception) :
    EnvironsLine G b deed reception :=
  h.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem isShareDrop_of_shareDropLine
    {before : Config Contrib} {b : Designatum} {deed reception : G.Weld}
    (h : ShareDropLine G before b deed reception) :
    G.IsShareDrop before reception :=
  h.right

omit [PreorderBot Contrib] in
/-- An environs-line is a delivery-fact. -/
theorem deliveredTo_of_environsLine
    {b : Designatum} {deed reception : G.Weld}
    (h : EnvironsLine G b deed reception) :
    DeliveredTo G deed reception :=
  h.right.right

end DirectedConvention

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem not_isShareDrop_of_tendency_atBot
    {before : Config Contrib} (h : AtBot before.tendency)
    (received : G.Weld) :
    ¬ G.IsShareDrop before received := by
  intro hdrop
  exact hdrop.right (Preorder.le_trans h (shareBot_le (G.share received)))

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem not_isShareDrop_of_eq_shareBot_tendency
    {before : Config Contrib} (h : before.tendency = shareBot)
    (received : G.Weld) :
    ¬ G.IsShareDrop before received :=
  not_isShareDrop_of_tendency_atBot G (atBot_of_eq_shareBot h) received

namespace DirectedConvention

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem no_shareDropLine_of_tendency_atBot
    {before : Config Contrib} (h : AtBot before.tendency)
    (b : Designatum) (deed reception : G.Weld) :
    ¬ ShareDropLine G before b deed reception :=
  fun hline =>
    not_isShareDrop_of_tendency_atBot G h reception hline.right

/-- Literal equality with the designated bottom gives the pole-class release
    obstruction. -/
theorem no_shareDropLine_of_eq_shareBot_tendency
    {before : Config Contrib} (h : before.tendency = shareBot)
    (b : Designatum) (deed reception : G.Weld) :
    ¬ ShareDropLine G before b deed reception :=
  no_shareDropLine_of_tendency_atBot G (atBot_of_eq_shareBot h) b deed reception

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem hasShareDropLanding_of_shareDropLine_actual
    {before : Config Contrib} {b : Designatum} {deed reception : G.Weld}
    (hline : ShareDropLine G before b deed reception)
    (hact : G.Actual reception) :
    HasShareDropLanding G before deed :=
  ⟨reception, ⟨⟨hline.left.right.right, hact⟩, hline.right⟩⟩

/-- Shortfall is closed at a delivered pair when, for any live prior tendency,
    delivery of the deed is enough to yield a share-drop landing for that deed.
    This is regime-relational effectiveness talk, not a nature possessed by a
    being. -/
def ShortfallClosedAt
    (before : Config Contrib) (deed reception : G.Weld) : Prop :=
  ¬ AtBot before.tendency →
    DeliveredTo G deed reception →
      HasShareDropLanding G before deed

/-- An explicit share-drop line with an actual reception supplies the local
    closure predicate. -/
theorem shortfallClosedAt_of_shareDropLine_actual
    {before : Config Contrib} {b : Designatum} {deed reception : G.Weld}
    (hline : ShareDropLine G before b deed reception)
    (hact : G.Actual reception) :
    ShortfallClosedAt G before deed reception :=
  fun _hlive _hdel =>
    hasShareDropLanding_of_shareDropLine_actual G hline hact

/-- Effective-terminus display, quantified over the run: the being is
    a responsive terminus and every delivered reception of one of its deeds
    closes shortfall for a live prior tendency.

    This descriptive standing form is legal as display over the run; it is not
    an act-time verdict or, by itself, the testimonial faith-object. The
    operational shushō-ittō face is `KsmdEffectiveOccurrence`, while
    `EffectiveTerminusNegative` checks that the universal conjunct is not
    recovered from actual-run data. Reading and motivation:
    Identification/Commentary.lean, C.4. -/
def KsmdEffectiveTerminus (b : Designatum) : Prop :=
  G.ResponsiveTerminus b ∧
    ∀ before deed reception,
      deed.agent = b →
        ShortfallClosedAt G before deed reception

theorem responsiveTerminus_of_ksmdEffectiveTerminus
    {b : Designatum} (h : KsmdEffectiveTerminus G b) :
    G.ResponsiveTerminus b :=
  h.left

theorem shortfallClosedAt_of_ksmdEffectiveTerminus
    {b : Designatum} (h : KsmdEffectiveTerminus G b)
    {before : Config Contrib} {deed reception : G.Weld}
    (hdeed : deed.agent = b) :
    ShortfallClosedAt G before deed reception :=
  h.right before deed reception hdeed

/-- If a responsive terminus has no delivered own deeds in the current regime,
    the universal shortfall-closure conjunct is satisfied vacuously. This is
    the sealed-regime face: teaching/non-teaching is not stored in the being,
    but in the delivery relation around it. The vacuous standing display is
    separated from enacted effectiveness by
    `not_effectivenessEnacted_of_undelivered`. -/
theorem ksmdEffectiveTerminus_of_responsiveTerminus_of_undelivered
    {b : Designatum} (hterm : G.ResponsiveTerminus b)
    (hundelivered : ∀ (deed reception : G.Weld),
      deed.agent = b → ¬ DeliveredTo G deed reception) :
    KsmdEffectiveTerminus G b := by
  refine ⟨hterm, ?_⟩
  intro _before deed reception hdeed _hlive hdel
  exact False.elim ((hundelivered deed reception hdeed) hdel)

end DirectedConvention

/- Reading and motivation: Identification/Commentary.lean, C.2. -/

namespace DirectedConvention

omit [PreorderBot Contrib] in
/-- A full reach-back is the same field-side fact as delivery. -/
theorem ksmdReachBackFull_iff_deliveredTo (deed reception : G.Weld) :
    KsmdReachBackFull G deed reception ↔ DeliveredTo G deed reception :=
  Iff.rfl

omit [PreorderBot Contrib] in
/-- The display-tier aiming lens unfolds to delivery and adds no mechanism. -/
theorem ksmdAimedAt_iff_deliveredTo (deed reception : G.Weld) :
    KsmdAimedAt G deed reception ↔ DeliveredTo G deed reception :=
  Iff.rfl

omit [PreorderBot Contrib] in
/-- Landing includes delivery. -/
theorem deliveredTo_of_landsAt
    {deed reception : G.Weld} (h : LandsAt G deed reception) :
    DeliveredTo G deed reception :=
  h.left

omit [PreorderBot Contrib] in
/-- Landing includes actuality of the reception. -/
theorem actual_of_landsAt
    {deed reception : G.Weld} (h : LandsAt G deed reception) :
    G.Actual reception :=
  h.right

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem landsAt_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    LandsAt G deed reception :=
  h.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem isShareDrop_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    G.IsShareDrop before reception :=
  h.right

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem deliveredTo_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    DeliveredTo G deed reception :=
  deliveredTo_of_landsAt G (landsAt_of_landsWithShareDrop G h)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem actual_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    G.Actual reception :=
  actual_of_landsAt G (landsAt_of_landsWithShareDrop G h)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem exists_landsAt_of_hasShareDropLanding
    {before : Config Contrib} {deed : G.Weld}
    (h : HasShareDropLanding G before deed) :
    ∃ reception, LandsAt G deed reception :=
  h.elim (fun reception hland =>
    ⟨reception, landsAt_of_landsWithShareDrop G hland⟩)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem exists_actual_reception_of_hasShareDropLanding
    {before : Config Contrib} {deed : G.Weld}
    (h : HasShareDropLanding G before deed) :
    ∃ reception, G.Actual reception :=
  h.elim (fun reception hland =>
    ⟨reception, actual_of_landsWithShareDrop G hland⟩)

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem exists_shareDrop_reception_of_hasShareDropLanding
    {before : Config Contrib} {deed : G.Weld}
    (h : HasShareDropLanding G before deed) :
    ∃ reception, G.IsShareDrop before reception :=
  h.elim (fun reception hland =>
    ⟨reception, isShareDrop_of_landsWithShareDrop G hland⟩)

end DirectedConvention

/- ==============================================================================
   Actual pairs
============================================================================== -/

namespace ReceptionPair

variable {G : CoreReadings Designatum Contrib}

omit [PreorderBot Contrib] in
/-- The first member of a reception pair is actual. -/
theorem first_actual (p : ReceptionPair G) :
    G.Actual p.first.weld :=
  p.first.actual

omit [PreorderBot Contrib] in
/-- The second member of a reception pair is actual. -/
theorem second_actual (p : ReceptionPair G) :
    G.Actual p.second.weld :=
  p.second.actual

omit [PreorderBot Contrib] in
/-- The pair's named relation is just delivery from first to second. -/
theorem firstConditionsSecond_iff_deliveredTo (p : ReceptionPair G) :
    p.FirstConditionsSecond ↔
      DirectedConvention.DeliveredTo G p.first.weld p.second.weld :=
  Iff.rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
omit [PreorderBot Contrib] in
theorem rePitchSequence_first_tendency
    (before : Config Contrib) (p : ReceptionPair G) :
    (rePitchSequence (G := G) before p).fst.tendency = G.share p.first.weld :=
  rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
omit [PreorderBot Contrib] in
theorem rePitchSequence_second_tendency
    (before : Config Contrib) (p : ReceptionPair G) :
    (rePitchSequence (G := G) before p).snd.tendency = G.share p.second.weld :=
  rfl

end ReceptionPair

/- ==============================================================================
   Tiers, utterances, and separate/fuse diagnostics
============================================================================== -/

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem floor_has_no_live_share :
    ¬ Tier.hasLiveShare G (Tier.floor : Tier G) :=
  fun h => h

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem actTime_hasLiveShare_iff_hasSelfPoleIndex (w : G.Weld) :
    Tier.hasLiveShare G (Tier.actTime w) ↔ G.HasSelfPoleIndex w :=
  Iff.rfl

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem not_actTime_hasLiveShare_of_atBot
    {w : G.Weld} (h : AtBot (G.share w)) :
    ¬ Tier.hasLiveShare G (Tier.actTime w) :=
  G.no_self_pole_index_of_atBot w h

/-- Equality with the designated bottom is a bridge into the pole-class
    act-time lemma. -/
theorem not_actTime_hasLiveShare_of_eq_shareBot
    {w : G.Weld} (h : G.share w = shareBot) :
    ¬ Tier.hasLiveShare G (Tier.actTime w) :=
  not_actTime_hasLiveShare_of_atBot G (atBot_of_eq_shareBot h)

/-- Collapse is impossible at the floor. -/
theorem not_collapse_floor (d : Distinction G) :
    ¬ d.Collapse (Tier.floor : Tier G) :=
  fun hcollapse => floor_has_no_live_share G hcollapse.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem hasLiveShare_of_collapse
    {d : Distinction G} {t : Tier G} (h : d.Collapse t) :
    Tier.hasLiveShare G t :=
  h.left

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem hasLiveShare_of_separated
    {d : Distinction G} {t : Tier G} (h : d.Separated t) :
    Tier.hasLiveShare G t :=
  h.left

/-- Separation rules out collapse at the same tier. -/
theorem not_collapse_of_separated
    {d : Distinction G} {t : Tier G} (h : d.Separated t) :
    ¬ d.Collapse t :=
  fun hcollapse => h.right hcollapse.right

/-- Obeying the rule supplies the fusion clause at every tier. -/
theorem fused_of_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse) (t : Tier G) :
    d.Fused t :=
  h.right t

/- Reading and motivation: Identification/Commentary.lean, C.2. -/
theorem separated_of_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse)
    {t : Tier G} (ht : Tier.hasLiveShare G t) :
    d.Separated t :=
  ⟨ht, h.left t ht⟩

/-- Fusion at the floor rules out freeze. -/
theorem not_freeze_of_fused_floor
    {d : Distinction G} (h : d.Fused (Tier.floor : Tier G)) :
    ¬ d.Freeze :=
  fun hfreeze => hfreeze (h (floor_has_no_live_share G))

/-- Error-freedom is the refutation-only reading of the separate/fuse rule:
    no live-tier collapse and no floor freeze. -/
def ErrorFree (d : Distinction G) : Prop :=
  (∀ t, ¬ d.Collapse t) ∧ ¬ d.Freeze

/-- Obedience supplies both refutations. The converse is not true for an
    arbitrary distinction; the floor-apophatic row language below is the
    special case where the missing genjō-fusion clause is built into the
    semantics by indiscernibility. -/
theorem errorFree_of_obeys
    {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ErrorFree G d :=
  ⟨fun t => Grid.not_collapse_of_obeysSeparateFuse h t,
    Grid.not_freeze_of_obeysSeparateFuse h⟩

namespace RecordedUtterance

variable {G : CoreReadings Designatum Contrib} {L : ClaimLanguage G}

omit [PreorderBot Contrib] in
/-- The answered call is the call carried by the utterance's weld. -/
@[simp]
theorem answersCall_eq_weld_call (u : RecordedUtterance G L) :
    answersCall u = u.weld.call :=
  rfl

omit [PreorderBot Contrib] in
/-- Fitting the offered tier is exactly truth at that tier. -/
theorem fitsOfferedTier_iff_trueAt (u : RecordedUtterance G L) :
    FitsOfferedTier u ↔ L.TrueAt u.offeredAt u.content :=
  Iff.rfl

end RecordedUtterance

namespace ErrorGrade

/-- Verdict errors speak in the assertable voice. -/
theorem verdict_voice_assertable :
    ErrorGrade.voice ErrorGrade.verdict = VerdictVoice.assertable :=
  rfl

/-- Shortfall errors speak in the displayable voice. -/
theorem shortfall_voice_displayable :
    ErrorGrade.voice ErrorGrade.shortfall = VerdictVoice.displayable :=
  rfl

end ErrorGrade


end Grid

namespace CoreReadings

variable {Designatum Contrib : Type} [PreorderBot Contrib]

abbrev withConditions (G : CoreReadings Designatum Contrib) :=
  Grid.withConditions G
abbrev withRespondsTo (G : CoreReadings Designatum Contrib) :=
  Grid.withRespondsTo G
abbrev rePitch_tendency_atBot_of_terminus_response
    (G : CoreReadings Designatum Contrib) :=
  Grid.rePitch_tendency_atBot_of_terminus_response G
abbrev grade_independent_of_conditions
    (G : CoreReadings Designatum Contrib) :=
  Grid.grade_independent_of_conditions G
abbrev share_independent_of_conditions
    (G : CoreReadings Designatum Contrib) :=
  Grid.share_independent_of_conditions G
abbrev rePitch_forgets (G : CoreReadings Designatum Contrib) :=
  Grid.rePitch_forgets G
abbrev accumulated_attainment_constant_of_same_final
    (G : CoreReadings Designatum Contrib)
    {α : Type} (score : Config Contrib → α)
    (before₁ before₂ : Config Contrib) (received : G.Weld) :=
  Grid.accumulated_attainment_constant_of_same_final
    G score before₁ before₂ received
abbrev not_isShareDrop_of_tendency_atBot
    (G : CoreReadings Designatum Contrib)
    {before : Config Contrib} (h : AtBot before.tendency)
    (received : G.Weld) :=
  Grid.not_isShareDrop_of_tendency_atBot G h received
abbrev fused_of_obeysSeparateFuse
    (G : CoreReadings Designatum Contrib)
    {d : Grid.Distinction G}
    (h : d.ObeysSeparateFuse) (t : Grid.Tier G) :=
  Grid.fused_of_obeysSeparateFuse G h t
abbrev separated_of_obeysSeparateFuse
    (G : CoreReadings Designatum Contrib)
    {d : Grid.Distinction G}
    (h : d.ObeysSeparateFuse)
    {t : Grid.Tier G} (ht : Grid.Tier.hasLiveShare G t) :=
  Grid.separated_of_obeysSeparateFuse G h ht
abbrev floor_has_no_live_share (G : CoreReadings Designatum Contrib) :=
  Grid.floor_has_no_live_share G
abbrev not_actTime_hasLiveShare_of_atBot
    (G : CoreReadings Designatum Contrib)
    {w : G.Weld} (h : AtBot (G.share w)) :=
  Grid.not_actTime_hasLiveShare_of_atBot G h

end CoreReadings

end KannoSoe
