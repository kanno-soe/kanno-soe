/-
================================================================================
  KannoSoe.Identification.Ownership
  Ownership faces, token-reflexivity, pole typing, and offices
================================================================================

Reading and motivation: Identification/Commentary.lean, C.2.
-/

import KannoSoe.Identification.Residues

namespace KannoSoe

namespace Grid

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/- ==============================================================================
   §2  Sower/reaper, reach-back, and KannoSoe-ownership-face
============================================================================== -/

namespace DirectedConvention

/-- The field-side report-face of "the sower reaps": the delivery line, before
    any act-time ownership is added. -/
def KsmdReportFace (deed reception : G.Weld) : Prop :=
  DeliveredTo G deed reception

/-- The full KannoSoe-ownership-face: delivery reaches an actual reception and that
    reception KannoSoe-appropriates. It is a deed at reception-time, not a standing
    relation. -/
def KsmdOwnershipFace (deed reception : G.Weld) : Prop :=
  LandsAt G deed reception ∧ G.KsmdAppropriates reception

/-- The source's vacuous reach-back ("an appropriating with nothing arrived
    to appropriate — not a falsehood ... but vacuous"): an actual,
    appropriating reception whose claimed deed never delivered to it. The
    vacuity is a property of this three-conjunct face; bare non-delivery
    alone is `NotDeliveredTo` and carries no appropriation. -/
def KsmdVacuousOwnershipFace (deed reception : G.Weld) : Prop :=
  NotDeliveredTo G deed reception ∧ G.Actual reception ∧ G.KsmdAppropriates reception

/-- The KannoSoe-ownership-face includes the report-face. -/
theorem ksmdReportFace_of_ksmdOwnershipFace
    {deed reception : G.Weld} (h : KsmdOwnershipFace G deed reception) :
    KsmdReportFace G deed reception :=
  h.left.left

/-- The KannoSoe-ownership-face includes actual reception. -/
theorem actual_of_ksmdOwnershipFace
    {deed reception : G.Weld} (h : KsmdOwnershipFace G deed reception) :
    G.Actual reception :=
  h.left.right

/-- The KannoSoe-ownership-face includes KannoSoe-appropriation at reception-time. -/
theorem ksmdAppropriates_of_ksmdOwnershipFace
    {deed reception : G.Weld} (h : KsmdOwnershipFace G deed reception) :
    G.KsmdAppropriates reception :=
  h.right

/-- Full landing plus KannoSoe-appropriation introduces the KannoSoe-ownership-face. -/
theorem ksmdOwnershipFace_intro
    {deed reception : G.Weld}
    (hland : LandsAt G deed reception) (happ : G.KsmdAppropriates reception) :
    KsmdOwnershipFace G deed reception :=
  ⟨hland, happ⟩

/-- Bare non-delivery cannot at the same time be a full KannoSoe-ownership-face for
    that deed and reception. -/
theorem not_ksmdOwnershipFace_of_vacuous
    {deed reception : G.Weld} (hv : NotDeliveredTo G deed reception) :
    ¬ KsmdOwnershipFace G deed reception :=
  fun hown => hv hown.left.left

/-- A vacuous KannoSoe-ownership attempt is not a full KannoSoe-ownership-face. -/
theorem not_ksmdOwnershipFace_of_ksmdVacuousOwnershipFace
    {deed reception : G.Weld} (hv : KsmdVacuousOwnershipFace G deed reception) :
    ¬ KsmdOwnershipFace G deed reception :=
  not_ksmdOwnershipFace_of_vacuous G hv.left

/-- The diachronic whose-question decomposes into delivery plus fresh
    KannoSoe-appropriation; no third cross-gap owner is part of this definition. -/
def KsmdDiachronicWhose (deed reception : G.Weld) : Prop :=
  DeliveredTo G deed reception ∧ G.KsmdAppropriates reception

theorem ksmdDiachronicWhose_iff_delivery_and_ksmdAppropriates
    (deed reception : G.Weld) :
    KsmdDiachronicWhose G deed reception ↔
      DeliveredTo G deed reception ∧ G.KsmdAppropriates reception :=
  Iff.rfl

/-- Delivery alone never settles the diachronic whose-question; the fresh
    reception-time appropriation conjunct is still required. -/
theorem no_diachronicWhose_from_series_alone
    {deed reception : G.Weld}
    (hno : ¬ G.KsmdAppropriates reception) :
    ¬ KsmdDiachronicWhose G deed reception := by
  intro hwhose
  exact hno ((ksmdDiachronicWhose_iff_delivery_and_ksmdAppropriates G
    deed reception).mp hwhose).right

/- ==============================================================================
   §2  Memory witness
============================================================================== -/

namespace MemoryWitness

/-- The trace-source deed in the checked recall witness. It deliberately repeats
    the prudence witness's concrete registers under fresh names: memory and
    prudence share the same display grid without coupling their namespaces. -/
def pastDeed : registerClockGrid.Weld :=
  registerWeld 1

/-- The later reception at which the trace is received and appropriated. -/
def recall : registerClockGrid.Weld :=
  registerWeld 2

/-- A claimed deed whose delivery line does not reach `recall`. -/
def confabulatedDeed : registerClockGrid.Weld :=
  registerWeld 0

/-- The trace-source deed is delivered to the later recall reception. -/
theorem trace_delivered :
    DeliveredTo registerClockGrid pastDeed recall :=
  rfl

theorem recall_ksmdAppropriates :
    registerClockGrid.KsmdAppropriates recall := by
  dsimp [Grid.KsmdAppropriates, Grid.HasSelfPoleIndex, Grid.share,
    registerClockGrid, recall, AtBot, shareBot]
  change ¬ (2 : Nat) ≤ 0
  exact Nat.not_succ_le_zero 1

/-- Genuine recall has the full ownership face: the trace lands at an actual
    later reception, and that reception freshly appropriates. -/
theorem recall_ksmdOwnershipFace :
    KsmdOwnershipFace registerClockGrid pastDeed recall :=
  ⟨⟨trace_delivered, rfl⟩, recall_ksmdAppropriates⟩

/-- The diachronic whose-question for recall is delivery plus fresh
    reception-time appropriation. -/
theorem recall_ksmdDiachronicWhose :
    KsmdDiachronicWhose registerClockGrid pastDeed recall :=
  ⟨trace_delivered, recall_ksmdAppropriates⟩

/-- The confabulated deed is not delivered to the recall reception. -/
theorem confabulated_not_delivered :
    NotDeliveredTo registerClockGrid confabulatedDeed recall := by
  dsimp [NotDeliveredTo, Grid.conditions, registerClockGrid, registerWeld,
    confabulatedDeed, recall]
  decide

/-- False memory has the vacuous ownership face: the reception is actual and
    appropriating, but the claimed deed did not arrive there. -/
theorem falseMemory_ksmdVacuousOwnershipFace :
    KsmdVacuousOwnershipFace registerClockGrid confabulatedDeed recall :=
  ⟨confabulated_not_delivered, ⟨rfl, recall_ksmdAppropriates⟩⟩

/-- The appropriating conjunct projected from the full recall face. -/
theorem fullFace_recall_ksmdAppropriates :
    registerClockGrid.KsmdAppropriates recall :=
  ksmdAppropriates_of_ksmdOwnershipFace registerClockGrid recall_ksmdOwnershipFace

/-- The appropriating conjunct projected from the vacuous false-memory face. -/
theorem vacuousFace_recall_ksmdAppropriates :
    registerClockGrid.KsmdAppropriates recall :=
  falseMemory_ksmdVacuousOwnershipFace.right.right

/-- Full recall and false memory share the same reception-side appropriation
    mark; the contrast is only whether delivery filled the second place. -/
theorem vacuity_not_inner_mark :
    registerClockGrid.KsmdAppropriates recall ∧
      registerClockGrid.KsmdAppropriates recall ∧
        ¬ KsmdOwnershipFace registerClockGrid confabulatedDeed recall :=
  ⟨fullFace_recall_ksmdAppropriates,
    vacuousFace_recall_ksmdAppropriates,
    not_ksmdOwnershipFace_of_ksmdVacuousOwnershipFace registerClockGrid
      falseMemory_ksmdVacuousOwnershipFace⟩

/-- Re-pitching into recall forgets every prior configuration: the mineness is
    made and spent at the recall weld, not stored in the trace. -/
theorem recall_spent
    (before1 before2 : Config Nat) :
    registerClockGrid.rePitch before1 recall =
      registerClockGrid.rePitch before2 recall :=
  registerClockGrid.rePitch_forgets before1 before2 recall

/-- The checked memory package: full recall, vacuous false memory, and
    recall-time spentness in one register-clock display. -/
theorem memory_witness :
    KsmdOwnershipFace registerClockGrid pastDeed recall ∧
      KsmdVacuousOwnershipFace registerClockGrid confabulatedDeed recall ∧
        (∀ before1 before2 : Config Nat,
          registerClockGrid.rePitch before1 recall =
            registerClockGrid.rePitch before2 recall) :=
  ⟨recall_ksmdOwnershipFace, falseMemory_ksmdVacuousOwnershipFace, recall_spent⟩

end MemoryWitness

/- ==============================================================================
   §2  Prudential privilege negative
============================================================================== -/

namespace PrudentialPrivilegeNegative

open BeingConvention

/-- The present-side fine register. -/
def deedAgent : RegisterCase :=
  .register 1

/-- The future-side fine register. -/
def receptionAgent : RegisterCase :=
  .register 2

/-- The future reception's mounted response. -/
def receptionResponse : RegisterCase :=
  .result 3

/-- The present concern/deed register in the checked prudence witness. -/
def deed : registerClockGrid.Weld :=
  registerWeld 1

/-- The future reception register delivered by `deed`. -/
def reception : registerClockGrid.Weld :=
  registerWeld 2

/-- The concrete actual pair used to route the witness through the same
    `ReceptionPair` carrier as the diachronic ownership vocabulary. -/
def pair : ReceptionPair registerClockGrid where
  first := { weld := deed, actual := rfl }
  second := { weld := reception, actual := rfl }

theorem pair_firstConditionsSecond :
    pair.FirstConditionsSecond := by
  rfl

theorem deed_ksmdAppropriates :
    registerClockGrid.KsmdAppropriates deed := by
  dsimp [Grid.KsmdAppropriates, Grid.HasSelfPoleIndex, Grid.share,
    registerClockGrid, deed, AtBot, shareBot]
  change ¬ (1 : Nat) ≤ 0
  exact Nat.not_succ_le_zero 0

theorem reception_ksmdAppropriates :
    registerClockGrid.KsmdAppropriates reception := by
  dsimp [Grid.KsmdAppropriates, Grid.HasSelfPoleIndex, Grid.share,
    registerClockGrid, reception, AtBot, shareBot]
  change ¬ (2 : Nat) ≤ 0
  exact Nat.not_succ_le_zero 1

/-- Ordinary diachronic ownership can be made at reception-time in the witness:
    delivery plus fresh KannoSoe-appropriation. -/
theorem reception_ksmdDiachronicWhose :
    KsmdDiachronicWhose registerClockGrid deed reception :=
  ⟨rfl, reception_ksmdAppropriates⟩

/-- The same pair also gives the full KannoSoe-ownership face. -/
theorem reception_ksmdOwnershipFace :
    KsmdOwnershipFace registerClockGrid deed reception :=
  ⟨⟨rfl, rfl⟩, reception_ksmdAppropriates⟩

/-- Merge reading: every fine register belongs to one macro tag. -/
abbrev kMerge : BeingCoarsening registerClockGrid Unit :=
  registerClockCoarsening

/-- Split reading: each fine register keeps its own macro tag. -/
def kSplit : BeingCoarsening registerClockGrid RegisterCase where
  proj := id

theorem merge_same_fiber :
    kMerge.SameFiber deedAgent receptionAgent :=
  rfl

/-- Pairwise boundary induced by the merge reading. -/
abbrev mergeBoundary (_p _q : RegisterCase) : Prop :=
  True

/-- Pairwise boundary induced by the split reading. -/
abbrev splitBoundary (p q : RegisterCase) : Prop :=
  p = q

theorem merge_boundary_holds :
    mergeBoundary deedAgent receptionAgent :=
  True.intro

theorem split_boundary_fails :
    ¬ ((RegisterCase.register 1) = (RegisterCase.register 2)) := by
  decide

/-- The grid data visible to a convention-free standing-owner recovery. -/
abbrev W : Type :=
  registerClockGrid.Weld

/-- Function, grade, and delivery data, with no supplied being-convention. -/
abbrev GridData : Type :=
  (RegisterCase -> RegisterCase -> Option RegisterCase) ×
    (RegisterCase -> Nat) ×
      (W -> W -> Prop)

def gridData : GridData :=
  (registerClockGrid.respondsTo, registerClockGrid.grade,
    registerClockGrid.conditions)

/-- A standing cross-gap "mine" relation over the witness grid. -/
abbrev StandingMine : Type :=
  registerClockGrid.Weld -> registerClockGrid.Weld -> Prop

/-- Agreement with the merge convention at the prudential pair. -/
def AgreesWithMergeAt (mine : StandingMine) : Prop :=
  mine deed reception ↔ mergeBoundary deedAgent receptionAgent

/-- Agreement with the split convention at the same prudential pair. -/
def AgreesWithSplitAt (mine : StandingMine) : Prop :=
  mine deed reception ↔ splitBoundary deedAgent receptionAgent

/-- Prudential privilege, as a checked recovery claim: from the grid data alone,
    recover a standing cross-gap "mine" relation that settles the pair before
    any supplied being-convention. Such a relation would have to agree with
    both legal readings of the same grid data. -/
def PrudentialPrivilege : Prop :=
  ∃ recover : GridData -> StandingMine,
    AgreesWithMergeAt (recover gridData) ∧
      AgreesWithSplitAt (recover gridData)

/-- The prudential privilege recovery claim fails in the register-clock witness:
    the merge and split being-conventions are both legal, but they disagree on
    whether the present deed-register and the future reception-register share a
    fiber. -/
theorem not_prudentialPrivilege :
    ¬ PrudentialPrivilege := by
  rintro ⟨recover, hmerge, hsplit⟩
  have hmine : recover gridData deed reception :=
    hmerge.mpr merge_boundary_holds
  have hnotMine : ¬ recover gridData deed reception := by
    intro h
    exact split_boundary_fails (hsplit.mp h)
  exact hnotMine hmine

/-- Re-pitching the actual pair leaves the final configuration reading only the
    received future weld's share. The prior tendency is not an inheritance
    register for the deed-side owner. -/
theorem rePitchSequence_final_forgets_prior
    (before1 before2 : Config Nat) :
    (ReceptionPair.rePitchSequence (G := registerClockGrid) before1 pair).snd =
      (ReceptionPair.rePitchSequence (G := registerClockGrid) before2 pair).snd :=
  registerClockGrid.rePitch_forgets
    (registerClockGrid.rePitch before1 pair.first.weld)
    (registerClockGrid.rePitch before2 pair.first.weld)
    pair.second.weld

/-- The final tendency of the pair is just the future reception's share. -/
theorem rePitchSequence_final_tendency
    (before : Config Nat) :
    (ReceptionPair.rePitchSequence (G := registerClockGrid) before pair).snd.tendency =
      registerClockGrid.share reception :=
  rfl

/-- The grade side of the witness does not inspect downstream delivery
    conditions. -/
theorem deed_grade_independent_of_conditions
    (conditions1 conditions2 :
      RegisterCase -> RegisterCase -> Prop) :
    (registerClockGrid.withConditions conditions1).grade
        deed.1 =
      (registerClockGrid.withConditions conditions2).grade
        deed.1 :=
  registerClockGrid.grade_independent_of_conditions
    conditions1 conditions2 deed.1

/-- The checked prudence package: fresh reception-time ownership is available,
    but standing grid-data privilege, stored inheritance, and delivery-sensitive
    grading are not. -/
theorem prudentialPrivilege_failure_modes :
    KsmdDiachronicWhose registerClockGrid deed reception ∧
      ¬ PrudentialPrivilege ∧
        (∀ before1 before2 : Config Nat,
          (ReceptionPair.rePitchSequence (G := registerClockGrid) before1 pair).snd =
            (ReceptionPair.rePitchSequence (G := registerClockGrid) before2 pair).snd) ∧
          (∀ conditions1 conditions2 :
            RegisterCase -> RegisterCase -> Prop,
            (registerClockGrid.withConditions conditions1).grade
                deed.1 =
              (registerClockGrid.withConditions conditions2).grade
                deed.1) :=
  ⟨reception_ksmdDiachronicWhose, not_prudentialPrivilege,
    rePitchSequence_final_forgets_prior, deed_grade_independent_of_conditions⟩

end PrudentialPrivilegeNegative

end DirectedConvention

/- ==============================================================================
   §2  Token-reflexivity
============================================================================== -/

/-- Token-reflexivity as a projection identity. Deliberately a `def` that
    can never fail (`selfAnchored` proves it for every weld): the content
    is the identity's *shape* — no route to "this act's agent" except
    through the completed weld — displayed, not risked. -/
def SelfAnchored (w : G.Weld) : Prop :=
  G.index w = w.agent

omit [PreorderBot Contrib] in
theorem selfAnchored (w : G.Weld) : SelfAnchored G w := rfl

/- ==============================================================================
   §3  Pole-typing and the verdict's own tier
============================================================================== -/

/-- The state-tool fits exactly when no live self-pole index remains. -/
def StateToolFits (w : G.Weld) : Prop :=
  ¬ G.HasSelfPoleIndex w

/-- The pole-class is the constructive direction of the pole-typing
    corollary: no self-pole index remains for a state-tool to miss. -/
theorem stateToolFits_of_atBot
    {w : G.Weld} (hshare : AtBot (G.share w)) :
    StateToolFits G w :=
  G.no_self_pole_index_of_atBot w hshare

/-- Literal equality with the designated bottom is a bridge into the
    pole-class pole-typing corollary. -/
theorem stateToolFits_of_eq_shareBot
    {w : G.Weld} (hshare : G.share w = shareBot) :
    StateToolFits G w :=
  stateToolFits_of_atBot G (atBot_of_eq_shareBot hshare)

/-- With decidability of the one pole-class comparison, pole-typing can be
    read as an iff: the state-tool fits just where the share is at the
    pole-class. -/
theorem atBot_of_stateToolFits {w : G.Weld}
    [Decidable (AtBot (G.share w))] (hfits : StateToolFits G w) :
    AtBot (G.share w) := by
  by_cases hshare : AtBot (G.share w)
  · exact hshare
  · exact False.elim (hfits hshare)

/-- With decidability of the one pole-class comparison, pole-typing is an
    exact iff. -/
theorem stateToolFits_iff_atBot (w : G.Weld)
    [Decidable (AtBot (G.share w))] :
    StateToolFits G w ↔ AtBot (G.share w) :=
  ⟨atBot_of_stateToolFits G, stateToolFits_of_atBot G⟩

/-- Terminus responses are reducible in the corollary's sense. -/
theorem stateToolFits_of_terminus_response
    {w : G.Weld}
    (hterm : G.Terminus w.agent) (hactual : G.Actual w) :
    StateToolFits G w :=
  G.no_self_pole_index_of_terminus_response hterm hactual

namespace DirectedConvention

/-- If the state-tool fits a reception, the KannoSoe-ownership-face cannot fire there. -/
theorem not_ksmdOwnershipFace_of_stateToolFits
    {deed reception : G.Weld} (hfits : StateToolFits G reception) :
    ¬ KsmdOwnershipFace G deed reception :=
  fun hown => hfits hown.right

end DirectedConvention

-- The paper's "a mis-feed at the floor is not a claim" verdict is carried
-- by `not_collapse_floor`; no separate theorem restates it.

/-- A distinction obeying the separate/fuse rule fuses at the floor. -/
theorem obeysRule_fuses_at_floor
    {d : Distinction G} (h : d.ObeysSeparateFuse) :
    d.Fused (Tier.floor : Tier G) :=
  G.fused_of_obeysSeparateFuse h Tier.floor

/-- The same distinction separates at live act-time diagnosis. -/
theorem obeysRule_separates_at_actTime
    {d : Distinction G} (h : d.ObeysSeparateFuse)
    {w : G.Weld} (hidx : G.HasSelfPoleIndex w) :
    d.Separated (Tier.actTime w) :=
  G.separated_of_obeysSeparateFuse h hidx

/- ==============================================================================
   §4  The office-spine and contemporary placements
============================================================================== -/

end Grid

/-- The KannoSoe-offices karmic ownership holds in the paper's identity-claim. -/
inductive KsmdOwnershipOffice
  | cetana
  | reception
  | practice
  | remorse
  | absolution
  | dedication

namespace KsmdOwnershipOffice

variable {Designatum Contrib : Type} [PreorderBot Contrib] {G : CoreReadings Designatum Contrib}

/-- Each office is assigned to a weld's act-time tier (the office
    argument is unused). The paper's further claim — discharged *not by a
    cross-gap state* — is architectural, carried by what `Config` does not
    contain and by the absence of any `Config`-consuming assignment
    function; it is not this definition's proposition. -/
def assignedTier (_office : KsmdOwnershipOffice) (w : G.Weld) : Grid.Tier G :=
  Grid.Tier.actTime w

omit [PreorderBot Contrib] in
theorem assignedTier_eq_actTime (office : KsmdOwnershipOffice) (w : G.Weld) :
    office.assignedTier w = Grid.Tier.actTime w := rfl

/-- Assigning an office to act-time has exactly the weld's live-share
    condition. -/
theorem assignedTier_hasLiveShare_iff
    (office : KsmdOwnershipOffice) (w : G.Weld) :
    Grid.Tier.hasLiveShare G (office.assignedTier w) ↔
      G.HasSelfPoleIndex w :=
  Iff.rfl

end KsmdOwnershipOffice

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

namespace SelfLineWitness

inductive Designatum
  | one
  | call
  | response
  | occurrence

def selfLineOccurrence : OccurrenceReading Designatum where
  occurrence d := d = .occurrence
  isBeing d := d = .one
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .occurrence => .one
    | d => d
  call
    | .occurrence => .call
    | d => d
  response
    | .occurrence => .response
    | d => d

def selfLineGrid : CoreReadings Designatum Nat where
  occurrence := selfLineOccurrence
  response := {
    respondsTo := fun _ _ => some .response
  }
  placement := {
    grade := fun _ => 1
  }
  conditioning := {
    conditions := fun _ _ => True
  }

def w : selfLineGrid.Weld :=
  ⟨.occurrence, rfl⟩

theorem w_ksmdAppropriates : selfLineGrid.KsmdAppropriates w := by
  intro hbot
  cases hbot

theorem selfLine_conditions_self : selfLineGrid.conditions w w :=
  True.intro

theorem selfLine_landsAt_self : Grid.DirectedConvention.LandsAt selfLineGrid w w :=
  ⟨True.intro, rfl⟩

theorem selfLine_ksmdOwnershipFace_self :
    Grid.DirectedConvention.KsmdOwnershipFace selfLineGrid w w :=
  ⟨⟨True.intro, rfl⟩, w_ksmdAppropriates⟩

end SelfLineWitness

end KannoSoe
