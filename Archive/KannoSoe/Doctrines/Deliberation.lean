/-
================================================================================
  KannoSoe.Doctrines.Deliberation
  Consequentialist display and deliberator-side underdetermination
================================================================================

This module records the checked face of the deliberator block: drop-counting as
a reading, the non-accumulation consequence of `rePitch`, the being-boundary and
transfer countermodels, invariance of grade under delivery conditions, and a
claim-language witness for delivery-arrogation.

Reading and motivation: Identification/Commentary.lean, C.5.
-/

import KannoSoe.Consequences.Basic

namespace KannoSoe

namespace Grid

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/- ==============================================================================
   Consequentialist convention: descriptive readings only
============================================================================== -/

namespace ConsequentialistConvention

open DirectedConvention.BeingConvention

/-- The deliberator's finite sample: an initial configuration and a finite list
    of actual receptions. No measure, utility, probability, or command over
    delivery is added. -/
structure DeliberationSample (G : CoreReadings Designatum Contrib) where
  before : Config Contrib
  run    : List (ActualWeld G)

/-- A descriptive objective candidate. Its domain is explicit so that further
    conventions have to be supplied as arguments rather than recovered from the
    grid. -/
abbrev Objective (G : CoreReadings Designatum Contrib) (Convention Value : Type) :=
  DeliberationSample G -> Convention -> Value

/-- Count share-drop receptions through a finite actual run, re-pitching after
    every reception. -/
def DropCount
    [∀ before received, Decidable (G.IsShareDrop before received)]
    (before : Config Contrib) : List (ActualWeld G) -> Nat
  | [] => 0
  | aw :: rest =>
      let after := G.rePitch before aw.weld
      let tail := DropCount after rest
      if G.IsShareDrop before aw.weld then tail + 1 else tail

theorem dropCount_eq_match
    [∀ before received, Decidable (G.IsShareDrop before received)]
    (before : Config Contrib) (run : List (ActualWeld G)) :
    DropCount G before run =
      match run with
      | [] => 0
      | aw :: rest =>
          let after := G.rePitch before aw.weld
          let tail := DropCount G after rest
          if G.IsShareDrop before aw.weld then tail + 1 else tail := by
  cases run <;> rfl

/-- The same count restricted by a supplied being-coarsening. The run still
    re-pitches at every actual reception; only the counted events are filtered
    by the convention. -/
def DropCountInFiber
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (b : Macro)
    (before : Config Contrib) : List (ActualWeld G) -> Nat
  | [] => 0
  | aw :: rest =>
      let after := G.rePitch before aw.weld
      let tail := DropCountInFiber κ b after rest
      if κ.InFiber b aw.weld then
        if G.IsShareDrop before aw.weld then tail + 1 else tail
      else tail

theorem dropCountInFiber_eq_match
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (b : Macro) (before : Config Contrib) (run : List (ActualWeld G)) :
    DropCountInFiber G κ b before run =
      match run with
      | [] => 0
      | aw :: rest =>
          let after := G.rePitch before aw.weld
          let tail := DropCountInFiber G κ b after rest
          if κ.InFiber b aw.weld then
            if G.IsShareDrop before aw.weld then tail + 1 else tail
          else tail := by
  cases run <;> rfl

/-- Sum fiber-restricted drop counts over a supplied finite macro-tag list. -/
def DropCountInFiberSum
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (tags : List Macro) (before : Config Contrib)
    (run : List (ActualWeld G)) : Nat :=
  match tags with
  | [] => 0
  | b :: rest =>
      DropCountInFiber G κ b before run +
        DropCountInFiberSum κ rest before run

theorem dropCountInFiber_le_dropCount
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (b : Macro) (before : Config Contrib)
    (run : List (ActualWeld G)) :
    DropCountInFiber G κ b before run ≤ DropCount G before run := by
  induction run generalizing before with
  | nil =>
      exact Nat.le_refl 0
  | cons aw rest ih =>
      unfold DropCountInFiber DropCount
      by_cases hfiber : κ.InFiber b aw.weld
      · by_cases hdrop : G.IsShareDrop before aw.weld
        · simp [hfiber, hdrop, ih]
        · simp [hfiber, hdrop, ih]
      · by_cases hdrop : G.IsShareDrop before aw.weld
        · simp [hfiber, hdrop]
          exact Nat.le_trans (ih (G.rePitch before aw.weld))
            (Nat.le_succ _)
        · simp [hfiber, hdrop, ih]

theorem dropCountInFiberSum_nil_run
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (tags : List Macro) (before : Config Contrib) :
    DropCountInFiberSum G κ tags before [] = 0 := by
  induction tags with
  | nil =>
      rfl
  | cons b rest ih =>
      unfold DropCountInFiberSum DropCountInFiber
      simp [ih]

theorem dropCountInFiberSum_cons_run_of_agent_not_mem
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (tags : List Macro) (before : Config Contrib)
    (aw : ActualWeld G) (rest : List (ActualWeld G))
    (hnotmem : κ.proj aw.weld.agent ∉ tags) :
    DropCountInFiberSum G κ tags before (aw :: rest) =
      DropCountInFiberSum G κ tags (G.rePitch before aw.weld) rest := by
  induction tags with
  | nil =>
      rfl
  | cons b tags ih =>
      simp at hnotmem
      have hnotFiber : ¬ κ.InFiber b aw.weld := by
        intro hfiber
        exact hnotmem.left hfiber
      unfold DropCountInFiberSum DropCountInFiber
      simp [hnotFiber, ih hnotmem.right]
      rw [← dropCountInFiber_eq_match (G := G) κ b
        (G.rePitch before aw.weld) rest]

theorem dropCountInFiberSum_cons_run_of_not_shareDrop
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (tags : List Macro) (before : Config Contrib)
    (aw : ActualWeld G) (rest : List (ActualWeld G))
    (hdrop : ¬ G.IsShareDrop before aw.weld) :
    DropCountInFiberSum G κ tags before (aw :: rest) =
      DropCountInFiberSum G κ tags (G.rePitch before aw.weld) rest := by
  induction tags with
  | nil =>
      rfl
  | cons b tags ih =>
      unfold DropCountInFiberSum DropCountInFiber
      by_cases hfiber : κ.InFiber b aw.weld
      · simp [hfiber, hdrop, ih]
        rw [← dropCountInFiber_eq_match (G := G) κ b
          (G.rePitch before aw.weld) rest]
      · simp [hfiber, ih]
        rw [← dropCountInFiber_eq_match (G := G) κ b
          (G.rePitch before aw.weld) rest]

theorem dropCountInFiberSum_cons_run_of_shareDrop
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (tags : List Macro) (before : Config Contrib)
    (aw : ActualWeld G) (rest : List (ActualWeld G))
    (hnodup : tags.Nodup)
    (hmem : κ.proj aw.weld.agent ∈ tags)
    (hdrop : G.IsShareDrop before aw.weld) :
    DropCountInFiberSum G κ tags before (aw :: rest) =
      DropCountInFiberSum G κ tags (G.rePitch before aw.weld) rest + 1 := by
  induction tags with
  | nil =>
      cases hmem
  | cons b tags ih =>
      cases hnodup with
      | cons hnotmem hnodup =>
          by_cases hfiber : κ.InFiber b aw.weld
          · have htailNotMem : κ.proj aw.weld.agent ∉ tags := by
              intro htail
              exact (hnotmem (κ.proj aw.weld.agent) htail) hfiber.symm
            have htail :=
              dropCountInFiberSum_cons_run_of_agent_not_mem
                (G := G) κ tags before aw rest htailNotMem
            unfold DropCountInFiberSum DropCountInFiber
            simp [hfiber, hdrop, htail]
            rw [← dropCountInFiber_eq_match (G := G) κ b
              (G.rePitch before aw.weld) rest]
            simp [Nat.add_assoc, Nat.add_comm]
          · have hneq : κ.proj aw.weld.agent ≠ b := hfiber
            have htailMem : κ.proj aw.weld.agent ∈ tags := by
              simpa [hneq] using hmem
            have htail := ih hnodup htailMem
            unfold DropCountInFiberSum DropCountInFiber
            simp [hfiber, htail, Nat.add_assoc]
            rw [← dropCountInFiber_eq_match (G := G) κ b
              (G.rePitch before aw.weld) rest]

theorem dropCount_eq_sum_dropCountInFiber
    [∀ before received, Decidable (G.IsShareDrop before received)]
    {Macro : Type} (κ : BeingCoarsening G Macro)
    [∀ b w, Decidable (κ.InFiber b w)]
    (tags : List Macro) (hnodup : tags.Nodup)
    (hmem : ∀ p : Designatum, κ.proj p ∈ tags)
    (before : Config Contrib) (run : List (ActualWeld G)) :
    DropCountInFiberSum G κ tags before run = DropCount G before run := by
  induction run generalizing before with
  | nil =>
      simpa [DropCount] using
        (dropCountInFiberSum_nil_run (G := G) κ tags before)
  | cons aw rest ih =>
      by_cases hdrop : G.IsShareDrop before aw.weld
      · calc
          DropCountInFiberSum G κ tags before (aw :: rest)
              = DropCountInFiberSum G κ tags (G.rePitch before aw.weld) rest + 1 :=
                dropCountInFiberSum_cons_run_of_shareDrop
                  (G := G) κ tags before aw rest hnodup (hmem aw.weld.agent) hdrop
          _ = DropCount G (G.rePitch before aw.weld) rest + 1 := by
                exact congrArg (fun n => n + 1)
                  (ih (G.rePitch before aw.weld))
          _ = DropCount G before (aw :: rest) := by
                unfold DropCount
                simp [hdrop]
                rw [← dropCount_eq_match (G := G)
                  (G.rePitch before aw.weld) rest]
      · calc
          DropCountInFiberSum G κ tags before (aw :: rest)
              = DropCountInFiberSum G κ tags (G.rePitch before aw.weld) rest :=
                dropCountInFiberSum_cons_run_of_not_shareDrop
                  (G := G) κ tags before aw rest hdrop
          _ = DropCount G (G.rePitch before aw.weld) rest := by
                exact ih (G.rePitch before aw.weld)
          _ = DropCount G before (aw :: rest) := by
                unfold DropCount
                simp [hdrop]
                rw [← dropCount_eq_match (G := G)
                  (G.rePitch before aw.weld) rest]

/-- Claim object for a plan that treats delivery as commanded: this deed's
    fruit is asserted to land at that reception. -/
structure DeliveryCommand (G : CoreReadings Designatum Contrib) where
  deed      : G.Weld
  reception : G.Weld

/-- A tiny object language for delivery-command claims. It makes such claims
    satisfiable only where the field-side delivery relation holds. -/
def deliveryCommandLanguage (G : CoreReadings Designatum Contrib) : ClaimLanguage G where
  Claim := DeliveryCommand G
  Holds
    | .floor, _ => False
    | .actTime _, claim =>
        DirectedConvention.DeliveredTo G claim.deed claim.reception

omit [PreorderBot Contrib] in
/-- A recorded delivery-command utterance fits its offered tier only when the
    commanded delivery is in fact delivered. -/
theorem deliveryCommand_unfit_of_not_delivered
    (u : RecordedUtterance G (deliveryCommandLanguage G))
    (hnot : ¬ DirectedConvention.DeliveredTo G u.content.deed u.content.reception) :
    ¬ u.FitsOfferedTier := by
  intro hfit
  change (deliveryCommandLanguage G).TrueAt u.offeredAt u.content at hfit
  cases hoff : u.offeredAt with
  | floor =>
      rw [hoff] at hfit
      exact hfit.elim
  | actTime _ =>
      rw [hoff] at hfit
      dsimp [deliveryCommandLanguage, ClaimLanguage.TrueAt] at hfit
      exact hnot hfit

end ConsequentialistConvention

end Grid

namespace AccumulationNegative

/-- Named face of `Grid.rePitch_forgets` for the deliberator block. -/
theorem rePitch_forgets
    {Designatum Contrib : Type} [PreorderBot Contrib] (G : CoreReadings Designatum Contrib)
    (before₁ before₂ : Config Contrib) (received : G.Weld) :
    G.rePitch before₁ received = G.rePitch before₂ received :=
  Grid.rePitch_forgets G before₁ before₂ received

/-- Named face of the no-accumulation corollary for run-valued scores that
    factor through `Config`. -/
theorem accumulated_attainment_constant_of_same_final
    {Designatum Contrib α : Type} [PreorderBot Contrib]
    (G : CoreReadings Designatum Contrib)
    (score : Config Contrib -> α)
    (before₁ before₂ : Config Contrib) (received : G.Weld) :
    score (G.rePitch before₁ received) =
      score (G.rePitch before₂ received) :=
  Grid.accumulated_attainment_constant_of_same_final
    G score before₁ before₂ received

end AccumulationNegative

/- ==============================================================================
   Objective negative: "my drops" requires a supplied being-convention
============================================================================== -/

namespace ObjectiveNegative

open Grid
open Grid.ConsequentialistConvention
open Grid.DirectedConvention.BeingConvention

/-- Two fine tags with different live shares. Merging or splitting them is still
    a diagnosis-time convention; the grid itself carries no macro owner. -/
inductive ObjectiveDesignatum
  | falseAgent
  | trueAgent
  | cue
  | response
  | falseOccurrence
  | trueOccurrence
deriving DecidableEq

def objectiveOccurrence : OccurrenceReading ObjectiveDesignatum where
  occurrence d := d = .falseOccurrence ∨ d = .trueOccurrence
  isBeing d := d = .falseAgent ∨ d = .trueAgent
  isCall d := d = .cue
  isResponse d := d = .response
  agent d :=
    match d with
    | .falseOccurrence => .falseAgent
    | .trueOccurrence => .trueAgent
    | _ => d
  call d :=
    match d with
    | .falseOccurrence | .trueOccurrence => .cue
    | _ => d
  response d :=
    match d with
    | .falseOccurrence | .trueOccurrence => .response
    | _ => d

def objectiveGrid : CoreReadings ObjectiveDesignatum Nat where
  occurrence := objectiveOccurrence
  response := {
    respondsTo := fun b c =>
      if (b = .falseAgent ∨ b = .trueAgent) ∧ c = .cue
      then some .response
      else none
  }
  placement := {
    grade := fun d =>
      match d with
      | .falseOccurrence => 2
      | .trueOccurrence => 1
      | _ => 0
  }
  conditioning := { conditions := fun _ _ => True }

instance objectiveGrid_isShareDrop_decidable
    (before : Config Nat) (received : objectiveGrid.Weld) :
    Decidable (objectiveGrid.IsShareDrop before received) := by
  rcases received with ⟨d, hd⟩
  cases d with
  | falseAgent | trueAgent | cue | response =>
      change Decidable (((0 : Nat) ≤ before.tendency) ∧
        ¬ before.tendency ≤ (0 : Nat))
      infer_instance
  | falseOccurrence =>
      change Decidable (((2 : Nat) ≤ before.tendency) ∧
        ¬ before.tendency ≤ (2 : Nat))
      infer_instance
  | trueOccurrence =>
      change Decidable (((1 : Nat) ≤ before.tendency) ∧
        ¬ before.tendency ≤ (1 : Nat))
      infer_instance

def mergeCoarsening : BeingCoarsening objectiveGrid Unit where
  proj _ := ()

def splitCoarsening : BeingCoarsening objectiveGrid Bool where
  proj p := if p = .trueAgent then true else false

instance mergeCoarsening_inFiber_decidable
    (b : Unit) (w : objectiveGrid.Weld) :
    Decidable (mergeCoarsening.InFiber b w) := by
  dsimp [Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber,
    mergeCoarsening]
  infer_instance

instance splitCoarsening_inFiber_decidable
    (b : Bool) (w : objectiveGrid.Weld) :
    Decidable (splitCoarsening.InFiber b w) := by
  dsimp [Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber,
    splitCoarsening]
  infer_instance

def wFalse : objectiveGrid.Weld :=
  ⟨.falseOccurrence, Or.inl rfl⟩

def wTrue : objectiveGrid.Weld :=
  ⟨.trueOccurrence, Or.inr rfl⟩

def before : Config Nat := { tendency := 3 }

def run : List (ActualWeld objectiveGrid) := [
  { weld := wFalse, actual := rfl },
  { weld := wTrue, actual := rfl } ]

def mergedDropCount : Nat :=
  DropCountInFiber objectiveGrid mergeCoarsening () before run

def splitFalseDropCount : Nat :=
  DropCountInFiber objectiveGrid splitCoarsening false before run

def splitTrueDropCount : Nat :=
  DropCountInFiber objectiveGrid splitCoarsening true before run

def splitDropCountSum : Nat :=
  DropCountInFiberSum objectiveGrid splitCoarsening [false, true] before run

theorem merge_dropCount :
    mergedDropCount = 2 := by
  decide

theorem split_false_dropCount :
    splitFalseDropCount = 1 := by
  decide

theorem split_true_dropCount :
    splitTrueDropCount = 1 := by
  decide

theorem split_dropCount_sum :
    splitDropCountSum = 2 := by
  decide

theorem split_dropCount_sum_eq_mergedDropCount :
    splitDropCountSum = mergedDropCount := by
  decide

/-- The same finite run receives different "my drops" counts under different
    legal being conventions. -/
theorem fiber_dropCounts_differ :
    mergedDropCount ≠ splitFalseDropCount := by
  decide

abbrev W := objectiveGrid.Weld

/-- The grid data visible to a convention-free recovery function. -/
abbrev GridData : Type :=
  (ObjectiveDesignatum -> ObjectiveDesignatum -> Option ObjectiveDesignatum) ×
    (ObjectiveDesignatum -> Nat) ×
      (ObjectiveDesignatum -> ObjectiveDesignatum -> Prop)

def gridData : GridData :=
  (objectiveGrid.respondsTo, objectiveGrid.grade,
    objectiveGrid.conditioning.conditions)

/-- No convention-free function of the same grid data can return both legal
    "my drop" readings. -/
theorem no_grid_data_objective_for_my_drops :
    ¬ ∃ recover : GridData -> Nat,
        recover gridData = mergedDropCount ∧
        recover gridData = splitFalseDropCount := by
  rintro ⟨_recover, hmerge, hsplit⟩
  exact fiber_dropCounts_differ (hmerge.symm.trans hsplit)

end ObjectiveNegative

/- ==============================================================================
   Transfer negative: track records underdetermine adaptive landing
============================================================================== -/

namespace TransferNegative

inductive TransferDesignatum
  | teacher
  | seen
  | fresh
  | track
  | lands
  | misses
  | seenOccurrence
  | landingFreshOccurrence
  | missingFreshOccurrence
  | staticFreshOccurrence
deriving DecidableEq

namespace Teacher
abbrev teacher : TransferDesignatum := .teacher
end Teacher

namespace Call
abbrev seen : TransferDesignatum := .seen
abbrev fresh : TransferDesignatum := .fresh
end Call

namespace Response
abbrev track : TransferDesignatum := .track
abbrev lands : TransferDesignatum := .lands
abbrev misses : TransferDesignatum := .misses
end Response

def trackClass : TransferDesignatum -> Prop
  | .seen  => True
  | _ => False

def transferOccurrence : OccurrenceReading TransferDesignatum where
  occurrence d :=
    d = .seenOccurrence ∨ d = .landingFreshOccurrence ∨
      d = .missingFreshOccurrence ∨ d = .staticFreshOccurrence
  isBeing d := d = .teacher
  isCall d := d = .seen ∨ d = .fresh
  isResponse d := d = .track ∨ d = .lands ∨ d = .misses
  agent d :=
    match d with
    | .seenOccurrence | .landingFreshOccurrence
    | .missingFreshOccurrence | .staticFreshOccurrence => .teacher
    | _ => d
  call d :=
    match d with
    | .seenOccurrence => .seen
    | .landingFreshOccurrence | .missingFreshOccurrence
    | .staticFreshOccurrence => .fresh
    | _ => d
  response d :=
    match d with
    | .seenOccurrence | .staticFreshOccurrence => .track
    | .landingFreshOccurrence => .lands
    | .missingFreshOccurrence => .misses
    | _ => d

def trackedOccurrence : TransferDesignatum → TransferDesignatum
  | .seen => .seenOccurrence
  | d => d

def landingGrid : CoreReadings TransferDesignatum Nat where
  occurrence := transferOccurrence
  response := {
    respondsTo := fun b c =>
      if b = .teacher then
        match c with
        | .seen => some .track
        | .fresh => some .lands
        | _ => none
      else none
  }
  placement := {
    grade := fun d =>
      match d with
      | .seenOccurrence => 5
      | .landingFreshOccurrence => 0
      | _ => 0
  }
  conditioning := { conditions := fun _ _ => True }

def missingGrid : CoreReadings TransferDesignatum Nat where
  occurrence := transferOccurrence
  response := {
    respondsTo := fun b c =>
      if b = .teacher then
        match c with
        | .seen => some .track
        | .fresh => some .misses
        | _ => none
      else none
  }
  placement := {
    grade := fun d =>
      match d with
      | .seenOccurrence => 5
      | .missingFreshOccurrence => 1
      | _ => 0
  }
  conditioning := { conditions := fun _ _ => True }

/-- The restricted track record: response and grade behavior on the seen call. -/
abbrev TrackData : Type := Option TransferDesignatum × Nat

def landingTrackData : TrackData :=
  (landingGrid.respondsTo Teacher.teacher Call.seen,
    landingGrid.grade .seenOccurrence)

def missingTrackData : TrackData :=
  (missingGrid.respondsTo Teacher.teacher Call.seen,
    missingGrid.grade .seenOccurrence)

theorem restricted_track_agrees :
    landingTrackData = missingTrackData :=
  rfl

theorem respondsTo_agrees_on_trackClass
    {c : TransferDesignatum} (hc : trackClass c) :
    landingGrid.respondsTo Teacher.teacher c =
      missingGrid.respondsTo Teacher.teacher c := by
  cases c <;> simp_all [trackClass, landingGrid, missingGrid]

theorem grade_agrees_on_trackClass
    {c : TransferDesignatum} (hc : trackClass c) :
    landingGrid.grade (trackedOccurrence c) =
      missingGrid.grade (trackedOccurrence c) := by
  cases c <;>
    simp_all [trackClass, trackedOccurrence, landingGrid, missingGrid]

def landingFreshEffect : Nat :=
  landingGrid.grade .landingFreshOccurrence

def missingFreshEffect : Nat :=
  missingGrid.grade .missingFreshOccurrence

theorem fresh_effect_disagrees :
    landingFreshEffect ≠ missingFreshEffect := by
  decide

theorem landing_adaptive :
    landingGrid.ResponseVariesWithCall Teacher.teacher := by
  refine ⟨Call.seen, Call.fresh, Response.track, Response.lands, rfl, rfl, ?_⟩
  intro h
  cases h

theorem missing_adaptive :
    missingGrid.ResponseVariesWithCall Teacher.teacher := by
  refine ⟨Call.seen, Call.fresh, Response.track, Response.misses, rfl, rfl, ?_⟩
  intro h
  cases h

/-- Agreement on the teacher's whole seen track record does not determine the
    fresh-call effect for adaptive responders. -/
theorem no_estimator_from_restricted_track :
    ¬ ∃ estimate : TrackData -> Nat,
        estimate landingTrackData = landingFreshEffect ∧
        estimate missingTrackData = missingFreshEffect := by
  rintro ⟨estimate, hlanding, hmissing⟩
  have heq : landingFreshEffect = missingFreshEffect := by
    calc
      landingFreshEffect = estimate landingTrackData := hlanding.symm
      _ = estimate missingTrackData := congrArg estimate restricted_track_agrees
      _ = missingFreshEffect := hmissing
  exact fresh_effect_disagrees heq

theorem adaptive_track_record_underdetermines_new_effect :
    landingGrid.ResponseVariesWithCall Teacher.teacher ∧
      missingGrid.ResponseVariesWithCall Teacher.teacher ∧
      landingTrackData = missingTrackData ∧
      landingFreshEffect ≠ missingFreshEffect ∧
      ¬ ∃ estimate : TrackData -> Nat,
          estimate landingTrackData = landingFreshEffect ∧
          estimate missingTrackData = missingFreshEffect :=
  ⟨landing_adaptive, missing_adaptive, restricted_track_agrees,
    fresh_effect_disagrees, no_estimator_from_restricted_track⟩

/-- In the invariant/static case, any mounted fresh-call response is the same
    response already seen in the restricted record. This is the contrast case:
    transfer holds exactly where response-adaptivity is absent. -/
theorem responseInvariant_determines_response
    {Designatum Contrib : Type} [PreorderBot Contrib] {G : CoreReadings Designatum Contrib}
    {b : Designatum} {seen fresh : Designatum} {rSeen rFresh : Designatum}
    (h : G.ResponseInvariant b)
    (hseen : G.respondsTo b seen = some rSeen)
    (hfresh : G.respondsTo b fresh = some rFresh) :
    rFresh = rSeen :=
  h fresh seen rFresh rSeen hfresh hseen

def staticGrid : CoreReadings TransferDesignatum Nat where
  occurrence := transferOccurrence
  response := {
    respondsTo := fun b _ =>
      if b = .teacher then some .track else none
  }
  placement := { grade := fun _ => 5 }
  conditioning := { conditions := fun _ _ => True }

theorem static_responseInvariant :
    staticGrid.ResponseInvariant Teacher.teacher := by
  intro _c₁ _c₂ _r₁ _r₂ h₁ h₂
  change some .track = some _r₁ at h₁
  change some .track = some _r₂ at h₂
  exact Option.some.inj (h₁.symm.trans h₂)

theorem static_fresh_response_determined :
    Response.track = Response.track :=
  responseInvariant_determines_response
    (G := staticGrid) (b := Teacher.teacher)
    (seen := Call.seen) (fresh := Call.fresh)
    (rSeen := Response.track) (rFresh := Response.track)
    static_responseInvariant rfl rfl

end TransferNegative

/- ==============================================================================
   Delivery-arrogation negative: a command is quotable, not satisfiable
============================================================================== -/

namespace DeliveryArrogationNegative

open Grid
open Grid.ConsequentialistConvention

inductive Designatum
  | planner
  | deed
  | fruit
  | utter
  | deedOccurrence
  | receptionOccurrence
deriving DecidableEq

namespace Being
abbrev planner : Designatum := .planner
end Being

namespace Call
abbrev deed : Designatum := .deed
abbrev fruit : Designatum := .fruit
end Call

namespace Response
abbrev utter : Designatum := .utter
end Response

def commandOccurrence : OccurrenceReading Designatum where
  occurrence d := d = .deedOccurrence ∨ d = .receptionOccurrence
  isBeing d := d = .planner
  isCall d := d = .deed ∨ d = .fruit
  isResponse d := d = .utter
  agent d :=
    match d with
    | .deedOccurrence | .receptionOccurrence => .planner
    | _ => d
  call d :=
    match d with
    | .deedOccurrence => .deed
    | .receptionOccurrence => .fruit
    | _ => d
  response d :=
    match d with
    | .deedOccurrence | .receptionOccurrence => .utter
    | _ => d

def commandGrid : CoreReadings Designatum Nat where
  occurrence := commandOccurrence
  response := {
    respondsTo := fun b c =>
      if b = .planner ∧ (c = .deed ∨ c = .fruit)
      then some .utter
      else none
  }
  placement := { grade := fun _ => 1 }
  conditioning := { conditions := fun _ _ => False }

def deed : commandGrid.Weld :=
  ⟨.deedOccurrence, Or.inl rfl⟩

def reception : commandGrid.Weld :=
  ⟨.receptionOccurrence, Or.inr rfl⟩

def commandUtterance :
    RecordedUtterance commandGrid (deliveryCommandLanguage commandGrid) where
  weld      := deed
  actual    := rfl
  offeredAt := Tier.actTime deed
  content   := { deed := deed, reception := reception }

theorem command_not_delivered :
    ¬ DirectedConvention.DeliveredTo commandGrid deed reception := by
  intro h
  cases h

theorem command_utterance_not_fits :
    ¬ commandUtterance.FitsOfferedTier :=
  deliveryCommand_unfit_of_not_delivered
    (G := commandGrid) commandUtterance command_not_delivered

theorem command_utterance_is_quotable :
    commandUtterance.answersCall = Call.deed ∧
      ¬ commandUtterance.FitsOfferedTier :=
  ⟨rfl, command_utterance_not_fits⟩

end DeliveryArrogationNegative

end KannoSoe
