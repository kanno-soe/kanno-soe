/-
================================================================================
  KannoSoe.Doctrines.Factors
  Path-factor hold/release readings over door-aware weld-classes
================================================================================
-/

import KannoSoe.Doctrines.Fetters
import KannoSoe.Doctrines.SuddenGradual

namespace KannoSoe

inductive PathFactor
  | rites
  | view
  | resolve
  | speech
  | conduct

namespace PathFactor

/-- Factor blocker classes are weld-classes. Speech is now the supplied
    speech-door class; conduct remains deliberately inert. -/
def blockerClass {Designatum Contrib : Type} [PreorderBot Contrib] {G : CoreReadings Designatum Contrib}
    (dr : G.DoorReading) (fr : G.FetterReading) :
    PathFactor → G.Weld → Prop
  | .rites, w => fr.provocationClass Fetter.ritesGrasp w
  | .view, w =>
      fr.provocationClass Fetter.identityView w ∨
        fr.provocationClass Fetter.doubt w
  | .resolve, w =>
      fr.provocationClass Fetter.sensualDesire w ∨
        fr.provocationClass Fetter.illWill w
  | .speech, w => dr.door w = .speech
  | .conduct, _ => False

end PathFactor

namespace Grid

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

theorem ritesView_union_covers_streamEntry_fetters
    (dr : G.DoorReading) (fr : G.FetterReading) (w : G.Weld) :
    (PathFactor.blockerClass dr fr .rites w ∨
      PathFactor.blockerClass dr fr .view w) ↔
      Path.cutClasses fr .streamEntry w := by
  constructor
  · rintro (hrites | hidentity | hdoubt)
    · exact ⟨.ritesGrasp, rfl, hrites⟩
    · exact ⟨.identityView, rfl, hidentity⟩
    · exact ⟨.doubt, rfl, hdoubt⟩
  · rintro ⟨f, hf, hclass⟩
    cases f with
    | identityView => exact Or.inr (Or.inl hclass)
    | doubt => exact Or.inr (Or.inr hclass)
    | ritesGrasp => exact Or.inl hclass
    | sensualDesire | illWill | formDesire | formlessDesire | conceit |
      restlessness | ignorance => cases hf

theorem resolve_covers_nonReturn_fetters
    (dr : G.DoorReading) (fr : G.FetterReading) (w : G.Weld) :
    PathFactor.blockerClass dr fr .resolve w ↔
      ∃ f : Fetter,
        Fetter.abandonedAt f = .nonReturn ∧ fr.provocationClass f w := by
  constructor
  · rintro (hsensual | hill)
    · exact ⟨.sensualDesire, rfl, hsensual⟩
    · exact ⟨.illWill, rfl, hill⟩
  · rintro ⟨f, hf, hclass⟩
    cases f with
    | sensualDesire => exact Or.inl hclass
    | illWill => exact Or.inr hclass
    | identityView | doubt | ritesGrasp | formDesire | formlessDesire | conceit |
      restlessness | ignorance => cases hf

theorem lower_fetters_covered_by_rites_view_resolve
    (dr : G.DoorReading) (fr : G.FetterReading) (w : G.Weld) :
    (PathFactor.blockerClass dr fr .rites w ∨
      PathFactor.blockerClass dr fr .view w ∨
        PathFactor.blockerClass dr fr .resolve w) ↔
      Path.cutClasses fr .nonReturn w := by
  constructor
  · rintro (hrites | hview | hresolve)
    · exact ⟨.ritesGrasp, Or.inl rfl, hrites⟩
    · rcases hview with hidentity | hdoubt
      · exact ⟨.identityView, Or.inl rfl, hidentity⟩
      · exact ⟨.doubt, Or.inl rfl, hdoubt⟩
    · rcases hresolve with hsensual | hill
      · exact ⟨.sensualDesire, Or.inr rfl, hsensual⟩
      · exact ⟨.illWill, Or.inr rfl, hill⟩
  · rintro ⟨f, hf, hclass⟩
    cases f with
    | identityView => exact Or.inr (Or.inl (Or.inl hclass))
    | doubt => exact Or.inr (Or.inl (Or.inr hclass))
    | ritesGrasp => exact Or.inl hclass
    | sensualDesire => exact Or.inr (Or.inr (Or.inl hclass))
    | illWill => exact Or.inr (Or.inr (Or.inr hclass))
    | formDesire | formlessDesire | conceit | restlessness | ignorance =>
        rcases hf with h | h <;> cases h

/-- A factor is held when the finite run contains an actual live weld of `b`
    in the factor's blocker class. -/
def FactorHeld (dr : G.DoorReading) (b : Designatum)
    (fr : G.FetterReading) (factor : PathFactor) (run : List G.Weld) : Prop :=
  ∃ w ∈ run, G.Actual w ∧ w.agent = b ∧
    PathFactor.blockerClass dr fr factor w ∧ G.HasSelfPoleIndex w

/-- A factor is released when the fine being is quiet on its blocker class. -/
def FactorReleased (dr : G.DoorReading) (b : Designatum)
    (fr : G.FetterReading) (factor : PathFactor) : Prop :=
  QuietOn G b (PathFactor.blockerClass dr fr factor)

theorem not_factorHeld_of_factorReleased
    {dr : G.DoorReading} {b : Designatum} {fr : G.FetterReading}
    {factor : PathFactor} {run : List G.Weld}
    (h : FactorReleased G dr b fr factor) :
    ¬ FactorHeld G dr b fr factor run := by
  rintro ⟨w, _hmem, hactual, hagent, hclass, hidx⟩
  exact hidx (h w hactual hagent hclass)

theorem factorReleased_rites_iff_ritesGrasp_cut
    (dr : G.DoorReading) (b : Designatum) (fr : G.FetterReading) :
    FactorReleased G dr b fr .rites ↔
      G.FetterCut b fr .ritesGrasp :=
  Iff.rfl

theorem factorReleased_view_iff
    (dr : G.DoorReading) (b : Designatum) (fr : G.FetterReading) :
    FactorReleased G dr b fr .view ↔
      G.FetterCut b fr .identityView ∧ G.FetterCut b fr .doubt := by
  constructor
  · intro h
    exact ⟨quietOn_mono (fun _ hc => Or.inl hc) h,
      quietOn_mono (fun _ hc => Or.inr hc) h⟩
  · rintro ⟨hidentity, hdoubt⟩ w hactual hagent (hc | hc)
    · exact hidentity w hactual hagent hc
    · exact hdoubt w hactual hagent hc

theorem factorReleased_resolve_iff
    (dr : G.DoorReading) (b : Designatum) (fr : G.FetterReading) :
    FactorReleased G dr b fr .resolve ↔
      G.FetterCut b fr .sensualDesire ∧ G.FetterCut b fr .illWill := by
  constructor
  · intro h
    exact ⟨quietOn_mono (fun _ hc => Or.inl hc) h,
      quietOn_mono (fun _ hc => Or.inr hc) h⟩
  · rintro ⟨hsensual, hill⟩ w hactual hagent (hc | hc)
    · exact hsensual w hactual hagent hc
    · exact hill w hactual hagent hc

def KsmdStreamEnterer (dr : G.DoorReading) (b : Designatum)
    (fr : G.FetterReading) (run : List G.Weld) : Prop :=
  FactorReleased G dr b fr .rites ∧ FactorHeld G dr b fr .view run

def KsmdStreamWinner (dr : G.DoorReading) (b : Designatum)
    (fr : G.FetterReading) : Prop :=
  FactorReleased G dr b fr .rites ∧ FactorReleased G dr b fr .view

def KsmdOnceReturner (dr : G.DoorReading) (b : Designatum)
    (fr : G.FetterReading) (run : List G.Weld) : Prop :=
  KsmdStreamWinner G dr b fr ∧ FactorHeld G dr b fr .resolve run

def KsmdNonReturner (dr : G.DoorReading) (b : Designatum)
    (fr : G.FetterReading) : Prop :=
  KsmdStreamWinner G dr b fr ∧ FactorReleased G dr b fr .resolve

theorem ksmdStreamWinner_iff_streamEntry_cutClasses
    (dr : G.DoorReading) (b : Designatum) (fr : G.FetterReading) :
    KsmdStreamWinner G dr b fr ↔
      QuietOn G b (Path.cutClasses fr .streamEntry) := by
  constructor
  · rintro ⟨hrites, hview⟩ w hactual hagent hclass
    rcases (ritesView_union_covers_streamEntry_fetters G dr fr w).mpr hclass with
      hritesClass | hviewClass
    · exact hrites w hactual hagent hritesClass
    · exact hview w hactual hagent hviewClass
  · intro hcut
    constructor
    · exact quietOn_mono
        (fun w hc => (ritesView_union_covers_streamEntry_fetters G dr fr w).mp
          (Or.inl hc)) hcut
    · exact quietOn_mono
        (fun w hc => (ritesView_union_covers_streamEntry_fetters G dr fr w).mp
          (Or.inr hc)) hcut

theorem ksmdNonReturner_iff_nonReturn_cut
    (dr : G.DoorReading) (b : Designatum) (fr : G.FetterReading) :
    KsmdNonReturner G dr b fr ↔ QuietOn G b (Path.cutClasses fr .nonReturn) := by
  constructor
  · rintro ⟨hstream, hresolve⟩ w hactual hagent hclass
    rcases (lower_fetters_covered_by_rites_view_resolve G dr fr w).mpr hclass with
      hrites | hview | hresolveClass
    · exact hstream.left w hactual hagent hrites
    · exact hstream.right w hactual hagent hview
    · exact hresolve w hactual hagent hresolveClass
  · intro hcut
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact quietOn_mono
        (fun w hc => (lower_fetters_covered_by_rites_view_resolve G dr fr w).mp
          (Or.inl hc)) hcut
    · exact quietOn_mono
        (fun w hc => (lower_fetters_covered_by_rites_view_resolve G dr fr w).mp
          (Or.inr (Or.inl hc))) hcut
    · exact quietOn_mono
        (fun w hc => (lower_fetters_covered_by_rites_view_resolve G dr fr w).mp
          (Or.inr (Or.inr hc))) hcut

theorem ksmdNonReturner_of_quietOn_univ
    (dr : G.DoorReading) (b : Designatum) (fr : G.FetterReading)
    (h : QuietOn G b (fun _ => True)) :
    KsmdNonReturner G dr b fr :=
  (ksmdNonReturner_iff_nonReturn_cut G dr b fr).mpr (quietOn_univ h)

theorem ksmdStreamWinner_of_ksmdNonReturner
    {dr : G.DoorReading} {b : Designatum} {fr : G.FetterReading}
    (h : KsmdNonReturner G dr b fr) : KsmdStreamWinner G dr b fr :=
  h.left

theorem not_ksmdStreamEnterer_of_ksmdStreamWinner
    {dr : G.DoorReading} {b : Designatum} {fr : G.FetterReading}
    {run : List G.Weld} (h : KsmdStreamWinner G dr b fr) :
    ¬ KsmdStreamEnterer G dr b fr run := by
  intro henterer
  exact (not_factorHeld_of_factorReleased G h.right) henterer.right

/-- When view-factor release uses the supplied owner-claim/mind-door
    factoring, a stream winner has no defiled identity-view voicing. -/
theorem streamWinner_no_identityView_voicing
    {L : ClaimLanguage G} (sr : SpeechReading G L) (vr : ViewReading G L)
    (b : Designatum) (fr : G.FetterReading)
    (hfactor : ∀ w : G.Weld,
      fr.provocationClass Fetter.identityView w ↔
        sr.door w = .mind ∧
          ∃ content, sr.voices w = some content ∧ vr.ownerClaim content)
    (h : KsmdStreamWinner G sr.toDoorReading b fr) :
    NoDefiledVoicing sr b vr.ownerClaim .mind :=
  (G.identityView_cut_iff_noDefiledVoicing sr vr b fr hfactor).mp
    ((factorReleased_view_iff G sr.toDoorReading b fr).mp h.right).left

/- Once-return attenuation remains a finite share-drop display, now over a
   weld-class rather than a call-class. -/

def ShareDropRunOn (before : Config Contrib) (ws : G.Weld → Prop)
    (run : List G.Weld) : Prop :=
  G.ShareDropRun before run ∧ ∀ w : G.Weld, w ∈ run → ws w

def ShareDropRunOnFactor (dr : G.DoorReading) (fr : G.FetterReading)
    (factor : PathFactor) (run : List G.Weld) : Prop :=
  ∃ before : Config Contrib,
    ShareDropRunOn G before (PathFactor.blockerClass dr fr factor) run

def KsmdResolveAttenuation (dr : G.DoorReading) (_b : Designatum)
    (fr : G.FetterReading) (run : List G.Weld) : Prop :=
  ∃ (before : Config Contrib) (received : G.Weld) (rest : List G.Weld),
    run = received :: rest ∧
      ShareDropRunOn G before (PathFactor.blockerClass dr fr .resolve) run ∧
      ¬ AtBot before.tendency ∧
      ¬ AtBot ((Grid.rePitchRun G before run).tendency)

def registerFactorDoorReading : registerClockGrid.DoorReading where
  door _ := .body

def registerResolveFactorReading : registerClockGrid.FetterReading where
  provocationClass f _ := match f with | .sensualDesire => True | _ => False

def registerResolveWeld : registerClockGrid.Weld :=
  registerWeld 2
def registerResolveRun : List registerClockGrid.Weld := [registerResolveWeld]

theorem registerResolve_streamWinner :
    KsmdStreamWinner registerClockGrid registerFactorDoorReading
      (RegisterCase.register 2)
      registerResolveFactorReading := by
  constructor <;> intro w _hactual _hagent hclass
  · cases hclass
  · rcases hclass with h | h <;> cases h

theorem registerResolve_held :
    FactorHeld registerClockGrid registerFactorDoorReading
      (RegisterCase.register 2)
      registerResolveFactorReading .resolve registerResolveRun := by
  refine ⟨registerResolveWeld, by simp [registerResolveRun], rfl, rfl,
    Or.inl True.intro, ?_⟩
  dsimp [Grid.HasSelfPoleIndex, Grid.share, registerClockGrid,
    registerResolveWeld, AtBot, shareBot]
  show ¬ (2 : Nat) ≤ 0
  decide

theorem registerResolve_attenuation :
    KsmdResolveAttenuation registerClockGrid registerFactorDoorReading
      (RegisterCase.register 2)
      registerResolveFactorReading registerResolveRun := by
  refine ⟨{ tendency := 5 }, registerResolveWeld, [], rfl, ?_, ?_, ?_⟩
  · constructor
    · exact Grid.ShareDropRun.cons rfl (by
        dsimp [Grid.IsShareDrop, Grid.share, registerClockGrid,
          registerResolveWeld]
        constructor
        · show (2 : Nat) ≤ 5
          decide
        · show ¬ (5 : Nat) ≤ 2
          decide) (Grid.ShareDropRun.nil _)
    · intro w hmem
      simp [registerResolveRun] at hmem
      subst w
      exact Or.inl True.intro
  · dsimp [AtBot, shareBot]
    show ¬ (5 : Nat) ≤ 0
    decide
  · dsimp [Grid.rePitchRun, Grid.rePitch, Grid.share, registerClockGrid,
      registerResolveRun, registerResolveWeld, AtBot, shareBot]
    show ¬ (2 : Nat) ≤ 0
    decide

theorem registerResolve_not_released :
    ¬ FactorReleased registerClockGrid registerFactorDoorReading
      (RegisterCase.register 2)
      registerResolveFactorReading .resolve := by
  intro hrelease
  have hbot := hrelease registerResolveWeld rfl rfl (Or.inl True.intro)
  dsimp [Grid.share, registerClockGrid, registerResolveWeld, AtBot, shareBot]
    at hbot
  exact Nat.not_succ_le_zero 1 hbot

theorem ksmdOnceReturner_attenuation_witness :
    KsmdOnceReturner registerClockGrid registerFactorDoorReading
        (RegisterCase.register 2)
        registerResolveFactorReading registerResolveRun ∧
      KsmdResolveAttenuation registerClockGrid registerFactorDoorReading
        (RegisterCase.register 2)
        registerResolveFactorReading registerResolveRun ∧
      ¬ FactorReleased registerClockGrid registerFactorDoorReading
        (RegisterCase.register 2)
        registerResolveFactorReading .resolve :=
  ⟨⟨registerResolve_streamWinner, registerResolve_held⟩,
    registerResolve_attenuation, registerResolve_not_released⟩

def RunsExhibitFactorOrder (dr : G.DoorReading) (fr : G.FetterReading)
    (runs : List (List G.Weld)) : Prop :=
  ∃ ritesRun viewRun resolveRun : List G.Weld,
    runs = [ritesRun, viewRun, resolveRun] ∧
      ShareDropRunOnFactor G dr fr .rites ritesRun ∧
      ShareDropRunOnFactor G dr fr .view viewRun ∧
      ShareDropRunOnFactor G dr fr .resolve resolveRun

def KsmdSerialFactorRegime (dr : G.DoorReading) (b : Designatum)
    (fr : G.FetterReading) (runs : List (List G.Weld)) : Prop :=
  RunsExhibitFactorOrder G dr fr runs →
    (∀ run ∈ runs, KsmdStreamEnterer G dr b fr run →
      KsmdStreamWinner G dr b fr) ∧
    (∀ run ∈ runs, KsmdOnceReturner G dr b fr run →
      KsmdNonReturner G dr b fr)

theorem ksmdSerialFactorRegime_conditional
    {dr : G.DoorReading} {b : Designatum} {fr : G.FetterReading}
    {runs : List (List G.Weld)}
    (hregime : KsmdSerialFactorRegime G dr b fr runs)
    (horder : RunsExhibitFactorOrder G dr fr runs) :
    (∀ run ∈ runs, KsmdStreamEnterer G dr b fr run →
      KsmdStreamWinner G dr b fr) ∧
    (∀ run ∈ runs, KsmdOnceReturner G dr b fr run →
      KsmdNonReturner G dr b fr) :=
  hregime horder

theorem ksmdSuddenArrival_consistent_with_factorScheme
    {before : Config Contrib} {received : G.Weld}
    (dr : G.DoorReading) (fr : G.FetterReading)
    (hsudden : Grid.KsmdSuddenArrival G before received)
    (hquiet : QuietOn G received.agent (fun _ => True)) :
    Grid.KsmdSuddenArrival G before received ∧
      KsmdStreamWinner G dr received.agent fr ∧
        KsmdNonReturner G dr received.agent fr := by
  have hnon := ksmdNonReturner_of_quietOn_univ
    G dr received.agent fr hquiet
  exact ⟨hsudden, hnon.left, hnon⟩

end Grid

namespace CoreReadings

variable {Designatum Contrib : Type} [PreorderBot Contrib]

abbrev FactorHeld (G : CoreReadings Designatum Contrib) :=
  Grid.FactorHeld G
abbrev FactorReleased (G : CoreReadings Designatum Contrib) :=
  Grid.FactorReleased G
abbrev KsmdStreamEnterer (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdStreamEnterer G
abbrev KsmdStreamWinner (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdStreamWinner G
abbrev KsmdOnceReturner (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdOnceReturner G
abbrev KsmdNonReturner (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdNonReturner G
abbrev ShareDropRunOn (G : CoreReadings Designatum Contrib) :=
  Grid.ShareDropRunOn G
abbrev ShareDropRunOnFactor (G : CoreReadings Designatum Contrib) :=
  Grid.ShareDropRunOnFactor G
abbrev KsmdResolveAttenuation (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdResolveAttenuation G
abbrev RunsExhibitFactorOrder (G : CoreReadings Designatum Contrib) :=
  Grid.RunsExhibitFactorOrder G
abbrev KsmdSerialFactorRegime (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdSerialFactorRegime G

end CoreReadings

end KannoSoe
