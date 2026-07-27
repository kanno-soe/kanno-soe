/-
================================================================================
  KannoSoe.Doctrines.FaithNegative
  Speech/mind strictness, undefiled nescience, and silent buddhas
================================================================================
-/

import KannoSoe.Doctrines.Faith

namespace KannoSoe
namespace FaithNegative

open Grid
open Grid.DirectedConvention

/-! ### A pole-share producer with true speech and a false thought -/

inductive CaseDesignatum
  | producer
  | speech
  | mind
  | target
  | response
  | speechOccurrence
  | mindOccurrence
  | targetOccurrence
  deriving DecidableEq

def occurrenceReading : OccurrenceReading CaseDesignatum where
  occurrence
    | .speechOccurrence | .mindOccurrence | .targetOccurrence => True
    | _ => False
  isBeing d := d = .producer
  isCall
    | .speech | .mind | .target => True
    | _ => False
  isResponse d := d = .response
  agent
    | .speechOccurrence | .mindOccurrence | .targetOccurrence => .producer
    | d => d
  call
    | .speechOccurrence => .speech
    | .mindOccurrence => .mind
    | .targetOccurrence => .target
    | d => d
  response
    | .speechOccurrence | .mindOccurrence | .targetOccurrence => .response
    | d => d

/-- Speech and thought occur at the pole.  The target is a merely possible
    reception used to make the thought-content false. -/
def grid : CoreReadings CaseDesignatum Nat where
  occurrence := occurrenceReading
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .producer, .speech | .producer, .mind => some .response
      | _, _ => none
  }
  placement := {
    grade := fun d =>
      match d with
      | .targetOccurrence => 1
      | _ => 0
  }
  conditioning := {
    conditions := fun deed reception =>
      deed = .mindOccurrence ∧ reception = .targetOccurrence
  }

def speechWeld : grid.Weld := ⟨.speechOccurrence, True.intro⟩
def mindWeld : grid.Weld := ⟨.mindOccurrence, True.intro⟩
def targetWeld : grid.Weld := ⟨.targetOccurrence, True.intro⟩

def poleBefore : Config Nat := ⟨0⟩
def liveBefore : Config Nat := ⟨1⟩

def trueContent : KsmdPathClaim grid :=
  ⟨poleBefore, speechWeld, targetWeld⟩

def falseContent : KsmdPathClaim grid :=
  ⟨liveBefore, mindWeld, targetWeld⟩

def reading : SpeechReading grid (ksmdPathClaimLanguage grid) where
  door w :=
    match w.call with
    | .speech => .speech
    | .mind => .mind
    | _ => .body
  voices w :=
    match w.call with
    | .speech => some trueContent
    | .mind => some falseContent
    | _ => none

def speechProduction : ProducedUtterance reading where
  weld := speechWeld
  actual := rfl
  content := trueContent
  voiced := rfl

def mindProduction : ProducedUtterance reading where
  weld := mindWeld
  actual := rfl
  content := falseContent
  voiced := rfl

theorem trueContent_trueAt :
    (ksmdPathClaimLanguage grid).TrueAt
      (Tier.actTime speechWeld) trueContent := by
  intro hlive
  exact False.elim (hlive (Nat.le_refl 0))

theorem liveBefore_not_atBot : ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 0 h

theorem mind_delivered_to_target :
    Grid.DirectedConvention.DeliveredTo grid mindWeld targetWeld :=
  ⟨rfl, rfl⟩

theorem mind_has_no_shareDropLanding :
    ¬ HasShareDropLanding grid liveBefore mindWeld := by
  rintro ⟨received, hland⟩
  have htarget :
      received.1 = CaseDesignatum.targetOccurrence :=
    hland.left.left.right
  have hactual : grid.Actual received := hland.left.right
  rcases received with ⟨d, hd⟩
  change d = CaseDesignatum.targetOccurrence at htarget
  subst d
  change (none : Option CaseDesignatum) =
    some CaseDesignatum.response at hactual
  contradiction

theorem falseContent_not_trueAt :
    ¬ (ksmdPathClaimLanguage grid).TrueAt
      (Tier.actTime mindWeld) falseContent := by
  intro htrue
  exact mind_has_no_shareDropLanding
    (htrue liveBefore_not_atBot mind_delivered_to_target)

theorem all_speech_productions_true :
    ∀ u : ProducedUtterance reading,
      reading.door u.weld = .speech →
        (ksmdPathClaimLanguage grid).TrueAt
          (Tier.actTime u.weld) u.content := by
  intro u hspeech
  cases hcall : u.weld.call with
  | speech =>
      have hcontent : u.content = trueContent := by
        simpa [reading, hcall] using u.voiced.symm
      rw [hcontent]
      intro hlive
      exact False.elim (hlive (Nat.le_refl 0))
  | mind => simp [reading, hcall] at hspeech
  | target => simp [reading, hcall] at hspeech
  | producer => simp [reading, hcall] at hspeech
  | response => simp [reading, hcall] at hspeech
  | speechOccurrence => simp [reading, hcall] at hspeech
  | mindOccurrence => simp [reading, hcall] at hspeech
  | targetOccurrence => simp [reading, hcall] at hspeech

/-- Production-instantiated fidelity sees precisely speech-door productions,
    all of which are true in the strictness model. -/
theorem old_speech_side_holds :
    KsmdNoDelusion grid (ProductionFidelity grid reading)
      CaseDesignatum.producer := by
  intro record _hagent hfid _w _hoff
  rcases hfid with ⟨u, hspeech, rfl⟩
  exact all_speech_productions_true u hspeech

theorem not_noNescience :
    ¬ KsmdNoNescience grid reading CaseDesignatum.producer := by
  intro h
  exact falseContent_not_trueAt
    (h mindProduction rfl (Or.inr rfl) (Nat.le_refl 0))

/-- No-nescience is deliberately stronger than the former speech-only test. -/
theorem noNescience_strictly_stronger_witness :
    KsmdNoDelusion grid (ProductionFidelity grid reading)
        CaseDesignatum.producer ∧
      (∀ u : ProducedUtterance reading,
        reading.door u.weld = .speech →
          (ksmdPathClaimLanguage grid).TrueAt
            (Tier.actTime u.weld) u.content) ∧
      ¬ KsmdNoNescience grid reading CaseDesignatum.producer :=
  ⟨old_speech_side_holds, all_speech_productions_true, not_noNescience⟩

/-- The false thought is cognitive error but not defiled: its occurrence has
    no live self-pole.  This is the checked akliṣṭa-ajñāna separation. -/
theorem aklishta_ajnana_witness :
    grid.Actual mindProduction.weld ∧
      AtBot (grid.share mindProduction.weld) ∧
      ¬ (ksmdPathClaimLanguage grid).TrueAt
        (Tier.actTime mindProduction.weld) mindProduction.content ∧
      ¬ grid.HasSelfPoleIndex mindProduction.weld := by
  refine ⟨mindProduction.actual, Nat.le_refl 0,
    falseContent_not_trueAt, ?_⟩
  exact grid.no_self_pole_index_of_atBot mindProduction.weld
    (Nat.le_refl 0)

theorem quiet_everywhere :
    QuietOn grid CaseDesignatum.producer (fun _ => True) := by
  rintro ⟨d, hd⟩ hactual _hagent _
  change occurrenceReading.occurrence d at hd
  change KannoSoe.Actual grid.occurrence grid.response ⟨d, hd⟩ at hactual
  change AtBot (grid.placement.grade d)
  cases d with
  | producer | speech | mind | target | response =>
      change False at hd
      contradiction
  | speechOccurrence | mindOccurrence =>
      exact Nat.le_refl 0
  | targetOccurrence =>
      change (none : Option CaseDesignatum) =
        some CaseDesignatum.response at hactual
      contradiction

/-- Three-door arhat quietness removes the afflictive self-pole but does not by
    itself make every speech-or-mind production true. -/
theorem arhat_retains_nescience_witness :
    QuietOn grid CaseDesignatum.producer (fun _ => True) ∧
      ¬ KsmdNoNescience grid reading CaseDesignatum.producer :=
  ⟨quiet_everywhere, not_noNescience⟩

/-! ### Sealed silent and thinking buddhas -/

namespace Sealed

inductive SealedDesignatum
  | buddha
  | call
  | response
  | occurrence

def occurrenceReading : OccurrenceReading SealedDesignatum where
  occurrence d := d = .occurrence
  isBeing d := d = .buddha
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .occurrence => .buddha
    | d => d
  call
    | .occurrence => .call
    | d => d
  response
    | .occurrence => .response
    | d => d

def grid : CoreReadings SealedDesignatum Nat where
  occurrence := occurrenceReading
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .buddha, .call => some .response
      | _, _ => none
  }
  placement := {
    grade := fun _ => 0
  }
  conditioning := {
    conditions := fun _ _ => False
  }

def weld : grid.Weld := ⟨.occurrence, rfl⟩
def poleBefore : Config Nat := ⟨0⟩
def content : KsmdPathClaim grid := ⟨poleBefore, weld, weld⟩

def silentReading : SpeechReading grid (ksmdPathClaimLanguage grid) where
  door _ := .mind
  voices _ := none

def thinkingReading : SpeechReading grid (ksmdPathClaimLanguage grid) where
  door _ := .mind
  voices _ := some content

def thought : ProducedUtterance thinkingReading where
  weld := weld
  actual := rfl
  content := content
  voiced := rfl

theorem responsiveTerminus :
    grid.ResponsiveTerminus SealedDesignatum.buddha := by
  constructor
  · intro c hc
    change c = SealedDesignatum.call at hc
    subst c
    exact ⟨SealedDesignatum.response, by simp [grid]⟩
  · intro _w _hactual _hagent
    exact Nat.le_refl 0

theorem own_deeds_undelivered
    (deed reception : grid.Weld)
    (_hdeed : deed.agent = SealedDesignatum.buddha) :
    ¬ Grid.DirectedConvention.DeliveredTo grid deed reception := by
  change ¬ False
  exact not_false

theorem effectiveTerminus :
    KsmdEffectiveTerminus grid SealedDesignatum.buddha :=
  ksmdEffectiveTerminus_of_responsiveTerminus_of_undelivered
    grid responsiveTerminus own_deeds_undelivered

theorem content_trueAt :
    (ksmdPathClaimLanguage grid).TrueAt (Tier.actTime weld) content := by
  intro hlive
  exact False.elim (hlive (Nat.le_refl 0))

theorem silent_noNescience :
    KsmdNoNescience grid silentReading SealedDesignatum.buddha := by
  intro u _ _ _
  have := u.voiced
  simp [silentReading] at this

theorem thinking_noNescience :
    KsmdNoNescience grid thinkingReading SealedDesignatum.buddha := by
  intro u _ _ _
  have hcontent : u.content = content := by
    simpa [thinkingReading] using u.voiced.symm
  rw [hcontent]
  intro hlive
  exact False.elim (hlive (Nat.le_refl 0))

theorem silent_fullyEnlightened :
    KsmdFullyEnlightened grid silentReading SealedDesignatum.buddha :=
  ⟨effectiveTerminus, silent_noNescience⟩

theorem thinking_fullyEnlightened :
    KsmdFullyEnlightened grid thinkingReading SealedDesignatum.buddha :=
  ⟨effectiveTerminus, thinking_noNescience⟩

def noFidelity
    (_ : RecordedUtterance grid (ksmdPathClaimLanguage grid)) : Prop := False

theorem silent_no_speech_occurrence :
    ¬ KsmdFaithfulSpeechOccurrence grid silentReading noFidelity
      SealedDesignatum.buddha := by
  rintro ⟨u, _hagent, hspeech, _⟩
  simp [silentReading] at hspeech

theorem thinking_no_speech_occurrence :
    ¬ KsmdFaithfulSpeechOccurrence grid thinkingReading noFidelity
      SealedDesignatum.buddha := by
  rintro ⟨u, _hagent, hspeech, _⟩
  simp [thinkingReading] at hspeech

theorem thinking_has_mind_production :
    ∃ u : ProducedUtterance thinkingReading,
      thinkingReading.door u.weld = .mind :=
  ⟨thought, rfl⟩

theorem no_effectiveness_enacted :
    ¬ KsmdEffectivenessEnacted grid SealedDesignatum.buddha :=
  not_effectivenessEnacted_of_undelivered grid own_deeds_undelivered

/-- Both sealed readings are fully enlightened.  One produces no thought and
    the other produces a true thought; neither silently acquires a testimonial
    or enacted deed witness. -/
theorem silent_buddha_models :
    KsmdFullyEnlightened grid silentReading SealedDesignatum.buddha ∧
      KsmdFullyEnlightened grid thinkingReading SealedDesignatum.buddha ∧
      (¬ KsmdFaithfulSpeechOccurrence grid silentReading noFidelity
        SealedDesignatum.buddha) ∧
      (¬ KsmdFaithfulSpeechOccurrence grid thinkingReading noFidelity
        SealedDesignatum.buddha) ∧
      (∃ u : ProducedUtterance thinkingReading,
        thinkingReading.door u.weld = .mind) ∧
      ¬ KsmdEffectivenessEnacted grid SealedDesignatum.buddha :=
  ⟨silent_fullyEnlightened, thinking_fullyEnlightened,
    silent_no_speech_occurrence, thinking_no_speech_occurrence,
    thinking_has_mind_production, no_effectiveness_enacted⟩

end Sealed

end FaithNegative
end KannoSoe
