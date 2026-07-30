/-
================================================================================
  KannoSoe.Doctrines.Faith
  Speech-only testimony and speech-or-mind no-nescience
================================================================================
-/

import KannoSoe.Doctrines.Shusho
import KannoSoe.Doctrines.Doors

namespace KannoSoe

namespace Grid
namespace DirectedConvention

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

structure KsmdPathClaim where
  before : Config Contrib
  deed : G.Weld
  reception : G.Weld

def ksmdPathClaimLanguage : ClaimLanguage G where
  Claim := KsmdPathClaim G
  Holds
    | .floor, _ => False
    | .actTime _, claim =>
        ShortfallClosedAt G claim.before claim.deed claim.reception

def Factive (Faith : Prop → Prop) : Prop :=
  ∀ P : Prop, Faith P → P

/-- The former speech-side character conjunct, retained as the comparison
    target for the deliberate strengthening to `KsmdNoNescience`. -/
def KsmdNoDelusion
    (Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop)
    (b : Designatum) : Prop :=
  ∀ u : RecordedUtterance G (ksmdPathClaimLanguage G),
    u.weld.agent = b → Fidelity u →
      ∀ w : G.Weld, u.offeredAt = Tier.actTime w →
        (ksmdPathClaimLanguage G).TrueAt u.offeredAt u.content

/-- Production-instantiated fidelity: a record is faithful here exactly when
    it is the speech-door record of a supplied production. -/
def ProductionFidelity
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (record : RecordedUtterance G (ksmdPathClaimLanguage G)) : Prop :=
  ∃ u : ProducedUtterance sr,
    ∃ hspeech : sr.door u.weld = .speech,
      u.toRecorded hspeech = record

/-- Positive truth at a production's own act-time for every speech-or-mind
    pole-share production. This is the cognitive-obscuration conjunct:
    thoughts are included, while testimony remains speech-only. -/
def KsmdNoNescience
    (sr : SpeechReading G (ksmdPathClaimLanguage G)) (b : Designatum) : Prop :=
  ∀ u : ProducedUtterance sr,
    u.weld.agent = b →
      (sr.door u.weld = .speech ∨ sr.door u.weld = .mind) →
      AtBot (G.share u.weld) →
        (ksmdPathClaimLanguage G).TrueAt
          (Tier.actTime u.weld) u.content

/-- For a terminus producer, every production-instantiated speech record is at
    pole, so no-nescience supplies the old speech-side no-delusion theorem. -/
theorem noDelusion_of_noNescience_of_terminus
    (sr : SpeechReading G (ksmdPathClaimLanguage G)) {b : Designatum}
    (hnescience : KsmdNoNescience G sr b) (hterm : G.Terminus b) :
    KsmdNoDelusion G (ProductionFidelity G sr) b := by
  intro record hagent hfid w hoff
  rcases hfid with ⟨u, hspeech, rfl⟩
  have hagentU : u.weld.agent = b := by simpa using hagent
  have htermU : G.Terminus u.weld.agent := by
    rw [hagentU]
    exact hterm
  change (ksmdPathClaimLanguage G).TrueAt
    (Tier.actTime u.weld) u.content
  exact hnescience u hagentU (Or.inl hspeech)
    (G.atBot_of_terminus_response htermU u.actual)

theorem ksmdNoDelusion_not_misfits
    {Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop}
    {b : Designatum} (h : KsmdNoDelusion G Fidelity b)
    (u : RecordedUtterance G (ksmdPathClaimLanguage G))
    (hutter : u.weld.agent = b) (hfid : Fidelity u) :
    ¬ u.MisfitsOfferedTier := by
  rintro ⟨w, hoff, hnot⟩
  exact hnot (h u hutter hfid w hoff)

/-- Full enlightenment combines effective termination with the strengthened
    speech-or-mind no-nescience conjunct. Including thought is the point: the
    jñeyāvaraṇa face is stronger than faithful speech alone. -/
structure KsmdFullyEnlightened
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (b : Designatum) : Prop where
  effective : KsmdEffectiveTerminus G b
  noNescience : KsmdNoNescience G sr b

/-- A non-vacuous faithful speech occurrence, tied to its production weld and
    therefore definitionally offered at that weld's act-time. -/
def KsmdFaithfulSpeechOccurrence
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop)
    (b : Designatum) : Prop :=
  ∃ u : ProducedUtterance sr,
    u.weld.agent = b ∧
      ∃ hspeech : sr.door u.weld = .speech,
        Fidelity (u.toRecorded hspeech) ∧
          (u.toRecorded hspeech).FitsOfferedTier

/-- Enacted faithful speech is standing full enlightenment plus a tied speech
    occurrence. -/
def KsmdFaithfulSpeechEnacted
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop)
    (b : Designatum) : Prop :=
  KsmdFullyEnlightened G sr b ∧
    KsmdFaithfulSpeechOccurrence G sr Fidelity b

structure KsmdFullyEnlightenedEnacted
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop)
    (b : Designatum) : Prop where
  standing : KsmdFullyEnlightened G sr b
  deedWitness : KsmdEffectivenessEnacted G b
  speechOccurrence : KsmdFaithfulSpeechOccurrence G sr Fidelity b

theorem ksmdEffectiveTerminus_of_fullyEnlightened
    {sr : SpeechReading G (ksmdPathClaimLanguage G)} {b : Designatum}
    (h : KsmdFullyEnlightened G sr b) : KsmdEffectiveTerminus G b :=
  h.effective

theorem ksmdFullyEnlightened_of_fullyEnlightenedEnacted
    {sr : SpeechReading G (ksmdPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop}
    {b : Designatum} (h : KsmdFullyEnlightenedEnacted G sr Fidelity b) :
    KsmdFullyEnlightened G sr b :=
  h.standing

theorem ksmdEffectivenessEnacted_of_fullyEnlightenedEnacted
    {sr : SpeechReading G (ksmdPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop}
    {b : Designatum} (h : KsmdFullyEnlightenedEnacted G sr Fidelity b) :
    KsmdEffectivenessEnacted G b :=
  h.deedWitness

theorem ksmdFaithfulSpeechEnacted_of_fullyEnlightenedEnacted
    {sr : SpeechReading G (ksmdPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop}
    {b : Designatum} (h : KsmdFullyEnlightenedEnacted G sr Fidelity b) :
    KsmdFaithfulSpeechEnacted G sr Fidelity b :=
  ⟨h.standing, h.speechOccurrence⟩

theorem ksmdNoNescience_of_factive_faith
    {Faith : Prop → Prop}
    {sr : SpeechReading G (ksmdPathClaimLanguage G)} {b : Designatum}
    (hfact : Factive Faith) (hfaith : Faith (KsmdFullyEnlightened G sr b)) :
    KsmdNoNescience G sr b :=
  (hfact _ hfaith).noNescience

/-- Factive faith plus a production witness gives truth for a speech record.
    Mind productions cannot supply `ProductionFidelity` and never enter this
    testimonial route. -/
theorem ksmd_says_true_of_faith
    {Faith : Prop → Prop}
    {sr : SpeechReading G (ksmdPathClaimLanguage G)} {b : Designatum}
    (hfact : Factive Faith) (hfaith : Faith (KsmdFullyEnlightened G sr b))
    (record : RecordedUtterance G (ksmdPathClaimLanguage G))
    (hagent : record.weld.agent = b)
    (hproduction : ProductionFidelity G sr record) :
    record.FitsOfferedTier := by
  rcases hproduction with ⟨u, hspeech, rfl⟩
  have hfull := hfact _ hfaith
  have hagentU : u.weld.agent = b := by simpa using hagent
  have htermU : G.Terminus u.weld.agent := by
    rw [hagentU]
    exact hfull.effective.left.right
  change (ksmdPathClaimLanguage G).TrueAt
    (Tier.actTime u.weld) u.content
  exact hfull.noNescience u hagentU (Or.inl hspeech)
    (G.atBot_of_terminus_response htermU u.actual)

theorem ksmd_no_misfit_of_stance
    {Faith : Prop → Prop}
    {sr : SpeechReading G (ksmdPathClaimLanguage G)} {b : Designatum}
    (hfact : Factive Faith) (hfaith : Faith (KsmdFullyEnlightened G sr b))
    (record : RecordedUtterance G (ksmdPathClaimLanguage G))
    (hagent : record.weld.agent = b)
    (hproduction : ProductionFidelity G sr record) :
    ¬ record.MisfitsOfferedTier := by
  intro hmisfit
  exact hmisfit.elim (fun _ hw => hw.right
    (ksmd_says_true_of_faith G hfact hfaith record hagent hproduction))

theorem ksmdPath_not_misfits_of_floor_offer
    (u : RecordedUtterance G (ksmdPathClaimLanguage G))
    (hoff : u.offeredAt = Tier.floor) : ¬ u.MisfitsOfferedTier := by
  rintro ⟨w, hact, _hfalse⟩
  rw [hoff] at hact
  cases hact

theorem fitsOfferedTier_of_ksmdEffectiveTerminus_ownDeed
    {b : Designatum} (h : KsmdEffectiveTerminus G b)
    (u : RecordedUtterance G (ksmdPathClaimLanguage G))
    (hdeed : u.content.deed.agent = b)
    (w : G.Weld) (hoff : u.offeredAt = Tier.actTime w) :
    u.FitsOfferedTier := by
  change (ksmdPathClaimLanguage G).TrueAt u.offeredAt u.content
  rw [hoff]
  exact h.right u.content.before u.content.deed u.content.reception hdeed

theorem ksmd_path_landing_of_stance
    {Faith : Prop → Prop}
    {sr : SpeechReading G (ksmdPathClaimLanguage G)} {b : Designatum}
    (hfact : Factive Faith) (hfaith : Faith (KsmdFullyEnlightened G sr b))
    (u : RecordedUtterance G (ksmdPathClaimLanguage G))
    (hagent : u.weld.agent = b) (hproduction : ProductionFidelity G sr u)
    (hdel : DeliveredTo G u.content.deed u.content.reception)
    (hctx : KsmdAversionContext G u.content.before u.content.reception) :
    HasShareDropLanding G u.content.before u.content.deed := by
  have hfit := ksmd_says_true_of_faith G hfact hfaith u hagent hproduction
  have hclosed :
      ShortfallClosedAt G u.content.before u.content.deed u.content.reception := by
    rcases hproduction with ⟨production, hspeech, hrecord⟩
    subst hrecord
    change (ksmdPathClaimLanguage G).TrueAt
      (Tier.actTime production.weld) production.content at hfit
    dsimp [ksmdPathClaimLanguage, ClaimLanguage.TrueAt] at hfit
    change ShortfallClosedAt G production.content.before
      production.content.deed production.content.reception
    exact hfit
  exact hclosed hctx.liveBefore hdel

def KsmdFaithOught
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : Designatum)
    (u : RecordedUtterance G (ksmdPathClaimLanguage G)) : Prop :=
  Factive Faith → Faith (KsmdFullyEnlightened G sr b) → Fidelity u →
    (∀ record, Fidelity record → ProductionFidelity G sr record) →
      u.weld.agent = b →
        DeliveredTo G u.content.deed u.content.reception →
          KsmdAversionContext G u.content.before u.content.reception →
            HasShareDropLanding G u.content.before u.content.deed

theorem ksmdFaithOught_conditional
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : Designatum)
    (u : RecordedUtterance G (ksmdPathClaimLanguage G)) :
    KsmdFaithOught G sr Fidelity Faith b u := by
  intro hfact hfaith hfid hproduces hagent hdel hctx
  exact ksmd_path_landing_of_stance G hfact hfaith u hagent
    (hproduces u hfid) hdel hctx

end DirectedConvention
end Grid
end KannoSoe
