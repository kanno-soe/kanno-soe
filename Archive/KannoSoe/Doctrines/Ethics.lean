/-
================================================================================
  KannoSoe.Doctrines.Ethics
  Ethics as the bundled production-fidelity conditional
================================================================================
-/

import KannoSoe.Doctrines.Faith

namespace KannoSoe
namespace Grid
namespace DirectedConvention

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/-- The stance carries factive faith and the model-side assertion that its
    fidelity predicate is instantiated by actual speech productions. -/
structure KsmdEthicsStance
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : Designatum) : Prop where
  factive : Factive Faith
  faith : Faith (KsmdFullyEnlightened G sr b)
  fidelityProduces : ∀ record, Fidelity record →
    ProductionFidelity G sr record

/-- The ethical code remains an implication type. The prior untied act-time
    witness is gone: production fidelity fixes the record's own act-time. -/
def KsmdEthicalCode
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : Designatum) : Prop :=
  KsmdEthicsStance G sr Fidelity Faith b →
    ∀ u : RecordedUtterance G (ksmdPathClaimLanguage G), Fidelity u →
      u.weld.agent = b →
        DeliveredTo G u.content.deed u.content.reception →
          KsmdAversionContext G u.content.before u.content.reception →
            HasShareDropLanding G u.content.before u.content.deed

theorem ksmd_stance_says_true
    {sr : SpeechReading G (ksmdPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop}
    {Faith : Prop → Prop} {b : Designatum}
    (hstance : KsmdEthicsStance G sr Fidelity Faith b)
    (u : RecordedUtterance G (ksmdPathClaimLanguage G))
    (hagent : u.weld.agent = b) (hfid : Fidelity u) :
    u.FitsOfferedTier :=
  ksmd_says_true_of_faith G hstance.factive hstance.faith u hagent
    (hstance.fidelityProduces u hfid)

theorem ksmd_ethics_landing_of_stance
    {sr : SpeechReading G (ksmdPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop}
    {Faith : Prop → Prop} {b : Designatum}
    (hstance : KsmdEthicsStance G sr Fidelity Faith b)
    (u : RecordedUtterance G (ksmdPathClaimLanguage G))
    (hagent : u.weld.agent = b) (hfid : Fidelity u)
    (hdel : DeliveredTo G u.content.deed u.content.reception)
    (hctx : KsmdAversionContext G u.content.before u.content.reception) :
    HasShareDropLanding G u.content.before u.content.deed :=
  ksmd_path_landing_of_stance G hstance.factive hstance.faith u hagent
    (hstance.fidelityProduces u hfid) hdel hctx

theorem ksmdEthicalCode_conditional
    (sr : SpeechReading G (ksmdPathClaimLanguage G))
    (Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop)
    (Faith : Prop → Prop) (b : Designatum) :
    KsmdEthicalCode G sr Fidelity Faith b := by
  intro hstance u hfid hagent hdel hctx
  exact ksmd_ethics_landing_of_stance G hstance u hagent hfid hdel hctx

theorem ksmdFaithOught_of_ethicalCode
    {sr : SpeechReading G (ksmdPathClaimLanguage G)}
    {Fidelity : RecordedUtterance G (ksmdPathClaimLanguage G) → Prop}
    {Faith : Prop → Prop} {b : Designatum}
    (hcode : KsmdEthicalCode G sr Fidelity Faith b)
    (u : RecordedUtterance G (ksmdPathClaimLanguage G)) :
    KsmdFaithOught G sr Fidelity Faith b u := by
  intro hfact hfaith hfid hproduces hagent hdel hctx
  exact hcode ⟨hfact, hfaith, hproduces⟩ u hfid hagent hdel hctx

namespace BeingConvention
namespace GridConvention

def KsmdEthicsConditionalVoice : ErrorGrade := ErrorGrade.verdict
def KsmdEthicsDetachedVoice : ErrorGrade := ErrorGrade.shortfall

theorem ksmd_ethics_conditional_voice_assertable :
    ErrorGrade.voice KsmdEthicsConditionalVoice = VerdictVoice.assertable := rfl

theorem ksmd_ethics_detached_voice_displayable :
    ErrorGrade.voice KsmdEthicsDetachedVoice = VerdictVoice.displayable := rfl

end GridConvention
end BeingConvention

end DirectedConvention
end Grid
end KannoSoe
