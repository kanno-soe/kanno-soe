/-
================================================================================
  KannoSoe.Doctrines.Sraddha
  The checked sraddha conditional
================================================================================

The grid proves the implication. It does not discharge the antecedents and it
does not assert the detached fourth-truth injunction in its own voice.

The faith antecedent is abstracted to a testimony principle in
`Doctrines/Faith.lean`; the conditional here remains the direct,
non-testimonial route.
-/

import KannoSoe.Doctrines.FourTruths

namespace KannoSoe

namespace Grid

namespace DirectedConvention

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/-- The receiver-side aversion context: a live prior tendency together with an
    actual live-mismatch reception. No imported desire primitive is added. -/
structure KsmdAversionContext
    (before : Config Contrib) (reception : G.Weld) where
  liveBefore : ¬ AtBot before.tendency
  clenchMismatch : G.ClenchMismatch reception

theorem actual_of_ksmdAversionContext
    {before : Config Contrib} {reception : G.Weld}
    (h : KsmdAversionContext G before reception) :
    G.Actual reception :=
  h.clenchMismatch.left

theorem hasSelfPoleIndex_of_ksmdAversionContext
    {before : Config Contrib} {reception : G.Weld}
    (h : KsmdAversionContext G before reception) :
    G.HasSelfPoleIndex reception :=
  h.clenchMismatch.right

/-- Given faith-shaped closure, delivery, and the receiver's live aversion
    context, the share-drop landing follows. -/
theorem ksmd_path_landing
    {g : Designatum} {before : Config Contrib} {deed reception : G.Weld}
    (hfaith : KsmdEffectiveTerminus G g)
    (hdeed : deed.agent = g)
    (hdel : DeliveredTo G deed reception)
    (hctx : KsmdAversionContext G before reception) :
    HasShareDropLanding G before deed :=
  hfaith.right before deed reception hdeed hctx.liveBefore hdel

/-- The fourth-truth ought as an implication type only. The detached consequent
    appears nowhere in this definition. -/
def KsmdPathOught
    (g : Designatum) (before : Config Contrib) (deed reception : G.Weld) :
    Prop :=
  KsmdEffectiveTerminus G g →
    deed.agent = g →
      DeliveredTo G deed reception →
        KsmdAversionContext G before reception →
          HasShareDropLanding G before deed

/-- The grid proves only the conditional: faith, delivery, and live aversion
    imply the landing. -/
theorem ksmdPathOught_conditional
    (g : Designatum) (before : Config Contrib) (deed reception : G.Weld) :
    KsmdPathOught G g before deed reception := by
  intro hfaith hdeed hdel hctx
  exact ksmd_path_landing G hfaith hdeed hdel hctx

/-- At the pole-class, no share-drop landing can be constructed for any deed. -/
theorem no_ksmd_path_at_pole
    {before : Config Contrib} (hbot : AtBot before.tendency)
    (deed : G.Weld) :
    ¬ HasShareDropLanding G before deed := by
  rintro ⟨reception, hland⟩
  exact G.not_isShareDrop_of_tendency_atBot hbot reception hland.right

/-- At the pole-class, the live-aversion antecedent itself fails. -/
theorem no_ksmd_aversion_context_at_pole
    {before : Config Contrib} (hbot : AtBot before.tendency)
    (reception : G.Weld) :
    ¬ KsmdAversionContext G before reception :=
  fun hctx => hctx.liveBefore hbot

namespace BeingConvention
namespace GridConvention

/-- The checked conditional is a grammatical verdict item. -/
def KsmdConditionalVoice : ErrorGrade :=
  ErrorGrade.verdict

/-- The detached injunction is only displayable as shortfall-voiced. -/
def KsmdDetachedOughtVoice : ErrorGrade :=
  ErrorGrade.shortfall

theorem ksmd_conditional_voice_assertable :
    ErrorGrade.voice KsmdConditionalVoice = VerdictVoice.assertable :=
  rfl

theorem ksmd_detached_ought_voice_displayable :
    ErrorGrade.voice KsmdDetachedOughtVoice = VerdictVoice.displayable :=
  rfl

end GridConvention
end BeingConvention

end DirectedConvention

end Grid

end KannoSoe
