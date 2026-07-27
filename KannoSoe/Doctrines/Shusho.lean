/-
================================================================================
  KannoSoe.Doctrines.Shusho
  Per-occurrence effectiveness face and standing-display fence
================================================================================

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import KannoSoe.Doctrines.Sraddha
import KannoSoe.Doctrines.Doors

namespace KannoSoe

namespace Grid

namespace DirectedConvention

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/-- The sho face of a single occurrence: an actual weld whose share sits in
    the pole-class. No standing rank is implied; the fact is about this act
    and is spent with it. Reading and motivation: Identification/Commentary.lean,
    C.4. -/
def KsmdPoleDeed (w : G.Weld) : Prop :=
  G.Actual w ∧ AtBot (G.share w)

/-- Shushō-ittō, grid-side: effective closure as a fact about one delivered
    occurrence -- a pole-typed actual deed landing with a share-drop against a
    live prior tendency. This, not the standing predicate, is what act-time
    verdicts may assert. Reading and motivation: Identification/Commentary.lean,
    C.4. -/
def KsmdEffectiveOccurrence
    (before : Config Contrib) (deed reception : G.Weld) : Prop :=
  KsmdPoleDeed G deed ∧
    ¬ AtBot before.tendency ∧
      LandsWithShareDrop G before deed reception

theorem ksmdEffectiveOccurrence_hasShareDropLanding
    {before : Config Contrib} {deed reception : G.Weld}
    (h : KsmdEffectiveOccurrence G before deed reception) :
    HasShareDropLanding G before deed :=
  ⟨reception, h.right.right⟩

theorem ksmdPoleDeed_of_terminus_response
    {w : G.Weld} (hterm : G.Terminus w.agent) (hactual : G.Actual w) :
    KsmdPoleDeed G w :=
  ⟨hactual, G.atBot_of_terminus_response hterm hactual⟩

/-- Any supplied production by a terminus producer has the per-occurrence
    shō face.  The statement is door-neutral; speech-door productions may then
    enter testimony, while mind-door productions remain character evidence. -/
theorem ksmdPoleDeed_of_produced_terminus
    {L : ClaimLanguage G} {sr : SpeechReading G L}
    (u : ProducedUtterance sr) (hterm : G.Terminus u.weld.agent) :
    KsmdPoleDeed G u.weld :=
  ksmdPoleDeed_of_terminus_response G hterm u.actual

/-- The standing display entails an occurrence face only once the deed is an
    actual mounted response and the regime supplies a live delivered pair. The
    landing witness may be a different actual reception from the supplied
    delivery, because `ShortfallClosedAt` asserts existence of a share-drop
    landing for that deed. -/
theorem ksmdEffectiveOccurrence_of_ksmdEffectiveTerminus
    {b : Designatum} {before : Config Contrib} {deed reception : G.Weld}
    (h : KsmdEffectiveTerminus G b)
    (hdeed : deed.agent = b)
    (hactual : G.Actual deed)
    (hdel : DeliveredTo G deed reception)
    (hlive : ¬ AtBot before.tendency) :
    ∃ reception',
      KsmdEffectiveOccurrence G before deed reception' := by
  rcases shortfallClosedAt_of_ksmdEffectiveTerminus G h hdeed hlive hdel with
    ⟨reception', hland⟩
  refine ⟨reception', ?_⟩
  refine ⟨?_, hlive, hland⟩
  have htermDeed : G.Terminus deed.agent := by
    simpa [hdeed] using h.left.right
  exact ksmdPoleDeed_of_terminus_response G htermDeed hactual

/-- The old sraddha landing route factors through the per-occurrence face once
    the speaker's deed is known to be actual. -/
theorem ksmd_path_landing_factors
    {g : Designatum} {before : Config Contrib} {deed reception : G.Weld}
    (hfaith : KsmdEffectiveTerminus G g)
    (hdeed : deed.agent = g)
    (hactual : G.Actual deed)
    (hdel : DeliveredTo G deed reception)
    (hctx : KsmdAversionContext G before reception) :
    ∃ reception',
      KsmdEffectiveOccurrence G before deed reception' :=
  ksmdEffectiveOccurrence_of_ksmdEffectiveTerminus
    G hfaith hdeed hactual hdel hctx.liveBefore

/-- Earned, non-vacuous effectiveness display: the standing pattern plus at
    least one actual effective occurrence witnessing it. The sealed-regime
    terminus satisfies the standing predicate vacuously and fails this enacted
    form. -/
def KsmdEffectivenessEnacted (b : Designatum) : Prop :=
  KsmdEffectiveTerminus G b ∧
    ∃ before deed reception,
      deed.agent = b ∧ KsmdEffectiveOccurrence G before deed reception

theorem ksmdEffectiveTerminus_of_effectivenessEnacted
    {b : Designatum} (h : KsmdEffectivenessEnacted G b) :
    KsmdEffectiveTerminus G b :=
  h.left

theorem not_effectivenessEnacted_of_undelivered
    {b : Designatum}
    (hundelivered : ∀ (deed reception : G.Weld),
      deed.agent = b → ¬ DeliveredTo G deed reception) :
    ¬ KsmdEffectivenessEnacted G b := by
  rintro ⟨_hstanding, before, deed, reception, hdeed, hocc⟩
  exact hundelivered deed reception hdeed
    (deliveredTo_of_landsWithShareDrop G hocc.right.right)

namespace BeingConvention
namespace GridConvention

/-- Per-occurrence effective landing is a grammatical verdict item. -/
def KsmdEffectiveOccurrenceVoice : ErrorGrade :=
  ErrorGrade.verdict

/-- The standing universal is displayable as shortfall-voiced, not assertable
    as an act-time verdict. -/
def KsmdStandingEffectivenessVoice : ErrorGrade :=
  ErrorGrade.shortfall

theorem ksmd_effective_occurrence_voice_assertable :
    ErrorGrade.voice KsmdEffectiveOccurrenceVoice = VerdictVoice.assertable :=
  rfl

theorem ksmd_standing_effectiveness_voice_displayable :
    ErrorGrade.voice KsmdStandingEffectivenessVoice = VerdictVoice.displayable :=
  rfl

end GridConvention
end BeingConvention

end DirectedConvention

end Grid

end KannoSoe
