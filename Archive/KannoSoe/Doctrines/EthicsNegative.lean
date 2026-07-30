/-
================================================================================
  KannoSoe.Doctrines.EthicsNegative
  Production-tied testimony and conditional ethics witnesses
================================================================================
-/

import KannoSoe.Doctrines.Ethics
import KannoSoe.Doctrines.FaithNegative

namespace KannoSoe
namespace EthicsNegative

open Grid
open Grid.DirectedConvention
open FaithNegative

/-- The false thought from the strictness model cannot cross the testimonial
    boundary: its supplied door is mind, not speech. -/
theorem mind_production_not_testimony :
    ¬ reading.door mindProduction.weld = .speech := by
  intro h
  cases h

/-- Re-read the same false production as speech to test the ethics boundary
    itself.  This separate reading is deliberate: door typing is model-supplied
    diagnostic structure, not recoverable from the grid. -/
def falseSpeechReading :
    SpeechReading grid (ksmdPathClaimLanguage grid) where
  door _ := .speech
  voices w :=
    match w.call with
    | .mind => some falseContent
    | _ => none

def falseSpeechProduction : ProducedUtterance falseSpeechReading where
  weld := mindWeld
  actual := rfl
  content := falseContent
  voiced := rfl

def falseRecord : RecordedUtterance grid (ksmdPathClaimLanguage grid) :=
  falseSpeechProduction.toRecorded rfl

def onlyFalseFidelity
    (record : RecordedUtterance grid (ksmdPathClaimLanguage grid)) : Prop :=
  record = falseRecord

/-- No factive ethics stance can license an admitted false speech production.
    The contradiction is tied to that production's own act-time; there is no
    free-standing tier witness. -/
theorem no_stance_over_false_speech
    (Faith : Prop → Prop) :
    ¬ KsmdEthicsStance grid falseSpeechReading onlyFalseFidelity Faith
      CaseDesignatum.producer := by
  intro hstance
  have hfit := ksmd_stance_says_true grid hstance falseRecord rfl rfl
  exact falseContent_not_trueAt hfit

/-- At a pole prior there is no live aversion antecedent and hence no detached
    practical conclusion, regardless of what production-tied stance is
    hypothesized. -/
theorem no_ethics_bearing_at_pole
    (Fidelity : RecordedUtterance grid (ksmdPathClaimLanguage grid) → Prop)
    (Faith : Prop → Prop)
    (_hstance : KsmdEthicsStance grid reading Fidelity Faith
      CaseDesignatum.producer) :
    ¬ KsmdAversionContext grid poleBefore targetWeld ∧
      ¬ HasShareDropLanding grid poleBefore mindWeld :=
  ⟨no_ksmd_aversion_context_at_pole grid (Nat.le_refl 0) targetWeld,
    no_ksmd_path_at_pole grid (Nat.le_refl 0) mindWeld⟩

end EthicsNegative
end KannoSoe
