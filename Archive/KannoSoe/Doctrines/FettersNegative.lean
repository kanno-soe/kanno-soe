/-
================================================================================
  KannoSoe.Doctrines.FettersNegative
  Fresh-weld, view-content, and factor-split countermodels
================================================================================
-/

import KannoSoe.Doctrines.Fetters
import KannoSoe.Doctrines.SraddhaNegative

namespace KannoSoe

namespace FettersNegative

open Grid
open Grid.DirectedConvention

/- The total quiet class still carries no actual-occurrence conjunct. -/

def noActualOccurrence : OccurrenceReading Unit where
  occurrence _ := False
  isBeing _ := False
  isCall _ := False
  isResponse _ := False
  agent := id
  call := id
  response := id

def noActualGrid : CoreReadings Unit Nat where
  occurrence := noActualOccurrence
  response := {
    respondsTo := fun _ _ => none
  }
  placement := {
    grade := fun _ => 0
  }
  conditioning := {
    conditions := fun _ _ => False
  }

theorem noActual_quiet : QuietOn noActualGrid () (fun _ => True) := by
  rintro ⟨_d, hd⟩
  exact False.elim hd

theorem noActual_no_occurrence :
    ¬ ∃ w : noActualGrid.Weld, noActualGrid.Actual w := by
  rintro ⟨w, hactual⟩
  exact False.elim w.property

/-- Total `QuietOn` alone is compatible with a grid having no actual welds. -/
theorem total_cut_carries_no_actual_occurrence :
    QuietOn noActualGrid () (fun _ => True) ∧
      ¬ ∃ w : noActualGrid.Weld, noActualGrid.Actual w :=
  ⟨noActual_quiet, noActual_no_occurrence⟩

theorem sraddha_total_quiet :
    QuietOn SraddhaNegative.zeroEffectGrid
      SraddhaNegative.CaseDesignatum.sraddha (fun _ => True) := by
  intro w hactual hagent _
  exact SraddhaNegative.sraddha_responsiveTerminus.right
    w hactual hagent

theorem sraddha_has_actual_occurrence :
    SraddhaNegative.zeroEffectGrid.ActualAgentInhabited
      SraddhaNegative.CaseDesignatum.sraddha :=
  ⟨SraddhaNegative.deed, rfl, rfl⟩

/-- Quietness plus an actual occurrence still does not entail regime-relative
    effectiveness. -/
theorem total_cut_with_actual_occurrence_not_ksmdEffectiveTerminus :
    QuietOn SraddhaNegative.zeroEffectGrid
      SraddhaNegative.CaseDesignatum.sraddha (fun _ => True) ∧
      SraddhaNegative.zeroEffectGrid.ActualAgentInhabited
        SraddhaNegative.CaseDesignatum.sraddha ∧
        ¬ KsmdEffectiveTerminus SraddhaNegative.zeroEffectGrid
          SraddhaNegative.CaseDesignatum.sraddha :=
  ⟨sraddha_total_quiet, sraddha_has_actual_occurrence,
    SraddhaNegative.not_ksmdEffectiveTerminus⟩

/- A quiet seen weld does not settle a fresh weld in the same fetter class. -/

inductive QuietDesignatum
  | being
  | seen
  | fresh
  | response
  | seenOccurrence
  | freshOccurrence

def quietOccurrence : OccurrenceReading QuietDesignatum where
  occurrence d := d = .seenOccurrence ∨ d = .freshOccurrence
  isBeing d := d = .being
  isCall
    | .seen | .fresh => True
    | _ => False
  isResponse d := d = .response
  agent
    | .seenOccurrence | .freshOccurrence => .being
    | d => d
  call
    | .seenOccurrence => .seen
    | .freshOccurrence => .fresh
    | d => d
  response
    | .seenOccurrence | .freshOccurrence => .response
    | d => d

def quietGrid : CoreReadings QuietDesignatum Nat where
  occurrence := quietOccurrence
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .being, .seen | .being, .fresh => some .response
      | _, _ => none
  }
  placement := {
    grade := fun _ => 0
  }
  conditioning := {
    conditions := fun _ _ => True
  }

def freshClenchGrid : CoreReadings QuietDesignatum Nat where
  occurrence := quietOccurrence
  response := quietGrid.response
  placement := {
    grade := fun d =>
      match d with
      | .freshOccurrence => 1
      | _ => 0
  }
  conditioning := quietGrid.conditioning

def quietSeen : quietGrid.Weld := ⟨.seenOccurrence, Or.inl rfl⟩
def freshSeen : freshClenchGrid.Weld := ⟨.seenOccurrence, Or.inl rfl⟩
def freshWeld : freshClenchGrid.Weld := ⟨.freshOccurrence, Or.inr rfl⟩

def quietReading : quietGrid.FetterReading where
  provocationClass _ _ := True

def freshReading : freshClenchGrid.FetterReading where
  provocationClass _ _ := True

theorem quiet_seen_run :
    quietGrid.RunQuietOn QuietDesignatum.being
      (quietReading.provocationClass Fetter.identityView) [quietSeen] := by
  intro w _hmem _hactual _hagent _hclass
  cases w
  dsimp [Grid.share, quietGrid, AtBot, shareBot]
  exact Nat.le_refl 0

theorem fresh_seen_run :
    freshClenchGrid.RunQuietOn QuietDesignatum.being
      (freshReading.provocationClass Fetter.identityView) [freshSeen] := by
  intro w hmem _hactual _hagent _hclass
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  dsimp [Grid.share, freshClenchGrid, freshSeen, AtBot, shareBot]
  exact Nat.le_refl 0

theorem quiet_fetterCut :
    quietGrid.FetterCut QuietDesignatum.being
      quietReading Fetter.identityView := by
  intro _w _hactual _hagent _hclass
  exact Nat.le_refl 0

theorem fresh_not_fetterCut :
    ¬ freshClenchGrid.FetterCut QuietDesignatum.being
      freshReading Fetter.identityView := by
  intro hcut
  have hbot := hcut freshWeld rfl rfl True.intro
  dsimp [Grid.share, freshClenchGrid, freshWeld, AtBot, shareBot] at hbot
  exact Nat.not_succ_le_zero 0 hbot

/-- Identical one-weld quiet transcripts admit opposite whole-class verdicts
    because the fresh weld is outside the run. -/
theorem seen_run_underdetermines_fetterCut :
    quietGrid.RunQuietOn QuietDesignatum.being
        (quietReading.provocationClass Fetter.identityView) [quietSeen] ∧
      freshClenchGrid.RunQuietOn QuietDesignatum.being
        (freshReading.provocationClass Fetter.identityView) [freshSeen] ∧
      quietGrid.FetterCut QuietDesignatum.being
          quietReading Fetter.identityView ∧
        ¬ freshClenchGrid.FetterCut QuietDesignatum.being
          freshReading Fetter.identityView :=
  ⟨quiet_seen_run, fresh_seen_run, quiet_fetterCut, fresh_not_fetterCut⟩

/- View content is also supplied rather than recovered. -/

def viewLanguage : ClaimLanguage quietGrid where
  Claim := Bool
  Holds _ _ := True

def ownerAll : quietGrid.ViewReading viewLanguage where
  ownerClaim _ := True

def ownerNone : quietGrid.ViewReading viewLanguage where
  ownerClaim _ := False

abbrev ViewGridData : Type :=
  (QuietDesignatum → QuietDesignatum → Option QuietDesignatum) ×
    (QuietDesignatum → Nat)

def viewGridData : ViewGridData := (quietGrid.respondsTo, quietGrid.grade)

theorem no_view_content_recovery :
    ¬ ∃ recover : ViewGridData → Bool → Prop,
      recover viewGridData = ownerAll.ownerClaim ∧
        recover viewGridData = ownerNone.ownerClaim := by
  rintro ⟨recover, hall, hnone⟩
  have ht : recover viewGridData true := by rw [hall]; exact True.intro
  have hf : ¬ recover viewGridData true := by rw [hnone]; exact fun h => h
  exact hf ht

/- One checked coarsening-freeze correlation: the owner classifier names the
   stored-owner claim about a supplied merge, but does not derive it. -/

inductive MergeClaim
  | freezeOwner (left right : Bool)
  | other
deriving DecidableEq

def mergeOccurrence : OccurrenceReading Bool where
  occurrence _ := True
  isBeing _ := True
  isCall _ := True
  isResponse _ := True
  agent := id
  call := id
  response := id

def mergeGrid : CoreReadings Bool Nat where
  occurrence := mergeOccurrence
  response := {
    respondsTo := fun b _ => some b
  }
  placement := {
    grade := fun _ => 0
  }
  conditioning := {
    conditions := fun _ _ => True
  }

def mergeLanguage : ClaimLanguage mergeGrid where
  Claim := MergeClaim
  Holds _ _ := True

def mergeViewReading : mergeGrid.ViewReading mergeLanguage where
  ownerClaim claim := claim = .freezeOwner false true

def suppliedMerge :
    Grid.DirectedConvention.BeingConvention.BeingCoarsening mergeGrid Unit where
  proj _ := ()

theorem ownerClaim_coarsening_freeze_correlation :
    mergeViewReading.ownerClaim (.freezeOwner false true) ∧
      suppliedMerge.SameFiber false true :=
  ⟨rfl, rfl⟩

/- The new typing keeps view and rites distinct in one concrete model. -/

def factorLanguage : ClaimLanguage Grid.doorWitnessGrid where
  Claim := Bool
  Holds _ _ := True

def factorSpeechReading :
    Grid.doorWitnessGrid.SpeechReading factorLanguage where
  toDoorReading := Grid.doorWitnessReading
  voices w := match w.call with | .mind => some true | _ => none

def factorViewReading :
    Grid.doorWitnessGrid.ViewReading factorLanguage where
  ownerClaim claim := claim = true

def factorFetterReading : Grid.doorWitnessGrid.FetterReading where
  provocationClass f w :=
    match f with
    | .identityView => w.call = .mind
    | .ritesGrasp => w.call = .body
    | _ => False

theorem factor_view_cut :
    Grid.doorWitnessGrid.FetterCut
      Grid.DoorWitnessDesignatum.being factorFetterReading
      Fetter.identityView := by
  rintro ⟨d, hd⟩ _hactual _hagent hclass
  change d = Grid.DoorWitnessDesignatum.speechOccurrence ∨
    d = .mindOccurrence ∨ d = .bodyOccurrence at hd
  change Grid.doorWitnessOccurrence.call d =
    Grid.DoorWitnessDesignatum.mind at hclass
  rcases hd with rfl | rfl | rfl
  · contradiction
  · exact Nat.le_refl 0
  · contradiction

theorem factor_rites_not_cut :
    ¬ Grid.doorWitnessGrid.FetterCut
      Grid.DoorWitnessDesignatum.being factorFetterReading
      Fetter.ritesGrasp := by
  intro hcut
  have hbot := hcut Grid.doorWitnessBodyWeld rfl rfl rfl
  exact Grid.doorWitnessBodyWeld_live hbot

theorem view_cut_rites_cut_split :
    Grid.doorWitnessGrid.FetterCut
      Grid.DoorWitnessDesignatum.being factorFetterReading
        Fetter.identityView ∧
      ¬ Grid.doorWitnessGrid.FetterCut
        Grid.DoorWitnessDesignatum.being factorFetterReading
        Fetter.ritesGrasp :=
  ⟨factor_view_cut, factor_rites_not_cut⟩

end FettersNegative

end KannoSoe
