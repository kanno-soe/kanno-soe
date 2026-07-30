/-
================================================================================
  KannoSoe.Consequences.ModelWitnesses
  Concrete discharges of general consequence-level statements
================================================================================

Concrete grids live here rather than in `Taxonomy`, whose statements remain
parametric in the grid wherever their content is general.
-/

import KannoSoe.Consequences.Taxonomy

namespace KannoSoe

/-- In the register clock, a live share-drop rung is not yet the pole. -/
theorem rung_not_pole_witness :
    ∃ before : Config Nat, ∃ received : registerClockGrid.Weld,
      registerClockGrid.Actual received ∧
        registerClockGrid.IsShareDrop before received ∧
        ¬ AtBot (registerClockGrid.share received) := by
  refine ⟨{ tendency := 5 }, registerWeld 2, ?_, ?_, ?_⟩
  · rfl
  · dsimp [Grid.IsShareDrop, Grid.share, registerClockGrid]
    constructor
    · show (2 : Nat) ≤ 5
      decide
    · show ¬ (5 : Nat) ≤ 2
      decide
  · dsimp [Grid.share, registerClockGrid, AtBot, shareBot]
    show ¬ (2 : Nat) ≤ 0
    decide

/-- Kensho cannot be held: a share-drop reception to the pole-class can be
    followed, in the same grid and by the same being, by a later actual weld
    with live share. There is no stored attainment for the next reception to
    inherit. -/
theorem backsliding_witness :
    ∃ (before : Config Nat) (kensho later : backslideGrid.Weld),
      backslideGrid.Actual kensho ∧
        backslideGrid.IsShareDrop before kensho ∧
          AtBot (backslideGrid.share kensho) ∧
            later.agent = kensho.agent ∧
              backslideGrid.Actual later ∧
                backslideGrid.HasSelfPoleIndex later := by
  refine ⟨{ tendency := 5 }, backslideWeld .gentle, backslideWeld .harsh,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · dsimp [Grid.IsShareDrop, Grid.share, backslideGrid]
    constructor
    · show (0 : Nat) ≤ 5
      decide
    · show ¬ (5 : Nat) ≤ 0
      decide
  · dsimp [Grid.share, backslideGrid, AtBot, shareBot]
    show (0 : Nat) ≤ 0
    decide
  · rfl
  · rfl
  · dsimp [Grid.HasSelfPoleIndex, Grid.share, backslideGrid, AtBot, shareBot]
    show ¬ (5 : Nat) ≤ 0
    decide

/-- The same backsliding witness routed through `ReceptionPair`: after the
    kensho reception the sequence is at the pole-class, and after the next
    reception it is live again. -/
theorem backsliding_rePitchSequence_witness :
    ∃ (before : Config Nat) (p : Grid.ReceptionPair backslideGrid),
      Grid.ReceptionPair.FirstConditionsSecond (G := backslideGrid) p ∧
        p.second.weld.agent = p.first.weld.agent ∧
          AtBot
            ((Grid.ReceptionPair.rePitchSequence (G := backslideGrid) before p).fst.tendency) ∧
            ¬ AtBot
              ((Grid.ReceptionPair.rePitchSequence (G := backslideGrid) before p).snd.tendency) := by
  refine ⟨{ tendency := 5 },
    { first := { weld := backslideWeld .gentle, actual := rfl },
      second := { weld := backslideWeld .harsh, actual := rfl } },
    ?_, ?_, ?_, ?_⟩
  · exact True.intro
  · rfl
  · dsimp [Grid.ReceptionPair.rePitchSequence, Grid.rePitch, Grid.share,
      backslideGrid, AtBot, shareBot]
    show (0 : Nat) ≤ 0
    decide
  · dsimp [Grid.ReceptionPair.rePitchSequence, Grid.rePitch, Grid.share,
      backslideGrid, AtBot, shareBot]
    show ¬ (5 : Nat) ≤ 0
    decide

/-- Cetanā witness A: two actual welds share the same field residue, while
    their shares differ. Grading tracks the completed weld rather than a
    common call-response event residue. -/
theorem cetana_grading_tracks_weld_not_field_witness :
    gradingCollisionGrid.Actual gradingCollisionLeft ∧
      gradingCollisionGrid.Actual gradingCollisionRight ∧
        gradingCollisionGrid.fieldOf gradingCollisionLeft =
          gradingCollisionGrid.fieldOf gradingCollisionRight ∧
          gradingCollisionGrid.share gradingCollisionLeft ≠
            gradingCollisionGrid.share gradingCollisionRight := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  dsimp [Grid.share, gradingCollisionGrid, gradingCollisionLeft,
    gradingCollisionRight]
  decide

/-- Cetanā witness B: a live-share weld remains live even when every delivery
    relation is removed, so grading can peak where object-axis standing fails. -/
theorem cetana_live_share_without_object_standing_witness :
    ∃ w : (registerClockGrid.withConditions (fun _ _ => False)).Weld,
      (registerClockGrid.withConditions (fun _ _ => False)).Actual w ∧
        (registerClockGrid.withConditions (fun _ _ => False)).HasSelfPoleIndex w ∧
          ¬ Grid.DirectedConvention.ObjectAxisStanding
            (registerClockGrid.withConditions (fun _ _ => False)) w := by
  refine ⟨registerWeld 5, ?_, ?_, ?_⟩
  · rfl
  · dsimp [Grid.HasSelfPoleIndex, Grid.share, registerClockGrid,
      Grid.withConditions, AtBot, shareBot]
    show ¬ (5 : Nat) ≤ 0
    decide
  · intro hstanding
    rcases hstanding with ⟨reception, hdelivered⟩
    exact hdelivered

/-- A standing tendency does not determine the dated reception: in the clock
    model a live prior tendency can re-pitch to a pole-class received share. -/
theorem standing_does_not_determine_dated :
    ∃ before : Config Nat, ∃ received : clockGrid.Weld,
      ¬ AtBot before.tendency ∧
        AtBot (clockGrid.rePitch before received).tendency := by
  refine ⟨{ tendency := 5 }, clockAdaptivePresent,
    ?_, ?_⟩
  · dsimp [AtBot, shareBot]
    show ¬ (5 : Nat) ≤ 0
    decide
  · exact clockGrid.rePitch_tendency_atBot_of_terminus_response
      { tendency := 5 } adaptive_is_terminus rfl

/-- Subitism as possibility: a single received weld moves the carried tendency
    from strictly above bottom to the pole-class. Magnitude is unconstrained by
    construction; frequency is asserted nowhere. -/
theorem subitism_possibility_witness :
    ∃ (before : Config Nat) (received : clockGrid.Weld),
      ¬ AtBot before.tendency ∧
        clockGrid.IsShareDrop before received ∧
          AtBot (clockGrid.rePitch before received).tendency := by
  refine ⟨{ tendency := 5 }, clockAdaptivePresent,
    ?_, ?_, ?_⟩
  · dsimp [AtBot, shareBot]
    show ¬ (5 : Nat) ≤ 0
    decide
  · dsimp [Grid.IsShareDrop, Grid.share, clockGrid]
    constructor
    · show (0 : Nat) ≤ 5
      decide
    · show ¬ (5 : Nat) ≤ 0
      decide
  · exact clockGrid.rePitch_tendency_atBot_of_terminus_response
      { tendency := 5 } adaptive_is_terminus rfl

/-- The adaptive clock concretely discharges the general, mark-free pole-tier
    inhabitation theorem. -/
theorem clock_poleTier_inhabited :
    ∃ w : clockGrid.Weld, clockGrid.Actual w ∧
      w.agent = Clock.adaptive ∧ AtBot (clockGrid.share w) ∧
        clockGrid.AtPoleClass w.agent :=
  poleTier_inhabited_of_liveTerminus adaptive_liveTerminus

end KannoSoe
