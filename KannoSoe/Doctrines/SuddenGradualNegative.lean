/-
================================================================================
  KannoSoe.Doctrines.SuddenGradualNegative
  Negative witnesses for sudden/gradual frequency claims
================================================================================

The positive module shows that sudden and gradual arrivals are grid-legal
shapes. This module keeps that claim honest: response and grade data do not
determine whether the far-re-pitching delivery line is supplied.
-/

import KannoSoe.Doctrines.SuddenGradual

namespace KannoSoe

namespace SuddenGradualNegative

open Grid.DirectedConvention

/- ==============================================================================
   Delivery frequency is not recovered from response/grade data
============================================================================== -/

def deliveredClockGrid : CoreReadings ClockCase Nat :=
  clockGrid.withConditions (fun _ _ => True)

def undeliveredClockGrid : CoreReadings ClockCase Nat :=
  clockGrid.withConditions (fun _ _ => False)

def deliveredPole : deliveredClockGrid.Weld :=
  clockAdaptivePresent

def undeliveredPole : undeliveredClockGrid.Weld :=
  clockAdaptivePresent

abbrev ClockResponseGradeData : Type :=
  (ClockCase -> ClockCase -> Option ClockCase) × (ClockCase -> Nat)

def deliveredResponseGradeData : ClockResponseGradeData :=
  (deliveredClockGrid.respondsTo, deliveredClockGrid.grade)

def undeliveredResponseGradeData : ClockResponseGradeData :=
  (undeliveredClockGrid.respondsTo, undeliveredClockGrid.grade)

theorem response_grade_data_agree :
    deliveredResponseGradeData = undeliveredResponseGradeData :=
  rfl

theorem share_data_agree :
    ∀ w : clockGrid.Weld,
      deliveredClockGrid.share w = undeliveredClockGrid.share w := by
  intro w
  exact clockGrid.share_independent_of_conditions
    (fun _ _ => True) (fun _ _ => False) w

theorem grade_data_agree :
    ∀ d : ClockCase,
      deliveredClockGrid.grade d = undeliveredClockGrid.grade d := by
  intro d
  exact clockGrid.grade_independent_of_conditions
    (fun _ _ => True) (fun _ _ => False) d

theorem deliveredPole_has_delivery :
    ∃ reception : deliveredClockGrid.Weld,
      Grid.DirectedConvention.DeliveredTo
        deliveredClockGrid deliveredPole reception :=
  ⟨deliveredPole, True.intro⟩

theorem undeliveredPole_no_delivery :
    ¬ ∃ reception : undeliveredClockGrid.Weld,
      Grid.DirectedConvention.DeliveredTo
        undeliveredClockGrid undeliveredPole reception := by
  rintro ⟨_reception, hdelivered⟩
  exact hdelivered

/-- No predicate recovered from response/grade data can determine whether the
    pole-reaching weld is delivered. The two grids agree on response and grade
    data but disagree on delivery. -/
theorem no_response_grade_recovery_of_pole_delivery :
    ¬ ∃ recover : ClockResponseGradeData -> Prop,
        (recover deliveredResponseGradeData ↔
          ∃ reception : deliveredClockGrid.Weld,
            Grid.DirectedConvention.DeliveredTo
              deliveredClockGrid deliveredPole reception) ∧
        (recover undeliveredResponseGradeData ↔
          ∃ reception : undeliveredClockGrid.Weld,
            Grid.DirectedConvention.DeliveredTo
              undeliveredClockGrid undeliveredPole reception) := by
  rintro ⟨recover, hdelivered, hundelivered⟩
  have hrecoveredDelivered : recover deliveredResponseGradeData :=
    hdelivered.mpr deliveredPole_has_delivery
  have hrecoveredUndelivered : recover undeliveredResponseGradeData := by
    rw [← response_grade_data_agree]
    exact hrecoveredDelivered
  exact undeliveredPole_no_delivery (hundelivered.mp hrecoveredUndelivered)

/-- Honesty clause for the sudden/gradual block: the grid can witness sudden
    arrival as a possibility, but response/grade data alone do not determine
    whether the relevant delivery line is present, much less how often. -/
theorem subitism_frequency_underdetermined :
    deliveredResponseGradeData = undeliveredResponseGradeData ∧
      (∀ w : clockGrid.Weld,
        deliveredClockGrid.share w = undeliveredClockGrid.share w) ∧
      (∀ d : ClockCase,
        deliveredClockGrid.grade d = undeliveredClockGrid.grade d) ∧
      (∃ reception : deliveredClockGrid.Weld,
        Grid.DirectedConvention.DeliveredTo
          deliveredClockGrid deliveredPole reception) ∧
      ¬ (∃ reception : undeliveredClockGrid.Weld,
        Grid.DirectedConvention.DeliveredTo
          undeliveredClockGrid undeliveredPole reception) ∧
      ¬ ∃ recover : ClockResponseGradeData -> Prop,
        (recover deliveredResponseGradeData ↔
          ∃ reception : deliveredClockGrid.Weld,
            Grid.DirectedConvention.DeliveredTo
              deliveredClockGrid deliveredPole reception) ∧
        (recover undeliveredResponseGradeData ↔
          ∃ reception : undeliveredClockGrid.Weld,
            Grid.DirectedConvention.DeliveredTo
              undeliveredClockGrid undeliveredPole reception) :=
  ⟨response_grade_data_agree, share_data_agree, grade_data_agree,
    deliveredPole_has_delivery, undeliveredPole_no_delivery,
    no_response_grade_recovery_of_pole_delivery⟩

end SuddenGradualNegative

end KannoSoe
