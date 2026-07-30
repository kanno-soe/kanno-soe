/-
================================================================================
  KannoSoe.Consequences.Compounds
  Compound positions as decompositions over taxonomy rows
================================================================================

Reading and motivation: Identification/Commentary.lean, C.2.
-/

import KannoSoe.Consequences.Taxonomy

namespace KannoSoe

namespace Grid

namespace DirectedConvention
namespace BeingConvention
namespace GridConvention

/-- Which error-slot of a taxonomy cell a component occupies. -/
inductive CellSide
  | collapse
  | freeze

/-- Whether a cited cell is part of the compound's stack or rides alongside it.
    This is not a grade distinction: every cell component is Grade 1. -/
inductive Role
  | core
  | alongside

/-- Prose-facing names for distinct faces of a taxonomy cell. Facets do not add
    rows; they keep repeated row/side citations from collapsing into one term. -/
inductive Facet
  | plain
  | epistemic
  | practical
  | maximized
  | furniture
  | structure
  | direction
  | domain
  | command

/-- Elements the prose explicitly marks grid-legal rather than erroneous. -/
inductive LegalElement
  | valueCreation
  | causalSkeleton

/-- One element of a compound position's decomposition.

    Components are classificatory data, not proofs that the cited rows collapse
    or freeze. The generated rows already prove their own `not_freeze` and
    collapse-self-refutation theorems; a compound records the error-slot a
    position occupies against that sound distinction. The row field is typed as
    `TableRow`, so a decomposition can only cite cells already present in the
    Grade-1 table. -/
inductive CompoundComponent
  | cell (row : TableRow) (side : CellSide) (facet : Facet) (role : Role)
  | legal (l : LegalElement)

namespace CompoundComponent

/-- Count only the stacked cells of a compound position. -/
def countCoreCells : List CompoundComponent -> Nat
  | [] => 0
  | cell _ _ _ Role.core :: xs => Nat.succ (countCoreCells xs)
  | _ :: xs => countCoreCells xs

/-- Count Grade-1 cells that are recorded as riding alongside the stack. -/
def countAlongsideCells : List CompoundComponent -> Nat
  | [] => 0
  | cell _ _ _ Role.alongside :: xs => Nat.succ (countAlongsideCells xs)
  | _ :: xs => countAlongsideCells xs

/-- Count non-error legal elements carried in the decomposition. -/
def countLegal : List CompoundComponent -> Nat
  | [] => 0
  | legal _ :: xs => Nat.succ (countLegal xs)
  | _ :: xs => countLegal xs

/-- Cells are Grade-1 verdict material; legal elements carry no verdict. -/
def voice : CompoundComponent -> Option VerdictVoice
  | cell _ _ _ _ => some VerdictVoice.assertable
  | legal _ => none

end CompoundComponent

/-- Compound positions whose prose decomposition is now made inspectable. -/
inductive CompoundPosition
  | skepticism
  | solipsism
  | exitPremise
  | existentialism
  | ledgerPicture

namespace CompoundPosition

/-- The table-cell decomposition of each compound position. -/
def decomposition : CompoundPosition -> List CompoundComponent
  | skepticism => [
      .cell (.prose .beingNonBeing) .freeze .epistemic .core ]
  | solipsism => [
      .cell (.generated .karmaInga) .freeze .maximized .core,
      .cell (.generated .perCallGlobal) .freeze .direction .core,
      .cell (.generated .subjectObjectAxis) .freeze .domain .core ]
  | exitPremise => [
      .cell (.prose .beingNonBeing) .freeze .practical .core,
      .cell (.generated .terminusExit) .collapse .plain .core,
      .cell (.generated .standingDated) .freeze .furniture .core,
      .cell (.generated .deliveryIndex) .collapse .plain .alongside ]
  | existentialism => [
      .cell .ladderSchema .freeze .plain .core,
      .cell (.generated .perCallGlobal) .freeze .direction .core,
      .cell (.generated .standingDated) .freeze .structure .core,
      .cell (.generated .karmaInga) .freeze .plain .core,
      .legal .valueCreation ]
  | ledgerPicture => [
      .cell (.generated .deliveryIndex) .freeze .plain .core,
      .cell (.generated .selfPoleTransposed) .freeze .plain .core,
      .cell (.generated .deliveryIndex) .collapse .command .alongside,
      .legal .causalSkeleton ]

theorem skepticism_decomposition :
    decomposition skepticism =
      [ .cell (.prose .beingNonBeing) .freeze .epistemic .core ] :=
  rfl

theorem solipsism_decomposition :
    decomposition solipsism =
      [ .cell (.generated .karmaInga) .freeze .maximized .core,
        .cell (.generated .perCallGlobal) .freeze .direction .core,
        .cell (.generated .subjectObjectAxis) .freeze .domain .core ] :=
  rfl

theorem exitPremise_decomposition :
    decomposition exitPremise =
      [ .cell (.prose .beingNonBeing) .freeze .practical .core,
        .cell (.generated .terminusExit) .collapse .plain .core,
        .cell (.generated .standingDated) .freeze .furniture .core,
        .cell (.generated .deliveryIndex) .collapse .plain .alongside ] :=
  rfl

theorem existentialism_decomposition :
    decomposition existentialism =
      [ .cell .ladderSchema .freeze .plain .core,
        .cell (.generated .perCallGlobal) .freeze .direction .core,
        .cell (.generated .standingDated) .freeze .structure .core,
        .cell (.generated .karmaInga) .freeze .plain .core,
        .legal .valueCreation ] :=
  rfl

theorem ledgerPicture_decomposition :
    decomposition ledgerPicture =
      [ .cell (.generated .deliveryIndex) .freeze .plain .core,
        .cell (.generated .selfPoleTransposed) .freeze .plain .core,
        .cell (.generated .deliveryIndex) .collapse .command .alongside,
        .legal .causalSkeleton ] :=
  rfl

theorem skepticism_core_cell_count :
    CompoundComponent.countCoreCells (decomposition skepticism) = 1 :=
  rfl

theorem solipsism_core_cell_count :
    CompoundComponent.countCoreCells (decomposition solipsism) = 3 :=
  rfl

theorem exitPremise_core_cell_count :
    CompoundComponent.countCoreCells (decomposition exitPremise) = 3 :=
  rfl

theorem exitPremise_alongside_cell_count :
    CompoundComponent.countAlongsideCells (decomposition exitPremise) = 1 :=
  rfl

theorem existentialism_core_cell_count :
    CompoundComponent.countCoreCells (decomposition existentialism) = 4 :=
  rfl

theorem existentialism_legal_count :
    CompoundComponent.countLegal (decomposition existentialism) = 1 :=
  rfl

theorem ledgerPicture_core_cell_count :
    CompoundComponent.countCoreCells (decomposition ledgerPicture) = 2 :=
  rfl

theorem ledgerPicture_alongside_cell_count :
    CompoundComponent.countAlongsideCells (decomposition ledgerPicture) = 1 :=
  rfl

theorem ledgerPicture_legal_count :
    CompoundComponent.countLegal (decomposition ledgerPicture) = 1 :=
  rfl

theorem exitPremise_voices :
    (decomposition exitPremise).map CompoundComponent.voice =
      [ some VerdictVoice.assertable, some VerdictVoice.assertable,
        some VerdictVoice.assertable, some VerdictVoice.assertable ] :=
  rfl

theorem existentialism_voices :
    (decomposition existentialism).map CompoundComponent.voice =
      [ some VerdictVoice.assertable, some VerdictVoice.assertable,
        some VerdictVoice.assertable, some VerdictVoice.assertable, none ] :=
  rfl

theorem ledgerPicture_voices :
    (decomposition ledgerPicture).map CompoundComponent.voice =
      [ some VerdictVoice.assertable, some VerdictVoice.assertable,
        some VerdictVoice.assertable, none ] :=
  rfl

theorem skepticism_contains_epistemic_nihilism :
    CompoundComponent.cell (.prose .beingNonBeing) .freeze .epistemic .core ∈
      decomposition skepticism := by
  simp [decomposition]

theorem solipsism_contains_row2_domain_evacuation :
    CompoundComponent.cell (.generated .subjectObjectAxis) .freeze .domain
        .core ∈
      decomposition solipsism := by
  simp [decomposition]

theorem exitPremise_contains_terminus_exit :
    CompoundComponent.cell (.generated .terminusExit) .collapse .plain .core ∈
      decomposition exitPremise := by
  simp [decomposition]

theorem exitPremise_contains_delivery_arrogation :
    CompoundComponent.cell (.generated .deliveryIndex) .collapse .plain
        .alongside ∈
      decomposition exitPremise := by
  simp [decomposition]

theorem existentialism_contains_sartrean_structure :
    CompoundComponent.cell (.generated .standingDated) .freeze .structure
        .core ∈
      decomposition existentialism := by
  simp [decomposition]

theorem existentialism_contains_legal_valueCreation :
    CompoundComponent.legal .valueCreation ∈ decomposition existentialism := by
  simp [decomposition]

theorem ledgerPicture_contains_possession_freeze :
    CompoundComponent.cell (.generated .deliveryIndex) .freeze .plain .core ∈
      decomposition ledgerPicture := by
  simp [decomposition]

theorem ledgerPicture_contains_transposed_mechanism :
    CompoundComponent.cell (.generated .selfPoleTransposed) .freeze .plain
        .core ∈
      decomposition ledgerPicture := by
  simp [decomposition]

theorem ledgerPicture_contains_delivery_arrogation :
    CompoundComponent.cell (.generated .deliveryIndex) .collapse .command
        .alongside ∈
      decomposition ledgerPicture := by
  simp [decomposition]

theorem ledgerPicture_contains_legal_causalSkeleton :
    CompoundComponent.legal .causalSkeleton ∈ decomposition ledgerPicture := by
  simp [decomposition]

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

theorem solipsism_karmaInga_row_not_freeze :
    ¬ (karmaIngaRow G).Freeze :=
  karmaIngaRow_not_freeze G

theorem solipsism_perCallGlobal_row_not_freeze :
    ¬ (perCallGlobalRow G).Freeze :=
  perCallGlobalRow_not_freeze G

theorem solipsism_subjectObjectAxis_row_not_freeze :
    ¬ (subjectObjectAxisRow G).Freeze :=
  subjectObjectAxisRow_not_freeze G

theorem exitPremise_terminusExit_collapse_self_refuting (t : Tier G) :
    ¬ (terminusExitRow G).Collapse t :=
  exit_collapse_self_refuting G t

theorem exitPremise_deliveryIndex_collapse_self_refuting (t : Tier G) :
    ¬ (deliveryIndexRow G).Collapse t :=
  misfed_register_collapse_self_refuting G t

theorem exitPremise_standingDated_row_not_freeze :
    ¬ (standingDatedRow G).Freeze :=
  standingDatedRow_not_freeze G

theorem existentialism_perCallGlobal_row_not_freeze :
    ¬ (perCallGlobalRow G).Freeze :=
  perCallGlobalRow_not_freeze G

theorem existentialism_standingDated_row_not_freeze :
    ¬ (standingDatedRow G).Freeze :=
  standingDatedRow_not_freeze G

theorem existentialism_karmaInga_row_not_freeze :
    ¬ (karmaIngaRow G).Freeze :=
  karmaIngaRow_not_freeze G

theorem ledgerPicture_deliveryIndex_row_not_freeze :
    ¬ (deliveryIndexRow G).Freeze :=
  deliveryIndexRow_not_freeze G

theorem ledgerPicture_deliveryIndex_collapse_self_refuting (t : Tier G) :
    ¬ (deliveryIndexRow G).Collapse t :=
  misfed_register_collapse_self_refuting G t

theorem ledgerPicture_selfPoleTransposed_row_not_freeze :
    ¬ (selfPoleTransposedRow G).Freeze :=
  selfPoleTransposedRow_not_freeze G

end CompoundPosition

end GridConvention
end BeingConvention
end DirectedConvention

end Grid

end KannoSoe
