/-
================================================================================
  KannoSoe.Meta.ReflexivityWitness
  One rung-indexed grid witnessing the ladder over its own labels
================================================================================

Jizang's fourfold two-truths are re-emptied here over their own rung labels.
This is a single legal reading package whose designata include ladder-rung
labels. It does not recover a canonical being boundary.
-/

import KannoSoe.Meta.Metaphysics

namespace KannoSoe

namespace Grid
namespace DirectedConvention
namespace BeingConvention
namespace GridConvention

inductive LadderRungCase
  | rung (n : Nat)
  | cue
  | result
  | occurrence (n : Nat)

/-- A concrete package whose designata include ladder-rung labels. -/
def ladderRungGrid : CoreReadings LadderRungCase Nat where
  occurrence := {
    occurrence := fun d =>
      match d with
      | .occurrence _ => True
      | _ => False
    isBeing := fun d =>
      match d with
      | .rung _ => True
      | _ => False
    isCall := fun d => d = .cue
    isResponse := fun d => d = .result
    agent := fun d =>
      match d with
      | .occurrence n => .rung n
      | _ => d
    call := fun d =>
      match d with
      | .occurrence _ => .cue
      | _ => d
    response := fun d =>
      match d with
      | .occurrence _ => .result
      | _ => d
  }
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .rung _, .cue => some .result
      | _, _ => none
  }
  placement := {
    grade := fun d =>
      match d with
      | .occurrence n => n
      | _ => 0
  }
  conditioning := { conditions := fun _ _ => True }

theorem ladderRungGrid_beings_sunyata :
    Metaphysics.Sunyata (beingsRow ladderRungGrid) :=
  Metaphysics.beings_sunyata ladderRungGrid

theorem ladderRungGrid_no_level_final :
    ∀ n, ¬ (beingsLadder ladderRungGrid n).Freeze :=
  beingsLadder_no_level_final ladderRungGrid

end GridConvention
end BeingConvention
end DirectedConvention
end Grid

end KannoSoe
