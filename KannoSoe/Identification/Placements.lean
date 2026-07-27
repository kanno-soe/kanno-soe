/-
================================================================================
  KannoSoe.Identification.Placements
  Contemporary placements
================================================================================

Reading and motivation: Identification/Commentary.lean.
-/

import KannoSoe.Identification.Ownership

namespace KannoSoe

/-- Contemporary positions placed by `Exposition/Identification.md`. -/
inductive ContemporaryPosition
  | siderits
  | ganeri
  | zahavi
  | sartre

/-- Their grid placement. -/
inductive ContemporaryPlacement
  | seriesQuestions
  | nearestAlly
  | retype
  | occupant

namespace ContemporaryPosition

/-- The grid placement assigned to each contemporary position in the paper. -/
def ksmdPlacement : ContemporaryPosition → ContemporaryPlacement
  | .siderits => .seriesQuestions
  | .ganeri => .nearestAlly
  | .zahavi => .retype
  | .sartre => .occupant

theorem siderits_ksmdPlacement :
    ksmdPlacement ContemporaryPosition.siderits = ContemporaryPlacement.seriesQuestions := rfl

theorem ganeri_ksmdPlacement :
    ksmdPlacement ContemporaryPosition.ganeri = ContemporaryPlacement.nearestAlly := rfl

theorem zahavi_ksmdPlacement :
    ksmdPlacement ContemporaryPosition.zahavi = ContemporaryPlacement.retype := rfl

theorem sartre_ksmdPlacement :
    ksmdPlacement ContemporaryPosition.sartre = ContemporaryPlacement.occupant := rfl

end ContemporaryPosition

namespace Grid

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/- Encoding check: the `retype` constructor exists and applies to any pair
   of distinctions (used by the Zahavi placement and the disposition/act
   redrawing). An `example`, not a theorem, for the same reason the voice
   and placement checks are. -/
theorem retype_constructor_exists
    (oldDistinction newDistinction : Distinction G) :
    ∃ out : GeneratorOutcome G,
      out = GeneratorOutcome.retype oldDistinction newDistinction :=
  ⟨GeneratorOutcome.retype oldDistinction newDistinction, rfl⟩

end Grid

end KannoSoe
