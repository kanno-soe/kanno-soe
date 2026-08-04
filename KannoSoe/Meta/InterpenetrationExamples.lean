import KannoSoe.Signature.Interpenetration
import KannoSoe.Meta.Examples

/-!
# Interpenetration examples

The declarations below instantiate formal priming for the galactic-tea
example. Calling the primed system a *floor-tier* presentation is a supplied
reading, not a formal status encoded by the model. Priming connects branches
which remain distinct in the base presentation and makes certification
uniform, with the same universal behavior exhibited directly by
`BeingAndGrading.universalLinkage`.
-/

namespace GalacticTea

abbrev PrimedGalacticTeaDesignatum := Option GalacticTeaDesignatum

/-- The galactic-tea elaboration with a fresh web designatum. -/
def primedTeaElaboration : Elaboration PrimedGalacticTeaDesignatum :=
  Elaboration.prime teaElaboration

/-- A designatum with no elaboration clause can reach only itself. -/
private theorem tea_reaches_eq_of_no_elaboration
    {d w : GalacticTeaDesignatum}
    (hnone : ∀ rawM, ¬ teaElaboration.Elab d rawM)
    (h : teaElaboration.Reaches d w) : w = d := by
  cases h with
  | refl _ => rfl
  | step hElab _ _ _ => exact (hnone _ hElab).elim

/-- Two distinct terminal designata are not joinable in the base elaboration. -/
private theorem tea_not_joinable_of_no_elaboration
    {a b : GalacticTeaDesignatum}
    (ha : ∀ rawM, ¬ teaElaboration.Elab a rawM)
    (hb : ∀ rawM, ¬ teaElaboration.Elab b rawM)
    (hne : a ≠ b) : ¬ teaElaboration.Joinable a b := by
  rintro ⟨w, haw, hbw⟩
  apply hne
  exact
    (tea_reaches_eq_of_no_elaboration ha haw).symm.trans
      (tea_reaches_eq_of_no_elaboration hb hbw)

/-- The terminal tea-drinking results are not joinable in the base system. -/
theorem tea_drinkingResults_not_joinable :
    ¬ teaElaboration.Joinable
      GalacticTeaDesignatum.meDrinkingTeaOnEarth
      GalacticTeaDesignatum.someoneDrinkingTeaOnVesper := by
  apply tea_not_joinable_of_no_elaboration
  · intro rawM
    simp [teaElaboration]
  · intro rawM
    simp [teaElaboration]
  · simp

/--
Priming makes the previously non-joinable terminal tea-drinking results
joinable.
-/
theorem primedTea_drinkingResults_joinable :
    primedTeaElaboration.Joinable
      (some GalacticTeaDesignatum.meDrinkingTeaOnEarth)
      (some GalacticTeaDesignatum.someoneDrinkingTeaOnVesper) :=
  Elaboration.prime_joinable_total teaElaboration _ _

/-- The terminal `moreEarth` and `moreVesper` residues are not joinable at base. -/
theorem tea_moreEarth_moreVesper_not_joinable :
    ¬ teaElaboration.Joinable
      GalacticTeaDesignatum.moreEarth
      GalacticTeaDesignatum.moreVesper := by
  apply tea_not_joinable_of_no_elaboration
  · intro rawM
    simp [teaElaboration]
  · intro rawM
    simp [teaElaboration]
  · simp

/--
Priming makes the previously non-joinable terminal branch residues joinable.
-/
theorem primedTea_moreEarth_moreVesper_joinable :
    primedTeaElaboration.Joinable
      (some GalacticTeaDesignatum.moreEarth)
      (some GalacticTeaDesignatum.moreVesper) :=
  Elaboration.prime_joinable_total teaElaboration _ _

/--
The linkage derived from the primed tea elaboration is universal. Unlike
`BeingAndGrading.universalLinkage`, whose proofs are definitionally `True`,
this universality is a theorem forced by the priming construction.
-/
theorem primedTea_linked_total
    (c₁ c₂ : Component PrimedGalacticTeaDesignatum) :
    (Linkage.ofElaboration primedTeaElaboration).Linked c₁ c₂ :=
  Elaboration.prime_linked_total teaElaboration c₁ c₂

/--
The raw five-component shape underlying `galacticTeaDependence`, stated
without reusing its certification proof so the primed example exposes exactly
which proof obligation priming discharges.
-/
def rawGalacticTeaDependence :
    RawMutualDependence GalacticTeaDesignatum where
  linkage := Linkage.ofElaboration teaElaboration
  c₁ := meDrinkingTea
  middle := [earth, bigBang, vesper]
  cₙ := someoneDrinkingTea

/-- The raw galactic-tea component chain lifted into the primed domain. -/
def primedGalacticTeaRaw :
    RawMutualDependence PrimedGalacticTeaDesignatum :=
  RawMutualDependence.mapComponents rawGalacticTeaDependence some
    (Linkage.ofElaboration primedTeaElaboration)

/--
Under the base elaboration, `galacticTeaDependence` supplies four explicit
adjacent-linkage proofs. Under the prime, the same component shape is certified
uniformly by `Elaboration.prime_certification_trivial`.
-/
def primedGalacticTeaDependence :
    MutualDependence PrimedGalacticTeaDesignatum where
  toRaw := primedTeaElaboration.certify primedGalacticTeaRaw
  holds := by
    exact
      Elaboration.prime_certification_trivial teaElaboration
        primedGalacticTeaRaw

end GalacticTea
