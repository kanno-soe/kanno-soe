import KannoSoe.Signature.V2

/-!
# Signature examples

Examples of certified beings, two-sided resonance grades, and direction.
-/

namespace BeingAndGrading

inductive Signal where
  | firstCall
  | firstBeing
  | firstResponse
  | firstResult
  | secondCall
  | secondBeing
  | secondResponse
  | secondResult
  deriving DecidableEq, Repr

open Signal

def universalLinkage : Linkage Signal where
  Linked := fun _ _ => True
  symm := fun _ => trivial

def firstResonance : Resonance Signal :=
  Resonance.mk' universalLinkage
    (Component.singleton firstCall) firstBeing firstResponse
    (Component.singleton firstResult) trivial trivial trivial

def secondResonance : Resonance Signal :=
  Resonance.mk' universalLinkage
    (Component.singleton secondCall) secondBeing secondResponse
    (Component.singleton secondResult) trivial trivial trivial

def singleBeing : Being Signal :=
  Being.ofResonances universalLinkage [firstResonance] (by simp) (by
    show
      universalLinkage.ChainLinked
        [Component.singleton firstBeing, Component.singleton firstResponse]
    exact .cons trivial (.single _))

theorem consecutiveMiddlesLinked :
    universalLinkage.Linked
      (Component.singleton firstResponse)
      (Component.singleton secondBeing) :=
  trivial

def multiBeing : Being Signal :=
  Being.ofResonances universalLinkage
    [firstResonance, secondResonance] (by simp) (by
      show
        universalLinkage.ChainLinked
          [Component.singleton firstBeing,
            Component.singleton firstResponse,
            Component.singleton secondBeing,
            Component.singleton secondResponse]
      exact
        .cons trivial
          (.cons consecutiveMiddlesLinked
            (.cons trivial (.single _))))

def natPreorderBot : PreorderBot Nat where
  le := (· ≤ ·)
  bot := 0
  leRefl := Nat.le_refl
  leTrans := Nat.le_trans
  botLeast := Nat.zero_le

def independentlyGraded : GradedResonance Signal natPreorderBot :=
  GradedResonance.ofResonance firstResonance 2 7

example :
    (GradedResonance.ofResonance
      (PB := natPreorderBot) firstResonance 2 7).callsGrade = 2 := by
  simp

example :
    (GradedResonance.ofResonance
      (PB := natPreorderBot) firstResonance 2 7).responsesGrade = 7 := by
  simp

def ungradedResonance : GradedResonance Signal natPreorderBot :=
  GradedResonance.ungraded firstResonance

example : ungradedResonance.callsGrade = natPreorderBot.bot := by
  simp [ungradedResonance]

example : ungradedResonance.responsesGrade = natPreorderBot.bot := by
  simp [ungradedResonance]

example : GradedResonance.IsUngraded ungradedResonance := by
  simp [GradedResonance.IsUngraded, ungradedResonance]

def lowerGrades : GradedResonance Signal natPreorderBot :=
  GradedResonance.ofResonance firstResonance 1 3

example : GradedResonance.le lowerGrades independentlyGraded := by
  change 1 ≤ 2 ∧ 3 ≤ 7
  decide

end BeingAndGrading

/-! ## Galactic tea drinking -/

namespace GalacticTea

inductive GalacticTeaDesignatum where
  | bigBangProducingEarth
  | bigBangProducingVesper
  | meDrinkingTeaOnEarth
  | someoneDrinkingTeaOnVesper
  deriving DecidableEq, Repr

open GalacticTeaDesignatum

def bigBang : Component GalacticTeaDesignatum :=
  Component.pair bigBangProducingEarth bigBangProducingVesper

def earth : Component GalacticTeaDesignatum :=
  Component.pair bigBangProducingEarth meDrinkingTeaOnEarth

def vesper : Component GalacticTeaDesignatum :=
  Component.pair bigBangProducingVesper someoneDrinkingTeaOnVesper

def meDrinkingTea : Component GalacticTeaDesignatum :=
  Component.singleton meDrinkingTeaOnEarth

def someoneDrinkingTea : Component GalacticTeaDesignatum :=
  Component.singleton someoneDrinkingTeaOnVesper

def teaLinkage : Linkage GalacticTeaDesignatum where
  Linked := fun c₁ c₂ => ∃ d, d ∈ c₁ ∧ d ∈ c₂
  symm := fun ⟨d, hc₁, hc₂⟩ => ⟨d, hc₂, hc₁⟩

theorem meDrinkingTea_earth_linked :
    teaLinkage.Linked meDrinkingTea earth := by
  simp [teaLinkage, meDrinkingTea, earth]

theorem earth_bigBang_linked : teaLinkage.Linked earth bigBang := by
  simp [teaLinkage, earth, bigBang]

theorem bigBang_vesper_linked : teaLinkage.Linked bigBang vesper := by
  simp [teaLinkage, bigBang, vesper]

theorem vesper_someoneDrinkingTea_linked :
    teaLinkage.Linked vesper someoneDrinkingTea := by
  simp [teaLinkage, vesper, someoneDrinkingTea]

def galacticTeaDependence : MutualDependence GalacticTeaDesignatum where
  toRaw :=
    ⟨teaLinkage, meDrinkingTea, [earth, bigBang, vesper],
      someoneDrinkingTea⟩
  holds :=
    .cons meDrinkingTea_earth_linked
      (.cons earth_bigBang_linked
        (.cons bigBang_vesper_linked
          (.cons vesper_someoneDrinkingTea_linked (.single _))))

theorem galacticTeaDependence_components :
    galacticTeaDependence.components =
      [meDrinkingTea, earth, bigBang, vesper, someoneDrinkingTea] :=
  rfl

def bigBangEarthTeaDependence : MutualDependence GalacticTeaDesignatum :=
  MutualDependence.triple teaLinkage bigBang earth meDrinkingTea
    (teaLinkage.symm earth_bigBang_linked)
    (teaLinkage.symm meDrinkingTea_earth_linked)

def bigBangVesperTeaDependence : MutualDependence GalacticTeaDesignatum :=
  MutualDependence.triple teaLinkage bigBang vesper someoneDrinkingTea
    bigBang_vesper_linked vesper_someoneDrinkingTea_linked

inductive TeaBefore :
    GalacticTeaDesignatum → GalacticTeaDesignatum → Prop where
  | bigBang_earth :
      TeaBefore bigBangProducingEarth meDrinkingTeaOnEarth
  | bigBang_vesper :
      TeaBefore bigBangProducingVesper someoneDrinkingTeaOnVesper

def teaRank : GalacticTeaDesignatum → Nat
  | bigBangProducingEarth => 0
  | bigBangProducingVesper => 0
  | meDrinkingTeaOnEarth => 1
  | someoneDrinkingTeaOnVesper => 1

theorem teaBefore_rank_lt {x y : GalacticTeaDesignatum} (h : TeaBefore x y) :
    teaRank x < teaRank y := by
  cases h <;> decide

def teaDirection : Directed GalacticTeaDesignatum :=
  Directed.ofBaseRank TeaBefore teaRank teaBefore_rank_lt

inductive TeaCauses :
    GalacticTeaDesignatum → GalacticTeaDesignatum → Prop where
  | bigBang_earth :
      TeaCauses bigBangProducingEarth meDrinkingTeaOnEarth
  | bigBang_vesper :
      TeaCauses bigBangProducingVesper someoneDrinkingTeaOnVesper

def teaCausal : Causal GalacticTeaDesignatum where
  toDirected := teaDirection
  Causes := TeaCauses
  causes_before := fun h => by
    cases h with
    | bigBang_earth =>
        exact Relation.TransGen.single TeaBefore.bigBang_earth
    | bigBang_vesper =>
        exact Relation.TransGen.single TeaBefore.bigBang_vesper
  certify := fun h => by
    cases h with
    | bigBang_earth =>
        exact .ofMutualDependence bigBangEarthTeaDependence
          (by
            change bigBangProducingEarth ∈ bigBang
            simp [bigBang])
          (by
            change meDrinkingTeaOnEarth ∈ meDrinkingTea
            simp [meDrinkingTea])
    | bigBang_vesper =>
        exact .ofMutualDependence bigBangVesperTeaDependence
          (by
            change bigBangProducingVesper ∈ bigBang
            simp [bigBang])
          (by
            change someoneDrinkingTeaOnVesper ∈ someoneDrinkingTea
            simp [someoneDrinkingTea])

example : Causation GalacticTeaDesignatum
    bigBangProducingEarth meDrinkingTeaOnEarth :=
  teaCausal.certify TeaCauses.bigBang_earth

example : Causation GalacticTeaDesignatum
    bigBangProducingVesper someoneDrinkingTeaOnVesper :=
  teaCausal.certify TeaCauses.bigBang_vesper

theorem earthVesperTea_not_before :
    ¬ teaDirection.Before
      meDrinkingTeaOnEarth someoneDrinkingTeaOnVesper := by
  intro h
  change Relation.TransGen TeaBefore
    meDrinkingTeaOnEarth someoneDrinkingTeaOnVesper at h
  exact Nat.lt_irrefl 1
    (Directed.rank_lt_of_transGen
      (base := TeaBefore) (rank := teaRank) teaBefore_rank_lt h)

theorem vesperEarthTea_not_before :
    ¬ teaDirection.Before
      someoneDrinkingTeaOnVesper meDrinkingTeaOnEarth := by
  intro h
  change Relation.TransGen TeaBefore
    someoneDrinkingTeaOnVesper meDrinkingTeaOnEarth at h
  exact Nat.lt_irrefl 1
    (Directed.rank_lt_of_transGen
      (base := TeaBefore) (rank := teaRank) teaBefore_rank_lt h)

theorem earthTea_not_before_bigBang :
    ¬ teaDirection.Before meDrinkingTeaOnEarth bigBangProducingEarth := by
  apply teaDirection.asymm
  change Relation.TransGen TeaBefore
    bigBangProducingEarth meDrinkingTeaOnEarth
  exact Relation.TransGen.single TeaBefore.bigBang_earth

theorem vesperTea_not_before_bigBang :
    ¬ teaDirection.Before
      someoneDrinkingTeaOnVesper bigBangProducingVesper := by
  apply teaDirection.asymm
  change Relation.TransGen TeaBefore
    bigBangProducingVesper someoneDrinkingTeaOnVesper
  exact Relation.TransGen.single TeaBefore.bigBang_vesper

end GalacticTea
