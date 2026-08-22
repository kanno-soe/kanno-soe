import KannoSoe.Signature.Rules

/-!
# Signature examples

Examples of certified beings, two-sided resonance grades, and temporality.
-/

namespace BeingAndGrading

inductive Signal where
  | firstCall
  | firstBeing
  | secondBeing
  | firstResponse
  | secondCall
  | thirdBeing
  | fourthBeing
  | secondResponse
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

open Signal

def universalInterdependence : Interdependence Signal where
  Interdependent := fun _ _ => True
  symm := fun _ => trivial

def firstResonance : Resonance Signal :=
  Resonance.mk' universalInterdependence
    (Component.singleton firstCall) firstBeing secondBeing
    (Component.singleton firstResponse) trivial trivial trivial

def secondResonance : Resonance Signal :=
  Resonance.mk' universalInterdependence
    (Component.singleton secondCall) thirdBeing fourthBeing
    (Component.singleton secondResponse) trivial trivial trivial

def singleBeing : Being Signal :=
  Being.ofMutualDependence
    (MutualDependence.pair universalInterdependence
      (Component.singleton a)
      (Component.singleton b) trivial) (by
        intro component hc
        change component ∈
          [Component.singleton a,
            Component.singleton b] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> exact ⟨_, rfl⟩)

theorem consecutiveBeingComponentsInterdependent :
    universalInterdependence.Interdependent
      (Component.singleton b)
      (Component.singleton c) :=
  trivial

def multiBeing : Being Signal :=
  Being.ofMutualDependence
    (MutualDependence.ofComponents universalInterdependence
      (Component.singleton a)
      (Component.singleton b)
      [Component.singleton c,
        Component.singleton d] (by
          exact
            .cons trivial
              (.cons consecutiveBeingComponentsInterdependent
                (.cons trivial (.single _))))) (by
        intro component hc
        change component ∈
          [Component.singleton a,
            Component.singleton b,
            Component.singleton c,
            Component.singleton d] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)

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
  | bigBang
  | earth
  | vesper
  | meDrinkingTea
  | someoneDrinkingTea
  | bigBangProducingEarth
  | moreBigBang
  | bigBangProducingVesper
  | moreEarth
  | meOnEarth
  | meDrinkingTeaOnEarth
  | moreVesper
  | someoneOnVesper
  | someoneDrinkingTeaOnVesper
  deriving DecidableEq, Repr

open GalacticTeaDesignatum

abbrev bigBang : Component GalacticTeaDesignatum :=
  Component.singleton GalacticTeaDesignatum.bigBang

abbrev earth : Component GalacticTeaDesignatum :=
  Component.singleton GalacticTeaDesignatum.earth

abbrev vesper : Component GalacticTeaDesignatum :=
  Component.singleton GalacticTeaDesignatum.vesper

abbrev meDrinkingTea : Component GalacticTeaDesignatum :=
  Component.singleton GalacticTeaDesignatum.meDrinkingTea

abbrev someoneDrinkingTea : Component GalacticTeaDesignatum :=
  Component.singleton GalacticTeaDesignatum.someoneDrinkingTea

theorem bigBang_designatum_mem :
    GalacticTeaDesignatum.bigBang ∈ bigBang := by
  simp [bigBang]

theorem meDrinkingTea_designatum_mem :
    GalacticTeaDesignatum.meDrinkingTea ∈ meDrinkingTea := by
  simp [meDrinkingTea]

theorem someoneDrinkingTea_designatum_mem :
    GalacticTeaDesignatum.someoneDrinkingTea ∈ someoneDrinkingTea := by
  simp [someoneDrinkingTea]

/-- The galactic-tea clauses as a finite elaboration-rule presentation. -/
abbrev teaElaboration : Elaboration GalacticTeaDesignatum :=
  Elaboration.ofRules [
    { source := GalacticTeaDesignatum.bigBang
      components :=
        [[bigBangProducingVesper], [moreBigBang], [bigBangProducingEarth]] },
    { source := GalacticTeaDesignatum.earth
      components :=
        [[bigBangProducingEarth], [moreEarth], [meOnEarth]] },
    { source := GalacticTeaDesignatum.vesper
      components :=
        [[bigBangProducingVesper], [moreVesper], [someoneOnVesper]] },
    { source := GalacticTeaDesignatum.meDrinkingTea
      components := [[meOnEarth], [meDrinkingTeaOnEarth]] },
    { source := GalacticTeaDesignatum.someoneDrinkingTea
      components := [[someoneOnVesper], [someoneDrinkingTeaOnVesper]] }
  ]

theorem bigBang_vesper_joinable :
    teaElaboration.Joinable
      GalacticTeaDesignatum.bigBang GalacticTeaDesignatum.vesper := by
  decide

theorem earth_bigBang_joinable :
    teaElaboration.Joinable
      GalacticTeaDesignatum.earth GalacticTeaDesignatum.bigBang := by
  decide

theorem vesper_someoneDrinkingTea_joinable :
    teaElaboration.Joinable
      GalacticTeaDesignatum.vesper
        GalacticTeaDesignatum.someoneDrinkingTea := by
  decide

theorem meDrinkingTea_earth_joinable :
    teaElaboration.Joinable
      GalacticTeaDesignatum.meDrinkingTea GalacticTeaDesignatum.earth := by
  decide

theorem bigBang_vesper_interdependent :
    teaElaboration.Interdependent bigBang vesper := by decide

theorem earth_bigBang_interdependent :
    teaElaboration.Interdependent earth bigBang := by decide

theorem vesper_someoneDrinkingTea_interdependent :
    teaElaboration.Interdependent vesper someoneDrinkingTea := by decide

theorem meDrinkingTea_earth_interdependent :
    teaElaboration.Interdependent meDrinkingTea earth := by decide

/-- The displayed component chain certified by the tea example. -/
abbrev galacticTeaChain : ElabRule GalacticTeaDesignatum :=
  { source := GalacticTeaDesignatum.meDrinkingTea
    components :=
      [[GalacticTeaDesignatum.meDrinkingTea],
        [GalacticTeaDesignatum.earth],
        [GalacticTeaDesignatum.bigBang],
        [GalacticTeaDesignatum.vesper],
        [GalacticTeaDesignatum.someoneDrinkingTea]] }

def galacticTeaDependence : MutualDependence GalacticTeaDesignatum where
  toRaw := galacticTeaChain.toRaw
    (Interdependence.ofElaboration teaElaboration)
  holds := by decide

theorem galacticTeaDependence_components :
    galacticTeaDependence.components =
      [meDrinkingTea, earth, bigBang, vesper, someoneDrinkingTea] :=
  rfl

def bigBangVesperTeaDependence : MutualDependence GalacticTeaDesignatum :=
  MutualDependence.triple teaElaboration bigBang vesper someoneDrinkingTea
    bigBang_vesper_interdependent vesper_someoneDrinkingTea_interdependent

def bigBangEarthTeaDependence : MutualDependence GalacticTeaDesignatum :=
  MutualDependence.triple teaElaboration bigBang earth meDrinkingTea
    earth_bigBang_interdependent.symm meDrinkingTea_earth_interdependent.symm

inductive TeaBefore :
    GalacticTeaDesignatum → GalacticTeaDesignatum → Prop where
  | bigBang_vesper :
      TeaBefore GalacticTeaDesignatum.bigBang
        GalacticTeaDesignatum.someoneDrinkingTea
  | bigBang_earth :
      TeaBefore GalacticTeaDesignatum.bigBang
        GalacticTeaDesignatum.meDrinkingTea

def teaRank : GalacticTeaDesignatum → Nat
  | .bigBang => 0
  | .vesper => 0
  | .earth => 0
  | .someoneDrinkingTea => 1
  | .meDrinkingTea => 1
  | bigBangProducingVesper => 0
  | moreBigBang => 0
  | bigBangProducingEarth => 0
  | moreVesper => 0
  | someoneOnVesper => 1
  | someoneDrinkingTeaOnVesper => 1
  | moreEarth => 0
  | meOnEarth => 1
  | meDrinkingTeaOnEarth => 1

theorem teaBefore_rank_lt {x y : GalacticTeaDesignatum} (h : TeaBefore x y) :
    teaRank x < teaRank y := by
  cases h <;> decide

def teaBefore_temporal {x y : GalacticTeaDesignatum}
    (h : Relation.TransGen TeaBefore x y) :
    Temporal GalacticTeaDesignatum x y := by
  induction h with
  | single hxy =>
      cases hxy with
      | bigBang_vesper =>
          exact .ofMutualDependence bigBangVesperTeaDependence
            bigBang_designatum_mem someoneDrinkingTea_designatum_mem
      | bigBang_earth =>
          exact .ofMutualDependence bigBangEarthTeaDependence
            bigBang_designatum_mem meDrinkingTea_designatum_mem
  | tail hxy hyz _ =>
      have hlt :=
        Temporality.rank_lt_of_transGen
          (base := TeaBefore) (rank := teaRank) teaBefore_rank_lt hxy
      cases hyz <;> exact (Nat.not_lt_zero _ hlt).elim

def teaTemporal : Temporality GalacticTeaDesignatum :=
  Temporality.ofBaseRank TeaBefore teaRank teaBefore_rank_lt teaBefore_temporal

inductive TeaCauses :
    GalacticTeaDesignatum → GalacticTeaDesignatum → Prop where
  | bigBang_vesper :
      TeaCauses GalacticTeaDesignatum.bigBang
        GalacticTeaDesignatum.someoneDrinkingTea
  | bigBang_earth :
      TeaCauses GalacticTeaDesignatum.bigBang
        GalacticTeaDesignatum.meDrinkingTea

def teaCausal : Causal GalacticTeaDesignatum where
  toTemporality := teaTemporal
  Causes := TeaCauses
  causes_before := fun h => by
    cases h with
    | bigBang_vesper =>
        exact Relation.TransGen.single TeaBefore.bigBang_vesper
    | bigBang_earth =>
        exact Relation.TransGen.single TeaBefore.bigBang_earth

example : Temporal GalacticTeaDesignatum
    GalacticTeaDesignatum.bigBang
      GalacticTeaDesignatum.someoneDrinkingTea :=
  teaTemporal.certify
    (Relation.TransGen.single TeaBefore.bigBang_vesper)

example : Temporal GalacticTeaDesignatum
    GalacticTeaDesignatum.bigBang GalacticTeaDesignatum.meDrinkingTea :=
  teaTemporal.certify
    (Relation.TransGen.single TeaBefore.bigBang_earth)

theorem vesperEarthTea_not_before :
    ¬ teaTemporal.Before
      GalacticTeaDesignatum.someoneDrinkingTea
        GalacticTeaDesignatum.meDrinkingTea := by
  intro h
  change Relation.TransGen TeaBefore
    GalacticTeaDesignatum.someoneDrinkingTea
      GalacticTeaDesignatum.meDrinkingTea at h
  exact Nat.lt_irrefl 1
    (Temporality.rank_lt_of_transGen
      (base := TeaBefore) (rank := teaRank) teaBefore_rank_lt h)

theorem earthVesperTea_not_before :
    ¬ teaTemporal.Before
      GalacticTeaDesignatum.meDrinkingTea
        GalacticTeaDesignatum.someoneDrinkingTea := by
  intro h
  change Relation.TransGen TeaBefore
    GalacticTeaDesignatum.meDrinkingTea
      GalacticTeaDesignatum.someoneDrinkingTea at h
  exact Nat.lt_irrefl 1
    (Temporality.rank_lt_of_transGen
      (base := TeaBefore) (rank := teaRank) teaBefore_rank_lt h)

theorem vesperTea_not_before_bigBang :
    ¬ teaTemporal.Before
      GalacticTeaDesignatum.someoneDrinkingTea
        GalacticTeaDesignatum.bigBang := by
  apply teaTemporal.asymm
  change Relation.TransGen TeaBefore
    GalacticTeaDesignatum.bigBang
      GalacticTeaDesignatum.someoneDrinkingTea
  exact Relation.TransGen.single TeaBefore.bigBang_vesper

theorem earthTea_not_before_bigBang :
    ¬ teaTemporal.Before GalacticTeaDesignatum.meDrinkingTea
      GalacticTeaDesignatum.bigBang := by
  apply teaTemporal.asymm
  change Relation.TransGen TeaBefore
    GalacticTeaDesignatum.bigBang GalacticTeaDesignatum.meDrinkingTea
  exact Relation.TransGen.single TeaBefore.bigBang_earth

end GalacticTea
