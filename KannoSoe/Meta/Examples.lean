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

def bigBang : Component GalacticTeaDesignatum :=
  Component.singleton GalacticTeaDesignatum.bigBang

def earth : Component GalacticTeaDesignatum :=
  Component.singleton GalacticTeaDesignatum.earth

def vesper : Component GalacticTeaDesignatum :=
  Component.singleton GalacticTeaDesignatum.vesper

def meDrinkingTea : Component GalacticTeaDesignatum :=
  Component.singleton GalacticTeaDesignatum.meDrinkingTea

def someoneDrinkingTea : Component GalacticTeaDesignatum :=
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

def teaElaboration : Elaboration GalacticTeaDesignatum where
  Elab d rawM :=
    (d = GalacticTeaDesignatum.bigBang ∧
        rawM.components =
          [Component.singleton bigBangProducingVesper,
            Component.singleton moreBigBang,
            Component.singleton bigBangProducingEarth]) ∨
      (d = GalacticTeaDesignatum.earth ∧
        rawM.components =
          [Component.singleton bigBangProducingEarth,
            Component.singleton moreEarth,
            Component.singleton meOnEarth]) ∨
      (d = GalacticTeaDesignatum.vesper ∧
        rawM.components =
          [Component.singleton bigBangProducingVesper,
            Component.singleton moreVesper,
            Component.singleton someoneOnVesper]) ∨
      (d = GalacticTeaDesignatum.meDrinkingTea ∧
        rawM.components =
          [Component.singleton meOnEarth,
            Component.singleton meDrinkingTeaOnEarth]) ∨
      (d = GalacticTeaDesignatum.someoneDrinkingTea ∧
        rawM.components =
          [Component.singleton someoneOnVesper,
            Component.singleton someoneDrinkingTeaOnVesper])

def bigBangElaborationTarget :
    RawMutualDependence GalacticTeaDesignatum :=
  RawMutualDependence.triple teaElaboration
    (Component.singleton bigBangProducingVesper)
    (Component.singleton moreBigBang)
    (Component.singleton bigBangProducingEarth)

def earthElaborationTarget : RawMutualDependence GalacticTeaDesignatum :=
  RawMutualDependence.triple teaElaboration
    (Component.singleton bigBangProducingEarth)
    (Component.singleton moreEarth)
    (Component.singleton meOnEarth)

def vesperElaborationTarget : RawMutualDependence GalacticTeaDesignatum :=
  RawMutualDependence.triple teaElaboration
    (Component.singleton bigBangProducingVesper)
    (Component.singleton moreVesper)
    (Component.singleton someoneOnVesper)

def meDrinkingTeaElaborationTarget :
    RawMutualDependence GalacticTeaDesignatum :=
  RawMutualDependence.pair teaElaboration
    (Component.singleton meOnEarth)
    (Component.singleton meDrinkingTeaOnEarth)

def someoneDrinkingTeaElaborationTarget :
    RawMutualDependence GalacticTeaDesignatum :=
  RawMutualDependence.pair teaElaboration
    (Component.singleton someoneOnVesper)
    (Component.singleton someoneDrinkingTeaOnVesper)

theorem bigBang_elaborates :
    teaElaboration.Elab
      GalacticTeaDesignatum.bigBang bigBangElaborationTarget := by
  simp [teaElaboration, bigBangElaborationTarget]

theorem earth_elaborates :
    teaElaboration.Elab
      GalacticTeaDesignatum.earth earthElaborationTarget := by
  simp [teaElaboration, earthElaborationTarget]

theorem vesper_elaborates :
    teaElaboration.Elab
      GalacticTeaDesignatum.vesper vesperElaborationTarget := by
  simp [teaElaboration, vesperElaborationTarget]

theorem meDrinkingTea_elaborates :
    teaElaboration.Elab GalacticTeaDesignatum.meDrinkingTea
      meDrinkingTeaElaborationTarget := by
  simp [teaElaboration, meDrinkingTeaElaborationTarget]

theorem someoneDrinkingTea_elaborates :
    teaElaboration.Elab GalacticTeaDesignatum.someoneDrinkingTea
      someoneDrinkingTeaElaborationTarget := by
  simp [teaElaboration, someoneDrinkingTeaElaborationTarget]

theorem bigBang_vesper_related :
    teaElaboration.Related
      GalacticTeaDesignatum.bigBang GalacticTeaDesignatum.vesper :=
  ⟨bigBangProducingVesper,
    Elaboration.Reaches.single bigBang_elaborates
      (rawM := bigBangElaborationTarget)
      (a := Component.singleton bigBangProducingVesper)
      (by simp [bigBangElaborationTarget]) (by simp),
    Elaboration.Reaches.single vesper_elaborates
      (rawM := vesperElaborationTarget)
      (a := Component.singleton bigBangProducingVesper)
      (by simp [vesperElaborationTarget]) (by simp)⟩

theorem earth_bigBang_related :
    teaElaboration.Related
      GalacticTeaDesignatum.earth GalacticTeaDesignatum.bigBang :=
  ⟨bigBangProducingEarth,
    Elaboration.Reaches.single earth_elaborates
      (rawM := earthElaborationTarget)
      (a := Component.singleton bigBangProducingEarth)
      (by simp [earthElaborationTarget]) (by simp),
    Elaboration.Reaches.single bigBang_elaborates
      (rawM := bigBangElaborationTarget)
      (a := Component.singleton bigBangProducingEarth)
      (by simp [bigBangElaborationTarget]) (by simp)⟩

theorem vesper_someoneDrinkingTea_related :
    teaElaboration.Related
      GalacticTeaDesignatum.vesper
        GalacticTeaDesignatum.someoneDrinkingTea :=
  ⟨someoneOnVesper,
    Elaboration.Reaches.single vesper_elaborates
      (rawM := vesperElaborationTarget)
      (a := Component.singleton someoneOnVesper)
      (by simp [vesperElaborationTarget]) (by simp),
    Elaboration.Reaches.single someoneDrinkingTea_elaborates
      (rawM := someoneDrinkingTeaElaborationTarget)
      (a := Component.singleton someoneOnVesper)
      (by simp [someoneDrinkingTeaElaborationTarget]) (by simp)⟩

theorem meDrinkingTea_earth_related :
    teaElaboration.Related
      GalacticTeaDesignatum.meDrinkingTea GalacticTeaDesignatum.earth :=
  ⟨meOnEarth,
    Elaboration.Reaches.single meDrinkingTea_elaborates
      (rawM := meDrinkingTeaElaborationTarget)
      (a := Component.singleton meOnEarth)
      (by simp [meDrinkingTeaElaborationTarget]) (by simp),
    Elaboration.Reaches.single earth_elaborates
      (rawM := earthElaborationTarget)
      (a := Component.singleton meOnEarth)
      (by simp [earthElaborationTarget]) (by simp)⟩

attribute [local simp] Elaboration.Related.refl
  bigBang_vesper_related earth_bigBang_related
  vesper_someoneDrinkingTea_related meDrinkingTea_earth_related

theorem bigBang_vesper_linked :
    teaElaboration.Linked bigBang vesper := by
  simp [Elaboration.Linked, bigBang, vesper]

theorem earth_bigBang_linked :
    teaElaboration.Linked earth bigBang := by
  simp [Elaboration.Linked, earth, bigBang]

theorem vesper_someoneDrinkingTea_linked :
    teaElaboration.Linked vesper someoneDrinkingTea := by
  simp [Elaboration.Linked, vesper, someoneDrinkingTea]

theorem meDrinkingTea_earth_linked :
    teaElaboration.Linked meDrinkingTea earth := by
  simp [Elaboration.Linked, meDrinkingTea, earth]

def galacticTeaDependence : MutualDependence GalacticTeaDesignatum where
  toRaw :=
    ⟨teaElaboration, meDrinkingTea, [earth, bigBang, vesper],
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

def bigBangVesperTeaDependence : MutualDependence GalacticTeaDesignatum :=
  MutualDependence.triple teaElaboration bigBang vesper someoneDrinkingTea
    bigBang_vesper_linked vesper_someoneDrinkingTea_linked

def bigBangEarthTeaDependence : MutualDependence GalacticTeaDesignatum :=
  MutualDependence.triple teaElaboration bigBang earth meDrinkingTea
    earth_bigBang_linked.symm meDrinkingTea_earth_linked.symm

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

def teaDirection : Directed GalacticTeaDesignatum :=
  Directed.ofBaseRank TeaBefore teaRank teaBefore_rank_lt

inductive TeaCauses :
    GalacticTeaDesignatum → GalacticTeaDesignatum → Prop where
  | bigBang_vesper :
      TeaCauses GalacticTeaDesignatum.bigBang
        GalacticTeaDesignatum.someoneDrinkingTea
  | bigBang_earth :
      TeaCauses GalacticTeaDesignatum.bigBang
        GalacticTeaDesignatum.meDrinkingTea

def teaCausal : Causal GalacticTeaDesignatum where
  toDirected := teaDirection
  Causes := TeaCauses
  causes_before := fun h => by
    cases h with
    | bigBang_vesper =>
        exact Relation.TransGen.single TeaBefore.bigBang_vesper
    | bigBang_earth =>
        exact Relation.TransGen.single TeaBefore.bigBang_earth
  certify := fun h => by
    cases h with
    | bigBang_vesper =>
        exact .ofMutualDependence bigBangVesperTeaDependence
          bigBang_designatum_mem someoneDrinkingTea_designatum_mem
    | bigBang_earth =>
        exact .ofMutualDependence bigBangEarthTeaDependence
          bigBang_designatum_mem meDrinkingTea_designatum_mem

example : Causation GalacticTeaDesignatum
    GalacticTeaDesignatum.bigBang
      GalacticTeaDesignatum.someoneDrinkingTea :=
  teaCausal.certify TeaCauses.bigBang_vesper

example : Causation GalacticTeaDesignatum
    GalacticTeaDesignatum.bigBang GalacticTeaDesignatum.meDrinkingTea :=
  teaCausal.certify TeaCauses.bigBang_earth

theorem vesperEarthTea_not_before :
    ¬ teaDirection.Before
      GalacticTeaDesignatum.someoneDrinkingTea
        GalacticTeaDesignatum.meDrinkingTea := by
  intro h
  change Relation.TransGen TeaBefore
    GalacticTeaDesignatum.someoneDrinkingTea
      GalacticTeaDesignatum.meDrinkingTea at h
  exact Nat.lt_irrefl 1
    (Directed.rank_lt_of_transGen
      (base := TeaBefore) (rank := teaRank) teaBefore_rank_lt h)

theorem earthVesperTea_not_before :
    ¬ teaDirection.Before
      GalacticTeaDesignatum.meDrinkingTea
        GalacticTeaDesignatum.someoneDrinkingTea := by
  intro h
  change Relation.TransGen TeaBefore
    GalacticTeaDesignatum.meDrinkingTea
      GalacticTeaDesignatum.someoneDrinkingTea at h
  exact Nat.lt_irrefl 1
    (Directed.rank_lt_of_transGen
      (base := TeaBefore) (rank := teaRank) teaBefore_rank_lt h)

theorem vesperTea_not_before_bigBang :
    ¬ teaDirection.Before
      GalacticTeaDesignatum.someoneDrinkingTea
        GalacticTeaDesignatum.bigBang := by
  apply teaDirection.asymm
  change Relation.TransGen TeaBefore
    GalacticTeaDesignatum.bigBang
      GalacticTeaDesignatum.someoneDrinkingTea
  exact Relation.TransGen.single TeaBefore.bigBang_vesper

theorem earthTea_not_before_bigBang :
    ¬ teaDirection.Before GalacticTeaDesignatum.meDrinkingTea
      GalacticTeaDesignatum.bigBang := by
  apply teaDirection.asymm
  change Relation.TransGen TeaBefore
    GalacticTeaDesignatum.bigBang GalacticTeaDesignatum.meDrinkingTea
  exact Relation.TransGen.single TeaBefore.bigBang_earth

end GalacticTea
