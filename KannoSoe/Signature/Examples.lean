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

inductive GalacticTeaCase where
  | bigBang
  | localTea
  | remoteTea
  deriving DecidableEq, Repr

open GalacticTeaCase

inductive TeaBefore : GalacticTeaCase → GalacticTeaCase → Prop where
  | bigBang_local : TeaBefore bigBang localTea
  | bigBang_remote : TeaBefore bigBang remoteTea

def teaRank : GalacticTeaCase → Nat
  | bigBang => 0
  | localTea => 1
  | remoteTea => 1

theorem teaBefore_rank_lt {x y : GalacticTeaCase} (h : TeaBefore x y) :
    teaRank x < teaRank y := by
  cases h <;> decide

def teaDirection : Directed GalacticTeaCase :=
  Directed.ofBaseRank TeaBefore teaRank teaBefore_rank_lt

inductive TeaCauses : GalacticTeaCase → GalacticTeaCase → Prop where
  | bigBang_local : TeaCauses bigBang localTea
  | bigBang_remote : TeaCauses bigBang remoteTea

def teaCausal : Causal GalacticTeaCase where
  toDirected := teaDirection
  Causes := TeaCauses
  causes_before := fun h => by
    cases h with
    | bigBang_local =>
        exact Relation.TransGen.single TeaBefore.bigBang_local
    | bigBang_remote =>
        exact Relation.TransGen.single TeaBefore.bigBang_remote

theorem localRemote_not_before :
    ¬ teaDirection.Before localTea remoteTea := by
  intro h
  change Relation.TransGen TeaBefore localTea remoteTea at h
  exact Nat.lt_irrefl 1
    (Directed.rank_lt_of_transGen
      (base := TeaBefore) (rank := teaRank) teaBefore_rank_lt h)

theorem remoteLocal_not_before :
    ¬ teaDirection.Before remoteTea localTea := by
  intro h
  change Relation.TransGen TeaBefore remoteTea localTea at h
  exact Nat.lt_irrefl 1
    (Directed.rank_lt_of_transGen
      (base := TeaBefore) (rank := teaRank) teaBefore_rank_lt h)

theorem tea_not_before_bigBang :
    ¬ teaDirection.Before localTea bigBang := by
  apply teaDirection.asymm
  change Relation.TransGen TeaBefore bigBang localTea
  exact Relation.TransGen.single TeaBefore.bigBang_local

end GalacticTea
