/-
================================================================================
  KannoSoe.Doctrines.Icchantika
  The icchantika as a declined foreclosure case
================================================================================

Reading and motivation: Identification/Commentary.lean, C.13.
-/

import KannoSoe.Doctrines.Sraddha

namespace KannoSoe

open Grid.DirectedConvention

variable {Designatum Contrib : Type} [PreorderBot Contrib]

/- ==============================================================================
   Icchantika typing
============================================================================== -/

/-- The icchantika read literally as a run-shape, not as a stored nature:
    an actual occurrence is supplied, and every actual response remains live
    at the self-pole index. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
def Icchantika (G : CoreReadings Designatum Contrib) (b : Designatum) : Prop :=
  G.ActualAgentInhabited b ∧
    ∀ w : G.Weld, G.Actual w → w.agent = b → G.HasSelfPoleIndex w

/-- An icchantika is the terminus's inverse on its mounted run: the mounted
    witness supplies a live self-pole index where terminus typing would force
    the pole-class. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
theorem icchantika_not_terminus
    {G : CoreReadings Designatum Contrib} {b : Designatum} (h : Icchantika G b) :
    ¬ G.Terminus b := by
  intro hterm
  rcases h.left with ⟨w, hactual, hagent⟩
  subst b
  exact h.right w hactual rfl
    (G.atBot_of_terminus_response hterm hactual)

/-- The honest negative fact: an icchantika cannot be seated as a fully
    enlightened agent on this run, because `KsmdEffectiveTerminus` includes
    terminus typing. This is not a verdict that the being cannot become buddha.
    Reading and motivation: `Identification/Commentary.lean`, C.13. -/
theorem not_ksmdEffectiveTerminus_of_icchantika
    {G : CoreReadings Designatum Contrib} {b : Designatum} (h : Icchantika G b) :
    ¬ KsmdEffectiveTerminus G b := by
  intro hfull
  exact icchantika_not_terminus (G := G) h hfull.left.right

/-- Receiver-side correction: whenever an actual reception is made by an
    icchantika and the prior tendency is live, the sraddha aversion antecedent
    is available. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
theorem aversionContext_of_icchantika_reception
    {G : CoreReadings Designatum Contrib} {before : Config Contrib} {b : Designatum}
    {reception : G.Weld}
    (hagent : reception.agent = b) (hic : Icchantika G b)
    (hactual : G.Actual reception) (hlive : ¬ AtBot before.tendency) :
    KsmdAversionContext G before reception := by
  refine
    { liveBefore := hlive
      clenchMismatch := ?_ }
  refine ⟨hactual, ?_⟩
  exact hic.right reception hactual hagent

/-- If a fully enlightened deliverer reaches an icchantika reception, the
    existing sraddha theorem supplies the share-drop landing: the icchantika is
    reachable as receiver even though it cannot be seated as the enlightened
    agent on its run. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
theorem icchantika_reachable
    {G : CoreReadings Designatum Contrib} {g b : Designatum} {before : Config Contrib}
    {deed reception : G.Weld}
    (hfaith : KsmdEffectiveTerminus G g)
    (hdeed : deed.agent = g)
    (hdel : Grid.DirectedConvention.DeliveredTo G deed reception)
    (hreceiver : reception.agent = b) (hic : Icchantika G b)
    (hactual : G.Actual reception) (hlive : ¬ AtBot before.tendency) :
    HasShareDropLanding G before deed :=
  ksmd_path_landing G hfaith hdeed hdel
    (aversionContext_of_icchantika_reception
      (G := G) hreceiver hic hactual hlive)

/- ==============================================================================
   Concrete non-foreclosure witness
============================================================================== -/

namespace IcchantikaCase

/-- The one designatum carrier for the declined foreclosure witness. -/
inductive CaseDesignatum
  | buddha
  | icchantika
  | call
  | response
  | buddhaOccurrence
  | icchantikaOccurrence
  deriving DecidableEq

def occurrenceReading : OccurrenceReading CaseDesignatum where
  occurrence
    | .buddhaOccurrence | .icchantikaOccurrence => True
    | _ => False
  isBeing
    | .buddha | .icchantika => True
    | _ => False
  isCall d := d = .call
  isResponse d := d = .response
  agent
    | .buddhaOccurrence => .buddha
    | .icchantikaOccurrence => .icchantika
    | d => d
  call
    | .buddhaOccurrence | .icchantikaOccurrence => .call
    | d => d
  response
    | .buddhaOccurrence | .icchantikaOccurrence => .response
    | d => d

/-- A concrete grid where the icchantika mounts a live response and a buddha
    deed is delivered to that response. -/
def grid : CoreReadings CaseDesignatum Nat where
  occurrence := occurrenceReading
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .buddha, .call | .icchantika, .call => some .response
      | _, _ => none
  }
  placement := {
    grade := fun d =>
      match d with
      | .icchantikaOccurrence => 1
      | _ => 0
  }
  conditioning := {
    conditions := fun deed reception =>
      deed = .buddhaOccurrence ∧ reception = .icchantikaOccurrence
  }

/-- A live prior tendency high enough for the icchantika reception itself to
    be a share-drop. -/
def liveBefore : Config Nat :=
  { tendency := 2 }

/-- The delivered buddha-side deed in the concrete witness. -/
def deed : grid.Weld :=
  ⟨.buddhaOccurrence, True.intro⟩

/-- The icchantika-side reception in the concrete witness. -/
def reception : grid.Weld :=
  ⟨.icchantikaOccurrence, True.intro⟩

/-- The prior tendency in the witness is live. -/
theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  dsimp [liveBefore, AtBot, shareBot]
  show ¬ (2 : Nat) ≤ 0
  decide

/-- The icchantika response is actual in the witness grid. -/
theorem reception_actual :
    grid.Actual reception :=
  rfl

/-- The buddha deed is actual in the witness grid. -/
theorem deed_actual :
    grid.Actual deed :=
  rfl

/-- The witness receiver satisfies the icchantika run-shape. -/
theorem receiver_icchantika :
    Icchantika grid CaseDesignatum.icchantika := by
  constructor
  · exact ⟨reception, reception_actual, rfl⟩
  · rintro ⟨d, hd⟩ _hactual hagent
    change occurrenceReading.occurrence d at hd
    change occurrenceReading.agent d = CaseDesignatum.icchantika at hagent
    change ¬ AtBot (grid.placement.grade d)
    cases d with
    | buddha =>
        change False at hd
        contradiction
    | icchantika =>
        change False at hd
        contradiction
    | call =>
        change False at hd
        contradiction
    | response =>
        change False at hd
        contradiction
    | buddhaOccurrence =>
        change CaseDesignatum.buddha = CaseDesignatum.icchantika at hagent
        contradiction
    | icchantikaOccurrence =>
        change ¬ (1 : Nat) ≤ 0
        decide

/-- The buddha deed is delivered to the icchantika reception. -/
theorem delivered :
    Grid.DirectedConvention.DeliveredTo grid deed reception :=
  ⟨rfl, rfl⟩

/-- The icchantika reception is itself a share-drop from the live prior
    tendency. -/
theorem reception_shareDrop :
    grid.IsShareDrop liveBefore reception := by
  dsimp [Grid.IsShareDrop, Grid.share, liveBefore, reception, grid]
  constructor
  · show (1 : Nat) ≤ 2
    decide
  · show ¬ (2 : Nat) ≤ 1
    decide

/-- The concrete icchantika receiver is constructible. -/
theorem constructible :
    ∃ b : CaseDesignatum, Icchantika grid b :=
  ⟨CaseDesignatum.icchantika, receiver_icchantika⟩

/-- The delivered icchantika reception lands as a share-drop in the concrete
    witness. -/
theorem landing :
    HasShareDropLanding grid liveBefore deed := by
  exact ⟨reception, ⟨⟨delivered, reception_actual⟩, reception_shareDrop⟩⟩

end IcchantikaCase

/-- Foreclosure is not recovered from the icchantika run: in a concrete grid an
    icchantika-typed receiver is actual, delivered to, and itself participates
    in a share-drop landing from a live prior tendency. Reading and motivation:
    `Identification/Commentary.lean`, C.13. -/
theorem icchantika_release_not_foreclosed :
    ∃ (before : Config Nat) (b : IcchantikaCase.CaseDesignatum)
      (deed reception : IcchantikaCase.grid.Weld),
      Icchantika IcchantikaCase.grid b ∧
        reception.agent = b ∧
          IcchantikaCase.grid.Actual reception ∧
            ¬ AtBot before.tendency ∧
              Grid.DirectedConvention.DeliveredTo
                  IcchantikaCase.grid deed reception ∧
                IcchantikaCase.grid.IsShareDrop before reception ∧
                  HasShareDropLanding IcchantikaCase.grid before deed := by
  refine ⟨IcchantikaCase.liveBefore, IcchantikaCase.CaseDesignatum.icchantika,
    IcchantikaCase.deed, IcchantikaCase.reception, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IcchantikaCase.receiver_icchantika
  · rfl
  · exact IcchantikaCase.reception_actual
  · exact IcchantikaCase.liveBefore_not_atBot
  · exact IcchantikaCase.delivered
  · exact IcchantikaCase.reception_shareDrop
  · exact IcchantikaCase.landing

end KannoSoe
