/-
================================================================================
  KannoSoe.Doctrines.Correlations
  Ten Bulls, Five Ranks, and stage-schemes as checked correlations
================================================================================

The doctrine vocabulary here is deliberately thin: named readings over existing
grid machinery, with the correlations stated as corollaries rather than new
axioms.
-/

import KannoSoe.Doctrines.Deliberation

namespace KannoSoe

namespace Grid

open DirectedConvention
open DirectedConvention.BeingConvention

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/- ==============================================================================
   Stage-schemes as coarsenings
============================================================================== -/

/-- A stage-scheme is a diagnosis-time coarsening of fine being tags. -/
abbrev StageScheme (Stage : Type) : Type :=
  BeingCoarsening G Stage

/-- The fifty-two-stage scheme, with no extra signature field. -/
abbrev FiftyTwoStageScheme : Type :=
  StageScheme G (Fin 52)

/-- The boundary relation read from a supplied coarsening. -/
abbrev CoarseningBoundary {Macro : Type} (κ : BeingCoarsening G Macro) :
    Designatum → Designatum → Prop :=
  κ.SameFiber

/- ==============================================================================
   Ten Bulls
============================================================================== -/

-- TODO(prose): verify Kuòān verse locus.

/-- The ten pictures, as data. The interpretation lives in the predicates
    below and the commentary. -/
inductive BullStage
  | seeking
  | footprints
  | glimpse
  | catching
  | taming
  | ridingHome
  | bullForgotten
  | bothForgotten
  | returningSource
  | marketplace

namespace BullStage

/-- Bulls 1-6 are the share-drop ascent portion of the sequence. -/
def ascentIndex : BullStage → Option Nat
  | .seeking => some 0
  | .footprints => some 1
  | .glimpse => some 2
  | .catching => some 3
  | .taming => some 4
  | .ridingHome => some 5
  | .bullForgotten
  | .bothForgotten
  | .returningSource
  | .marketplace => none

theorem seeking_ascentIndex : ascentIndex seeking = some 0 := rfl
theorem footprints_ascentIndex : ascentIndex footprints = some 1 := rfl
theorem glimpse_ascentIndex : ascentIndex glimpse = some 2 := rfl
theorem catching_ascentIndex : ascentIndex catching = some 3 := rfl
theorem taming_ascentIndex : ascentIndex taming = some 4 := rfl
theorem ridingHome_ascentIndex : ascentIndex ridingHome = some 5 := rfl

end BullStage

/-- A finite run in which every received weld is actual and drops the current
    carried share, after which the configuration is re-pitched to that weld. -/
inductive ShareDropRun : Config Contrib → List G.Weld → Prop
  | nil (before : Config Contrib) : ShareDropRun before []
  | cons {before : Config Contrib} {received : G.Weld} {rest : List G.Weld} :
      G.Actual received →
      G.IsShareDrop before received →
      ShareDropRun (G.rePitch before received) rest →
        ShareDropRun before (received :: rest)

/-- Bulls 1-6 as a run-fact: the climb is per-call and stores no altitude. -/
structure BullAscent where
  before : Config Contrib
  run    : List G.Weld
  drops  : ShareDropRun G before run

/-- Bull 7: probe-constancy with a live self-pole index still present. -/
def KsmdBullSeven (b : Designatum) : Prop :=
  G.ProbeConstant b (fun _ => True) ∧
    ∃ w : G.Weld, G.Actual w ∧ w.agent = b ∧ G.HasSelfPoleIndex w

/-- Bull 8: the empty circle as the pole-class.  The retired function-zero
    disjunct is absent; this is terminus typing. -/
abbrev KsmdBullEight (b : Designatum) : Prop :=
  G.AtPoleClass b

/-- Bull 9: return to source as call-entire terminus response. -/
abbrev KsmdBullNine (b : Designatum) : Prop :=
  G.ResponsiveTerminus b

/-- Bull 10: marketplace functioning through at least one delivery line into
    another sentient fiber. The existential reading is the modest picture-level
    claim; stronger universal delivery is a separate asymptote. -/
def KsmdBullTen {Macro : Type} (S : SentienceReading G)
    (κ : BeingCoarsening G Macro)
    (b : Designatum) : Prop :=
  G.ResponsiveTerminus b ∧
    ∃ deed reception : G.Weld,
      κ.InFiber (κ.proj b) deed ∧
      G.Actual reception ∧
      ¬ κ.SameFiber deed.agent reception.agent ∧
      κ.SentientTag S (κ.proj reception.agent) ∧
      DirectedConvention.DeliveredTo G deed reception

/-- The shelved stronger bodhisattva reading: delivery reaches every other
    sentient fiber. The source picture does not require this strength. -/
def StrongKsmdBullTen {Macro : Type} (S : SentienceReading G)
    (κ : BeingCoarsening G Macro)
    (b : Designatum) : Prop :=
  G.ResponsiveTerminus b ∧
    ∀ m : Macro,
      κ.SentientTag S m →
        m ≠ κ.proj b →
          ∃ deed reception : G.Weld,
            κ.InFiber (κ.proj b) deed ∧
            κ.InFiber m reception ∧
            G.Actual reception ∧
            DirectedConvention.DeliveredTo G deed reception

theorem bullSeven_not_terminus {b : Designatum}
    (h : KsmdBullSeven G b) :
    ¬ G.Terminus b := by
  intro hterm
  rcases h.right with ⟨w, hactual, hagent, hidx⟩
  rw [← hagent] at hterm
  exact hidx (G.atBot_of_terminus_response hterm hactual)

theorem bullSeven_not_bullEight {b : Designatum}
    (h : KsmdBullSeven G b) :
    ¬ KsmdBullEight G b := by
  exact bullSeven_not_terminus G h

theorem bullTen_to_bullNine {Macro : Type}
    {S : SentienceReading G} {κ : BeingCoarsening G Macro} {b : Designatum}
    (h : KsmdBullTen G S κ b) :
    KsmdBullNine G b :=
  h.left

theorem bullNine_to_terminus {b : Designatum}
    (h : KsmdBullNine G b) :
    G.Terminus b :=
  h.right

theorem terminus_to_bullEight {b : Designatum}
    (h : G.Terminus b) :
    KsmdBullEight G b :=
  h

theorem bullNine_to_bullEight {b : Designatum}
    (h : KsmdBullNine G b) :
    KsmdBullEight G b :=
  terminus_to_bullEight G h.right

theorem bullTen_to_bullEight {Macro : Type}
    {S : SentienceReading G} {κ : BeingCoarsening G Macro} {b : Designatum}
    (h : KsmdBullTen G S κ b) :
    KsmdBullEight G b :=
  bullNine_to_bullEight G h.left

/-- Bull 10 is explicitly reading-relative: under the constant-false
    sentience reading its marketplace destination cannot be inhabited. -/
theorem not_ksmdBullTen_allInsentient {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Designatum) :
    ¬ KsmdBullTen G (SentienceReading.allInsentient G) κ b := by
  rintro ⟨_hterm, deed, reception, _hdeed, _hactual, _hcross,
    hsentient, _hdel⟩
  exact κ.allInsentient_not_sentientTag (κ.proj reception.agent) hsentient

end Grid

/- ==============================================================================
   Five Ranks
============================================================================== -/

/-- Dongshan's Five Ranks as data. -/
inductive FiveRank
  | shoChuHen
  | henChuSho
  | shoChuRai
  | henChuShi
  | kenChuTo

/-- Thin reading labels for the ranks. -/
inductive RankReading
  | hostWithinGuest
  | guestWithinHost
  | comingFromHost
  | arrivingWithinGuest
  | marketplaceArrival

namespace FiveRank

def reading : FiveRank → RankReading
  | .shoChuHen => .hostWithinGuest
  | .henChuSho => .guestWithinHost
  | .shoChuRai => .comingFromHost
  | .henChuShi => .arrivingWithinGuest
  | .kenChuTo => .marketplaceArrival

theorem kenChuTo_reading :
    reading kenChuTo = RankReading.marketplaceArrival :=
  rfl

end FiveRank

namespace Grid

open DirectedConvention.BeingConvention

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/-- A minimal object-language for rank-diagnosis utterances. It records the
    rank named by an utterance without adding a new semantic row. -/
inductive RankClaim
  | says (r : FiveRank)

def rankLanguage : ClaimLanguage G where
  Claim := RankClaim
  Holds
    | .floor, _ => False
    | .actTime _, _ => True

abbrev RecordedRankUtterance : Type :=
  RecordedUtterance G (rankLanguage G)

/-- The 到 rank's checked shape: marketplace arrival is exactly the Bull 10
    delivery pattern under the supplied coarsening. -/
abbrev KenChuToShape {Macro : Type} (S : SentienceReading G)
    (κ : BeingCoarsening G Macro)
    (b : Designatum) : Prop :=
  KsmdBullTen G S κ b

theorem kenChuTo_implies_ksmdBullTen {Macro : Type}
    {S : SentienceReading G} {κ : BeingCoarsening G Macro} {b : Designatum}
    (h : KenChuToShape G S κ b) :
    KsmdBullTen G S κ b :=
  h

end Grid

namespace CoreReadings

variable {Designatum Contrib : Type} [PreorderBot Contrib]

abbrev StageScheme (G : CoreReadings Designatum Contrib) :=
  Grid.StageScheme G
abbrev FiftyTwoStageScheme (G : CoreReadings Designatum Contrib) :=
  Grid.FiftyTwoStageScheme G
abbrev KsmdBullSeven (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdBullSeven G
abbrev KsmdBullEight (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdBullEight G
abbrev KsmdBullNine (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdBullNine G
abbrev ShareDropRun (G : CoreReadings Designatum Contrib) :=
  Grid.ShareDropRun G
abbrev KsmdBullTen (G : CoreReadings Designatum Contrib)
    {Macro : Type} (S : Grid.SentienceReading G)
    (κ : Grid.DirectedConvention.BeingConvention.BeingCoarsening G Macro) :=
  Grid.KsmdBullTen G S κ
abbrev StrongKsmdBullTen (G : CoreReadings Designatum Contrib)
    {Macro : Type} (S : Grid.SentienceReading G)
    (κ : Grid.DirectedConvention.BeingConvention.BeingCoarsening G Macro) :=
  Grid.StrongKsmdBullTen G S κ
abbrev rankLanguage (G : CoreReadings Designatum Contrib) :=
  Grid.rankLanguage G
abbrev RecordedRankUtterance (G : CoreReadings Designatum Contrib) :=
  Grid.RecordedRankUtterance G
abbrev KenChuToShape (G : CoreReadings Designatum Contrib)
    {Macro : Type} (S : Grid.SentienceReading G)
    (κ : Grid.DirectedConvention.BeingConvention.BeingCoarsening G Macro) :=
  Grid.KenChuToShape G S κ

end CoreReadings

end KannoSoe
