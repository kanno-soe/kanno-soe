/-
================================================================================
  KannoSoe.Doctrines.FourTruths
  Checked four-truth-facing consequences in the grid's own vocabulary
================================================================================

This module separates the grid-derived clench mismatch from its supplied
phenomenal reading.  Mismatch covaries with share because it is read from the
same Row-2 display value; whether that mismatch is suffered is relative to a
`SentienceReading`.
-/

import KannoSoe.Consequences.Basic

namespace KannoSoe

namespace Grid

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/- ==============================================================================
   Truths 1-3: mismatch as a display reading
============================================================================== -/

/-- `KsmdMismatchGrade` is read from the same structure as share. This is
    covariation, not a second operational measure. -/
def KsmdMismatchGrade (w : G.Weld) : Contrib :=
  G.share w

omit [PreorderBot Contrib] in
@[simp]
theorem ksmdMismatchGrade_eq_share (w : G.Weld) :
    KsmdMismatchGrade G w = G.share w :=
  rfl

/-- Ordinal covariation: lowering share lowers mismatch grade in the same
    display order, because the two readings unfold to the same value. -/
theorem ksmdMismatchGrade_le_of_share_le {w₁ w₂ : G.Weld}
    (h : G.share w₁ ≼ G.share w₂) :
    KsmdMismatchGrade G w₁ ≼ KsmdMismatchGrade G w₂ :=
  h

/-- The structural content formerly carried by `KsmdMismatchLive`: an actual
    occurrence with a live self-pole index.  It is grid-statable for sentient
    and insentient acts alike. -/
def ClenchMismatch (w : G.Weld) : Prop :=
  G.Actual w ∧ G.HasSelfPoleIndex w

/-- Given occurrence actuality, clench mismatch is exactly the live self-pole
    index condition. -/
theorem clenchMismatch_iff_hasSelfPoleIndex
    {w : G.Weld} (hactual : G.Actual w) :
    ClenchMismatch G w ↔ G.HasSelfPoleIndex w := by
  constructor
  · intro h
    exact h.right
  · intro hidx
    exact ⟨hactual, hidx⟩

/-- Dukkha is the sentient reading of a structural clench mismatch.  The
    structure is derived; the suffering is supplied. -/
def KsmdDukkha (S : SentienceReading G) (w : G.Weld) : Prop :=
  S.sentient w ∧ ClenchMismatch G w

theorem clenchMismatch_of_ksmdDukkha
    {S : SentienceReading G} {w : G.Weld} (h : KsmdDukkha G S w) :
    ClenchMismatch G w :=
  h.right

theorem sentientAct_of_ksmdDukkha
    {S : SentienceReading G} {w : G.Weld} (h : KsmdDukkha G S w) :
    G.SentientAct S w :=
  ⟨h.right.left, h.left⟩

/-- Insentient appropriation carries the same structural mismatch without a
    dukkha reading. -/
theorem clenchMismatch_of_insentientAppropriation
    {S : SentienceReading G} {w : G.Weld}
    (h : G.InsentientAppropriation S w) :
    ClenchMismatch G w :=
  ⟨h.left.left, h.right⟩

theorem not_ksmdDukkha_of_insentientAct
    {S : SentienceReading G} {w : G.Weld}
    (h : G.InsentientAct S w) :
    ¬ KsmdDukkha G S w :=
  fun hdukkha => h.right hdukkha.left

/-- A terminus response has mismatch grade at the pole-class. -/
theorem ksmdMismatch_atBot_of_terminus_response
    {w : G.Weld}
    (hterm : G.Terminus w.agent) (hactual : G.Actual w) :
    AtBot (KsmdMismatchGrade G w) :=
  G.atBot_of_terminus_response hterm hactual

/-- A terminus response has no clench mismatch. -/
theorem not_clenchMismatch_of_terminus_response
    {w : G.Weld}
    (hterm : G.Terminus w.agent) (hactual : G.Actual w) :
    ¬ ClenchMismatch G w := by
  intro h
  exact h.right (ksmdMismatch_atBot_of_terminus_response G hterm hactual)

theorem not_ksmdDukkha_of_terminus_response
    (S : SentienceReading G)
    {w : G.Weld}
    (hterm : G.Terminus w.agent) (hactual : G.Actual w) :
    ¬ KsmdDukkha G S w :=
  fun h => not_clenchMismatch_of_terminus_response G hterm hactual h.right

end Grid

namespace CoreReadings

variable {Designatum Contrib : Type} [PreorderBot Contrib]

abbrev KsmdMismatchGrade (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdMismatchGrade G
abbrev ClenchMismatch (G : CoreReadings Designatum Contrib) :=
  Grid.ClenchMismatch G
abbrev KsmdDukkha (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdDukkha G
abbrev not_clenchMismatch_of_terminus_response
    (G : CoreReadings Designatum Contrib) {w : G.Weld}
    (hterm : G.Terminus w.agent) (hactual : G.Actual w) :=
  Grid.not_clenchMismatch_of_terminus_response G hterm hactual

end CoreReadings

end KannoSoe
