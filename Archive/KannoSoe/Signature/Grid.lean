/-
================================================================================
  KannoSoe.Signature.Grid
  Compatibility namespace for independent readings
================================================================================

`Grid` is retained only as a namespace while the library migrates its public
vocabulary.  There is no `Grid` structure and no primitive agent/call/response
triple.  Concrete models package independent readings in `CoreReadings`; a weld
is the occurrence-reading-generated subtype.
-/

import KannoSoe.Signature.Readings

namespace KannoSoe

universe u v

/-- A carried contribution tendency.  It stores no occurrence or designatum. -/
@[ext]
structure Config (Contrib : Type v) where
  tendency : Contrib

namespace Grid

variable {Designatum : Type u} {Contrib : Type v}
variable [PreorderBot Contrib]

/- --------------------------------------------------------------------------
   Compatibility projections from a `CoreReadings` package
-------------------------------------------------------------------------- -/

/-- Occurrences selected by the package's occurrence reading. -/
abbrev Weld (G : CoreReadings Designatum Contrib) := G.occurrence.Weld

/-- The independently supplied response rule. -/
abbrev respondsTo (G : CoreReadings Designatum Contrib) :
    Designatum → Designatum → Option Designatum :=
  G.response.respondsTo

/-- Direct placement of a designatum in the contribution display. -/
abbrev grade (G : CoreReadings Designatum Contrib) :
    Designatum → Contrib :=
  G.placement.grade

/-- Conditioning restricted to occurrence designata for compatibility with
    the established theorem vocabulary. -/
def conditions (G : CoreReadings Designatum Contrib)
    (deed reception : Weld G) : Prop :=
  G.conditioning.conditions deed.1 reception.1

variable (G : CoreReadings Designatum Contrib)

/- --------------------------------------------------------------------------
   Actuality, placement, and self-pole vocabulary
-------------------------------------------------------------------------- -/

def Actual (w : Weld G) : Prop :=
  KannoSoe.Actual G.occurrence G.response w

def index (w : Weld G) : Designatum := w.agent

def share (w : Weld G) : Contrib :=
  KannoSoe.share G.occurrence G.placement w

def HasSelfPoleIndex (w : Weld G) : Prop := ¬ AtBot (share G w)

def selfPoleIndex (w : Weld G) (_h : HasSelfPoleIndex G w) : Designatum :=
  w.agent

theorem strict_shareBot_of_hasSelfPoleIndex (w : Weld G)
    (h : HasSelfPoleIndex G w) :
    Strict (shareBot : Contrib) (share G w) :=
  ⟨shareBot_le (share G w), h⟩

def KsmdAppropriates (reception : Weld G) : Prop :=
  HasSelfPoleIndex G reception

theorem no_self_pole_index_of_atBot (w : Weld G)
    (h : AtBot (share G w)) :
    ¬ HasSelfPoleIndex G w :=
  fun hidx => hidx h

theorem no_self_pole_index_of_eq_shareBot
    (w : Weld G) (h : share G w = shareBot) :
    ¬ HasSelfPoleIndex G w :=
  no_self_pole_index_of_atBot G w (atBot_of_eq_shareBot h)

theorem selfPoleIndex_eq_agent_of_hasSelfPoleIndex
    (w : Weld G) (h : HasSelfPoleIndex G w) :
    selfPoleIndex G w h = w.agent :=
  rfl

theorem not_ksmdAppropriates_of_atBot
    (w : Weld G) (h : AtBot (share G w)) :
    ¬ KsmdAppropriates G w :=
  no_self_pole_index_of_atBot G w h

theorem not_ksmdAppropriates_of_eq_shareBot
    (w : Weld G) (h : share G w = shareBot) :
    ¬ KsmdAppropriates G w :=
  not_ksmdAppropriates_of_atBot G w (atBot_of_eq_shareBot h)

omit [PreorderBot Contrib] in
theorem share_eq_grade_check (w : Weld G) :
    share G w = grade G w.1 :=
  rfl

/-- Constancy of placement over actual occurrences of one agent in a supplied
    call class.  The predicate now ranges over occurrence designata instead of
    hypothetical primitive triples. -/
def ProbeConstant (b : Designatum) (cs : Designatum → Prop) : Prop :=
  ∀ w₁ w₂ : Weld G,
    Actual G w₁ →
    Actual G w₂ →
    w₁.agent = b →
    w₂.agent = b →
    cs w₁.call →
    cs w₂.call →
    OrderEq (share G w₁) (share G w₂)

/- --------------------------------------------------------------------------
   Response and terminus vocabulary
-------------------------------------------------------------------------- -/

def MountsAt (b c : Designatum) : Prop :=
  KannoSoe.MountsAt G.response b c

/-- Every designatum marked as a call receives a response. -/
def RespondsToEveryCall (b : Designatum) : Prop :=
  ∀ c, G.occurrence.isCall c → MountsAt G b c

/-- Every actual occurrence by the designatum lies at the pole. -/
def Terminus (b : Designatum) : Prop :=
  ∀ w : Weld G, Actual G w → w.agent = b → AtBot (share G w)

def ActualAgentInhabited (b : Designatum) : Prop :=
  ∃ w : Weld G, Actual G w ∧ w.agent = b

def LiveTerminus (b : Designatum) : Prop :=
  ActualAgentInhabited G b ∧ Terminus G b

def ResponsiveTerminus (b : Designatum) : Prop :=
  RespondsToEveryCall G b ∧ Terminus G b

/-- Every selected occurrence by the designatum lies at the pole, whether or
    not the response reading makes that occurrence actual.  This is the
    explicit hypothetical counterpart to `Terminus`. -/
def HypotheticalTerminus (b : Designatum) : Prop :=
  ∀ w : Weld G, w.agent = b → AtBot (share G w)

/-- A selected occurrence realizes a response-rule triple when its three role
    faces are that agent, call, and response. -/
def OccurrenceRealizes (b c r : Designatum) : Prop :=
  ∃ w : Weld G, w.agent = b ∧ w.call = c ∧ w.response = r

theorem terminus_of_hypotheticalTerminus
    {b : Designatum} (h : HypotheticalTerminus G b) :
    Terminus G b :=
  fun w _hactual hagent => h w hagent

theorem atBot_of_terminus_response
    {w : Weld G}
    (hterm : Terminus G w.agent) (hactual : Actual G w) :
    AtBot (share G w) :=
  hterm w hactual rfl

theorem no_self_pole_index_of_terminus_response
    {w : Weld G}
    (hterm : Terminus G w.agent) (hactual : Actual G w) :
    ¬ HasSelfPoleIndex G w :=
  no_self_pole_index_of_atBot G w
    (atBot_of_terminus_response G hterm hactual)

theorem not_ksmdAppropriates_of_terminus_response
    {w : Weld G}
    (hterm : Terminus G w.agent) (hactual : Actual G w) :
    ¬ KsmdAppropriates G w :=
  not_ksmdAppropriates_of_atBot G w
    (atBot_of_terminus_response G hterm hactual)

def AtPoleClass (b : Designatum) : Prop := Terminus G b

/-- A responsive terminus is live once an actual occurrence by it is supplied. -/
theorem responsiveTerminus_live_of_actual
    (b : Designatum) (h : ResponsiveTerminus G b)
    (w : Weld G) (hactual : Actual G w) (hagent : w.agent = b) :
    LiveTerminus G b :=
  ⟨⟨w, hactual, hagent⟩, h.right⟩

/-- A call makes a responsive terminus live only when response-rule outputs
    are explicitly realized by selected occurrences.  `RespondsToEveryCall`
    supplies the output; `hrealize` supplies the occurrence token. -/
theorem responsiveTerminus_live_of_call
    (b c : Designatum) (h : ResponsiveTerminus G b)
    (hcall : G.occurrence.isCall c)
    (hrealize : ∀ r, G.response.respondsTo b c = some r →
      OccurrenceRealizes G b c r) :
    LiveTerminus G b := by
  rcases h.left c hcall with ⟨r, hresponse⟩
  rcases hrealize r hresponse with ⟨w, hagent, hwcall, hwresponse⟩
  apply responsiveTerminus_live_of_actual G b h w
  · unfold Actual KannoSoe.Actual
    rw [hagent, hwcall, hwresponse]
    exact hresponse
  · exact hagent

/- --------------------------------------------------------------------------
   Configuration and delivery structure
-------------------------------------------------------------------------- -/

def rePitch (_before : Config Contrib) (received : Weld G) :
    Config Contrib :=
  { tendency := share G received }

def IsShareDrop (before : Config Contrib) (received : Weld G) : Prop :=
  Strict (share G received) before.tendency

def ConditionsEither (w₁ w₂ : Weld G) : Prop :=
  conditions G w₁ w₂ ∨ conditions G w₂ w₁

omit [PreorderBot Contrib] in
theorem conditionsEither_symm
    {w₁ w₂ : Weld G} (h : ConditionsEither G w₁ w₂) :
    ConditionsEither G w₂ w₁ :=
  h.elim Or.inr Or.inl

inductive ConditionsEitherChain : Weld G → Weld G → Prop
  | refl (w : Weld G) : ConditionsEitherChain w w
  | step {w₁ w₂ w₃ : Weld G} :
      ConditionsEither G w₁ w₂ →
      ConditionsEitherChain w₂ w₃ →
      ConditionsEitherChain w₁ w₃

/-- Reverse only the independently supplied conditioning reading. -/
def transpose (G : CoreReadings Designatum Contrib) :
    CoreReadings Designatum Contrib where
  occurrence := G.occurrence
  response := G.response
  placement := G.placement
  conditioning := G.conditioning.transpose

omit [PreorderBot Contrib] in
theorem transpose_conditions (w₁ w₂ : Weld G) :
    conditions (transpose G) w₁ w₂ ↔ conditions G w₂ w₁ :=
  Iff.rfl

omit [PreorderBot Contrib] in
theorem transpose_transpose :
    transpose (transpose G) = G :=
  rfl

omit [PreorderBot Contrib] in
theorem transpose_conditionsEither_iff (w₁ w₂ : Weld G) :
    ConditionsEither (transpose G) w₁ w₂ ↔ ConditionsEither G w₁ w₂ :=
  ⟨fun h => h.elim Or.inr Or.inl,
   fun h => h.elim Or.inr Or.inl⟩

namespace DirectedConvention

abbrev TimeDirection {α : Type u} [Preorder α] (a b : α) : Prop :=
  Strict a b

theorem timeDirection_of_hasSelfPoleIndex
    (w : Weld G) (h : HasSelfPoleIndex G w) :
    TimeDirection (shareBot : Contrib) (share G w) :=
  strict_shareBot_of_hasSelfPoleIndex G w h

def KsmdReachBackFull (deed reception : Weld G) : Prop :=
  KannoSoe.DeliveredTo G.occurrence G.conditioning deed reception

def DeliveredTo (deed reception : Weld G) : Prop :=
  KannoSoe.DeliveredTo G.occurrence G.conditioning deed reception

def SameAgentDelivery (deed reception : Weld G) : Prop :=
  DeliveredTo G deed reception ∧ deed.agent = reception.agent

def CrossAgentDelivery (deed reception : Weld G) : Prop :=
  DeliveredTo G deed reception ∧ deed.agent ≠ reception.agent

omit [PreorderBot Contrib] in
theorem transpose_deliveredTo_iff (deed reception : Weld G) :
    DeliveredTo (transpose G) deed reception ↔ DeliveredTo G reception deed :=
  Iff.rfl

def NotDeliveredTo (deed reception : Weld G) : Prop :=
  ¬ conditions G deed reception

omit [PreorderBot Contrib] in
theorem deliveredTo_or_not (deed reception : Weld G)
    [hdec : Decidable (conditions G deed reception)] :
    DeliveredTo G deed reception ∨ NotDeliveredTo G deed reception :=
  match hdec with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr h

def LandsAt (deed reception : Weld G) : Prop :=
  DeliveredTo G deed reception ∧ Actual G reception

def ObjectAxisStanding (deed : Weld G) : Prop :=
  ∃ reception, DeliveredTo G deed reception

def LandsWithShareDrop
    (before : Config Contrib) (deed reception : Weld G) : Prop :=
  LandsAt G deed reception ∧ IsShareDrop G before reception

def HasShareDropLanding
    (before : Config Contrib) (deed : Weld G) : Prop :=
  ∃ reception, LandsWithShareDrop G before deed reception

def EnvironsLine (b : Designatum) (deed reception : Weld G) : Prop :=
  Actual G deed ∧ reception.agent = b ∧ conditions G deed reception

def ShareDropLine
    (before : Config Contrib) (b : Designatum)
    (deed reception : Weld G) : Prop :=
  EnvironsLine G b deed reception ∧ IsShareDrop G before reception

def KsmdAimedAt (deed reception : Weld G) : Prop :=
  DeliveredTo G deed reception

omit [PreorderBot Contrib] in
theorem deliveredTo_iff_ksmdReachBackFull (deed reception : Weld G) :
    DeliveredTo G deed reception ↔ KsmdReachBackFull G deed reception :=
  Iff.rfl

omit [PreorderBot Contrib] in
theorem objectAxisStanding_of_landsAt
    (deed reception : Weld G) (h : LandsAt G deed reception) :
    ObjectAxisStanding G deed :=
  ⟨reception, h.left⟩

theorem objectAxisStanding_of_hasShareDropLanding
    (before : Config Contrib) (deed : Weld G)
    (h : HasShareDropLanding G before deed) :
    ObjectAxisStanding G deed :=
  h.elim fun reception hland => ⟨reception, hland.left.left⟩

end DirectedConvention

/- --------------------------------------------------------------------------
   Response-shape vocabulary
-------------------------------------------------------------------------- -/

def ResponseInvariant (b : Designatum) : Prop :=
  ∀ c₁ c₂ r₁ r₂,
    respondsTo G b c₁ = some r₁ →
    respondsTo G b c₂ = some r₂ →
    r₁ = r₂

def ResponseVariesWithCall (b : Designatum) : Prop :=
  ∃ c₁ c₂ r₁ r₂,
    respondsTo G b c₁ = some r₁ ∧
    respondsTo G b c₂ = some r₂ ∧
    r₁ ≠ r₂

/- --------------------------------------------------------------------------
   Packaged actual occurrences and reception pairs
-------------------------------------------------------------------------- -/

structure ActualWeld (G : CoreReadings Designatum Contrib) where
  weld   : Weld G
  actual : Actual G weld

structure ReceptionPair (G : CoreReadings Designatum Contrib) where
  first  : ActualWeld G
  second : ActualWeld G

namespace ReceptionPair

def FirstConditionsSecond
    {G : CoreReadings Designatum Contrib} (p : ReceptionPair G) : Prop :=
  DirectedConvention.KsmdReachBackFull G p.first.weld p.second.weld

def rePitchSequence
    {G : CoreReadings Designatum Contrib}
    (before : Config Contrib) (p : ReceptionPair G) :
    Config Contrib × Config Contrib :=
  let afterFirst := rePitch G before p.first.weld
  (afterFirst, rePitch G afterFirst p.second.weld)

end ReceptionPair

/- --------------------------------------------------------------------------
   Field-residue underdetermination
-------------------------------------------------------------------------- -/

def fieldOf (w : Weld G) : Designatum × Designatum :=
  (w.call, w.response)

omit [PreorderBot Contrib] in
theorem no_agent_recovery_of_field_collision
    (w₁ w₂ : Weld G)
    (h₁ : Actual G w₁) (h₂ : Actual G w₂)
    (hfield : fieldOf G w₁ = fieldOf G w₂)
    (hne : w₁.agent ≠ w₂.agent) :
    ¬ ∃ recover : Designatum × Designatum → Designatum,
        ∀ w : Weld G,
          Actual G w → recover (fieldOf G w) = index G w := by
  rintro ⟨recover, hrec⟩
  apply hne
  calc
    w₁.agent = recover (fieldOf G w₁) := (hrec w₁ h₁).symm
    _ = recover (fieldOf G w₂) := congrArg recover hfield
    _ = w₂.agent := hrec w₂ h₂

end Grid

/- Field-notation bridge for packages.  The declarations themselves remain in
   the temporary `Grid` compatibility namespace, preserving established public
   names while `G.foo` continues to elaborate for a `CoreReadings` package. -/
namespace CoreReadings

variable {Designatum : Type u} {Contrib : Type v}
variable [PreorderBot Contrib]

abbrev Weld (G : CoreReadings Designatum Contrib) := Grid.Weld G
abbrev respondsTo (G : CoreReadings Designatum Contrib) := Grid.respondsTo G
abbrev grade (G : CoreReadings Designatum Contrib) := Grid.grade G
abbrev conditions (G : CoreReadings Designatum Contrib) := Grid.conditions G
abbrev Actual (G : CoreReadings Designatum Contrib) := Grid.Actual G
abbrev index (G : CoreReadings Designatum Contrib) := Grid.index G
abbrev share (G : CoreReadings Designatum Contrib) := Grid.share G
abbrev HasSelfPoleIndex (G : CoreReadings Designatum Contrib) :=
  Grid.HasSelfPoleIndex G
abbrev selfPoleIndex (G : CoreReadings Designatum Contrib) :=
  Grid.selfPoleIndex G
abbrev strict_shareBot_of_hasSelfPoleIndex
    (G : CoreReadings Designatum Contrib) :=
  Grid.strict_shareBot_of_hasSelfPoleIndex G
abbrev KsmdAppropriates (G : CoreReadings Designatum Contrib) :=
  Grid.KsmdAppropriates G
abbrev no_self_pole_index_of_atBot
    (G : CoreReadings Designatum Contrib) :=
  Grid.no_self_pole_index_of_atBot G
abbrev no_self_pole_index_of_eq_shareBot
    (G : CoreReadings Designatum Contrib) :=
  Grid.no_self_pole_index_of_eq_shareBot G
abbrev selfPoleIndex_eq_agent_of_hasSelfPoleIndex
    (G : CoreReadings Designatum Contrib) :=
  Grid.selfPoleIndex_eq_agent_of_hasSelfPoleIndex G
abbrev not_ksmdAppropriates_of_atBot
    (G : CoreReadings Designatum Contrib) :=
  Grid.not_ksmdAppropriates_of_atBot G
abbrev not_ksmdAppropriates_of_eq_shareBot
    (G : CoreReadings Designatum Contrib) :=
  Grid.not_ksmdAppropriates_of_eq_shareBot G
abbrev share_eq_grade_check (G : CoreReadings Designatum Contrib) :=
  Grid.share_eq_grade_check G
abbrev ProbeConstant (G : CoreReadings Designatum Contrib) :=
  Grid.ProbeConstant G
abbrev MountsAt (G : CoreReadings Designatum Contrib) := Grid.MountsAt G
abbrev RespondsToEveryCall (G : CoreReadings Designatum Contrib) :=
  Grid.RespondsToEveryCall G
abbrev Terminus (G : CoreReadings Designatum Contrib) := Grid.Terminus G
abbrev ActualAgentInhabited (G : CoreReadings Designatum Contrib) :=
  Grid.ActualAgentInhabited G
abbrev LiveTerminus (G : CoreReadings Designatum Contrib) :=
  Grid.LiveTerminus G
abbrev ResponsiveTerminus (G : CoreReadings Designatum Contrib) :=
  Grid.ResponsiveTerminus G
abbrev HypotheticalTerminus (G : CoreReadings Designatum Contrib) :=
  Grid.HypotheticalTerminus G
abbrev OccurrenceRealizes (G : CoreReadings Designatum Contrib) :=
  Grid.OccurrenceRealizes G
abbrev terminus_of_hypotheticalTerminus
    (G : CoreReadings Designatum Contrib) {b : Designatum}
    (h : G.HypotheticalTerminus b) :=
  Grid.terminus_of_hypotheticalTerminus G h
abbrev atBot_of_terminus_response
    (G : CoreReadings Designatum Contrib) {w : G.Weld}
    (hterm : G.Terminus w.agent) (hactual : G.Actual w) :=
  Grid.atBot_of_terminus_response G hterm hactual
abbrev no_self_pole_index_of_terminus_response
    (G : CoreReadings Designatum Contrib) {w : G.Weld}
    (hterm : G.Terminus w.agent) (hactual : G.Actual w) :=
  Grid.no_self_pole_index_of_terminus_response G hterm hactual
abbrev not_ksmdAppropriates_of_terminus_response
    (G : CoreReadings Designatum Contrib) {w : G.Weld}
    (hterm : G.Terminus w.agent) (hactual : G.Actual w) :=
  Grid.not_ksmdAppropriates_of_terminus_response G hterm hactual
abbrev AtPoleClass (G : CoreReadings Designatum Contrib) :=
  Grid.AtPoleClass G
abbrev responsiveTerminus_live_of_actual
    (G : CoreReadings Designatum Contrib) :=
  Grid.responsiveTerminus_live_of_actual G
abbrev responsiveTerminus_live_of_call
    (G : CoreReadings Designatum Contrib) :=
  Grid.responsiveTerminus_live_of_call G
abbrev rePitch (G : CoreReadings Designatum Contrib) := Grid.rePitch G
abbrev IsShareDrop (G : CoreReadings Designatum Contrib) :=
  Grid.IsShareDrop G
abbrev ConditionsEither (G : CoreReadings Designatum Contrib) :=
  Grid.ConditionsEither G
abbrev ConditionsEitherChain (G : CoreReadings Designatum Contrib) :=
  Grid.ConditionsEitherChain G
abbrev conditionsEither_symm
    (G : CoreReadings Designatum Contrib) {w₁ w₂ : G.Weld}
    (h : G.ConditionsEither w₁ w₂) :=
  Grid.conditionsEither_symm G h
abbrev transpose (G : CoreReadings Designatum Contrib) := Grid.transpose G
abbrev transpose_conditions (G : CoreReadings Designatum Contrib) :=
  Grid.transpose_conditions G
abbrev transpose_transpose (G : CoreReadings Designatum Contrib) :=
  Grid.transpose_transpose G
abbrev transpose_conditionsEither_iff
    (G : CoreReadings Designatum Contrib) :=
  Grid.transpose_conditionsEither_iff G
abbrev ResponseInvariant (G : CoreReadings Designatum Contrib) :=
  Grid.ResponseInvariant G
abbrev ResponseVariesWithCall (G : CoreReadings Designatum Contrib) :=
  Grid.ResponseVariesWithCall G
abbrev ActualWeld (G : CoreReadings Designatum Contrib) :=
  Grid.ActualWeld G
abbrev ReceptionPair (G : CoreReadings Designatum Contrib) :=
  Grid.ReceptionPair G
abbrev fieldOf (G : CoreReadings Designatum Contrib) := Grid.fieldOf G
abbrev no_agent_recovery_of_field_collision
    (G : CoreReadings Designatum Contrib) :=
  Grid.no_agent_recovery_of_field_collision G

end CoreReadings

end KannoSoe
