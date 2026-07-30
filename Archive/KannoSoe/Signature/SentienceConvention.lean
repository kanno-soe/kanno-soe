/-
================================================================================
  KannoSoe.Signature.SentienceConvention
  Supplied sentience readings over occurrence designata
================================================================================
-/

import KannoSoe.Signature.Grid

namespace KannoSoe

universe u v

namespace Grid

variable {Designatum : Type u} {Contrib : Type v}
variable [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

/-- Compatibility specialization of the independent sentience reading. -/
abbrev SentienceReading (_G : CoreReadings Designatum Contrib) :=
  KannoSoe.SentienceReading Designatum

namespace SentienceReading

variable {G : CoreReadings Designatum Contrib}

def allSentient (G : CoreReadings Designatum Contrib) :
    SentienceReading G :=
  KannoSoe.SentienceReading.allSentient Designatum

def allInsentient (G : CoreReadings Designatum Contrib) :
    SentienceReading G :=
  KannoSoe.SentienceReading.allInsentient Designatum

/-- Conditioning transposition does not alter sentience. -/
def transpose (S : SentienceReading G) :
    SentienceReading (Grid.transpose G) :=
  S

omit [PreorderBot Contrib] in
@[simp]
theorem transpose_sentient
    (S : SentienceReading G) (w : Grid.Weld G) :
    S.transpose.sentient w.1 ↔ S.sentient w.1 :=
  Iff.rfl

end SentienceReading

def SentientAct (S : SentienceReading G) (w : Weld G) : Prop :=
  KannoSoe.SentientAct G.occurrence G.response S w

def InsentientAct (S : SentienceReading G) (w : Weld G) : Prop :=
  KannoSoe.InsentientAct G.occurrence G.response S w

def OrdinaryAct (S : SentienceReading G) (w : Weld G) : Prop :=
  KannoSoe.OrdinaryAct G.occurrence G.response G.placement S w

def TerminusAct (S : SentienceReading G) (w : Weld G) : Prop :=
  KannoSoe.TerminusAct G.occurrence G.response G.placement S w

def InsentientAppropriation
    (S : SentienceReading G) (w : Weld G) : Prop :=
  KannoSoe.InsentientAppropriation G.occurrence G.response G.placement S w

def StoneAct (S : SentienceReading G) (w : Weld G) : Prop :=
  KannoSoe.StoneAct G.occurrence G.response G.placement S w

omit [PreorderBot Contrib] in
theorem actual_of_sentientAct
    {S : SentienceReading G} {w : Weld G}
    (h : SentientAct G S w) :
    Actual G w :=
  h.left

omit [PreorderBot Contrib] in
theorem actual_of_insentientAct
    {S : SentienceReading G} {w : Weld G}
    (h : InsentientAct G S w) :
    Actual G w :=
  h.left

omit [PreorderBot Contrib] in
theorem not_insentientAct_of_sentientAct
    {S : SentienceReading G} {w : Weld G}
    (h : SentientAct G S w) :
    ¬ InsentientAct G S w :=
  fun hi => hi.right h.right

omit [PreorderBot Contrib] in
theorem not_sentientAct_of_insentientAct
    {S : SentienceReading G} {w : Weld G}
    (h : InsentientAct G S w) :
    ¬ SentientAct G S w :=
  fun hs => h.right hs.right

theorem actual_act_fourfold
    (S : SentienceReading G) (w : Weld G)
    [Decidable (S.sentient w.1)]
    [Decidable (AtBot (share G w))]
    (hactual : Actual G w) :
    OrdinaryAct G S w ∨ TerminusAct G S w ∨
      InsentientAppropriation G S w ∨ StoneAct G S w := by
  by_cases hsentient : S.sentient w.1
  · by_cases hpole : AtBot (share G w)
    · exact Or.inr (Or.inl ⟨⟨hactual, hsentient⟩, hpole⟩)
    · exact Or.inl ⟨⟨hactual, hsentient⟩, hpole⟩
  · by_cases hpole : AtBot (share G w)
    · exact Or.inr (Or.inr (Or.inr ⟨⟨hactual, hsentient⟩, hpole⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨⟨hactual, hsentient⟩, hpole⟩))

/-- The non-sentience readings visible to a would-be recovery function. -/
abbrev SentienceGridData
    (_G : CoreReadings Designatum Contrib) : Type (max u v) :=
  RespondsToReading Designatum ×
    PlacementReading Designatum Contrib ×
      ConditionsReading Designatum

def sentienceGridData : SentienceGridData G :=
  (G.response, G.placement, G.conditioning)

omit [PreorderBot Contrib] in
theorem actual_weld_readings_split
    (w : Weld G) (hactual : Actual G w) :
    SentientAct G (SentienceReading.allSentient G) w ∧
      InsentientAct G (SentienceReading.allInsentient G) w :=
  ⟨⟨hactual, True.intro⟩, ⟨hactual, fun h => h⟩⟩

omit [PreorderBot Contrib] in
theorem no_sentience_recovery
    (w : Weld G) (hactual : Actual G w) :
    ¬ ∃ recover : SentienceGridData G → Weld G → Prop,
      recover (sentienceGridData G) =
          SentientAct G (SentienceReading.allSentient G) ∧
        recover (sentienceGridData G) =
          SentientAct G (SentienceReading.allInsentient G) := by
  rintro ⟨recover, hall, hnone⟩
  have hsplit := actual_weld_readings_split G w hactual
  have htrue : recover (sentienceGridData G) w := by
    rw [hall]
    exact hsplit.left
  have hfalse : ¬ recover (sentienceGridData G) w := by
    rw [hnone]
    exact not_sentientAct_of_insentientAct G hsplit.right
  exact hfalse htrue

end Grid

namespace CoreReadings

variable {Designatum : Type u} {Contrib : Type v}
variable [PreorderBot Contrib]

abbrev SentienceReading (G : CoreReadings Designatum Contrib) :=
  Grid.SentienceReading G
abbrev SentientAct (G : CoreReadings Designatum Contrib) :=
  Grid.SentientAct G
abbrev InsentientAct (G : CoreReadings Designatum Contrib) :=
  Grid.InsentientAct G
abbrev OrdinaryAct (G : CoreReadings Designatum Contrib) :=
  Grid.OrdinaryAct G
abbrev TerminusAct (G : CoreReadings Designatum Contrib) :=
  Grid.TerminusAct G
abbrev InsentientAppropriation (G : CoreReadings Designatum Contrib) :=
  Grid.InsentientAppropriation G
abbrev StoneAct (G : CoreReadings Designatum Contrib) :=
  Grid.StoneAct G
abbrev actual_of_sentientAct
    (G : CoreReadings Designatum Contrib)
    {S : G.SentienceReading} {w : G.Weld}
    (h : G.SentientAct S w) :=
  Grid.actual_of_sentientAct G h
abbrev actual_of_insentientAct
    (G : CoreReadings Designatum Contrib)
    {S : G.SentienceReading} {w : G.Weld}
    (h : G.InsentientAct S w) :=
  Grid.actual_of_insentientAct G h
abbrev not_insentientAct_of_sentientAct
    (G : CoreReadings Designatum Contrib)
    {S : G.SentienceReading} {w : G.Weld}
    (h : G.SentientAct S w) :=
  Grid.not_insentientAct_of_sentientAct G h
abbrev not_sentientAct_of_insentientAct
    (G : CoreReadings Designatum Contrib)
    {S : G.SentienceReading} {w : G.Weld}
    (h : G.InsentientAct S w) :=
  Grid.not_sentientAct_of_insentientAct G h
abbrev actual_act_fourfold (G : CoreReadings Designatum Contrib) :=
  Grid.actual_act_fourfold G
abbrev SentienceGridData (G : CoreReadings Designatum Contrib) :=
  Grid.SentienceGridData G
abbrev sentienceGridData (G : CoreReadings Designatum Contrib) :=
  Grid.sentienceGridData G
abbrev actual_weld_readings_split
    (G : CoreReadings Designatum Contrib) :=
  Grid.actual_weld_readings_split G
abbrev no_sentience_recovery (G : CoreReadings Designatum Contrib) :=
  Grid.no_sentience_recovery G

end CoreReadings

end KannoSoe
