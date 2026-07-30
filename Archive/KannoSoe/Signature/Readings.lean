/-
================================================================================
  KannoSoe.Signature.Readings
  Independent readings over a common designatum carrier
================================================================================

This module is the draft-3c substrate.  A model supplies one carrier of
designata.  Occurrences are selected from that carrier, and their agent, call,
and response faces are readings of the occurrence designatum rather than
primitive carrier coordinates.  Actuality, placement, conditioning, and
sentience remain independent readings.
-/

import KannoSoe.Signature.Order

namespace KannoSoe

universe u v

variable {Designatum : Type u} {Contrib : Type v}

/-- The occurrence and role reading over a common carrier of designata. -/
@[ext]
structure OccurrenceReading (Designatum : Type u) where
  occurrence : Designatum → Prop

  isBeing    : Designatum → Prop
  isCall     : Designatum → Prop
  isResponse : Designatum → Prop

  agent    : Designatum → Designatum
  call     : Designatum → Designatum
  response : Designatum → Designatum

namespace OccurrenceReading

/-- A weld is a designatum selected by an occurrence reading. -/
abbrev Weld (O : OccurrenceReading Designatum) :=
  { d : Designatum // O.occurrence d }

/- `OccurrenceReading.Weld` is intentionally a subtype.  Field notation for a
   subtype is resolved through the root `Subtype` namespace, so these narrowly
   typed helpers make `w.agent`, `w.call`, and `w.response` available without
   turning weld back into a primitive record. -/
def _root_.Subtype.agent {Designatum : Type u}
    {O : OccurrenceReading Designatum} (w : O.Weld) : Designatum :=
  O.agent w.1

def _root_.Subtype.call {Designatum : Type u}
    {O : OccurrenceReading Designatum} (w : O.Weld) : Designatum :=
  O.call w.1

def _root_.Subtype.response {Designatum : Type u}
    {O : OccurrenceReading Designatum} (w : O.Weld) : Designatum :=
  O.response w.1

namespace Weld

variable {Designatum : Type u} {O : OccurrenceReading Designatum}

/-- The agent face read from an occurrence designatum. -/
def agent (w : O.Weld) : Designatum := O.agent w.1

/-- The call face read from an occurrence designatum. -/
def call (w : O.Weld) : Designatum := O.call w.1

/-- The response face read from an occurrence designatum. -/
def response (w : O.Weld) : Designatum := O.response w.1

@[simp]
theorem coe_mk (d : Designatum) (h : O.occurrence d) :
    ((⟨d, h⟩ : O.Weld) : Designatum) = d :=
  rfl

@[simp]
theorem agent_mk (d : Designatum) (h : O.occurrence d) :
    (⟨d, h⟩ : O.Weld).agent = O.agent d :=
  rfl

@[simp]
theorem call_mk (d : Designatum) (h : O.occurrence d) :
    (⟨d, h⟩ : O.Weld).call = O.call d :=
  rfl

@[simp]
theorem response_mk (d : Designatum) (h : O.occurrence d) :
    (⟨d, h⟩ : O.Weld).response = O.response d :=
  rfl

end Weld

/-- Swap the call and response readings while retaining the occurrence
    carrier, occurrence predicate, and agent reading. -/
def transposeCR (O : OccurrenceReading Designatum) :
    OccurrenceReading Designatum where
  occurrence := O.occurrence
  isBeing := O.isBeing
  isCall := O.isResponse
  isResponse := O.isCall
  agent := O.agent
  call := O.response
  response := O.call

@[simp]
theorem transposeCR_occurrence (O : OccurrenceReading Designatum)
    (d : Designatum) :
    O.transposeCR.occurrence d ↔ O.occurrence d :=
  Iff.rfl

@[simp]
theorem transposeCR_agent (O : OccurrenceReading Designatum)
    (d : Designatum) :
    O.transposeCR.agent d = O.agent d :=
  rfl

@[simp]
theorem transposeCR_call (O : OccurrenceReading Designatum)
    (d : Designatum) :
    O.transposeCR.call d = O.response d :=
  rfl

@[simp]
theorem transposeCR_response (O : OccurrenceReading Designatum)
    (d : Designatum) :
    O.transposeCR.response d = O.call d :=
  rfl

@[simp]
theorem transposeCR_transposeCR (O : OccurrenceReading Designatum) :
    O.transposeCR.transposeCR = O :=
  rfl

/-- Re-read a weld under call/response transposition.  The occurrence
    designatum itself is unchanged. -/
def Weld.transposeCR {O : OccurrenceReading Designatum} (w : O.Weld) :
    O.transposeCR.Weld :=
  ⟨w.1, w.2⟩

@[simp]
theorem Weld.transposeCR_agent {O : OccurrenceReading Designatum}
    (w : O.Weld) :
    w.transposeCR.agent = w.agent :=
  rfl

@[simp]
theorem Weld.transposeCR_call {O : OccurrenceReading Designatum}
    (w : O.Weld) :
    w.transposeCR.call = w.response :=
  rfl

@[simp]
theorem Weld.transposeCR_response {O : OccurrenceReading Designatum}
    (w : O.Weld) :
    w.transposeCR.response = w.call :=
  rfl

@[simp]
theorem Weld.transposeCR_transposeCR {O : OccurrenceReading Designatum}
    (w : O.Weld) :
    w.transposeCR.transposeCR = w :=
  rfl

end OccurrenceReading

/-- The supplied response rule.  `Option` keeps partial response semantics
    independent from the carrier migration. -/
@[ext]
structure RespondsToReading (Designatum : Type u) where
  respondsTo : Designatum → Designatum → Option Designatum

/-- A supplied placement of every designatum in the contribution display. -/
@[ext]
structure PlacementReading
    (Designatum : Type u) (Contrib : Type v) where
  grade : Designatum → Contrib

/-- A supplied conditioning relation between designata. -/
@[ext]
structure ConditionsReading (Designatum : Type u) where
  conditions : Designatum → Designatum → Prop

namespace ConditionsReading

/-- Reverse only the conditioning relation. -/
def transpose (C : ConditionsReading Designatum) :
    ConditionsReading Designatum where
  conditions d₁ d₂ := C.conditions d₂ d₁

@[simp]
theorem transpose_conditions (C : ConditionsReading Designatum)
    (d₁ d₂ : Designatum) :
    C.transpose.conditions d₁ d₂ ↔ C.conditions d₂ d₁ :=
  Iff.rfl

@[simp]
theorem transpose_transpose (C : ConditionsReading Designatum) :
    C.transpose.transpose = C :=
  rfl

end ConditionsReading

/-- A supplied sentience marking on designata.  Occurrence-level definitions
    apply it to the occurrence designatum itself. -/
@[ext]
structure SentienceReading (Designatum : Type u) where
  sentient : Designatum → Prop

namespace SentienceReading

def allSentient (Designatum : Type u) : SentienceReading Designatum where
  sentient _ := True

def allInsentient (Designatum : Type u) : SentienceReading Designatum where
  sentient _ := False

end SentienceReading

/-- A convenience package for concrete models.  The readings remain
    independently usable, and derived definitions below accept only their
    actual dependencies. -/
@[ext]
structure CoreReadings
    (Designatum : Type u) (Contrib : Type v) where
  occurrence   : OccurrenceReading Designatum
  response     : RespondsToReading Designatum
  placement    : PlacementReading Designatum Contrib
  conditioning : ConditionsReading Designatum

/- --------------------------------------------------------------------------
   Derived definitions with explanatory dependencies
-------------------------------------------------------------------------- -/

/-- An occurrence is actual when its response reading agrees with the
    occurrence's three role faces. -/
def Actual
    (O : OccurrenceReading Designatum)
    (R : RespondsToReading Designatum)
    (w : O.Weld) : Prop :=
  R.respondsTo w.agent w.call = some w.response

/-- The contribution assigned directly to an occurrence designatum. -/
def share
    (O : OccurrenceReading Designatum)
    (P : PlacementReading Designatum Contrib)
    (w : O.Weld) : Contrib :=
  P.grade w.1

/-- Whether a supplied response rule mounts some response at an agent/call
    pair. -/
def MountsAt
    (R : RespondsToReading Designatum)
    (b c : Designatum) : Prop :=
  ∃ r, R.respondsTo b c = some r

/-- Delivery supplied independently by a conditioning reading. -/
def DeliveredTo
    (O : OccurrenceReading Designatum)
    (C : ConditionsReading Designatum)
    (deed reception : O.Weld) : Prop :=
  C.conditions deed.1 reception.1

/-- An actual occurrence marked sentient by a supplied reading. -/
def SentientAct
    (O : OccurrenceReading Designatum)
    (R : RespondsToReading Designatum)
    (S : SentienceReading Designatum)
    (w : O.Weld) : Prop :=
  Actual O R w ∧ S.sentient w.1

/-- An actual occurrence not marked sentient by a supplied reading. -/
def InsentientAct
    (O : OccurrenceReading Designatum)
    (R : RespondsToReading Designatum)
    (S : SentienceReading Designatum)
    (w : O.Weld) : Prop :=
  Actual O R w ∧ ¬ S.sentient w.1

/-- The sentient, live-self-share cell of the act square. -/
def OrdinaryAct
    [PreorderBot Contrib]
    (O : OccurrenceReading Designatum)
    (R : RespondsToReading Designatum)
    (P : PlacementReading Designatum Contrib)
    (S : SentienceReading Designatum)
    (w : O.Weld) : Prop :=
  SentientAct O R S w ∧ ¬ AtBot (share O P w)

/-- The sentient, pole-share cell of the act square. -/
def TerminusAct
    [PreorderBot Contrib]
    (O : OccurrenceReading Designatum)
    (R : RespondsToReading Designatum)
    (P : PlacementReading Designatum Contrib)
    (S : SentienceReading Designatum)
    (w : O.Weld) : Prop :=
  SentientAct O R S w ∧ AtBot (share O P w)

/-- The insentient, live-self-share cell of the act square. -/
def InsentientAppropriation
    [PreorderBot Contrib]
    (O : OccurrenceReading Designatum)
    (R : RespondsToReading Designatum)
    (P : PlacementReading Designatum Contrib)
    (S : SentienceReading Designatum)
    (w : O.Weld) : Prop :=
  InsentientAct O R S w ∧ ¬ AtBot (share O P w)

/-- The insentient, pole-share cell of the act square. -/
def StoneAct
    [PreorderBot Contrib]
    (O : OccurrenceReading Designatum)
    (R : RespondsToReading Designatum)
    (P : PlacementReading Designatum Contrib)
    (S : SentienceReading Designatum)
    (w : O.Weld) : Prop :=
  InsentientAct O R S w ∧ AtBot (share O P w)

end KannoSoe
