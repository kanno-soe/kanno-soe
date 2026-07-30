/-
================================================================================
  KannoSoe.Doctrines.Ledger
  Productivity-ledger register, reception commands, and the purge face
================================================================================

This module records the checked face of the ledger case. The neutral machinery
states that landings inherit the call modality of the receiving function; the
case model then runs the Baizhang/Huichang shape without adding a new taxonomy
row or a state-sized being.

Reading and motivation: Identification/Commentary.lean, C.7.
-/

import KannoSoe.Consequences.Taxonomy

namespace KannoSoe

namespace Grid

variable {Designatum Contrib : Type} [PreorderBot Contrib]
variable (G : CoreReadings Designatum Contrib)

namespace DirectedConvention

open BeingConvention

/- ==============================================================================
   Function-side modality
============================================================================== -/

/-- A being mounts responses only at calls in a supplied modality. This is
    neutral function-side vocabulary: the modality is a predicate on calls, not
    a value judgement about the receiver. -/
def MountsOnlyIn (b : Designatum) (M : Designatum -> Prop) : Prop :=
  ∀ c r, G.respondsTo b c = some r -> M c

omit [PreorderBot Contrib] in
/-- An actual weld at a modality-restricted receiver carries a call in that
    modality. -/
theorem modality_of_actual
    {M : Designatum -> Prop} {w : G.Weld}
    (hM : MountsOnlyIn G w.agent M) (hactual : G.Actual w) :
    M w.call :=
  hM w.call w.response hactual

omit [PreorderBot Contrib] in
/-- Any landing at a modality-restricted receiver carries a call in that
    modality. -/
theorem landing_call_in_modality
    {M : Designatum -> Prop} {deed reception : G.Weld}
    (hM : MountsOnlyIn G reception.agent M)
    (hland : LandsAt G deed reception) :
    M reception.call :=
  modality_of_actual G hM hland.right

omit [PreorderBot Contrib] in
/-- A weld whose call lies outside the receiver's modality cannot be actual. -/
theorem not_actual_outside_modality
    {M : Designatum -> Prop} {w : G.Weld}
    (hM : MountsOnlyIn G w.agent M) (hout : ¬ M w.call) :
    ¬ G.Actual w :=
  fun hactual => hout (modality_of_actual G hM hactual)

omit [PreorderBot Contrib] in
/-- A reception whose call lies outside the receiver's modality cannot be a
    landing. -/
theorem no_landing_outside_modality
    {M : Designatum -> Prop} {deed reception : G.Weld}
    (hM : MountsOnlyIn G reception.agent M) (hout : ¬ M reception.call) :
    ¬ LandsAt G deed reception :=
  fun hland => hout (landing_call_in_modality G hM hland)

namespace BeingConvention

omit [PreorderBot Contrib] in
/-- If every fine tag under a macro tag shares a modality restriction, then any
    landing in that fiber carries a call in the same modality. -/
theorem fiber_landing_call_in_modality
    {Macro : Type} (κ : BeingCoarsening G Macro)
    {b : Macro} {M : Designatum -> Prop}
    (hfiberM : ∀ p : Designatum, κ.proj p = b -> MountsOnlyIn G p M)
    {deed reception : G.Weld}
    (hfiber : κ.InFiber b reception)
    (hland : LandsAt G deed reception) :
    M reception.call :=
  landing_call_in_modality G (hfiberM reception.agent hfiber) hland

end BeingConvention

end DirectedConvention

/- ==============================================================================
   Reception-command language
============================================================================== -/

/-- Claim object for a command that treats reception itself as commanded: this
    deed is asserted to land at that reception. -/
structure ReceptionCommand where
  deed      : G.Weld
  reception : G.Weld

/-- A tiny object language for reception-command claims. Such claims are
    satisfiable only where the field-side delivery reaches an actual reception. -/
def receptionCommandLanguage : ClaimLanguage G where
  Claim := ReceptionCommand G
  Holds
    | .floor, _ => False
    | .actTime _, claim =>
        DirectedConvention.LandsAt G claim.deed claim.reception

omit [PreorderBot Contrib] in
/-- A recorded reception-command utterance fits its offered tier only when the
    commanded reception actually lands. -/
theorem receptionCommand_unfit_of_no_landing
    (u : RecordedUtterance G (receptionCommandLanguage G))
    (hnot : ¬ DirectedConvention.LandsAt G u.content.deed u.content.reception) :
    ¬ u.FitsOfferedTier := by
  intro hfit
  change (receptionCommandLanguage G).TrueAt u.offeredAt u.content at hfit
  cases hoff : u.offeredAt with
  | floor =>
      rw [hoff] at hfit
      exact hfit.elim
  | actTime _ =>
      rw [hoff] at hfit
      dsimp [receptionCommandLanguage, ClaimLanguage.TrueAt] at hfit
      exact hnot hfit

namespace DirectedConvention
namespace BeingConvention
namespace GridConvention

/-- The ledger census face delegates to the existing per-call/global row. -/
theorem ledger_census_misfits_live_offer
    (u : RecordedUtterance G (rowLanguage G))
    (hcontent : u.content = .denied .perCallGlobal)
    (hlive : Tier.hasLiveShare G u.offeredAt) :
    ¬ u.FitsOfferedTier :=
  denied_misfits_live_offer G .perCallGlobal u hcontent hlive

/-- The ledger prognosis face delegates to the existing standing/dated row. -/
theorem ledger_prognosis_misfits_live_offer
    (u : RecordedUtterance G (rowLanguage G))
    (hcontent : u.content = .denied .standingDated)
    (hlive : Tier.hasLiveShare G u.offeredAt) :
    ¬ u.FitsOfferedTier :=
  denied_misfits_live_offer G .standingDated u hcontent hlive

end GridConvention
end BeingConvention
end DirectedConvention

end Grid

/- ==============================================================================
   Ledger case
============================================================================== -/

namespace LedgerCase

open Grid
open Grid.DirectedConvention
open Grid.DirectedConvention.BeingConvention

inductive Designatum
  | master
  | official
  | practitioner
  | economic
  | floor
  | decree
  | code
  | comply
  | display
  | codeOccurrence
  | officialComplyOccurrence
  | practitionerCodeOccurrence
  | decreeOccurrence
  | commandedOccurrence
deriving DecidableEq

namespace Being
abbrev master : Designatum := .master
abbrev official : Designatum := .official
abbrev practitioner : Designatum := .practitioner
end Being

namespace Call
abbrev economic : Designatum := .economic
abbrev floor : Designatum := .floor
abbrev decree : Designatum := .decree
end Call

namespace Response
abbrev code : Designatum := .code
abbrev comply : Designatum := .comply
abbrev display : Designatum := .display
end Response

/-- The economic modality: the one call class the official ledger can receive. -/
def economicModality : Designatum -> Prop
  | .economic => True
  | _ => False

def ledgerOccurrence : OccurrenceReading Designatum where
  occurrence d :=
    d = .codeOccurrence ∨ d = .officialComplyOccurrence ∨
      d = .practitionerCodeOccurrence ∨ d = .decreeOccurrence ∨
        d = .commandedOccurrence
  isBeing d := d = .master ∨ d = .official ∨ d = .practitioner
  isCall d := d = .economic ∨ d = .floor ∨ d = .decree
  isResponse d := d = .code ∨ d = .comply ∨ d = .display
  agent d :=
    match d with
    | .codeOccurrence | .decreeOccurrence => .master
    | .officialComplyOccurrence | .commandedOccurrence => .official
    | .practitionerCodeOccurrence => .practitioner
    | _ => d
  call d :=
    match d with
    | .codeOccurrence | .officialComplyOccurrence
    | .practitionerCodeOccurrence => .economic
    | .decreeOccurrence => .decree
    | .commandedOccurrence => .floor
    | _ => d
  response d :=
    match d with
    | .codeOccurrence | .practitionerCodeOccurrence => .code
    | .officialComplyOccurrence | .commandedOccurrence => .comply
    | .decreeOccurrence => .display
    | _ => d

/-- Three beings, three calls, three responses, constant live grade. Delivery
    reaches exactly receptions whose response is `code` or `comply`; actuality
    remains controlled by `respondsTo`. -/
def ledgerGrid : CoreReadings Designatum Nat where
  occurrence := ledgerOccurrence
  response := {
    respondsTo := fun b c =>
      match b, c with
      | .master, .economic => some .code
      | .master, .decree => some .display
      | .official, .economic => some .comply
      | .practitioner, .economic => some .code
      | _, _ => none
  }
  placement := { grade := fun _ => 1 }
  conditioning := {
    conditions := fun _ reception =>
      match reception with
      | .codeOccurrence | .officialComplyOccurrence
      | .practitionerCodeOccurrence | .commandedOccurrence => True
      | _ => False
  }

def codeWeld : ledgerGrid.Weld :=
  ⟨.codeOccurrence, Or.inl rfl⟩

def officialComplyWeld : ledgerGrid.Weld :=
  ⟨.officialComplyOccurrence, Or.inr (Or.inl rfl)⟩

def practitionerCodeWeld : ledgerGrid.Weld :=
  ⟨.practitionerCodeOccurrence, Or.inr (Or.inr (Or.inl rfl))⟩

def decreeWeld : ledgerGrid.Weld :=
  ⟨.decreeOccurrence, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩

def commandedReception : ledgerGrid.Weld :=
  ⟨.commandedOccurrence, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

theorem codeWeld_actual :
    ledgerGrid.Actual codeWeld :=
  rfl

theorem officialComplyWeld_actual :
    ledgerGrid.Actual officialComplyWeld :=
  rfl

theorem practitionerCodeWeld_actual :
    ledgerGrid.Actual practitionerCodeWeld :=
  rfl

theorem decreeWeld_actual :
    ledgerGrid.Actual decreeWeld :=
  rfl

theorem official_mountsOnlyIn_economic :
    MountsOnlyIn ledgerGrid Being.official economicModality := by
  intro c r h
  cases c <;> simp [ledgerGrid, economicModality] at h ⊢

theorem official_actualAgentInhabited :
    ledgerGrid.ActualAgentInhabited Being.official :=
  ⟨officialComplyWeld, officialComplyWeld_actual, rfl⟩

theorem official_landing_only_economic
    {deed reception : ledgerGrid.Weld}
    (hagent : reception.agent = Being.official)
    (hland : LandsAt ledgerGrid deed reception) :
    economicModality reception.call := by
  apply landing_call_in_modality ledgerGrid ?_ hland
  simpa [hagent] using official_mountsOnlyIn_economic

theorem floor_speech_never_lands_at_official
    {deed reception : ledgerGrid.Weld}
    (hagent : reception.agent = Being.official)
    (hcall : reception.call = Call.floor) :
    ¬ LandsAt ledgerGrid deed reception := by
  intro hland
  have hmod : economicModality reception.call :=
    official_landing_only_economic hagent hland
  rw [hcall] at hmod
  exact hmod

theorem code_lands_at_official :
    LandsAt ledgerGrid codeWeld officialComplyWeld :=
  ⟨True.intro, officialComplyWeld_actual⟩

theorem code_lands_at_practitioner :
    LandsAt ledgerGrid codeWeld practitionerCodeWeld :=
  ⟨True.intro, practitionerCodeWeld_actual⟩

theorem code_ruler_not_exempt :
    LandsAt ledgerGrid codeWeld codeWeld :=
  ⟨True.intro, codeWeld_actual⟩

theorem one_act_two_receivers :
    LandsAt ledgerGrid codeWeld officialComplyWeld ∧
      LandsAt ledgerGrid codeWeld practitionerCodeWeld :=
  ⟨code_lands_at_official, code_lands_at_practitioner⟩

inductive Sector
  | state
  | sangha
deriving DecidableEq

def sectorCoarsening : BeingCoarsening ledgerGrid Sector where
  proj p := if p = Being.official then Sector.state else Sector.sangha

def ledgerSentienceReading : ledgerGrid.SentienceReading :=
  Grid.SentienceReading.allSentient ledgerGrid

theorem state_tag_sentient :
    sectorCoarsening.SentientTag ledgerSentienceReading Sector.state :=
  ⟨officialComplyWeld, ⟨officialComplyWeld_actual, by
      change True
      exact True.intro⟩, rfl⟩

theorem state_fiber_shares_register :
    ∀ p : Designatum,
      sectorCoarsening.proj p = Sector.state ->
        MountsOnlyIn ledgerGrid p economicModality := by
  intro p hp
  cases p <;> simp [sectorCoarsening] at hp
  exact official_mountsOnlyIn_economic

theorem state_fiber_landing_economic
    {deed reception : ledgerGrid.Weld}
    (hfiber : sectorCoarsening.InFiber Sector.state reception)
    (hland : LandsAt ledgerGrid deed reception) :
    economicModality reception.call :=
  fiber_landing_call_in_modality ledgerGrid sectorCoarsening
    state_fiber_shares_register hfiber hland

theorem commandedReception_delivered :
    Grid.DirectedConvention.DeliveredTo
      ledgerGrid decreeWeld commandedReception :=
  True.intro

theorem commandedReception_not_actual :
    ¬ ledgerGrid.Actual commandedReception := by
  intro h
  cases h

theorem commandedReception_not_lands :
    ¬ LandsAt ledgerGrid decreeWeld commandedReception :=
  fun hland => commandedReception_not_actual hland.right

def decreeUtterance :
    RecordedUtterance ledgerGrid (receptionCommandLanguage ledgerGrid) where
  weld      := decreeWeld
  actual    := decreeWeld_actual
  offeredAt := Tier.actTime decreeWeld
  content   := { deed := decreeWeld, reception := commandedReception }

theorem decree_utterance_not_fits :
    ¬ decreeUtterance.FitsOfferedTier :=
  receptionCommand_unfit_of_no_landing ledgerGrid
    decreeUtterance commandedReception_not_lands

/-- The decree can engineer the delivery line while failing to command the
    purported reception. -/
theorem decree_engineers_calls_not_receptions :
    Grid.DirectedConvention.DeliveredTo
        ledgerGrid decreeWeld commandedReception ∧
      ¬ ledgerGrid.Actual commandedReception ∧
        ¬ decreeUtterance.FitsOfferedTier :=
  ⟨commandedReception_delivered, commandedReception_not_actual,
    decree_utterance_not_fits⟩

end LedgerCase

end KannoSoe
