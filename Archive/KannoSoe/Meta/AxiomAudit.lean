import Lean
import KannoSoe.Meta.Invariance
import KannoSoe.Meta.InvarianceNegative
import KannoSoe.Meta.ReflexivityWitness
import KannoSoe.Meta.VerdictLedger
import KannoSoe.Consequences.ModelWitnesses
import KannoSoe.Doctrines.SraddhaNegative
import KannoSoe.Doctrines.FaithNegative
import KannoSoe.Doctrines.Deliberation
import KannoSoe.Doctrines.Ledger
import KannoSoe.Doctrines.CorrelationsNegative
import KannoSoe.Doctrines.FettersNegative
import KannoSoe.Doctrines.FactorsNegative
import KannoSoe.Doctrines.EffectiveTerminusNegative
import KannoSoe.Doctrines.Shusho

namespace KannoSoe

/-- One declaration and the exact set of axioms it is permitted to use. -/
structure AxiomAuditEntry where
  name : Lean.Name
  allowed : List Lean.Name := []
deriving Repr

/-- The single source of truth for the project's axiom audit. -/
def axiomAuditLedger : List AxiomAuditEntry := [
  { name := ``Grid.no_agent_recovery_of_field_collision },
  { name := ``Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick },
  { name := ``Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton },
  { name := ``Grid.relabel_rePitch },
  { name := ``Grid.no_natural_agent_recovery_from_config,
    allowed := [``propext, ``Quot.sound] },
  { name := ``ConfigLeakWitness.registerClock_config_recovers_agent,
    allowed := [``propext] },
  { name := ``ConfigLeakWitness.no_agent_recovery_from_config_of_share_collision,
    allowed := [``propext] },
  { name := ``strict_asymm },
  { name := ``strict_trans },
  { name := ``Grid.transpose_transpose },
  { name := ``DirectionNegative.no_direction_recovery_from_conditionsEither,
    allowed := [``propext, ``Quot.sound] },
  { name := ``CoverageNegative.directionVoid_needs_coverage },
  { name := ``CoverageNegative.ksmdEffectiveTerminus_needs_coverage,
    allowed := [``propext] },
  { name := ``Grid.stateToolFits_iff_atBot },
  { name := ``Grid.map_actual_iff },
  { name := ``Grid.map_isShareDrop_iff },
  { name := ``Grid.map_transpose },
  { name := ``Grid.actual_weld_readings_split },
  { name := ``Grid.no_sentience_recovery },
  { name := ``sentience_share_square_inhabited, allowed := [``propext] },
  { name := ``Grid.DirectedConvention.DirectionCoarsening.mapDir_resolutionBounded_iff },
  { name := ``DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit },
  { name := ``DirectionCoarseningWitness.twoResolution_directionCoarsening_independence },
  { name := ``DirectionCoarseningWitness.registerClock_directionCoarsening_independence,
    allowed := [``propext] },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_not_fused_of_nonlive_denial },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_not_obeys_of_nonlive_denial },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_obeys_of_no_occurrences },
  { name := ``ContentNegative.contentBeingsRow_not_obeys_hypothetical,
    allowed := [``propext] },
  { name := ``ContentNegative.contentGridLensRow_not_obeys_hypothetical,
    allowed := [``propext] },
  { name := ``ContentNegative.contentWeldRow_not_obeys_hypothetical,
    allowed := [``propext] },
  { name := ``ContentNegative.contentIntraWeldArrowRow_not_obeys_fixedResponse,
    allowed := [``propext] },
  { name := ``ContentNegative.contentBeforeAfterRow_not_obeys_twoBottom },
  { name := ``Grid.DirectedConvention.map_landsWithShareDrop_iff },
  { name := ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff },
  { name := ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_fiberAtPoleOn_iff },
  { name := ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber },
  { name := ``Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne },
  { name := ``Grid.map_ksmdBullSeven_iff },
  { name := ``Grid.map_ksmdBullTen_iff },
  { name := ``Grid.bullSeven_not_bullEight },
  { name := ``Grid.bullTen_to_bullNine },
  { name := ``CorrelationsNegative.pratyekabuddha_countermodel,
    allowed := [``propext] },
  { name := ``CorrelationsNegative.no_stage_boundary_recovery,
    allowed := [``propext] },
  { name := ``Grid.classQuiet_no_clench_in_class },
  { name := ``Fetter.kind_lower_iff_cut_by_nonReturn },
  { name := ``Grid.arhatPathQuiet_iff_quietOn_univ },
  { name := ``Grid.terminus_iff_quietOn_univ },
  { name := ``Grid.atPoleClass_iff_quietOn_univ },
  { name := ``Grid.all_fetters_cut_at_arhat },
  { name := ``Grid.identityView_cut_iff_noDefiledVoicing },
  { name := ``Grid.conceit_excluded_of_quietOn },
  { name := ``Grid.ksmdIrreversibleRegime_conditional },
  { name := ``Grid.lower_fetters_covered_by_rites_view_resolve },
  { name := ``Grid.ksmdStreamWinner_iff_streamEntry_cutClasses },
  { name := ``Grid.ksmdNonReturner_iff_nonReturn_cut },
  { name := ``Grid.ksmdSerialFactorRegime_conditional },
  { name := ``Grid.ksmdOnceReturner_attenuation_witness, allowed := [``propext] },
  { name := ``FactorsNegative.no_hold_conceit_boundary_recovery,
    allowed := [``propext] },
  { name := ``FactorsNegative.factor_order_underdetermined, allowed := [``propext] },
  { name := ``FettersNegative.seen_run_underdetermines_fetterCut, allowed := [``propext] },
  { name := ``Grid.DirectedConvention.ksmdPathOught_conditional },
  { name := ``Grid.DirectedConvention.ksmdFaithOught_conditional },
  { name := ``Grid.DirectedConvention.ksmd_says_true_of_faith },
  { name := ``Grid.DirectedConvention.noDelusion_of_noNescience_of_terminus },
  { name := ``Grid.DirectedConvention.ksmdFullyEnlightened_of_fullyEnlightenedEnacted },
  { name := ``FaithNegative.noNescience_strictly_stronger_witness,
    allowed := [``propext] },
  { name := ``FaithNegative.aklishta_ajnana_witness,
    allowed := [``propext] },
  { name := ``FaithNegative.arhat_retains_nescience_witness,
    allowed := [``propext] },
  { name := ``FaithNegative.Sealed.silent_buddha_models,
    allowed := [``propext] },
  { name := ``Grid.DirectedConvention.no_ksmd_path_at_pole },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.pole_validates_all_claims },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.denied_misfits_live_offer },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys_iff_errorFree },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.reEmptied_obeys_of_errorFree },
  { name := ``rung_not_pole_witness, allowed := [``propext] },
  { name := ``standing_does_not_determine_dated, allowed := [``propext] },
  { name := ``Grid.DirectedConvention.map_ksmdAversionContext_iff },
  { name := ``OrthogonalityNegative.ksmdEffectiveTerminus_stronger_than_terminus,
    allowed := [``propext] },
  { name := ``MisFeedNegative.fence_and_gate, allowed := [``propext] },
  { name := ``misFeed_entries_carry_decomposition },
  { name := ``Grid.grade_independent_of_conditions },
  { name := ``Grid.rePitch_forgets },
  { name := ``Grid.respondsToEveryCall_of_no_call },
  { name := ``Grid.DirectedConvention.PrudentialPrivilegeNegative.prudentialPrivilege_failure_modes,
    allowed := [``propext] },
  { name := ``Grid.ConsequentialistConvention.dropCountInFiber_le_dropCount,
    allowed := [``propext] },
  { name := ``Grid.ConsequentialistConvention.dropCount_eq_sum_dropCountInFiber,
    allowed := [``propext] },
  { name := ``Grid.ConsequentialistConvention.map_dropCountInFiberSum,
    allowed := [``propext] },
  { name := ``ObjectiveNegative.split_dropCount_sum_eq_mergedDropCount,
    allowed := [``propext] },
  { name := ``ObjectiveNegative.no_grid_data_objective_for_my_drops,
    allowed := [``propext] },
  { name := ``TransferNegative.adaptive_track_record_underdetermines_new_effect,
    allowed := [``propext] },
  { name := ``Grid.DirectedConvention.not_effectivenessEnacted_of_undelivered },
  { name := ``EffectiveTerminusNegative.no_effectiveTerminus_recovery_from_run,
    allowed := [``propext] },
  { name := ``DeliveryArrogationNegative.command_utterance_not_fits,
    allowed := [``propext] },
  { name := ``Grid.DirectedConvention.landing_call_in_modality },
  { name := ``LedgerCase.decree_engineers_calls_not_receptions, allowed := [``propext] },
  { name := ``LedgerCase.official_actualAgentInhabited, allowed := [``propext] },
  { name := ``InteriorDirectionNegative.transposeCR_involutive,
    allowed := [``propext] },
  { name := ``InteriorDirectionNegative.unorderedCRContent_transpose_invariant,
    allowed := [``propext] },
  { name := ``InteriorDirectionNegative.transpose_swaps_readings,
    allowed := [``propext] },
  { name := ``DoerDeedNegative.priority_readings_disagree },
  { name := ``DoerDeedNegative.no_priority_recovery },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_not_freeze },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.no_order_collapse_self_refuting },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_not_freeze },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.no_prior_doer_collapse_self_refuting },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_obeys_of_variation },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.contentIntraWeldArrowRow_obeys_of_variation },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.interior_order_denial_unfit_for_live_utterer },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys_succ },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_no_level_final },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys_succ },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_no_level_final },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.Metaphysics.intraWeldArrow_sunyata },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.Metaphysics.doerDeed_sunyata },
  { name := ``Grid.map_responseVariesWithCall_iff },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowRow_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedRow_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_contentIntraWeldArrowRow_obeys_of_variation },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys_succ },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_no_level_final },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys_succ },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_no_level_final },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_beings_sunyata,
    allowed := [``propext] },
  { name := ``Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_no_level_final,
    allowed := [``propext] }
]

open Lean Elab Command Meta

syntax (name := verifyAxiomAudit) "#verify_axiom_audit" : command

unsafe def evalAxiomAuditLedger : Term.TermElabM (List AxiomAuditEntry) := do
  evalExpr (List AxiomAuditEntry)
    (mkApp (mkConst ``List [Level.zero]) (mkConst ``AxiomAuditEntry))
    (mkConst ``axiomAuditLedger)

private def renderNames (names : List Lean.Name) : String :=
  "[" ++ String.intercalate ", " (names.map (fun name => name.toString)) ++ "]"

@[command_elab verifyAxiomAudit] unsafe def elabVerifyAxiomAudit : CommandElab :=
    fun _stx => do
  let entries <- liftTermElabM evalAxiomAuditLedger
  let env <- getEnv
  let mut failures : Array String := #[]
  for entry in entries do
    if !env.contains entry.name then
      failures := failures.push s!"{entry.name}: declaration is not in the environment"
    else
      let actual := (← Lean.collectAxioms entry.name).toList
      let unexpected := actual.filter (fun name => !entry.allowed.contains name)
      let absent := entry.allowed.filter (fun name => !actual.contains name)
      unless unexpected.isEmpty && absent.isEmpty do
        failures := failures.push
          s!"{entry.name}: unexpected {renderNames unexpected}; expected-but-absent {renderNames absent}; allowed {renderNames entry.allowed}; actual {renderNames actual}"
  unless failures.isEmpty do
    let details := failures.foldl (fun acc item => acc ++ "\n" ++ item) ""
    throwError m!"axiom audit failed:{details}"

#verify_axiom_audit

end KannoSoe
