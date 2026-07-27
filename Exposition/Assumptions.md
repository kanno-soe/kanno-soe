<!-- GENERATED from KannoSoe/Meta/AssumptionLedger.lean by `lake exe exposition_gen` - do not edit -->

# Assumptions

Generated from `KannoSoe/Meta/AssumptionLedger.lean` by `lake exe exposition_gen`. `KannoSoe/Meta/AxiomAudit.lean` holds the compile-checked axiom ledger; statement prose is canonical here.

## A. What Is Asserted

### A.1 No prior agent

A weld is an occurrence designatum selected by an `OccurrenceReading`. Its agent, call, and response are role-readings of that occurrence; `Grid.index` and `Grid.share` are derived projections, not fields recovered from a separate performer or act. `Grid.no_agent_recovery_of_field_collision` records the internal obstruction: the same call-response field residue can be produced by distinct actual agents.

**Checked anchors (Signature):** `KannoSoe.OccurrenceReading.Weld` (proof), `KannoSoe.OccurrenceReading.Weld.agent` (proof), `KannoSoe.OccurrenceReading.Weld.call` (proof), `KannoSoe.OccurrenceReading.Weld.response` (proof), `KannoSoe.Grid.index` (proof), `KannoSoe.Grid.share` (proof), `KannoSoe.Grid.no_agent_recovery_of_field_collision` (witness)

### A.2 Nothing self-indexed is stored

`Config` stores only `tendency : Contrib`. It has no owner, designatum, weld, or field-residue slot. `rePitch` uses the received weld's share and ignores the prior configuration value. The checked claim is architectural and definability-level: whole-carrier relabelling acts trivially on configurations and commutes with `rePitch`, and no relabelling-equivariant recovery of a designatum from a configuration exists. It is not an information-flow claim; see the declined entry below.

**Checked anchors (Signature):** `KannoSoe.Config` (proof), `KannoSoe.Config.tendency` (proof), `KannoSoe.Grid.rePitch` (proof)

**Downstream elaboration:** `KannoSoe.Equiv` (proof), `KannoSoe.Grid.relabel` (proof), `KannoSoe.Config.relabel_fixed` (proof), `KannoSoe.Grid.relabel_rePitch` (proof), `KannoSoe.Grid.no_natural_agent_recovery_from_config` (witness), `KannoSoe.ConfigLeakWitness.no_agent_recovery_from_config_of_share_collision` (witness)

### A.3 The self-pole index is just live share

`HasSelfPoleIndex w` is `not AtBot (share w)`, and when the predicate is live the carried `selfPoleIndex` is the weld's agent tag.

**Checked anchors (Signature):** `KannoSoe.Grid.HasSelfPoleIndex` (proof), `KannoSoe.Grid.selfPoleIndex_eq_agent_of_hasSelfPoleIndex` (proof), `KannoSoe.Grid.no_self_pole_index_of_atBot` (proof)

### A.4 Sentience is a supplied per-weld reading

A `SentienceReading` marks welds, not beings. Together with live or pole share it yields the four actual act-kinds `OrdinaryAct`, `TerminusAct`, `InsentientAppropriation`, and `StoneAct`; the checked square witnesses all four. `SentientTag`, `StoneTag`, and `Intermittent` are reading-relative quantified displays over those acts.

**Checked anchors (Signature):** `KannoSoe.Grid.SentienceReading` (proof), `KannoSoe.Grid.SentientAct` (proof), `KannoSoe.Grid.InsentientAct` (proof), `KannoSoe.Grid.OrdinaryAct` (proof), `KannoSoe.Grid.TerminusAct` (proof), `KannoSoe.Grid.InsentientAppropriation` (proof), `KannoSoe.Grid.StoneAct` (proof), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.SentientTag` (proof), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.StoneTag` (proof), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.Intermittent` (proof), `KannoSoe.sentience_share_square_inhabited` (witness)

### A.5 Call/response is universal per occurrence

Every actual weld is a mounted call/response occurrence. `respondsTo` remains `Option`-valued only to distinguish actual from hypothetical triples; `none` is not aggregated into a per-being doctrinal category. In Madhyamaka terms it marks non-arising, not a cessation or state entered by a being.

**Checked anchors (Signature):** `KannoSoe.Grid.Actual` (proof), `KannoSoe.Grid.MountsAt` (proof)

**Downstream elaboration:** `KannoSoe.Grid.mountsAt_iff_exists_actual` (proof)

### A.6 Self-lines are permitted, not built in

The bare signature does not impose irreflexivity on `conditions`; a model may supply reflexive delivery, and then the directed vocabulary can read a self-line.

**Checked anchors (Signature):** `KannoSoe.Grid.conditions` (proof), `KannoSoe.Grid.DirectedConvention.DeliveredTo` (proof), `KannoSoe.Grid.DirectedConvention.LandsAt` (proof), `KannoSoe.AssumptionLocalWitnesses.signature_self_line_permitted` (witness)

**Downstream elaboration:** `KannoSoe.SelfLineWitness.selfLine_landsAt_self` (witness), `KannoSoe.SelfLineWitness.selfLine_ksmdOwnershipFace_self` (witness)

### A.7 Dukkha and Bull 10 are reading-relative

`ClenchMismatch` and its share covariation are grid-derived. `KsmdDukkha` adds the supplied mark: the structure is derived, the suffering is supplied. Bull 10 likewise quantifies over `SentientTag` under a reading; with the constant-false reading its marketplace is empty and the predicate is unsatisfiable.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `KannoSoe.Grid.ClenchMismatch` (proof), `KannoSoe.Grid.KsmdDukkha` (proof), `KannoSoe.Grid.clenchMismatch_of_ksmdDukkha` (proof), `KannoSoe.Grid.KsmdBullTen` (proof), `KannoSoe.Grid.not_ksmdBullTen_allInsentient` (proof)

## B. What Is Deliberately Declined

### B.1 No arrow in `conditions`

The signature assumes no asymmetry, irreflexivity, or transitivity for `conditions`. `ConditionsEither` is the symmetric field fact; direction enters only in `Grid.DirectedConvention`. The downstream `DirectionNegative` witness elaborates this as non-recovery from symmetric closure.

**Checked anchors (Signature):** `KannoSoe.Grid.ConditionsEither` (proof), `KannoSoe.Grid.conditionsEither_symm` (proof), `KannoSoe.Grid.DirectedConvention.TimeDirection` (proof), `KannoSoe.Grid.transpose` (witness), `KannoSoe.Grid.transpose_conditionsEither_iff` (witness), `KannoSoe.Grid.DirectedConvention.transpose_deliveredTo_iff` (witness), `KannoSoe.OccurrenceReading.transposeCR` (witness), `KannoSoe.AssumptionLocalWitnesses.no_direction_recovery_from_conditionsEither` (witness), `KannoSoe.InteriorDirectionNegative.no_interior_direction_recovery` (witness)

**Downstream elaboration:** `KannoSoe.DirectionNegative.no_direction_recovery_from_conditionsEither` (witness)

### B.2 No `PreorderTop`

The signature supplies only `PreorderBot`. The share-zero pole is an attained bottom order-class (`AtBot`); the total-share or solipsist pole is an asymptote, not an element of the interface. `StrongSelfConditioningTag` is named and shelved in the being convention for the same reason.

**Checked anchors (Signature):** `KannoSoe.PreorderBot` (proof), `KannoSoe.AtBot` (proof), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.StrongSelfConditioningTag` (proof), `KannoSoe.AssumptionLocalWitnesses.nat_preorderBot_has_no_top` (witness)

### B.3 No privileged person-partition

A being boundary is supplied by a diagnosis-time `BeingCoarsening`, not stored as a field of `Grid`. The signature already admits both identity and total coarsenings for any grid; the downstream `BeingNegative` witness elaborates this as non-recovery of a unique partition from grid data.

**Checked anchors (Signature):** `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening` (proof), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber` (proof), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.SameFiber` (proof), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.id` (witness), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.total` (witness), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber` (witness), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne` (witness), `KannoSoe.AssumptionLocalWitnesses.partition_merge_split_disagree` (witness)

**Downstream elaboration:** `KannoSoe.BeingNegative.no_partition_recovery` (witness)

### B.4 Direction resolution is display, not signature furniture

A clock's finite delivery-axis resolution is supplied by a diagnosis-time `DirectionCoarsening`, not by a `Grid` field and not by any pole or legitimacy predicate.

**Checked anchors (Signature):** `KannoSoe.Grid.DirectedConvention.DirectionCoarsening` (proof), `KannoSoe.Grid.DirectedConvention.DirectionCoarsening.SameTick` (proof), `KannoSoe.Grid.DirectedConvention.DirectionCoarsening.ResolutionBounded` (proof), `KannoSoe.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick` (proof), `KannoSoe.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton` (proof), `KannoSoe.Grid.DirectedConvention.DirectionCoarsening.transpose_subTickDelivery` (witness)

**Downstream elaboration:** `KannoSoe.DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit` (witness), `KannoSoe.DirectionCoarseningWitness.twoResolution_directionCoarsening_independence` (witness), `KannoSoe.Grid.DirectedConvention.DirectionCoarsening.mapDir_resolutionBounded_iff` (proof), `KannoSoe.CoverageNegative.directionVoid_needs_coverage` (witness)

### B.5 Contribution values are display, not operational tokens

The Signature layer itself uses only order and pole vocabulary around `share`. The downstream `DisplayReparam` / `InvarianceNegative` modules give the full transport discipline: order- and pole-preserving display changes preserve the legal predicates, while equality to the chosen bottom does not.

**Checked anchors (Signature):** `KannoSoe.Grid.share_eq_grade_check` (proof), `KannoSoe.AtBot` (proof), `KannoSoe.OrderEq` (proof), `KannoSoe.Grid.Terminus` (proof)

**Downstream elaboration:** `KannoSoe.DisplayReparam` (proof), `KannoSoe.DisplayReparam.atBot_iff` (proof), `KannoSoe.InvarianceNegative.oldEqTerminus_not_invariant` (witness)

### B.6 The enlightenment ladder names standing and enacted vacuity

The operational, assertable effectiveness content is per-occurrence: `KsmdEffectiveOccurrence` states an actual pole-deed landing as a share-drop against a live prior tendency. The descriptive universal `KsmdEffectiveTerminus` remains legal as run-display and direct-path hypothesis, but no estimator from actual-run response/share data decides it. Standing `KsmdFullyEnlightened` adds positive own-act-time `KsmdNoNescience` over speech-or-mind productions. A quiet arhat may still fail that cognitive conjunct; sealed silent and true-thinking buddhas witness its two silent faces. `KsmdFullyEnlightenedEnacted` separately adds an effective deed witness and a production-tied speech occurrence.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `KannoSoe.Grid.DirectedConvention.KsmdEffectiveOccurrence` (proof), `KannoSoe.Grid.DirectedConvention.KsmdEffectivenessEnacted` (proof), `KannoSoe.Grid.DirectedConvention.not_effectivenessEnacted_of_undelivered` (proof), `KannoSoe.Grid.DirectedConvention.KsmdFullyEnlightened` (proof), `KannoSoe.Grid.DirectedConvention.KsmdNoNescience` (proof), `KannoSoe.Grid.DirectedConvention.KsmdFullyEnlightenedEnacted` (proof), `KannoSoe.FaithNegative.noNescience_strictly_stronger_witness` (witness), `KannoSoe.FaithNegative.arhat_retains_nescience_witness` (witness), `KannoSoe.FaithNegative.Sealed.silent_buddha_models` (witness), `KannoSoe.EffectiveTerminusNegative.actual_run_data_underdetermines_effectiveTerminus` (witness), `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.ksmd_effective_occurrence_voice_assertable` (proof), `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.ksmd_standing_effectiveness_voice_displayable` (proof)

### B.7 No blanket noninterference for the contribution carrier

Grading may depend on the agent — `gradingCollisionGrid` grades by being deliberately (cetanā) — so a model's stored tendency may extensionally coincide with an agent tag; `registerClockGrid` witnesses the coincidence. The signature therefore declines the information-flow reading of non-storage. `Grid.rePitch_forgets` bounds the coincidence to a single reception's footprint: nothing accumulates into a diachronic bearer, and the configuration is fibered over no being. The asserted claim is typing plus relabelling equivariance.

**Checked anchors (Signature):** `KannoSoe.gradingCollisionGrid` (witness), `KannoSoe.registerClockGrid` (witness)

**Downstream elaboration:** `KannoSoe.ConfigLeakWitness.registerClock_config_recovers_agent` (witness), `KannoSoe.Config.relabel_fixed` (proof), `KannoSoe.Grid.relabel_rePitch` (proof), `KannoSoe.Grid.rePitch_forgets` (proof)

### B.8 No recovered door boundary

`DoorReading` totally classifies fine welds as body, speech, or mind, but that diagnosis is supplied rather than recovered from response or grade data. Totality and adequacy to the canonical three doors are modeling claims.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `KannoSoe.Grid.DoorReading` (proof), `KannoSoe.DoorsNegative.no_door_boundary_recovery` (witness)

### B.9 No recovered voicing

`SpeechReading` supplies optional content independently of door. Thoughts and bodily intimations are representable, while only speech productions cross into testimony; neither voicing nor its production weld is recovered from visible grid data or content alone.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `KannoSoe.Grid.SpeechReading` (proof), `KannoSoe.Grid.ProducedUtterance` (proof), `KannoSoe.DoorsNegative.no_voicing_recovery` (witness), `KannoSoe.DoorsNegative.no_production_recovery` (witness)

### B.10 No recovered view content

`ViewReading.ownerClaim` supplies which claims count as stored-owner views. The checked coarsening-freeze model is a correlation for one such reading, not a derivation of content from the grid.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `KannoSoe.Grid.ViewReading` (proof), `KannoSoe.FettersNegative.no_view_content_recovery` (witness), `KannoSoe.FettersNegative.ownerClaim_coarsening_freeze_correlation` (witness)

### B.11 No sentience recovery from grid data

Given an actual weld, the same complete response, grade, and delivery data classify it as a `SentientAct` under the constant-true reading and an `InsentientAct` under the constant-false reading. Behavior, share, clench, and delivery therefore jointly underdetermine the mark on the actual domain.

**Checked anchors (Signature):** `KannoSoe.Grid.SentienceReading` (proof), `KannoSoe.Grid.actual_weld_readings_split` (proof), `KannoSoe.Grid.no_sentience_recovery` (witness)

### B.12 No plenitude over being-call pairs

Universal call/response ranges over actual occurrences; it does not assert that every `Being × Call` pair returns a response. The `Option` seam remains load-bearing for hypothetical variation and candidate receptions.

**Checked anchors (Signature):** `KannoSoe.Grid.respondsTo` (proof), `KannoSoe.Grid.Actual` (proof), `KannoSoe.Grid.DirectedConvention.EnvironsLine` (proof)

**Downstream elaboration:** `KannoSoe.ContentNegative.hypotheticalGrid_no_actual` (witness), `KannoSoe.ContentNegative.contentBeingsRow_not_obeys_hypothetical` (witness), `KannoSoe.ContentNegative.fixedResponseGrid_no_variation` (witness), `KannoSoe.ContentNegative.contentIntraWeldArrowRow_not_obeys_fixedResponse` (witness)

### B.13 No aggregate sentience scalar

Sentience is marked per weld. `Intermittent` records fibers containing both marked and unmarked actual acts, but the system assigns no degree of sentience to a tag.

**Checked anchors (Signature):** `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.Intermittent` (proof), `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.Patchy` (proof)

### B.14 No insentient-clench exclusion

An unmarked actual weld may retain live self-share. `InsentientAppropriation` is an inhabited cell of the checked square, so appropriation and structural mismatch do not recover sentience.

**Checked anchors (Signature):** `KannoSoe.Grid.InsentientAppropriation` (proof), `KannoSoe.square_insentientAppropriation` (witness)

**Downstream elaboration:** `KannoSoe.Grid.clenchMismatch_of_insentientAppropriation` (proof)

## C. Conveniences and Stand-Ins

### C.1 Hand-rolled order classes

`Preorder` and `PreorderBot` are hand-rolled to keep assumptions visible and dependency-free. They play the local role Mathlib order classes would play, without importing Mathlib.

**Checked anchors (Signature):** `KannoSoe.Preorder` (proof), `KannoSoe.PreorderBot` (proof), `KannoSoe.shareBot` (proof), `KannoSoe.shareBot_le` (proof)

### C.2 `_before` is retained but currently ignored by `rePitch`

`rePitch` keeps a `_before` slot because the operation is conceptually a re-pitch from a prior configuration. The current implementation ignores that slot; the proof anchor below is a tripwire for the day that changes.

**Checked anchors (Signature):** `KannoSoe.Grid.rePitch` (proof)

> Note: The signature file keeps an `rfl` example showing that two prior configurations produce the same re-pitch for the same received weld.

### C.3 The scalar is display over a partial order

`KsmdMismatchGrade` lives in `Doctrines`, so this Signature module does not import it; the Signature-side checked fact is that `share` is the only contribution value exported by a weld.

**Checked anchors (Signature):** `KannoSoe.Grid.share` (proof), `KannoSoe.Grid.share_eq_grade_check` (proof)

**Downstream elaboration:** `KannoSoe.Grid.KsmdMismatchGrade` (proof), `KannoSoe.Grid.ksmdMismatchGrade_eq_share` (proof)

### C.4 `Models.lean` witnesses are illustrative

The clock and register-clock models anchor possibility checks and mark-invariance witnesses; they are not uniqueness claims.

**Checked anchors (Signature):** `KannoSoe.clockGrid` (witness), `KannoSoe.registerClockGrid` (witness), `KannoSoe.registerClock_insentient_proficient` (witness), `KannoSoe.clock_pole_readings_split` (witness), `KannoSoe.registerClock_rung_readings_split` (witness), `KannoSoe.rigid_terminus_vacuous` (witness), `KannoSoe.adaptive_liveTerminus` (witness), `KannoSoe.sentience_share_square_inhabited` (witness), `KannoSoe.registerClock_macro_selfConditioning` (witness)

## Axiom audit

`#verify_axiom_audit` compares each declaration's collected axiom set with this allowlist during every build.

| Declaration | Allowed axioms |
|---|---|
| `KannoSoe.Grid.no_agent_recovery_of_field_collision` | None |
| `KannoSoe.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick` | None |
| `KannoSoe.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton` | None |
| `KannoSoe.Grid.relabel_rePitch` | None |
| `KannoSoe.Grid.no_natural_agent_recovery_from_config` | `propext`, `Quot.sound` |
| `KannoSoe.ConfigLeakWitness.registerClock_config_recovers_agent` | `propext` |
| `KannoSoe.ConfigLeakWitness.no_agent_recovery_from_config_of_share_collision` | `propext` |
| `KannoSoe.strict_asymm` | None |
| `KannoSoe.strict_trans` | None |
| `KannoSoe.Grid.transpose_transpose` | None |
| `KannoSoe.DirectionNegative.no_direction_recovery_from_conditionsEither` | `propext`, `Quot.sound` |
| `KannoSoe.CoverageNegative.directionVoid_needs_coverage` | None |
| `KannoSoe.CoverageNegative.ksmdEffectiveTerminus_needs_coverage` | `propext` |
| `KannoSoe.Grid.stateToolFits_iff_atBot` | None |
| `KannoSoe.Grid.map_actual_iff` | None |
| `KannoSoe.Grid.map_isShareDrop_iff` | None |
| `KannoSoe.Grid.map_transpose` | None |
| `KannoSoe.Grid.actual_weld_readings_split` | None |
| `KannoSoe.Grid.no_sentience_recovery` | None |
| `KannoSoe.sentience_share_square_inhabited` | `propext` |
| `KannoSoe.Grid.DirectedConvention.DirectionCoarsening.mapDir_resolutionBounded_iff` | None |
| `KannoSoe.DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit` | None |
| `KannoSoe.DirectionCoarseningWitness.twoResolution_directionCoarsening_independence` | None |
| `KannoSoe.DirectionCoarseningWitness.registerClock_directionCoarsening_independence` | `propext` |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_not_fused_of_nonlive_denial` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_not_obeys_of_nonlive_denial` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_obeys_of_no_occurrences` | None |
| `KannoSoe.ContentNegative.contentBeingsRow_not_obeys_hypothetical` | `propext` |
| `KannoSoe.ContentNegative.contentGridLensRow_not_obeys_hypothetical` | `propext` |
| `KannoSoe.ContentNegative.contentWeldRow_not_obeys_hypothetical` | `propext` |
| `KannoSoe.ContentNegative.contentIntraWeldArrowRow_not_obeys_fixedResponse` | `propext` |
| `KannoSoe.ContentNegative.contentBeforeAfterRow_not_obeys_twoBottom` | None |
| `KannoSoe.Grid.DirectedConvention.map_landsWithShareDrop_iff` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_fiberAtPoleOn_iff` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne` | None |
| `KannoSoe.Grid.map_ksmdBullSeven_iff` | None |
| `KannoSoe.Grid.map_ksmdBullTen_iff` | None |
| `KannoSoe.Grid.bullSeven_not_bullEight` | None |
| `KannoSoe.Grid.bullTen_to_bullNine` | None |
| `KannoSoe.CorrelationsNegative.pratyekabuddha_countermodel` | `propext` |
| `KannoSoe.CorrelationsNegative.no_stage_boundary_recovery` | `propext` |
| `KannoSoe.Grid.classQuiet_no_clench_in_class` | None |
| `KannoSoe.Fetter.kind_lower_iff_cut_by_nonReturn` | None |
| `KannoSoe.Grid.arhatPathQuiet_iff_quietOn_univ` | None |
| `KannoSoe.Grid.terminus_iff_quietOn_univ` | None |
| `KannoSoe.Grid.atPoleClass_iff_quietOn_univ` | None |
| `KannoSoe.Grid.all_fetters_cut_at_arhat` | None |
| `KannoSoe.Grid.identityView_cut_iff_noDefiledVoicing` | None |
| `KannoSoe.Grid.conceit_excluded_of_quietOn` | None |
| `KannoSoe.Grid.ksmdIrreversibleRegime_conditional` | None |
| `KannoSoe.Grid.lower_fetters_covered_by_rites_view_resolve` | None |
| `KannoSoe.Grid.ksmdStreamWinner_iff_streamEntry_cutClasses` | None |
| `KannoSoe.Grid.ksmdNonReturner_iff_nonReturn_cut` | None |
| `KannoSoe.Grid.ksmdSerialFactorRegime_conditional` | None |
| `KannoSoe.Grid.ksmdOnceReturner_attenuation_witness` | `propext` |
| `KannoSoe.FactorsNegative.no_hold_conceit_boundary_recovery` | `propext` |
| `KannoSoe.FactorsNegative.factor_order_underdetermined` | `propext` |
| `KannoSoe.FettersNegative.seen_run_underdetermines_fetterCut` | `propext` |
| `KannoSoe.Grid.DirectedConvention.ksmdPathOught_conditional` | None |
| `KannoSoe.Grid.DirectedConvention.ksmdFaithOught_conditional` | None |
| `KannoSoe.Grid.DirectedConvention.ksmd_says_true_of_faith` | None |
| `KannoSoe.Grid.DirectedConvention.noDelusion_of_noNescience_of_terminus` | None |
| `KannoSoe.Grid.DirectedConvention.ksmdFullyEnlightened_of_fullyEnlightenedEnacted` | None |
| `KannoSoe.FaithNegative.noNescience_strictly_stronger_witness` | `propext` |
| `KannoSoe.FaithNegative.aklishta_ajnana_witness` | `propext` |
| `KannoSoe.FaithNegative.arhat_retains_nescience_witness` | `propext` |
| `KannoSoe.FaithNegative.Sealed.silent_buddha_models` | `propext` |
| `KannoSoe.Grid.DirectedConvention.no_ksmd_path_at_pole` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.pole_validates_all_claims` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.denied_misfits_live_offer` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.rowOf_obeys_iff_errorFree` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.reEmptied_obeys_of_errorFree` | None |
| `KannoSoe.rung_not_pole_witness` | `propext` |
| `KannoSoe.standing_does_not_determine_dated` | `propext` |
| `KannoSoe.Grid.DirectedConvention.map_ksmdAversionContext_iff` | None |
| `KannoSoe.OrthogonalityNegative.ksmdEffectiveTerminus_stronger_than_terminus` | `propext` |
| `KannoSoe.MisFeedNegative.fence_and_gate` | `propext` |
| `KannoSoe.misFeed_entries_carry_decomposition` | None |
| `KannoSoe.Grid.grade_independent_of_conditions` | None |
| `KannoSoe.Grid.rePitch_forgets` | None |
| `KannoSoe.Grid.respondsToEveryCall_of_no_call` | None |
| `KannoSoe.Grid.DirectedConvention.PrudentialPrivilegeNegative.prudentialPrivilege_failure_modes` | `propext` |
| `KannoSoe.Grid.ConsequentialistConvention.dropCountInFiber_le_dropCount` | `propext` |
| `KannoSoe.Grid.ConsequentialistConvention.dropCount_eq_sum_dropCountInFiber` | `propext` |
| `KannoSoe.Grid.ConsequentialistConvention.map_dropCountInFiberSum` | `propext` |
| `KannoSoe.ObjectiveNegative.split_dropCount_sum_eq_mergedDropCount` | `propext` |
| `KannoSoe.ObjectiveNegative.no_grid_data_objective_for_my_drops` | `propext` |
| `KannoSoe.TransferNegative.adaptive_track_record_underdetermines_new_effect` | `propext` |
| `KannoSoe.Grid.DirectedConvention.not_effectivenessEnacted_of_undelivered` | None |
| `KannoSoe.EffectiveTerminusNegative.no_effectiveTerminus_recovery_from_run` | `propext` |
| `KannoSoe.DeliveryArrogationNegative.command_utterance_not_fits` | `propext` |
| `KannoSoe.Grid.DirectedConvention.landing_call_in_modality` | None |
| `KannoSoe.LedgerCase.decree_engineers_calls_not_receptions` | `propext` |
| `KannoSoe.LedgerCase.official_actualAgentInhabited` | `propext` |
| `KannoSoe.InteriorDirectionNegative.transposeCR_involutive` | `propext` |
| `KannoSoe.InteriorDirectionNegative.unorderedCRContent_transpose_invariant` | `propext` |
| `KannoSoe.InteriorDirectionNegative.transpose_swaps_readings` | `propext` |
| `KannoSoe.DoerDeedNegative.priority_readings_disagree` | None |
| `KannoSoe.DoerDeedNegative.no_priority_recovery` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_obeys` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowRow_not_freeze` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.no_order_collapse_self_refuting` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_obeys` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedRow_not_freeze` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.no_prior_doer_collapse_self_refuting` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.contentLayerRow_obeys_of_variation` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.contentIntraWeldArrowRow_obeys_of_variation` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.interior_order_denial_unfit_for_live_utterer` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_obeys_succ` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.intraWeldArrowLadder_no_level_final` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_obeys_succ` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.doerDeedLadder_no_level_final` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.Metaphysics.intraWeldArrow_sunyata` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.Metaphysics.doerDeed_sunyata` | None |
| `KannoSoe.Grid.map_responseVariesWithCall_iff` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowRow_obeys` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedRow_obeys` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.map_contentIntraWeldArrowRow_obeys_of_variation` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_obeys_succ` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.map_intraWeldArrowLadder_no_level_final` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_obeys_succ` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.map_doerDeedLadder_no_level_final` | None |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_beings_sunyata` | `propext` |
| `KannoSoe.Grid.DirectedConvention.BeingConvention.GridConvention.ladderRungGrid_no_level_final` | `propext` |
