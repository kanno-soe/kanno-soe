# Kannō-Sōe Mutual Dependence

An axiomatic reconstruction of Zen sayings in an ontology-under-erasure act-grammar.

The project implements a deliberately simplified model for discussing Mahayana Buddhist metaphysics. It is most useful for conditional and independence results: *if* one accepts the model's translation of a claim, a proof can show that the translated claim needs no richer machinery. The conditional matters. Oversimplifying the object proves something about the simplification, not automatically about Buddhism, Nāgārjuna, Jizang, or the world. The account below therefore marks three statuses throughout: **formal model structure**, **a manually supplied interpretation**, and **the philosophical act-grammar laid over that structure**.

## The formal core: designata, elaboration, and Mutual Dependence

A **designatum** is simply something the model can designate. It does not first divide designata into people, objects, events, thoughts, or times.

A **component** is a nonempty group of designata.

An **elaboration** (⇓ reads as "elaborates to") is a relation saying that a designatum may be expanded into a raw Mutual Dependence; because it is a relation rather than a function, one designatum may have no stated elaboration, one elaboration, or several alternatives.

The basic shape of a Mutual Dependence `m` is a list of at least two components where every adjacent pair are symmetrically interdepending:

```text
    m ⇓ [C1 ⋈ C2 ⋈ C3 ⋈ ... ⋈ Cn]

    not required: a temporal order, a causal arrow, or direct C1/Cn interdependence
```

as an equation:
```math
C_1 \bowtie \cdots \bowtie C_n
\quad\Longleftrightarrow\quad
\bigwedge_{i=1}^{n-1}(C_i\bowtie C_{i+1})
```

The mutual dependence, when considered as a shape, has a left side C1, and a right side Cn.

As components may contain designata, and a designatum may be elaborated to a mutual dependence, the elaborated components can look like:

```text
  ab ⇓ [a ⋈ b]
  fg ⇓ [f ⋈ g]
  m  ⇓ [{ab, c, d} ⋈ {e} ⋈ {fg} ⋈ {h}]
```

Here the first component of `m` has 3 designata, `ab` which designates (elaborates to) a mutual dependence `[a ⋈ b]`, and `c`, and `d`, which each are designata without defined elaboration.

A designata **reaches** (`d →* w`) if in zero or more steps of elaboration, `d` can elaborate toward another designatum `w`.

Designata of neighbouring components are **joinable** (↓) if there is a shared designatum `w` that both can reach (it is focused reachability, explanation follows). The shape of the elaborated mutual dependences is considered relevant when elaborating on each side of the neighbouring components. If we consider the first and second components of `m` above, `ab` is in the first component, and we only consider the right side of its shape, `b`, in terms of reach with the neighbouring component to its right, `{e}`. Elaborations of those reached designata may then be followed again. The designata are **joinable** when their reach-trees have some designatum in common:

```text
                              +--> p ---->
                             /
    designatum b --elaborates
                             \
                              +--> q ----> common witness w

    designatum e --elaborates----> r ----> common witness w

    b ↓ e  :=  there is some w reached from both b and e
```

as an equation:
```math
d \downarrow e
\quad\Longleftrightarrow\quad
\exists w.\; d \to^{*} w \leftarrow^{*} e
```

This joinability is reflexive and symmetric, but it need not be transitive. An interdependence (⋈) between two components is a stronger requirement than just finding a joinable pair: every designatum in the first component must have a joinable partner in the second, and every designatum in the second must have a joinable partner in the first.

```text
    component C                       component D
    +---------+                       +---------+
    | c1      | -- joinable partner ↓ | d?      |
    | c2      | -- joinable partner ↓ | d?      |
    | c?      | ↓ joinable partner -- | d1      |
    | ...     |                       | ...     |
    +---------+                       +---------+

    C ⋈ D  requires coverage in both directions.
```

as an equation (interdependence is the Egli–Milner lifting of joinability):
```math
A\;\overline{\downarrow}\;B
\iff
\bigl(\forall d\in A\,\exists e\in B.\;d\downarrow e\bigr)
\land
\bigl(\forall e\in B\,\exists d\in A.\;e\downarrow d\bigr)
```
```math
A\bowtie B
\quad\overset{\mathrm{def}}{\Longleftrightarrow}\quad
A\;\overline{\downarrow}\;B
```

The chain may be any finite length. It can be sliced and compatible chains can be catenated, but the word *chain* must not smuggle in time: these arrows display symmetric interdependence, not before and after. Also note that although the examples in this exposition involve linear chains, two chains may include the same component. Taken together then it is really a chain network (net for short), with components having a "valency". An interior component of a chain has valency 2, while a junction in a chain network can have valency >2.

This is the minimal formal structure of **Mutual Dependence** (*sōe*). Throughout, that structure is read as **mujishō-sōe**: mutual dependence without-own-being (*mujishō*), in which neither side supplies a self-standing substrate for the other.

## Resonance as a Mutual Dependence

A **Resonance** is the following four-component special case of Mutual Dependence, with its middle components forced to be singletons:

```text
    calls ⋈ {b1} ⋈ {b2} ⋈ responses
```

The intended reading is that `b1` is the receiving view or moment of a being and `b2` is its responding view or moment. Formally, however, `b1` and `b2` are two interdependent singleton designata in the same certified dependence. The model does not prove that they are numerically identical, temporally successive, conscious, or personal. The names **calls**, **receiving**, **responding**, and **responses** are role-readings of the shape.

An **Encounter** is a Resonance viewed merely as a Mutual Dependence. It retains the concrete `calls ⋈ {b1} ⋈ {b2} ⋈ responses` shape while everything about it being a resonance is temporarily forgotten. *Encounter* is an expository alias, not a new Lean type. Every Encounter is a Mutual Dependence; not every Mutual Dependence has the four-component singleton-middle shape needed to be an Encounter.

Because designata may elaborate into any raw dependence the modeler supplies and later certifies, the same Resonance shape can be used for a person answering a question or a stone answering the wind by rolling downhill:

```text
    {wind} ⋈ {stone-receiving} ⋈ {stone-responding} ⋈ {rolling}
```

Nothing in the ungraded structure privileges the person. Nor does the stone example prove a doctrine about sentience: it proves only that the Resonance constructor asks for interdependent singleton designata in its two middle positions, not a prior metaphysical kind called *person*.

## Graded Resonance and Being

A **Graded Resonance** adds two independent grades to a Resonance: a calls-side grade and a responses-side grade. The grade type need only be a preorder with a bottom element. It need not be numerical, total, or metrically spaced. The intended reading is **dis-resonance**: volition insofar as it is *sāsrava*—with outflows, ripening in further becoming. Bottom is *anāsrava* at this Resonance: the act is not productive of further becoming, without implying either the absence of volition or the global attainment of arhatship. `0` is only the familiar numerical example. How a bottom grading relates in the world is left as a functional question about the relating of such moments, and could be modelled by downstream effects on other resonances.

```text
                    one Graded Resonance

   calls ⋈ (callsGrade) {b1} ⋈ {b2} (responsesGrade) ⋈ responses

     callsGrade and responsesGrade are independent coordinates.
```

Thus a stone may be *assigned* bottom on both sides, while a grumpy person who has stubbed a toe may be *assigned* a non-bottom calls grade, a non-bottom responses grade, or both. Those are interpretations supplied to the model; the model itself does not infer a grade from stonehood, pain, personality, or behavior. `IsUngraded` means exactly that both grades are bottom. “Ungraded” here therefore means no dis-resonance entered on either side, not absence of calls from the resonance and not absence of response.

Grading is sentience-neutral. A sentience reading *could* be supplied as additional information, but it's not inherently required in the model.

A **Being** is a nonempty list of Resonances whose singleton middle components flatten into one certified Mutual Dependence:

```text
of Resonance 1       of Resonance 2              of Resonance n
{r1b1} ⋈ {r1b2}  ⋈  {r2b1} ⋈ {r2b2}  ⋈ ... ⋈  {rnb1} ⋈ {rnb2}

    Being = the certified chain of these receiving/responding moments
```

The calls and responses surrounding each Resonance do not constitute the Being's formal spine; its `b1,b2,...` middle moments do. This is a conventional construction of a being out of interdependent moments, not a proof of a persisting owner behind them.

## Direction and Causation are overlays

Mutual Dependence and Resonance contain no time-directedness. A **Directed** interpretation is supplied separately as a strict transitive **Before** (≺) relation. A domain may then supply a **Causal** (↝) interpretation with a `x ↝ y` relation, a proof that causing implies `x ≺ y`, and, for every causal claim, a **Causation** certificate.

That certificate is itself just another Mutual Dependence in a precise and limited sense: it exhibits some certified Mutual Dependence whose first component contains `x` and whose last component contains `y`.

```text
    dependence certificate:   {x, ...} ⋈ ... ⋈ {..., y}
    directed overlay:          x ≺ y
    causal assertion:          x ↝ y

    x ↝ y  =>  x ≺ y
    x ↝ y  =>  a Mutual Dependence with `x` in the left and `y` in the right of its shape
```

Forgetting the causal and temporal overlays leaves the underlying Mutual Dependence; adding the overlays is additional data. Therefore this does not say that every Mutual Dependence is causal, that symmetric interdependence secretly points from cause to effect, or that every Directed fact is causal. Causation as another Mutual Dependence names the certified dependence-skeleton of a causal claim, not a reduction of causality to symmetry.

Accordingly, **mujishō-sōe** is the dependence-structure retained when either grading or the causal and directional overlays are forgotten.

## From empty dependence to the provisional middle

> Whatever is dependently co-arisen  
> That is explained to be emptiness.  
> That, being a dependent designation,  
> Is itself the middle way.
>
> — Nāgārjuna, *Mūlamadhyamakakārikā* 24.18

Remove grades from a Graded Resonance and everything else about it being a resonance and the Mutual Dependence remains. That remainder does not by itself prove a Buddhist metaphysics. The philosophical bridge begins when the act-grammar reads it as **mujishō-sōe**: mutual dependence under the condition of no own-being.

*Mujishō* (無自性) means without self-nature or own-being. The model's interdependence relation is a simple formal analogue: neither interdependent component is entered as the self-standing base of the other. This is an **interpretation of** Mutual Dependence, not a theorem extracted from `Interdependent`; supplied elaborations can encode many domains, and Lean does not turn a symmetric reach relation into Nāgārjuna by itself.

The interpretive route begins with Nāgārjuna's *MMK* 24.18: what dependently originates is empty of own-being; that emptiness is itself dependently designated; just this is the middle way. Dependence therefore cannot mean relations among already self-subsisting things, while emptiness cannot become a deeper thing beneath them. Applied to the Encounter above, the point is not that `calls`, `b1`, `b2`, and `responses` vanish. It is that none supplies the final bearer of the answering.

Jizang supplies the next turn. In the fourfold two truths, each stated ultimate—including the conventional/ultimate distinction itself—can become the conventional content of the next analysis. The iteration does not discover a fifth, finally unconditioned proposition. It ends at words forgotten, thought cut off (言忘慮絶): not another claim, but the place where words and thought no longer do separating work. That claimless place is called the **floor**. The middle can then manifest as this case instead of becoming another object of analysis. This manifestation is called the **genjō**, **provisional middle**.

The first row of the act-grammar can now be shown:

| Dependence reading | Enactment reading |
|---|---|
| **mujishō-sōe** — Mutual Dependence without own-being | **genjō** — the dependence manifesting as this case |

The **dependence-face** names the relation retained when additions are forgotten; the **enactment-face** names how that relation comes forward as a case. Mujishō-sōe is therefore the dependence-face of Row 1: this Encounter has no self-standing substrate. Genjō is its enactment-face: that empty dependence nevertheless manifests as this call, this receiving, this response. *Provisional* does not mean half-real or merely hypothetical. It says that the case is concrete without being promoted into a final ground. The move from Jizang's recursive discipline to *genjō* is the reconstruction's move into Dōgen's vocabulary, not a claim that Jizang himself supplied this grid.

## From no rank to practice-realization

> Monk: “What is the true person of no rank?”  
> Linji: “Speak! Speak!”  
> The monk hesitates.  
> Linji pushes him away: “The true person of no rank—what a dried piece of shit!”
>
> — Linji Yixuan, *The Record of Linji*

Genjō answers how groundless dependence comes forward as a case.

Linji supplies its guard-image. The reconstruction reads the true person of no rank (無位真人) along a seam: *no rank* (無位) is non-attainment; the true person going in and out (真人…出入) through the face-gates prevents no-rank from becoming inert; the whole figure holds no-rank and activity together. When the monk asks what the true person is—and then hesitates under Linji’s demand to speak—the phrase threatens to become a resting-place. Linji’s rebuff destroys that possibility, discarding even the “true person of no rank” once it begins to function as something identifiable or possessable. This no-rank, no-resting-place reading is called the **non-attaining middle**, or the **unattaining middle** when the emphasis falls on nothing being obtained or stored.

The reconstruction states that reading in Dōgen's vocabulary. **Shu** (修) is practice, the concrete doing. **Shō** (証) is realization, with the non-attaining floor-face at a bottom placement in any given grading, read here under the governing *mujishō* condition—no own-being, no rank, nothing possessed. The homophone matters: the *shō* in *mujishō* is 性, nature, while the **shō** in *shushō* is 証, realization—governed by the *mujishō* no-own-being reading.

Shō gains determinate content through a contrast within practice. At a bottom placement, practice has its non-attaining floor-face face: the act's subject-position is ceded, with nothing in the doing answering to a dis-resonant "self-forwards". At a non-bottom placement, that same practice is delusive to the extent that it arrogates the subject-position. This gives the non-attaining floor-face its grading counterpart. Genjō has no corresponding delusion term: its contrast is empty dependence versus manifestation, not non-bottom delusion versus unattaining bottom placement.

**Shushō** (修証) says practice-realization; **shushō-ittō** says that its practice and realization are non-dual. That cannot mean two events—practice first and an attained realization later—nor a still shō somehow acting by itself.

```text
                         one Graded Resonance

 practice, the doing (shu) ---- shushō ---- (shō) realization, as verified

                      shushō-ittō: not two events
```

**Genjō**, the provisional middle, answers *how does empty dependence manifest as this case?* **Shō** answers *what is realization as verified?* Manifestation is not possession of realization; realization is not a second activity alongside manifestation. Their distinction will remain live when the grading is diagnosed and lose its separating work where not.

## The act-grammar grid

> *Carrying the self forward to practice-realize the myriad dharmas is delusion; the myriad dharmas advancing to practice-realize the self is satori.*
>
> — Eihei Dōgen, *Genjōkōan*

> *Practice amid activity is immeasurably superior to practice amid stillness.*
>
> — Hakuin Ekaku, *Orategama* I, quoting Dahui Zonggao

The three-row **act-grammar** can now be shown whole. Each row pairs a dependence-reading with an enactment-reading of one Resonance.

| Dependence reading | Enactment reading | Modelling |
|---|---|---|
| **mujishō-sōe** — Mutual Dependence without own-being | **genjō** — the dependence manifesting as this case | Mutual Dependence |
| **kannō-sōe** — responsive resonance placed under dis-resonance grading | **banpō susumite** — the myriad dharmas advancing, the being verified | Graded Resonance |
| **engi / inga** — dependent arising and cause/effect under an added direction | **dōchū no kufū** — practice in the midst of activity | Directed + Causal + Causation |

Read under the essay's title, the enactment cells pick out three aspects of the quoted passage: genjō is the actualizing of the case, banpō susumite is the dharmas advancing and the self being verified, and shu is the practice-realizing that occurs. These are not three events, three agents, or a chronology from Row 1 to Row 3. Row 1 reads that act as manifestation without substrate; Row 2 reads it as this being's graded receiving and responding; Row 3 reads the doing under direction and causation. Conversely, forgetting Row 3's overlays and Row 2's grades returns the Mutual Dependence with which the formal account began.

## Floor-face and act-time face

The **floor** is not a first moment, a hidden base, or a final substance. It is the tier at which no deeper support is claimed and no distinction is doing separating work. A **floor-face** is this Encounter read under that no-own-being, no-claim condition. **Act-time** is the conventional diagnostic tier at which this call, this receiving, this response, this practice, and the distinctions needed to describe them are live. It is not a second Resonance before or after the floor-face.

The shushō reading introduced above is one example:

```text
                         one Graded Resonance

        act-time face                            floor-face

   concrete practice (shu) ---- shushō ---- (shō) the being-verified
   in receiving/responding
```

Act-time follows the concrete receiving at `b1` or responding at `b2`; the floor-face reads that same `b1` or `b2` without an independently standing receiver or responder. Shu and shō are reciprocal faces of that receiving or responding within the Graded Resonance: one name follows the enactment, the other its no-own-being, non-attaining realization.

## Separate/fuse, utterances, and their offers

The **separate/fuse rule** states how distinctions behave across those tiers. At act-time a useful distinction separates. At the floor it fuses, meaning that it makes no separating claim there—not that its two sides become one substance and not that both propositions are asserted.

```text
                         distinction separates      distinction fuses
    act-time diagnosis   A | B   rule obeyed        A >< B  collapse
    floor                A || B  freeze             A . B   rule obeyed
```

The two error cells occupy one diagonal; the other diagonal is the rule obeyed.

**Collapse**, written `><`, is premature fusion under act-time diagnosis; **freeze**, written `||`, is a useful separation reified as a floor-claim. These are expository operators, not Lean syntax. “There is no time, no being, and no Resonance” is a collapse when offered where a response is occurring. A flowing time-container, substantial Being, stored shō, or self-existing Resonance is the corresponding kind of freeze.

An **utterance** here is not a sentence-shape in isolation. It is content carried by a resonance, with the call it answers and the tier at which it is offered. The taxonomy (in the section below) grades that offer, not the words alone: ordinary narration offered conventionally at act-time is declined as no error; the same words offered as ultimate furniture can freeze, while a denial offered as live diagnosis can collapse.

## A taxonomy of error

> This section still references the old version of the code, and *weld*, a conceptual fore-runner to (Graded) Resonance. The older model generally produces reasonable conclusions, however mostly as a result of structural artifact from reasonable modelling decisions as opposed to being meaningfully proven.

Classical nihilism turns out to be a freeze, not a collapse: the void is emptiness reified as an *absence* — a snake wrongly grasped is still grasping. And mis-typing — the state-tool for an act-job, the faculty-reading of Row 2 — is the freeze applied to the act/state distinction specifically: an act frozen into a standing configuration.

The errors are categorised in two grades:

1. **Grammatical errors** — tier-errors and typing-errors. These the system can *assert*, because a mis-feed is a conventional-tier logic verdict, not a value. The fox's mistake is assertable. (Assertable, note, *within the lens*: "tier-error" and "mis-feed" are verdicts of the two-truths machinery itself, compelled inside it and offered outside — the banner's clause governs the grid's own voice, and the asymmetry between the two grades is an asymmetry in that voice, not an appeal to lens-free logic.)
2. **Soteriological shortfalls** — arrogation, self-forward, low resonance, failure to meet beings. These the system can only *display* — Row 2 placements and Row 3 directions, valence borrowed from the object. The five hundred fox lives were returns, not punishments; by the same token "he failed to act as a bodhisattva" is never an asserted wrong, only a displayed asymmetry.

### Grade 1: the generator's output

| Distinction | Collapse (fused at act-time) | Freeze (distinction held at floor) |
|---|---|---|
| Being / non-being (Nishitani) | — | Nihilism: absolute non-being taken as privative void, one more member of the pair. It wears an epistemic face — skepticism, no-floor reified into no-warrant, as if conventional standing had ever rested on a final floor (the *sarvaṃ yujyate* reversal declined: it is *because* of emptiness that everything works) — and a practical face — annihilationism, death held as a floor-event, an exit the loop never had; the fox died five hundred times and no death was the release |
| Level *n* / level *n*+1 (Jizang's fourfold — Nāgārjuna's 空空, iterated; Lean-generated by `ladder_obeys`) | Skipping the ladder — cheap transcendence, floor-talk without having emptied anything | Eternalism at level *n*: this pair is the final floor (`no_final_level_of_errorFree`, `ladder_obeys_of_errorFree`) |
| The ladder / its terminus | — | Emptiness-sickness (空病): seeking a fifth negation, the emptying itself frozen into a path-object instead of the seeking dropped. The absence is structural: there is no "completed ladder" claim constructor (`no_final_level_of_errorFree`). As a formal-model analogue of 空空, priming is image-idempotent for `Reaches`: a second priming mints a further web-designatum but adds no paths among once-primed designata (`prime_reaches_exhausted_on_image`). `Joinable` is unchanged there only in the weaker, trivial sense that the first priming already made it total (`prime_joinable_exhausted_on_image`) |
| Rung / pole of the grade (kenshō / genjō) | A kenshō spoken *as* genjō — a rung as the floor; the Zen sickness (禅病) of "stinking of Zen," an opening inflated into arrival — the fox's error at another joint (`rungPoleRow_obeys`, `kensho_as_genjo_collapse_self_refuting`, `rung_not_pole_witness`) | Genjō held as *final* kenshō — the pole as top rung, awakening as a still attainment, daigo as rank; "full satori" is this freeze miniaturized — a state-word for a per-call pattern (`rungPoleRow_not_freeze`) |
| genjō / shō (two middles) | Conflating them — manifestation taken as realization, or conversely | Holding the two-middles distinction itself as a final floor-claim |
| shō / satori (証 / 悟) | Reading the floor-face as the awakening-mode, or conversely | Satori as a datable possession |
| shu / shō (the weld) | **The fox**: not-fall asserted conventionally — antinomianism. Converse fox: not-obscure insisted on at the floor — moralizing where nothing falls (`foxWeldRow_obeys`, `fox_notFall_collapse_self_refuting`, `fox_utterance_misfits_live_offer`) | Two one-sided freezes: shō without shu (quietism, Dahui's silent-illumination target — emptiness that only empties) and shu without shō (practice as means to a later attainment, breaking shushō-ittō) (`foxWeldRow_not_freeze`) |
| Row 2 adverb / Row 3 verb | The placement *being* the self — grade collapsed into agent | Resonance held as a faculty; buddha-nature as substance; the empty agent re-based |
| Doer / deed | *No doer, only deeds* — bundle-reductionism spoken as live diagnosis, mounted by a being answering a call (`doerDeedRow_obeys`, `no_prior_doer_collapse_self_refuting`) | The prior doer: kāraka held prior to karman, MMK 8's target occupying its own cell; the soul in relational dress, distinct from the Pudgalavāda cell because here the *priority* is reified (`doerDeedRow_not_freeze`, `DoerDeedNegative.no_priority_recovery`) |
| Function / share | Universal response identified with its share-cell — share-zero treated as non-response, or live share treated as the only real function; the identity *I-making just is the clench* is this collapse in embryo (`functionShareRow_obeys`, `function_share_cell_collapse_self_refuting`) | Function frozen into a standing device-nature — the mirror given a stand; originally not a single thing (本来無一物) is the corrective (`functionShareRow_not_freeze`) |
| karma / inga | The mis-feed: an index-free field fed to an index-requiring designation (`karmaIngaRow_obeys`, `misfeed_collapse_self_refuting`) | The soul: the index *stored* between welds — a standing bearer. Maximized, the solipsist's stored-index face annexes the whole field; the self-forward and Row 2-domain faces are neighboring cells in the compound decomposition rather than new rows (the solipsist is the stone's inverse: all response, no call, unable even to state what listening to Hyakujō would be) (`karmaIngaRow_not_freeze`, `solipsism_decomposition`) |
| Sowing / reaping (the diachronic index) | Ownership read off the series alone; sameness-of-being as bare continuity-fact (`sowingReapingRow_obeys`, `series_ownership_collapse_self_refuting`, `no_diachronicWhose_from_series_alone`) | The retrospective soul: the reach-back held as a standing backward relation rather than spent at reception — memory's felt storedness read literally is this freeze in psychological dress (`sowingReapingRow_not_freeze`) |
| Delivery-question / index-question | Mis-fed in either direction: an index-question fed to the index-free field (*did I earn this?* — akṛtābhyāgama's mis-feed half; *does the Tathāgata exist after death?* — the same mis-feed at the pole), or a delivery-fact arrogated by the weld — an act claiming command of what arrives next ("easy"; every exit-arithmetic; Devadatta's aim), authority over the one register no act holds (`deliveryIndexRow_obeys`, `misfed_register_collapse_self_refuting`) | One's future occurrence at others' Row 2 held now as a first-personal possession — "my potential," "my worth to them" — a delivery-fact, read at *their* act-times off whatever the field brings, frozen into something the being holds and could therefore weigh, spend, or withdraw — prudential privilege is this freeze's forward-facing twin, the cross-gap *whose* held as rational ground (`deliveryIndexRow_not_freeze`) |
| Weld / event-type (severity) | Karma graded off the event-type with the weld erased — Cunda owed remorse, intention deleted from the arithmetic (`weldEventTypeRow_obeys`, `eventType_grading_collapse_self_refuting`) | Victim-rank: severity read off the victim's station — the honorific inflating the crime; rank smuggled back through the tariff (`weldEventTypeRow_not_freeze`) |
| Disposition / act (seed / clench) — **retyped: the distinction is standing/dated, never configuration/act** | The dated occurrence read off the standing tendency — *he arrogates, so this act was arrogated* — prognosis substituted for diagnosis, Row 2 made to read seeds instead of deeds (what the determination reads — the configuration's part in driving *this* response — is not this cell: every act is the configuration's act); dukkha read off the seed — the proneness to suffer mistaken for suffering occurring — is the same collapse at the valence (`standingDatedRow_obeys`, `prognosis_as_diagnosis_collapse_self_refuting`, `standing_does_not_determine_dated`) | The seed as bearer — ālaya frozen into a self carrying mineness between acts. Two further faces: the clench as *furniture* — contraction mistaken for a standing thing removable only with its substrate ("only ending me ends this"), dukkha held substrate-bound being this freeze wearing its valence, where de-clench is demolition-free by the same theorem that makes kenshō unholdable; and the clench as *structure* — contraction made constitutive of the being (anguish as the very form of consciousness — the Sartrean face; Zahavi's thin for-me-ness is expressly *not* this cell, taking the retype instead, per the placement in Identification) (`standingDatedRow_not_freeze`) |
| Subject-axis / object-axis | Object-axis delivery identified with the receiver's own subject-position (`subjectObjectAxisRow_obeys`, `object_axis_as_subject_collapse_self_refuting`) | Object-axis standing denied — to another, reflexively, in the solipsist's Row 2 evacuation, or held annullable by the being. The death-freeze is re-derived without vacuity: unmarked pole welds have object-axis standing without a sentience mark, live share, natural door assignment, or landing-pattern; where remains-welds arise, death changes the character of new occurrences and cannot subtract the standing of those already actual (`subjectObjectAxisRow_not_freeze`, `solipsism_contains_row2_domain_evacuation`) |
| Per-weld mark / standing sentience | Sentience identified with grid-visible function, in either direction — the retired `SentientTag = MountsSomewhere` identity was this collapse; machine behavior does not recover the mark (`standingSentienceRow_obeys`, `sentience_from_function_collapse_self_refuting`, `no_sentience_recovery`) | Sentience held as a nature the being has — affirmation or denial as nature (性); the mark is per act or it becomes a soul-shaped kind (`standingSentienceRow_not_freeze`) |
| Per-call / global altitude | — | The stage-scheme error: bhūmis as rank held, a global altitude, rather than cross-sections of the loop's run — and its diagnostic twin, a delivery-fact read as altitude: "this being cannot awaken" said of a being some calls cannot reach. The freeze is two-banked: on the responder's side, upāya held as a standing competence — the device as possession, deployed unread of who is asking. The self-forward direction canonized as ontology or human condition is this row's direction face. The stored-quantity picture of awakening — an altitude accumulated and held — is this freeze under its sudden/gradual face (§2) (`perCallGlobalRow_not_freeze`, `solipsism_decomposition`, `existentialism_decomposition`) |
| Description / injunction (the orange) | "Eat this": the displayed asymmetry taken up *by the theory* as command — theodicy is this collapse applied to akṛtābhyāgama, suffering asserted as assignment; "escape this" — the fourth truth said in the theory's voice — is the same collapse applied to dukkha. Mirrored on the recipient's side: defiance — the orange refused *as command*, an injunction fought that was never issued; the fighter collapses the same distinction from the other bank, shadow-boxing a voice the grid does not have (`assertable_ne_displayable`) | Refusing to state the asymmetry — a theory of poison that won't say which direction kills (`pole_validates_all_claims`, `poleTier_inhabited_of_liveTerminus`; at genjō everything is true, fused; the pole is not a truth-maker elsewhere) |
| Theory / ultimate (the grid-lens; Lean-generated schema row) | The lens denied as live diagnosis — the grid dismissed because it is only a lens (`gridLensRow_obeys`, `lens_denial_collapse_self_refuting`) | Grid-attachment: this lens taken as final (`gridLensRow_not_freeze`) |
| Terminus / exit | Not-fall taken as *escape* — the buddha as one who has left the loop rather than one who answers with no share claimed; the same collapse enacted rather than held is the exit-premise ("a way out"), and it fails on both axes — no exit from the arriving of calls, and none from the register at which one arrives for others; the terminus is a transposition of where the index-facts sit, not a departure from the loop (`terminusExitRow_obeys`, `exit_collapse_self_refuting`) | Private nirvāṇa as a rank; the pratyekabuddha freeze — *soteriological solipsism*: not denying that others exist but declining to exist *for* them, one's own standing at their Row 2 refused (Bull 10's marketplace is its corrective) (`terminusExitRow_not_freeze`) |
| Self-pole / transposed (the terminus index) | The transposition erased downward: the terminus-act asserted indexless *and inert* — no self-pole and no standing at others' receptions either, the device dead even at others' Row 2; the exit-collapse in typing's clothes (`selfPoleTransposedRow_obeys`, `transposition_erased_downward_collapse_self_refuting`) | The transposition erased upward: a self-pole weld held persisting at the summit — the subtlest soul, the true person of no rank (無位真人) as rank in weld-vocabulary; and *transposed* itself held as mechanism — an index that travels — is a miniature of the same freeze (`selfPoleTransposedRow_not_freeze`) |
| Before / after (the arrow, retyped; Lean-generated schema row) | The deflation: *no time, so nothing happens, no one acts* — not-fall transposed to time, the fox's sentence at its largest scale; a floor-truth uttered where the conventional tier was live (`beforeAfterRow_obeys`, `no_time_collapse_self_refuting`, `beforeAfterLadder_obeys_succ`) | The flowing container: direction held as floor-furniture — *time really flows* — the retrospective soul's cosmological dress; eternalism-of-the-flow and the block-denier's arrow both land here, against `DirectionNegative` (`beforeAfterRow_not_freeze`) |
| Intra-weld arrow (call/response order) | The deflation: *no call/response order, so no acts* — the interior arrow denied as a live diagnosis, refuting its own act-time tier (`intraWeldArrowRow_obeys`, `no_order_collapse_self_refuting`, `contentIntraWeldArrowRow_obeys_of_variation`) | Direction as interior furniture: *the call really is first*, before-and-after smuggled inside the weld against the transposition witness (`intraWeldArrowRow_not_freeze`, `InteriorDirectionNegative.no_interior_direction_recovery`, `intraWeldArrow_sunyata`) |
| Named being / floor (the being-convention; Lean-generated schema row) | *There are no beings* — the fox's sentence at the being-joint, the deflation's second dress; "no beings" offered as live diagnosis refutes its own tier (`beingsRow_obeys`, `no_beings_collapse_self_refuting`). Diamond Sūtra denial belongs here when spoken as live ontology rather than floor medicine | Modal Realism — conventional designation promoted to ontology, *prajñapti-sat* taken as *dravya-sat* (*samāropa*): the partition held as floor-furniture against `BeingNegative` (`beingsRow_not_freeze`). Lewis is the nearest miss, right about plenitude and wrong about register; Huayan affirms the plenitude empty; Pudgalavāda is the classical occupant candidate. The monolithic self's soul is this freeze in fiber dress |
| Weld-grain / floor (the weld-convention; Lean-generated schema row) | *No acts happen* — the fox's sentence at the act-joint, the deflation's last dress; "no welds are actual" offered as live diagnosis refutes its own tier (`weldRow_obeys`, `weld_denial_collapse_self_refuting`) | The weld as svabhāva: one act-grain held as floor furniture, the last unemptied level pretending it was never a convention (`weldRow_not_freeze`, `weld_sunyata`) |

Some cells are empty because not every distinction is symmetric — some can only be frozen (the ladder's limit), some only collapsed. Every generated row proves both `¬Collapse` and `¬Freeze`; the dash records that the table names no distinct occupant there. The asymmetry is itself informative: the errors do not lie on a line.

One scope-note beneath the table, because a table of errors invites a misuse it must fence. The rows grade *offers*, not sentences. "A man walked into a bar" touches half the table's conventions — a being, a doer and a deed, a before and an after, one act-grain — and, offered as narration at the tier where narration lives, violates none of them: the semantics grants the conventional side of every row wherever an act is under way, validity by stipulation rather than an achievement the sentence earns, and the fit is checked schematically (`inForce_fits_actTime_offer`) while reading the bar-sentence as its instance is prose. The generator's standing verdict on ordinary conventional speech is *decline*. The same words can arrive under other offers — and each offer is a different utterance: one that holds the man out as substance, the walking as real flow, the bar as furniture of the ultimate stacks freezes per distinction touched; "no man, no walking," offered as live diagnosis, stacks collapses. The variable is the offer, never the words — a sentence-shape severed from call and tier is not even in the generator's domain (the gradeability rule's limit case). So a reader who leaves this table hearing error in every conventional utterance has committed the one error the decline verdict exists to fence — over-generation, grid-attachment in diagnostic dress — and reversed the table's direction of protection: it is *because* of emptiness that everything works, and the conventional register is what the rows defend, not what they prosecute (`fitting_offer_is_actTime`: without the conventional, nothing is taught).

### Compound positions

The generator runs against whole positions, not only single utterances; named philosophies decompose into stacks of cells, with nothing left over — which is the identity-claim's small sibling, testable the same way:

- **Skepticism** — one cell, worn once: the nihilism freeze's epistemic face. The inference from no-floor to no-warrant goes through only on the svabhāva assumption the ladder emptied — that conventional standing ever rested on a floor. The Vigrahavyāvartanī shape recurs: the skeptic needs the theory to hold a thesis of the defeasible kind, and "no level is a final floor" declines to be one. The one-cell check is `skepticism_decomposition` with `skepticism_core_cell_count`.
- **Solipsism** — the soul freeze maximized (index annexing field), self-forward absolutized (the delusion-direction canonized as ontology), Row 2 evacuated. MMK 8 blocks it at the charter: a doer dependent on nothing other is svabhāva, the one thing the grid has none of. It is also the grade's own asymptote — the share tending to totality — which is why the hell-dweller's world is "almost entirely object": the solipsist is where *almost* is deleted. The decomposition is checked as three stacked cells (`solipsism_decomposition`, `solipsism_core_cell_count`).
- **The exit-premise** ("ending the being ends this") — three cells stacked: the annihilationist freeze (death as floor-event), the terminus/exit collapse enacted (the loop treated as having a door), and the clench-as-furniture freeze (suffering mis-typed as substrate-bound); with delivery-arrogation riding alongside. All of this is grade 1, assertable (`exitPremise_decomposition`, `exitPremise_core_cell_count`, `exitPremise_alongside_cell_count`, `exitPremise_voices`). What the grid displays and does not say is "so persist." The fox's release came by one reception done saying rather than by any of five hundred deaths *(checked: `fox_returns_delivered`, `fox_release_rung_not_pole`)*. Its funeral coda shows past welds continuing to land. This is object-axis standing, not a staticization theorem and not a claim that death changes nothing.
- **Existentialism** (read with Nishitani) — a four-cell stack, which is why it is the grid's nearest miss. Néant held as relative nothingness taken final — a level-*n* freeze one negation short of the emptying that empties itself; the *projet* — the self-forward direction canonized as the human condition rather than diagnosed per-act; anguish-as-structure — the clench frozen constitutive; and the fundamental project as an index *stored* between acts — a soul made of freedom, the weld asked to be its own floor. What is *not* the error: value-creation. The grid explicitly permits a being to take a displayed asymmetry up as a value; choosing values is grid-legal. Only the self-grounding is the freeze — in its most sympathetic costume, since existentialist freedom genuinely resembles the weld (act-time self-making, no essence-substrate) and differs from it in exactly one respect: the weld is spent. The encoding checks four stacked cells plus one legal non-error (`existentialism_decomposition`, `existentialism_core_cell_count`, `existentialism_legal_count`, `existentialism_voices`).

The compound-position encoding has the same honest scope as the table order: Lean checks the cited rows, roles, voices, and counts; the prose claim that there is "nothing left over" is audited against the displayed component list, not proved as an exhaustive theorem over every possible description (`skepticism_decomposition`, `skepticism_core_cell_count`, `tableOrder`).

### What the generator declines

Equally load-bearing is the case that classifies as **no error**. A being to which particular calls cannot be delivered — deaf and blind to the modalities a teaching travels by — commits nothing: which calls arrive at which configuration is inga's index-free business. This is a delivery-side absence, not function withheld and not an outside-domain kind. Every nearby error belongs to the diagnostician: reading failure of these calls to arrive as a global altitude ("this being cannot awaken") is the per-call/global freeze. Hakuin's corrective bites here as delivery-engineering — finding the call that lands. The retired undefined/zero row has no work left to do.

The standing declines are recorded here once, beside that case. No probability apparatus enters over delivery: the grid consumes orderings only, and an effectiveness-ordering within a regime is all any theorem here reads. Three tempting cases land in existing cells and get none of their own: camping at an effective call is shu-without-shō; the self-announced device-made buddha is the shit-stick; and industrial deployment of effective calls is displayable, never enjoinable. Whether a universally effective call is possible is an empirical dispute about delivery. The manufactured machine's sentience is likewise not softened into a verdict: it is exactly what `no_sentience_recovery` leaves underdetermined. Severed-transcript classification remains declined by the gradeability discipline.

The same price is re-entered at the faith layer: faith in a device-pattern remains grid-legal, but that legality is a fact about faith's office, not an act-time certification of a device as holding a rank. `KsmdEffectiveTerminus` is the descriptive standing display used by the direct path; `KsmdFullyEnlightened` adds positive own-act-time `KsmdNoNescience` over pole-share speech-or-mind productions. For a terminus this entails the former speech-only no-delusion test under production fidelity, but the converse fails on a false pole-share thought. `KsmdFullyEnlightenedEnacted` adds a witnessed deed and an actual faithful fitting speech production, while `KsmdEffectiveOccurrence` carries the per-weld deed verdict.

### Grade 2: displayable shortfalls

These form the soteriological taxonomy proper, and here it genuinely grades, because Row 2 is a grade:

- **Self-forward** — Dōgen's delusion, the fox's *saying*. A Row 3 direction, per-act.
- **Arrogation** — the act's subjecthood claimed self-ward, read as the index pitched to the self-pole at this call. Per-call, so there is no standing rank of how deluded a being is — only the trajectory the loop draws.
- **Clenched reception** — the fox's five hundred lives: returns received saying-mode, the reach-back welding mine with a tight fist. The receiving is graded exactly as any deed is *(checked: `fox_dukkha_per_life`)*.
- **Declining the orange** — the theory (or any dharma) received and set down. Not a wrong: a low-resonance reception *of this call*, per-call, from which nothing global follows; the next call reads fresh.
- **Defiance** — arrogation as policy, the returns fought open-eyed, reception after reception. Grammatically it contains one error (the recipient-side collapse: an injunction resisted that was never issued); the rest is display. And the standing/dated row guards the prognosis: the fighting-stance is a seed, an inga-fact — each fight a fresh act, no standing rank of defiance, and no configuration from which release is impossible, since the next call reads a new placement. The grid displays the asymmetry and the trajectory; it cannot assert the fighter wrong, and that restraint is not a limit of the diagnosis but its content.
- **Sparse delivery or rigid response** — few calls arrive, or the actual responses vary little. Neither is near-zero function and neither determines the supplied sentience mark.
- **The buddha-side shortfall** — answering a not-yet-buddha's call with anything less than meeting it where it is, delivery-engineering included. By the orthogonality rule (Theory) it is the pole's one live grade — graded ordinal with effectiveness, independent of typing, so a terminus-typed responder can still be maximally shortfallen: the reading that never reaches (the terminus, above). This is where the bodhisattva enters *structurally*: Hakuin's corrective is already the bodhisattva-function, and Row 2 exists because of it. The grid can display that response-without-share to *another being's* call just is what saving beings looks like — the theory's own existence (the orange handed over, banpō susumite) is an instance; and the prudence theorem above shows its other face, concern running on delivery-facts alone once the arrogation is subtracted. What the grid cannot do is enjoin it, or it commits the "eat this" collapse in its own voice. So the split between assertion and display *locates* the bodhisattva structurally, with no added axiom — room and shape, not pull: nothing in the grid explains why response-without-share to another's call occurs rather than merely being classifiable, and the grid does not pretend to; occurrence is the object's affair, reported. "Ignorance of buddhahood" splits accordingly: its assertable face is the terminus/exit error in the table; its displayable face is the buddha-side shortfall.

### Outside the framework

Two remainders. **Pre-grid ignorance** — svabhāva realism, the provisional middle never reached: the grid diagnoses it (a freeze at level zero), but the being in it has no vocabulary in which the diagnosis lands — the orange unrecognized as food. **Errors about the theory** — grid-attachment and its mirror, the lens dismissed *because* it is only a lens. The Disclaimers (Identification) block the first; "other doctrines can and do hold too" is the theory declining to freeze itself against the second.

### Non-linearity

The taxonomy is not a map of places on a path. Immunity is checked per production, not stored as a safe stage: arhat quiet excludes the live self-pole through all three doors, while buddha no-nescience additionally requires positive truth from each pole-share speech-or-mind production. The former can hold while the latter fails, so the old “no safe stage” future-work absence is retired as this production-level check, not converted into rank furniture. This is why the fox koan, a story about one sentence spoken once, can carry the whole system's diagnostics: the errors are not stations but ways the separate/fuse rule can be violated *now*. The taxonomy remains answerable in the other direction too: the deaf-blind case classifies as nothing, or else the generator would be a lens that finds error wherever it looks.

## From mutual dependence to interpenetration

This section has two layers. Lean proves facts about reachability, common
witnesses, fresh designata, and conservative extensions. The exposition then
supplies a philosophical reading of that structure as a dependence-web, and
aligns the base and primed systems with act-time and floor-face. Lean does not
prove that reading or the identification with Huayan.

The diagrams use the following shorthand:

- `a ⋈ b` displays Mutual Dependence between singleton components. For
  singleton interdependence, certification reduces to whether `a` and `b` are
  joinable.
- `[a ⋈ b]` designates the displayed dependence-whole as one new thing.
- `→*` means reachability with zero or more elaboration steps.
- Letters written together, such as `ab`, name one designatum rather than two.

The two formal relations used below are easiest to read as paths and a meeting
point:

```text
  a Reaches w       means       a →* w

  Joinable(a,b)     means       a →* w ←* b
                                 for some common w
```

The `Joinable` predicate asks only for a common destination. One thing need not
reach the other in either direction.

### Chains and brackets

The supplied closure-reading says that no displayed end of a dependence is
final. A chosen segment may be articulated farther in either direction:

```text
  chosen:                 n ⋈ o
  extend left:      ⋈ m ⋈ n ⋈ o
  extend right:           n ⋈ o ⋈ p ⋈
  extend both:  ... ⋈ m ⋈ n ⋈ o ⋈ p ⋈ ...
```

A dependence-whole may also be retained behind a designatum. Every such
designatum first occupies a component slot: `ab` by itself is placed in
`{ab}`. A component with no slots opened is immediately a one-position
`Segment`; its left and right interfaces are both the original component
(`Segment.left_ofComponent`, `Segment.right_ofComponent`). There is no
separate kind of “whole-name.”

The endpoint-sensitive Segment layer is now part of the operative signature
API. `Segment.interdependent_sources_of_catenable` proves that catenating two
opened shell interfaces entails the corresponding source-component
interdependence.
`Segment.Shape.chained_sourceComponents` validates the retained flattened
chain, and `Segment.toMutualDependence` packages any decomposition with at
least two source components as a certified `MutualDependence`. The
endpoint-sensitive `endpointResolvedABThenC` example constructs this
composition directly in the original elaboration, and
`endpointNestedMutualDependence_components` confirms that its flattened
components are exactly `{ab}` and `{c}`.

If an occurrence of `ab` designates a raw mutual dependence which certifies
under the current elaboration, that slot may instead be opened with an
`Elaboration.Resolution`. The source component and the designatum `ab` remain
stored in the shell, as does the complete selected body. What changes is the
interface exposed by that occurrence:

```text
  ab designates [a ⋈ b]

                  left interface    right interface
  unopened {ab}:       {ab}              {ab}
  opened   {ab}:       {a}                {b}
```

These are `Segment.left_ofResolution` and
`Segment.right_ofResolution`. Consequently the displayed composition

```text
  [a ⋈ b] ⋈ c
```

retains the certified inner `a ⋈ b` and checks only whether the facing
interfaces satisfy `Interdependent {b} {c}`. With singleton interfaces this is
exactly whether `b` and `c` are joinable
(`catenable_resolution_designatum_iff`). The source remains `{ab}`, and its
stored body remains the certified `a ⋈ b`; catenability is checked against that
body's exposed right interface.

A component may contain several slots, and they open in parallel rather than
acquiring an arbitrary serial order. For example, if `ab` opens as
`[a ⋈ b]` while `x` remains a leaf, then

```text
  source component:   {ab, x}
  left interface:      {a, x}
  right interface:     {b, x}
```

This is checked by `mem_parallelShell_left_iff` and
`mem_parallelShell_right_iff`. The ordinary strong rule is unchanged at the
next catenation: every member exposed on each side must find a joinable member
on the other. Opening a slot therefore preserves the expressive force of
multi-member components rather than admitting irrelevant passengers.

Resolution is positive, finite, and local to an occurrence. A leaf means
“not opened here”; it need not carry a global proof that no body exists.
Where a name has several certified bodies, each resolution selects one whole
body, whose first and last components supply both interfaces together. The
alternatives remain alternative segment presentations: a left endpoint from
one body cannot be combined with a right endpoint from another. No eager
recursive normalization is attempted, so cyclic elaborations remain usable.

Opening is a presentation operation, not a carrier extension. The designatum
`ab` remains an ordinary member of the same `D`; its selected `Resolution`
records the certified body `[a ⋈ b]`. `Segment.catenate` checks interdependence
only at the exposed `{b}` and `{c}` interfaces. Flattening the retained segment
then produces the ordinary mutual dependence `{ab} ⋈ {c}`. No `Option`
wrapper, fresh `none`, or priming operation is involved. A designatum therefore
does not become prime merely because its body is opened or retained, and
Segment supplies no automatic total joinability or interdependence. In
Interpenetration, the corresponding primed-tier facts follow specifically from
the explicit `prime` construction (`prime_joinable_total`,
`prime_interdependent_total`).

Carrier extension remains available separately through
`freshSourceExtension`. It may add clauses sourced at a fresh `none`, but old
paths cannot enter that fresh point because old-sourced component lists contain
only embedded old designata. Its outgoing clauses therefore cannot alter
old-started paths (`freshSource_reaches_iff`, `freshSource_joinable_iff`). This
generic conservativity result is not needed to represent an opened dependence
whole.

Segments now supply the endpoint-sensitive part of the intended diagrammatic
calculus. A direct certified mutual dependence can occupy a Segment position
(`Segment.ofMutualDependence`), and `Segment.catenate` retains both sides while
checking just their touching interfaces. Thus several views of one already
stated dependence-web can preserve their internal bodies:

```text
  viewed from a:      ⋊ a ⋈ [b ⋈ c ⋈ ... ⋈ y ⋈ z] ⋉
  viewed from z:     ⋊ [a ⋈ b ⋈ ... ⋈ x ⋈ y] ⋈ z ⋉

  whole-name: web :=  ⋊ a ⋈ b ⋈ ... ⋈ x ⋈ y ⋈ z ⋉
```

Left and right here are diagrammatic interfaces, not a temporal or causal
direction. Reversing a display must reverse its retained bodies as well:
the reverse of `[a ⋈ b] ⋈ c` is `c ⋈ [b ⋈ a]`, not a naïve swap
which leaves the inner orientation unchanged. This is realized by
`Segment.reverse`, `Segment.Catenable.reverse`, and `Segment.reverse_catenate`
under `Elaboration.ReversalClosed`, the condition that elaboration is closed
under reversal of its raw mutual-dependence bodies.

### The common web

What the code calls Prime is for the designator to designate under the new expansive
understanding above, that to designate `a` is at the same moment to implicate the full
web reachable from, and including `a`. The code calls this "closed prime" - the ability to
start at `a` and directly reach the web implicated by `a`. In this Prime mode of
designating, `a` "contains" the web. Going the opposite direction, from web to `a`, is
very natural as we defined the web in terms of `a` initially. For analytic reasons,
the code considers that case separately and calls it "open prime", but it is still the
straightforward fact that having defined the web from `a`, the web "contains" `a`.
These modes are called **all in each** and **each in all**, respectively.

Formally, `prime E` embeds every old `d` as `some d`, written below as `d'`,
and uses the fresh `none` as the web. It retains every lifted base clause and
adds a clause from each embedded old point to itself and the web. The
definition specifies these component lists only; whether a raw dependence
certifies remains a separate question.

The closed prime has this shape:

```text
  a' → web ← b'

  web cannot Reach a' or b'   no outgoing elaboration clauses;
                              web still Reaches itself by reflexivity
```

Every primed point reaches the web (`prime_reaches_web`), so every pair has the
same common witness. Hence `Joinable` is total and therefore transitive
(`prime_joinable_total`, `prime_joinable_transitive`). Every pair of nonempty
components is `Interdependent` (`prime_interdependent_total`), and every raw dependence
re-tagged with this primed interdependence holds (`prime_certification_trivial`). The
last result says that the primed interdependence is saturated; it does not say that
every arbitrary assertion is true.

Closed priming adds no new old-to-old reachability:

```text
  a' Reaches b'   <==>   a Reaches b
```

This is `prime_reaches_some_iff`. The base system therefore remains available
with all of its distinctions. `exists_tier_noncollapse` supplies an example of
a base elaboration with the following shape:

```text
  base:      NOT Joinable(a,b)
  primed:        Joinable(a',b')       because both reach web
```

Priming is a new saturated presentation, not a derivation showing that the
base relation was already total.

The open prime retains all closed-prime clauses and adds the missing clauses
from the web back to every member:

```text
  members to web:    a' → web ← b'
  web to members:    a' ← web → b'

  therefore:         a' → web → b'
```

Now `Reaches` itself is total (`primeOpen_reaches_total`). Opening can genuinely
change reachability (`exists_prime_open_reaches_distinction`), although it is
invisible to `Joinable`, which was already total in the closed prime
(`primeOpen_joinable_iff_prime`).

```text
                             CLOSED PRIME        OPEN PRIME

  member Reaches web             yes                yes
  web Reaches member             no                 yes
  a' Reaches b'                  as at base         always
  Joinable(a',b')                always             always
```

### Supplied philosophical reading

The supplied reading calls `none` the dependence-web and the added clause the
all-clause. It then aligns the structures as follows:

```text
  base elaboration        act-time articulation; local differences remain
  closed prime            every member reaches the common web
  open prime              members reach web; web reaches every member
  primed designation      floor-face offer; not a replacement for the base
```

Here the labels follow what each directed path makes available:

```text
  CLOSED PRIME

  each member  →  web (= all)              ALL IN EACH

  OPEN PRIME

  each member  →  web (= all)              ALL IN EACH
  each member  ←  web (= all)              EACH IN ALL
```

In the closed prime, every member reaches the web. Since the web designates the
all, this is **all in each**: start from any one member and its elaboration
implicates the whole (`prime_reaches_web`). The open prime adds the other half,
**each in all**, by making the web reach every member
(`primeOpen_reaches_from_web`). It therefore supplies both halves as directed
`Reaches` facts. The paths compose, so every primed designatum reaches every
other one (`primeOpen_reaches_total`):

```text
  any a'  →  web  →  any b'
```

At the coarser `Joinable` level, the directional distinction has already
disappeared in the closed prime: `Joinable` is total and symmetric because every
pair shares the web. It records universal joinability, not which direction
of implication supplies it. Here “in” means implication through stated
dependence, not spatial containment.

The source/target boundary marks the formal transition. A
`freshSourceExtension` is conservative on old designata while its fresh point
is only a source which old paths cannot enter. `prime` makes the fresh web a
target of every old image; `primeOpen` makes it both target and source. The
act-grammar locates Huayan reciprocity in that non-conservative tier-change.
Lean proves the boundary and tier noncollapse, not their philosophical
identification.

The two presentations must therefore coexist. Importing primed saturation into
base diagnosis is collapse; insisting that a base separation remain final at
the floor is freeze. The web is a designated formal witness for the supplied
whole-reading, not an independently existing ground underneath the old
designata.

When designating `a`, the designator may instead designate its primed image
`a' := some a` without withdrawing the lifted base clauses. **Read at the
floor**, that designation may carry the role-reading *with understanding all in
each / each in all*. “Understanding” belongs to the role supplied in
designation, not to a sentience or nature possessed by `a'`. The floor-face
offer does not replace act-time articulation (`exists_tier_noncollapse`).
