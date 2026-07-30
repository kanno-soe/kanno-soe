# Kannō-Sōe Mutual Dependence — I. Theory

*An axiomatic reconstruction of Zen sayings in an ontology-under-erasure act-grammar. First of three files: **Theory** (this file), **Theorems**, **Identification**. Cross-references to the companion files are marked (Theorems) and (Identification).*

## Abstract

*Kannō-Sōe Mutual Dependence* (*KSMD*; formerly *Weld and Arrow*) is an **axiomatic reconstruction** of the Zen masters' sayings about karma, action, suffering, and awakening. A small signature of primitives — a field that carries every diachronic connection without an owner, and welds, single occurrences of answering a call, at which every index is made, spent, and never stored — is fixed in the Signature layer, and the tradition's sayings are recovered as its consequences. The development is Lean-first and exposited in prose, under one governing posit: **everything diachronic belongs to the field; every index is enacted and nothing indexed is stored; karma names this loop.**

From the fixed generator — one rule, separate under act-time diagnosis and fuse at the floor — the error-taxonomy falls out as collapse/freeze pairs. The *catalogue* of positions the generator is run against is curated in the Consequences layer and grows as new targets are identified; the generating rule in the Signature does not move. The doctrinal cases — the fox koan, the three killings, other-power, pariṇāmanā, the Ten Bulls, the Five Ranks — are **tests the reconstruction must pass**, not premises it is built from.

What Lean establishes is **internal consistency and derivability**, not exclusivity: given the primitives the consequences follow, each reading is gated by a sibling countermodel, and no theorem depends on an added axiom. It is not shown — and Lean cannot show — that this is the only coherent reconstruction of karma. KSMD is one definition among many; the signature deliberately declines to privilege its own choices (no top pole, no privileged person-partition, scalar and direction as display), and other doctrines can and do hold too.

The scope is bounded and the boundary is marked as data. The *grammar* of ownerless continuation is in scope and derived — continuity without a transmigrating bearer, the flame passed without a self to carry it. The *cosmology* of rebirth — persistence across biological death, the realms, the mechanism — is ceded as a world-fact. So is the phenomenal attribution: sentience is supplied per weld and is never recovered from response, share, clench, or delivery. Throughout, what the system asserts is grammar; what it can only display is worth — no value appears in its own voice. This is a fresh reconstruction, not an exegesis of Abhidharma nor of Dōgen; the lens is minimalist by design.

The layered library — Signature → Consequences → Doctrines → Identification → Meta → Exposition — keeps the Signature as axioms and the later layers as consequences and tests. Its non-storage claim is architectural — `Config` has no owner-typed slot — and checked at the level of definability: whole-carrier relabelling acts trivially on configurations and commutes with `rePitch` (`Config.relabel_fixed`, `Grid.relabel_rePitch`), while no equivariant recovery exists (`Grid.no_natural_agent_recovery_from_config`). This is not a blanket information-flow claim: cetanā requires grading to depend on the occurrence, and a model's stored tendency may therefore reveal a register number encoded by that occurrence (`ConfigLeakWitness.registerClock_config_recovers_agent`). The value remains a grade in the field register; what is never stored is the designatum *as index*. Every reading is gated by a sibling countermodel, and the taxonomy's rows and verdict history are inspectable data.

## What the V2 formal model is

The project implements a deliberately simplified model for discussing Mahayana Buddhist metaphysics. It is most useful for conditional and independence results: *if* one accepts the model's translation of a claim, a proof can show that the translated claim needs no richer machinery. The conditional matters. Oversimplifying the object proves something about the simplification, not automatically about Buddhism, Nāgārjuna, Jizang, or the world. The account below therefore marks three statuses throughout: **formal V2 structure**, **a manually supplied interpretation**, and **the philosophical act-grammar laid over that structure**.

### The formal core: designata, elaboration, and Mutual Dependence

A **designatum** is simply something the model can designate. V2 does not first divide designata into people, objects, events, thoughts, or times. A **component** is a nonempty group of designata. An **elaboration** is a relation saying that a designatum may be expanded into a raw Mutual Dependence; because it is a relation rather than a function, one designatum may have no stated elaboration, one elaboration, or several alternatives.

Elaboration induces **reach**. A designatum reaches itself, and it reaches anything occurring in any component of one of its elaborations; elaborations of those reached designata may then be followed again. Two designata are **related** when their reach-trees have some designatum in common:

```text
                           +--> p --+
                          /         |
    designatum a --elaborates       +--> common witness w
                          \         |
                           +--> q --+

    designatum b --elaborates --> r ----> common witness w

    Related(a,b)  :=  there is some w reached from both a and b
```

This relatedness is reflexive and symmetric, but V2 expressly shows that it need not be transitive. A linkage between two components is stronger than finding one attractive pair: every designatum in the first component must have a related partner in the second, and every designatum in the second must have a related partner in the first.

```text
    component C                         component D
    +---------+                         +---------+
    | c1      | ---- related partner -> | d?      |
    | c2      | ---- related partner -> | d?      |
    | c?      | <- related partner ---- | d1      |
    | ...     |                         | ...     |
    +---------+                         +---------+

    Linked(C,D) requires coverage in both directions.
```

A raw Mutual Dependence is a list of at least two components carrying one such symmetric linkage. A certified **Mutual Dependence** adds the proof that every adjacent pair is linked:

```text
    C1 <--> C2 <--> C3 <--> ... <--> Cn

    required: Linked(Ci, C(i+1)) for every adjacent pair
    not required: a temporal order, a causal arrow, or direct C1/Cn linkage
```

The chain may be any finite length. It can be sliced and compatible chains can be joined, but the word *chain* must not smuggle in time: these arrows display symmetric linkage, not before and after. This is the minimal formal structure of **Mutual Dependence** (*sōe*) used by V2. Throughout, that structure is read as **mujishō-sōe**: mutual dependence without-own-being (*mujishō*), in which neither side supplies a self-standing substrate for the other.

### Resonance as a Mutual Dependence

A **Resonance** is the following four-component special case of Mutual Dependence, with its middle components forced to be singletons:

```text
    calls <--> {b1} <--> {b2} <--> responses
```

The intended reading is that `b1` is the receiving view or moment of a being and `b2` is its responding view or moment. Formally, however, `b1` and `b2` are two designata joined in the same certified dependence. V2 does not prove that they are numerically identical, temporally successive, conscious, or personal. The names **calls**, **receiving**, **responding**, and **responses** are role-readings of the shape.

An **Encounter** is a Resonance viewed merely as a Mutual Dependence. It retains the concrete `calls--b1--b2--responses` shape while everything about it being a resonance is temporarily forgotten. *Encounter* is an expository alias, not a new Lean type. Every Encounter is a Mutual Dependence; not every Mutual Dependence has the four-component singleton-middle shape needed to be an Encounter.

Because designata may elaborate into any raw dependence the modeler supplies and later certifies, the same Resonance shape can be used for a person answering a question or a stone answering the wind by rolling downhill:

```text
    {wind} <--> {stone-receiving} <--> {stone-responding} <--> {rolling}
```

Nothing in the ungraded structure privileges the person. Nor does the stone example prove a doctrine about sentience: it proves only that the Resonance constructor asks for linked designata, not a prior metaphysical kind called *person*.

### Graded Resonance and Being

A **Graded Resonance** adds two independent grades to a Resonance: a calls-side grade and a responses-side grade. The grade type need only be a preorder with a bottom element. It need not be numerical, total, or metrically spaced. The intended reading is **dis-resonance**: volition insofar as it is *sāsrava*—with outflows, ripening in further becoming. Bottom is *anāsrava* at this Resonance: the act is not productive of further becoming, without implying either the absence of volition or the global attainment of arhatship. `0` is only the familiar numerical example.

```text
                       one Graded Resonance

    calls --[callsGrade]--> b1 <--> b2 --[responsesGrade]--> responses

    callsGrade and responsesGrade are independent coordinates.
```

Thus a stone may be *assigned* bottom on both sides, while a grumpy person who has stubbed a toe may be *assigned* a non-bottom calls grade, a non-bottom responses grade, or both. Those are interpretations supplied to the model; V2 does not infer a grade from stonehood, pain, personality, or behavior. `IsUngraded` means exactly that both grades are bottom. “Ungraded” here therefore means no dis-resonance entered on either side, not absence from the Resonance and not absence of response.

A **Being** is a nonempty list of Resonances whose singleton middle components flatten into one certified Mutual Dependence:

```text
      Resonance 1       Resonance 2                Resonance n
      b1 <--> b2  <-->  b1 <--> b2  <--> ... <-->  b1 <--> b2

    Being = the certified linkage of these receiving/responding moments
```

The calls and responses surrounding each Resonance do not constitute the Being's formal spine; its `b1,b2,...` middle moments do. This is a conventional construction of a being out of linked moments, not a proof of a persisting owner behind them.

### Direction and Causation are overlays

Mutual Dependence and Resonance contain no time-directedness. A **Directed** interpretation is supplied separately as a strict transitive **Before** relation. A domain may then supply a **Causal** interpretation with a `Causes(x,y)` relation, a proof that causing implies `Before`, and, for every causal claim, a **Causation** certificate.

That certificate is itself just another Mutual Dependence in a precise and limited sense: it exhibits some certified Mutual Dependence whose first component contains `x` and whose last component contains `y`.

```text
    dependence certificate:   {x,...} <--> ... <--> {...,y}
    directed overlay:          x ----------------------> y
    causal assertion:          Causes(x,y)

    Causes(x,y)  =>  Before(x,y)
    Causes(x,y)  =>  a Mutual Dependence joins endpoint-components
```

Forgetting the causal and temporal overlays leaves the underlying Mutual Dependence; adding the overlays is additional data. Therefore V2 does **not** say that every Mutual Dependence is causal, that symmetric linkage secretly points from cause to effect, or that every `Before` fact is causal. Causation as another Mutual Dependence names the certified dependence-skeleton of a causal claim, not a reduction of causality to symmetry.

Accordingly, **mujishō-sōe** is the dependence-structure retained when either grading or the causal and directional overlays are forgotten.

### From empty dependence to the provisional middle

Remove grades from a Graded Resonance and everything else about it being a resonance and the Mutual Dependence remains. That remainder does not by itself prove a Buddhist metaphysics. The philosophical bridge begins when the act-grammar reads it as **mujishō-sōe**: mutual dependence under the condition of no own-being.

*Mujishō* (無自性) means without self-nature or own-being. V2's certified linkage is a deliberately small formal analogue: neither linked component is entered as the self-standing base of the other. This is an **interpretation of** Mutual Dependence, not a theorem extracted from `Linked`; supplied elaborations can encode many domains, and Lean does not turn a symmetric reach relation into Nāgārjuna by itself.

The interpretive route begins with Nāgārjuna's *MMK* 24.18: what dependently originates is empty of own-being; that emptiness is itself dependently designated; just this is the middle way. Dependence therefore cannot mean relations among already self-subsisting things, while emptiness cannot become a deeper thing beneath them. Applied to the Encounter above, the point is not that `calls`, `b1`, `b2`, and `responses` vanish. It is that none supplies the final bearer of the answering.

Jizang supplies the next turn. In the fourfold two truths, each stated ultimate—including the conventional/ultimate distinction itself—can become the conventional content of the next analysis. The iteration does not discover a fifth, finally unconditioned proposition. It ends at 言忘慮絶: not another claim, but the place where words and thought no longer do separating work. The manuscript calls that claimless place the **floor**. The middle can then manifest as this case instead of becoming another object of analysis. The manuscript calls this manifestation the **provisional middle**.

The first pair can now be shown by itself:

| Row | Dependence reading | Enactment reading |
|---|---|---|
| 1 | **mujishō-sōe** — Mutual Dependence without own-being | **genjō** — the dependence manifesting as this case |

The **dependence-face** names the relation retained when additions are forgotten; the **enactment-face** names how that relation comes forward as a case. Mujishō-sōe is therefore the dependence-face of Row 1: this Encounter has no self-standing substrate. Genjō is its enactment-face: that empty dependence nevertheless manifests as this call, this receiving, this response. *Provisional* does not mean half-real or merely hypothetical. It says that the case is concrete without being promoted into a final ground. The move from Jizang's recursive discipline to *genjō* is the reconstruction's move into Dōgen's vocabulary, not a claim that Jizang himself supplied this grid.

### From no rank to practice-realization

Genjō answers how groundless dependence comes forward as a case.

Linji supplies its guard-image. The reconstruction reads 無位真人 along a seam: 無位, *no rank*, is non-attainment; 真人…出入, the true person going in and out through the face-gates, prevents no-rank from becoming inert; the whole figure holds no-rank and activity together. When the monk tries to identify the true person as something one could grasp, Linji's rebuff blocks precisely the resting-place the phrase might otherwise invite. The manuscript calls this no-rank, no-resting-place reading the **non-attaining middle**, or the **unattaining middle** when the emphasis falls on nothing being obtained or stored.

The reconstruction states that reading in Dōgen's vocabulary. **Shu** (修) is practice, the concrete doing. **Shō** (証) is realization: the non-attaining floor-face at a bottom placement in any given grading, read here under the governing *mujishō* condition—no own-being, no rank, nothing possessed.

On this sentience-neutral reading, shō gains determinate content through a contrast within practice. At a bottom placement, practice has its shō face: the act's subject-position is ceded, with nothing in the doing answering to a self-pole. At a non-bottom placement, that same practice is delusive to the extent that it arrogates the subject-position. This does not identify shō with 悟 (*satori*); it gives the non-attaining floor-face its grading counterpart. Genjō has no corresponding delusion term: its contrast is empty dependence versus manifestation, not non-bottom versus bottom placement.

The homophone matters: the *shō* in *mujishō* is 性, nature, while the **shō** in *shushō* is 証, realization. The argument relates them—a realization governed by the no-own-being reading—but they are neither the same word nor two pieces waiting to be joined.

**Shushō** (修証) says practice-realization; **shushō-ittō** says that its practice and realization are non-dual. On this reconstruction, that cannot mean two events—practice first and an attained realization later—nor a still shō somehow acting by itself. It means one bottom-placed Graded Resonance read in its doing and in its non-attaining realization:

```text
                     one bottom-placed Graded Resonance

   practice, the doing (shu) ---- shushō ---- (shō) realization without rank

                        shushō-ittō: not two events
```

The two middles can now be distinguished without making either mysterious. **Genjō**, the provisional middle, answers *how does empty dependence manifest as this case?* **Shō**, the non-attaining middle, answers *what is realization when no rank is acquired?* Manifestation is not possession of realization; realization is not a second activity alongside manifestation. Their distinction will remain live when the case is diagnosed, then lose its separating work at the floor and at genjō.

### Dōgen's sentence and the three-row grid

> *Carrying the self forward to practice-realize the myriad dharmas is delusion; the myriad dharmas advancing to practice-realize the self is satori. To study the way is to study the self; to study the self is to forget the self; to forget the self is to be verified by the myriad dharmas.*
— Eihei Dōgen, *Genjōkōan*

The three-row **act-grammar** can now be shown whole. Each row pairs a dependence-reading with an enactment-reading of one Resonance. The last column identifies the V2 structure used for the modelling:

| Row | Dependence reading | Enactment reading | V2 modelling |
|---|---|---|---|
| 1 | **mujishō-sōe** — Mutual Dependence without own-being | **genjō** — the dependence manifesting as this case | Mutual Dependence |
| 2 | **kannō-sōe** — responsive resonance placed under dis-resonance grading | **banpō susumite** — the myriad dharmas advancing, the being verified | Graded Resonance |
| 3 | **engi / inga** — dependent arising and cause/effect under an added direction | **shu** — practice, the concrete doing | Directed + Causal + Causation |

Read under the essay's title, the enactment cells pick out three aspects of the quoted passage: genjō is the actualizing of the case, banpō susumite is the dharmas advancing and the self being verified, and shu is the practice-realizing that occurs. These are not three events, three agents, or a chronology from Row 1 to Row 3. All concrete acting is Row 3: the one practice at act-time. Row 1 reads that act as manifestation without substrate; Row 2 reads it as this being's graded receiving and responding; Row 3 reads the doing under direction and causation. The passive 証せらるる fixes shō's grammar as the *being-verified* face, while Dōgen's 悟 (*satori*) remains the awakening named in the contrast and is not silently substituted for 証. Conversely, forgetting Row 3's overlays and Row 2's grades returns the Mutual Dependence with which the formal account began.

The compound vocabulary marks crossings among these readings. The equations below state the reconstruction's compositions, not historical etymologies:

- **genjōkōan** = genjō + kōan: Row 1 manifestation in a Row 2 particular case—this Resonance, this call, this being's capacity to listen.
- **shugenjō** = shu + genjō: Row 3 practice as Row 1 manifestation—a directed Resonance manifesting without a retained scaffold. This is the manuscript's compound, and the inclusion runs one way: practice run scaffold-free is genjō, but not every manifestation is practice.

### Floor-face and act-time face

The **floor** is not a first moment, a hidden base, or a final substance. It is the tier at which no deeper support is claimed and no distinction is doing separating work. A **floor-face** is this Encounter read under that no-own-being, no-claim condition. **Act-time** is the conventional diagnostic tier at which this call, this receiving, this response, this practice, and the distinctions needed to describe them are live. It is not a second Resonance before or after the floor-face.

The shushō reading introduced above is one example:

```text
                     one bottom-placed Graded Resonance

        act-time face                            floor-face

   concrete practice (shu) ---- shushō ---- (shō) no attainment,
   in receiving/responding                  the being-verified
```

At a bottom placement, the two readings meet without becoming two formal coordinates. Act-time follows the concrete receiving at `b1` or responding at `b2`; the floor-face reads that same middle without an independently standing receiver or responder. Shu and shō are reciprocal faces of that bottom-placed receiving or responding within the Graded Resonance: one name follows the enactment, the other its no-own-being, non-attaining realization. Bottom permits this reading; it does not manufacture or store a realized entity.

### Separate/fuse, utterances, and their offers

The **separate/fuse rule** states how distinctions behave across those tiers. At act-time a useful distinction separates. At the floor it fuses, meaning that it makes no separating claim there—not that its two sides become one substance and not that both propositions are asserted.

```text
                         distinction separates      distinction fuses
    act-time diagnosis   A | B   rule obeyed        A >< B  collapse
    floor / genjō        A || B  freeze              A . B   rule obeyed
```

The two error cells occupy one diagonal; the other diagonal is the rule obeyed. The rule says that distinctions fuse at **genjō** as well, but floor and genjō are not synonyms. *Floor* names the status of claims when no deeper support is asserted. *Genjō* names the manifested case at the provisional middle, where recursive emptying is no longer retained as a scaffold; it was introduced through the empty-dependence/manifestation pair, not through a delusion/realization pair. *Shō* is grading-relative: it names practice's non-attaining floor-face at bottom, against delusive practice at non-bottom. This is why genjō and shō must be distinguished under act-time diagnosis while their distinction itself ceases to separate at the floor and at genjō.

The two violations generate the error taxonomy in [Theorems.md](Theorems.md). **Collapse**, written `><`, is premature fusion under act-time diagnosis; **freeze**, written `||`, is a useful separation reified as a floor-claim. These are expository operators, not Lean syntax. “There is no time, no being, and no Resonance” is a collapse when offered where a response is occurring. A flowing time-container, substantial Being, stored shō, or self-existing Resonance is the corresponding kind of freeze.

An **utterance** here is not a sentence-shape in isolation. It is content carried by a resonance, with the call it answers and the tier at which it is offered. The taxonomy grades that offer, not the words alone: ordinary narration offered conventionally at act-time is declined as no error; the same words offered as ultimate furniture can freeze, while a denial offered as live diagnosis can collapse. Under another offer, the same words make another utterance; severed from call and tier, they remain quotable but ungradeable. The full scope fence is stated [beneath the taxonomy table](Theorems.md#a-taxonomy-of-error).

### V2 Summary

The model can now be restated densely without importing unexplained vocabulary. Designata elaborate; shared reach supplies relatedness; two-way coverage links components; adjacent linked components form Mutual Dependences. A Resonance is the four-component `calls--{b1}--{b2}--responses` case; viewed merely as a Mutual Dependence, it is called an Encounter. A Graded Resonance places independent dis-resonance grades at its calls and responses locations; bottom at both is `IsUngraded`. A Being links the middle receiving/responding designata of one or more Resonances. Direction is supplied as `Before`; Causation adds `Causes`, implies `Before`, and certifies its endpoints with another Mutual Dependence. The act-grammar reads this one structure through mujishō-sōe/genjō, kannō-sōe/banpō susumite, and engi/inga/shu. Shō is its non-attaining floor-face; shushō names the act-time and floor faces together. The taxonomy then asks whether a live distinction was collapsed (`><`) or a useful distinction was frozen (`||`).

## The rules, each preceded by what motivated it

The V2 bridge above fixed the formal handles and introduced the vocabulary in dependency order. This section now makes a second, source-led pass: it motivates each rule, then develops the soteriological readings that the compact V2 account deliberately left supplied.

### Not Nothing

Per Nishitani — absolute non-being is not a privative void, but beyond being/non-being distinction.

### Śūnyatā

Why not leave it at Nishitani? It would be a mistake of analysis: "beyond being/non-being" is itself a designation, and analysis, wherever applied, finds no own-being in its designatum — the ultimate included. Both of these findings are the Buddha's: the world empty of self (SN 35.85), and the middle between "it is" and "it is not" (SN 12.15). Per Nāgārjuna — deepening the emptiness from self to own-being, widening it to every dharma — whatever is dependently originated is emptiness, and that, being a dependent designation, is itself the middle path (*MMK* 24.18). And emptiness is not exempt from the analysis that produced it: śūnyatā, analysed, is empty (空空). Every stated ultimate is a prajñapti — a finding, not a caution.

### Provisionally-designated middle

Why not leave it at Nāgārjuna? Because 空空 stated once settles a fact but not a structure. "Emptiness is empty" is itself a designation, so the analysis applies again — and again — and nothing in a single application determines what the regress is: vicious, terminating at some fifth resting point, or benign. Per Jizang — the fourfold two truths (四重二諦) is the structure: one operation iterated, in which each level's stated ultimate — including the two-truths sorting itself — is, definitionally, the next level's conventional content; no level is a final floor; and the terminus is not a further negation but 言忘慮絶, the tier at which words do no separating work. The regress is uniform and benign — a checkable theorem. This is **genjō**, the provisional middle: manifestation, always going out into a particular case.

Distinct from it, and never equated with it, is the **non-attaining middle** at the floor. Read Linji's 無位真人 along its own seam: 無位 (no rank) is the floor-face — no metaphysical rank, anātman; 真人…出入 (the true person going in and out) is the *acting*; and the whole compound 無位真人 is the weld of the two — shushō-ittō, the true person going in and out. The non-attaining middle is the 無位 alone — **shō**: realization as anātman, agential only because welded, never a still attainment. It is *not* the whole true-person, which is the weld (reading 無位真人 as a rank one rests at is exactly the reification Linji shoves off as 乾屎橛 — the more common reading takes the shit-stick as shock-deflation of the *question* itself rather than of rank-reification specifically; the rank-reading is compatible with it and is the one used here). Two middles, then: genjō provisional, shō non-attaining. The system turns on keeping them apart — but *at act-time*, and by the same separate/fuse rule that governs everything here (stated as a rule below): the two-middles distinction is itself a conventional-tier diagnosis. It separates under act-time diagnosis, where *which middle?* is live, and fuses at the floor and at genjō. "Keeping them apart" is an act-time imperative, not a final floor-claim.

### The act-grammar

Why not leave it at Jizang? Per Dahui, Zen doesn't cease at the self-emptying floor: emptiness that only empties can host neither Zen activity nor the vibrant person who acts. So the floor is turned into an act-grammar, here using Dōgen's vocabulary.

Three rows, each a dependence/enactment pair; all three conventional.

| Dependence | Enactment |
|---|---|
| **mujishō-sōe** — no-own-being as mutual-dependence; each-in-all, no substrate. | **genjō** — manifesting entire: the act out in its case with nothing of it claimed back; full = no remainder of arrogation, which is why one floor holds both arrivals; the seam where the scaffold dissolves. |
| **kannō-sōe** — resonance as mutual-dependence; the placement of the act's index between the being and the dharmas (*how much of the listening to Hyakujō is the self doing?*). | **banpō susumite** — the myriad dharmas advancing — the reception practising, the self verified — one act, two poles of one placement. |
| **engi / inga** — directedness with no moral ground; the blind arrow. | **shu** — practice (gyōji); the weld at act-time, direction bound along the blind arrow, *and the I-making that indexes it*; not-obscure (不昧). |

*(kannō-sōe rather than the canonical kannō-dōkō, to keep the coupling connotation-light: the -sōe already carries mutual-dependence.)*

The floor is emptiness that empties even itself (Jizang, 空空): the ultimate is never a thing, never a final substrate. Everything here is conventional — the path, the grid's distinctions, the two truths themselves — and no level stands as the last floor.

The enactment column is not three agents. Its three cells are the three parts of one sentence of Dōgen's — *carrying the self forward to practice-realize the myriad dharmas is delusion; the myriad dharmas advancing (banpō susumite) to practice-realize the self is satori.* genjō (Row 1) is the actualizing; banpō susumite (Row 2) is the dharmas-forward that clarifies the self; shu (Row 3) is practice. And the sentence's sequel fixes shō's grammar: *to forget the self is to be verified by the myriad dharmas* — 万法に証せらるる, 証 in the **passive voice**. Realization, in the very line the grid mines, is objecthood — the self standing where the dharmas' advance certifies it. The grid spends this below. The manuscript's compound vocabulary then names the *relations* among the cells, not the cells:

- **genjōkōan** = genjō + kōan — Row 1's manifestation in Row 2's particular case (*can this being listen to Hyakujō?*).
- **shugenjō** = shu + genjō — Row 3 practice as Row 1 manifestation: *practice run scaffold-free is nothing but genjō* — and not conversely, since genjō also holds unmarked pole acts (the current stone cell). The "nothing but" runs from the narrower to the wider: {practice run scaffold-free} ⊊ {genjō}.
- **shushō** = shu + shō — the weld (below). Here shō is 証 — realization-as-not-fall, the floor-face — *not* 悟 (satori, the awakening named in the Dōgen sentence just above), and *not* genjō, but the floor's non-attaining middle: anātman — and, per the passive above, the act's subject-position ceded: shō is the *being-verified* face of the one act whose doing is shu. Practice and realization are non-dual (shushō-ittō) because they are the two poles of one index-placement, not two acts joined.

So the column is one act seen through three dependence-lenses, and **all acting is Row 3**, at act-time. genjō and banpō susumite are not further agents; they are that single Row-3 act read at the tier of manifestation and at the tier of the particular self it clarifies.

### Attainment

Why not a table of just the first row? Hakuin gives the corrective: the *not-yet-buddha* mustn't be ignored; realization must meet beings where they are — which is why Row 2 exists.

Row 2 is the being's resonance to the dharmas — and its content must be typed with care. The grade is not a neutral magnitude, index-free like the field: what Row 2 states is the **placement of the act's index**: how the one act's subjecthood distributes between the being and the dharmas. When the hell-dweller acts, the world is almost entirely object and he is subject — the act's subjecthood arrogated nearly whole to the self-pole. At the other pole the distribution inverts: the act's subject-position ceded to what advances, the being standing as the verified (証せらるる), object among the objects that act on it. A line of the The Ten Oxherding Pictures states the inversion in the object-language — *in delusion all is unreal; in satori all is real* (paraphrase from Taming the Bull Verse); and Yongjia's *Zhengdaoge* carries a near-inverse of the same figure, the six realms vivid in dream and the cosmos empty on waking, so the epigram's pedigree is mixed and nothing below leans on the line — the mechanism stands without it) — and Caoshan's commentary on the Five Ranks turns on exactly this interchange of host and guest. The grid can display the line with a mechanism: At high self-share, what is met is never the dharma but the arrogation mirrored — the seed's echo, the question heard as a challenge to a rank — so the world *of that act* is unreal in a precise sense: the self's projection, the call drowned in the response. At share-zero the things of themselves are met — streams flow, flowers are red of themselves (Bull 9). Reality-status remains the object's valence, reported; but the report shows its gears.

**Clench** is the weld's *self-share* — how much of the act's subjecthood the I-making arrogates (the scalar this phrasing suggests is priced in the determination below). Self here is a dependently-arisen process, not a receptive state — ahaṃkāra, I-making, living in Row 3's enactment pole (MMK 8: kāraka and karma — the doer proceeds dependent on the deed, the deed on the doer, neither prior, neither based) — and I-making is never identical to the clench: I-making is the welding-**function**, clench its share-**degree**, and running the two together generates at the summit exactly the collapse the taxonomy names (Theorems). The near-analytic link between them holds. Resonance is the ceded share, and to hear a call at all is to cede subject-position to what calls; a weld that arrogates the whole act leaves nothing for the call to land as. The link is construction, not correlation: one index, two ends, and Row 2 reads where it sits. So the grade and the self are one doing seen twice — the arrogation (Row 3) *read as* the placement (Row 2), never the placement *being* the self — and Row 2 still does exactly one thing, the adverb.

#### What fixes a placement

The grade must not be left as a metaphor doing a measurement's work, so the determination is stated: **the share is the actual composition of the act's drive** — how much of what actually drove *this* response was the call, and how much was the configuration's self-maintenance. Not a modal profile of the responder; an actual-sequence fact about this occurrence: in this act, the rank defended did this much of the driving and the question did that much. Subjecthood arrogated is response driven by the arrogation — the rank defended, the echo answered; subjecthood ceded is response driven by what calls. Counterfactual variation — vary the call and see what the response tracks — is how a third party *probes* the composition, a display over it, never what it consists in. The fox's sentence (run whole at this file's end) reads high-share because the rank's self-maintenance drove the reply and the question drove almost nothing — which the probe shows, since any question grazing the attainment meets the same defense; the sameness of the defense displays what was driving, it is not what "driving" means. The mirror (Theorems: the terminus) reads share-zero for the inverse reason: the response driven by the call entire, nothing in the doing answering to a self-pole because none is driving. So a Row 2 statement is truth-apt and answers to something: the composition of what drove *this* act at *this* call — an occurrence-fact about the weld, field-describable in full, third-personal in register exactly because it is a composition, indexical in content because what the composition locates is the placement of the act's subjecthood. The determination is causal, not phenomenal: no inner glow is consulted, and the grade never was a report of how the act felt.

And the scalar is priced before it can inflate. What Row 2 states is an **ordering**, not a measure: this act more arrogated than that one, this reception markedly less claimed than the last, with the two poles standing as qualitative facts — share-zero is *nothing in the drive answering to a self-pole*, the solipsist asymptote *nothing answering to the call* — and with real cases in between, some of them, where call and self-maintenance interact in the driving, simply incomparable. "Fraction," "degree," the scale itself are display conventions over that partial order, legal exactly as "mirror" is legal (Theorems: the terminus), and no measure is owed: families of causal-contribution measures exist and any member would serve, but the grid needs only the ordering they agree on, and everything built on the grade consumes only the ordering — kenshō is *markedly less claimed*, the dukkha covariation is *more share, more mismatch*, the poles are qualitative, the solipsist a limit. That is this section's honesty-clause, paid rather than hidden: the determination relocated from profile to composition, the scalar demoted to display — a smaller claim than a measure, and the whole of what the soteriology reads.

One cell of the taxonomy is retyped by this determination — the fourth generator-verdict's second exercise (the first is Zahavi, in the placement discussion (Identification); the third is the arrow (Karma)), and forced rather than chosen. The disposition/act cell forbids Row 2 "reading dispositions instead of deeds," and the composition-determination openly involves the configuration: the self-maintenance that drives is the configuration's own. Collision? No — retype. The cell's content was never *no configuration-involvement* — every act is the configuration's act, and a deed driven by no standing thing would be no one's deed twice over — its content is **standing/dated**: the collapse is inferential, the dated occurrence read off the standing tendency — *he is an arrogator, so this act was arrogated* — prognosis substituted for diagnosis. What Row 2 reads is what drove *this* response; what the seed states is what *tends* to drive responses; the first is spent, the second carried, and only reading the first off the second is the error. The redrawing is entered in the taxonomy's table (Theorems), and the generator is answerable for it exactly as it is answerable for the Zahavi retype: a taxonomy that cannot be forced open by the system's own clauses has frozen against its author.

Row 2 is therefore *not* free of indexing — and saying so breaches nothing, because the typing claim was about storage and register, never about content. Row 2 states an indexical fact in a third-personal register, as *he said "now" at noon* is a third-personal statement about an indexical: nothing in the statement is *had* first-personally, and a statement holds nothing. The three-verb discipline stands untouched — the field carries, the weld makes and spends, Row 2 states — but what is stated is the index's placement, not a neutral quantity. The field-side account (Identification) loses nothing here and gains nothing: Row 2's statements are occurrence-facts about welds, field-describable in full, as the determination just given makes explicit. What the identification adds is never the grade but the welding; the third register is a register of speech, not a third kind of fact.

Two things must be kept split: the universal subject-**function** of an actual call/response occurrence and the **share** claimed within that response. Every actual weld is in the domain. The `none` region of `respondsTo` marks only the actual/hypothetical seam and may not be aggregated into a kind of being. The solipsist remains the share asymptote — the call drowned by self-maintenance — while the terminus is the pole at which the call is answered with none of the act claimed. The scale therefore has no function-zero outside edge. Sentience cuts across it as a supplied per-weld mark, yielding four actual cells: sentient/live-share, sentient/pole, insentient/live-share, and insentient/pole. The last is the current stone cell.

The grade still grades — not-yet-buddha → buddha — with the pole at the top of the scale without the pole being *good*. The framework *displays* an asymmetry along the grade — cession one way, arrogation the other — but enjoins no motion along it: the theory is itself a dharma among the myriad (object-axis), an orange handed over, not an "eat this". Release is an event the grid can *show* (the fox lets go), not a good the grid *asserts*; a being may take the asymmetry up as a value, the description does not. The vocabulary's valence — *clarify*, *release*, *full* — is borrowed object-language: a theory of a soteriology must state the asymmetry its object turns on, as a theory of poison states which direction kills, enjoining neither. And what the killing *consists in* need not stay borrowed: the Dukkha section (Theorems) derives, in the grid's own vocabulary, what the arrogation-direction costs. So no value is *asserted* in the system, and the system still states exactly what a soteriology would latch onto — and states even *that* inside the grid: the theory's own soteriological reach is an instance of **banpō susumite**, a dharma advancing to clarify a self *if* a self resonates to it. Row 2 exists wherever a not-yet-buddha does.

The self is the contraction into which the arrow's return pitches — but because the return is itself a deed (reception, Row 3), it *re-makes* the self it is *for*: nothing indexed is stored between, only re-welded at each act-time. Partial share reads a self being made, whether or not the supplied sentience mark is present. Share-zero is the pole, treated in its own section (Theorems: the terminus). So the agent-index karma needs is never stipulated and never read off a field: it is *enacted* in the weld (shu), *stated* by the grade (Row 2), held by neither. I-making is thereby detached from sentience rather than re-identified with it.

Genjō, then, is one manifestation-floor containing both pole cells: the marked terminus act and the unmarked stone act. The stone now arrives *on* the scale at the pole, not from outside it, and the formerly open "third arrival" — a function-mounted, never-clenched act — is no third structural cell at all: it is one of those two according to the supplied mark. Only the marked terminus run is the buddha-side practice history, which is exactly why *practice-run-scaffold-free is a proper subset of genjō*. Both arrivals answer a call with no share claimed; the grid distinguishes their landing patterns, when it can, but cannot recover the mark that types either one.

The magnitude is always per-call — not a global altitude the being holds but kannō-sōe projected onto *this* dharma now; *can it listen to Hyakujō?* is one call, and another call reads another placement off the same being. So the vast space of self-indexing beings, each relocating through karmic action, is no map anyone carries — it is the trajectory the loop draws across successive act-time re-pitchings: a cross-section at each act, vastness only over the run.

#### The sentience joint

The old domain joint has retired: actual call/response is universal, and `none` has only seam-office. What must now be owned by name is the **sentience joint**. `SentienceReading` supplies a predicate on welds; no grid field constrains it, and constant-true and constant-false readings extend the same grid data. Drive-composition remains the grid's entire answer to share and clench, but it is no answer at all to phenomenality. The mark is per occurrence: holding it as a nature a being has freezes the standing-sentience row; identifying it with visible function collapses that row.

The consequence is best exhibited on a manufactured case, and the grid does not flinch from it. A fixed cuckoo-clock chime and an adaptive chime are both actual responses when they occur. Their drive-composition can differ, and either can be marked or unmarked by a supplied reading without changing any response, share, clench, or delivery fact. In particular, a shutdown-resisting machine may occupy the insentient/live-share cell: `KsmdAppropriates` fires although dukkha does not. Conversely an adaptive share-zero artifact can occupy either pole cell. This is the Chinese-room discomfort stated honestly: composition settles the structural typing; phenomenality remains maximally underdetermined.

The same discipline applies to standing effectiveness. Shushō-ittō is per occurrence and assertable only there; `KsmdEffectiveTerminus` is 不落-shaped and displayable as a run pattern, while full enlightenment is the further two-obscurations bundle with no-nescience over pole-share speech-or-mind productions. Testimony remains speech-only and production-tied. The fox-guard applies to adaptive devices and marked responders alike; the sentience mark itself is never inferred from either.

#### The three doors

Every fine weld may be diagnosed through body, speech, or mind. This is a supplied `DoorReading`, not a boundary recovered from response or share data. Canonical arhat display is quiet through all three doors: every actual weld by the being is at the pole. A door-typed śrāvaka-arhat is the regional speech-and-mind form, so live body-door residue—share-vāsanā—can remain without contradicting that regional diagnosis. Response-form vāsanā at pole share is not claimed here.

Voicing is likewise supplied and deliberately door-neutral. A thought can be a mind-door voicing and an expressive deed can remain representable at the body door, but only an actual speech-door production enters testimony. `KsmdDefiledFalsehood` is therefore precise: false speech at its own act-time with a live self-pole. Calling that schema deliberate lying requires an additional intent-reading; the theory does not hide that modeling step inside the name.

#### Orthogonality

The manufactured case pays for a rule the terminus needs. Give the call a rate — **effectiveness**, the fraction of its arrivals after which a share-ceding reception occurs — regime-relational throughout ([Glossary.md](Glossary.md)): a fact about call–configuration pairs, never a property the object holds. Then run the two builds against the rates, and the extreme corners witness a strict orthogonality: **function is universal; share types; effectiveness grades; sentience is supplied; adaptivity is the terminus's manner, never the ground of landing.** A fixed call can land universally without reading anyone — effectiveness and adaptivity fully severed; and the tradition itself attests fixed calls at the other extreme of rate, Xiangyan's pebble on bamboo, the morning star, so the ordinary clock differs from the pebble only in rate. A reading device can reach no one: the adaptive build at zero effectiveness reads every arriving configuration and lands nothing — pole-typed and maximally shortfallen, the proof-case that typing and grading are orthogonal. The stone's crack is now itself an unmarked pole weld with object-axis standing; a monk's downstream reception may still share-drop because delivery never consults the mark. What share settles is where the index sits; what grading measures is what lands; what the mark says is supplied; none determines either of the others.

#### Kenshō: rungs on the grade

The grade admits *events*, and the tradition already names them: **kenshō** — typed here as a per-call share-ceding event, a call answered with markedly less of the act arrogated, re-pitching the configuration. Not a sighting of a substrate: 見性 reads literally "seeing the nature," and 性 risks the faculty-freeze — buddha-nature as a standing thing glimpsed — so the term is taken over with its metaphysics stripped, the event kept, the seen-thing declined. Kenshō is countable — Dahui's great awakening eighteen times, small awakenings beyond count, the line Hakuin loved *(the line circulates via Hakuin; commonly traced to Dahui's nianpu — locus to be verified)* — which is exactly what a rung is and exactly what a terminus isn't. And because nothing indexed is stored between acts, a kenshō *cannot be held*: post-kenshō backsliding, which the tradition treats as an embarrassment needing explanation, falls out here as a theorem (restated in Theorems). The being loses no attainment; there was never a stored configuration to lose, only the next act's re-weld reading a re-pitched fit. Many kenshōs, none possessed.

The typing keeps three words apart. **Kenshō** is the rung — a countable per-call event on the grade. **Satori** (悟) keeps the role the Dōgen sentence gives it — the dharmas-forward *mode*, pole-typed, not rung-typed. **Genjō** is the pole itself — and the pole is not the top rung: it is in-domain — share-zero is a placement, not a departure — but it is not a rung one attains and keeps, because nothing indexed is stored and placement is per-call. The pole is a pattern the run can answer at, never an altitude held. So "full satori" as a possessed rank is declined: not a scale-word past the scale's edge but a *state*-word offered for a per-call pattern — the freeze, not a category hole. The Jizang parallel holds: the fourfold ladder terminates in dropping the seeking, and the grade terminates in the ceasing of arrogation — in both, what looks like a last rung is the ending of a doing, and mistaking the ending of a doing for a rank held is the shared error-shape at both termini. What the ending leaves — whether the pole-deed still welds, and where — is the transposition's business (Theorems: the terminus).

### Karma: the circuit and its registers

Why not a table of just two rows? The fox koan (*Mumonkan, Case 2*, Wumen Huikai) is the test. The old man's mistake was a *tier-error*, not a wrong: he asserted *not-fall* where *not-obscure* was called for — a floor-truth spoken at the conventional level, which is antinomian, since a floor-truth can only ever be *spoken inside* a conventional act. Held each at its proper tier, the two are non-dual. The five hundred fox lives are not desert or punishment; they are returns — the loop running.

*(Dōgen read the fox twice, and the doubling must be owned rather than elided. Daishugyō diagnoses: it reads the production weld's share, while its floor face is error-free by silence and structurally unproduced *(checked: `daishugyo_floor_face_error_free`, `daishugyo_floor_face_unproduced`)*. Jinshin inga instructs: “not obscure, full stop” is a fitting speech production, while counterfactually voicing the floor repeats the old man's defiled falsehood *(checked: `jinshinInga_instruction_fits`, `jinshinInga_floor_voicing_defiled`, `oldMan_defiledFalsehood`)*. The two fascicles' core verdicts now converge on one production vocabulary. And the contra's remainder now has a measured width. Jinshin inga's verdict-noun is* teaching *— a production category — so its unconditional surface quantifies over the hearable and forecloses nothing it cannot reach; symmetrically, no production could record an ontological foreclosure without instantiating the very schema both fascicles convict, since a floor-tier verdict voiced at act-time is the old man's error-shape. So a Dōgen who foreclosed only the register and a Dōgen who foreclosed the held would leave the same corpus, sentence for sentence: the difference lives in the unproduced* (checked half: `daishugyo_floor_face_unproduced`)*, and the corpus is productions. The historical contra is therefore narrowed to a question no production keeping the fascicles' own discipline can separate — a find could break the equivalence only by showing that discipline broken, which would reopen what the discipline was. The system states the equivalence and returns no verdict, its floor clause silent here as everywhere. (Eihei kōroku 7.40, a 1252 jōdō marking exclusive fumai inga as itself one-sided, is the prose anchor for the register-bounded reading — the closest a production comes to its register's edge, and still a production.)*

Karma is a circuit, not a payload one row carries. At act-time a deed welds an agent-index onto the blind arrow, and the being's reception of the arrow's returned result is itself a deed, not a state. Row 2 only *states* the being's re-pitched placement — the fit between this call and this arrogation, not a faculty it holds (which would re-base the empty agent); it has no verbs. So the loop closes inside the grid: a deed welds an index → the arrow returns → reception re-pitches the Row 2 configuration → which the next deed reads from. The circuit's status splits, owned here once. The re-pitch arc is checked, chained included: within any supplied finite run, each step reads the configuration the previous reception re-pitched, and run histories sharing their final reception hand the field the same configuration *(checked: `rePitchRun_cons`, `ShareDropRun`, `rePitchRun_forgets_same_final`)*. The reads-from arc is not a theorem and none is owed: which call the field delivers next — hence which deed next reads the configuration — is the delivery cession (instructive absence 5, why calls land), so the closure is asserted in the identification's voice, a modeling claim over checked parts, not a checked transition system. And one magnitude is deliberately unconstrained: nothing in the grid bounds how far a single reception's re-pitch moves the configuration — owned here as a feature, in one sentence, and spent where the sudden/gradual question is met (Theorems).

#### What is carried, what is made, what is stated

Between deeds nothing *self-indexed* is stored. The claim is architectural and definability-level, not information-flow noninterference: `Config` has no `Being` field, relabelling is invisible to it and commutes with `rePitch`, and no relabelling-equivariant family recovers an agent from it. Something *is* carried — and saying so plainly absorbs, rather than silently deletes, the tradition's own storage machinery. The seeds (bīja, vāsanā, the ālaya-vijñāna's freight) are taken over here deflated: conditioning-facts in the impersonal series, dharmas among the myriad, index-free in this precise register sense — granted to the field as fully as the flame was. What the field stores is a fact *about* the series — *this configuration tends to arrogate at calls like this* — never a stored self, never a held mineness. Because grading may depend on the acting tag, the stored grade may coincide extensionally with it in a model; `registerClockGrid` witnesses exactly that honest limit. `Grid.rePitch_forgets` bounds the coincidence to one reception's footprint: nothing accumulates into a diachronic bearer, and the configuration is fibered over no being. The seed is not a foreign organ transplanted in to appease Yogācāra; it was already sitting in Row 2's cell: the being's own returns are among the myriad dharmas that advance. And the standing/dated typing must be held firmly, or the whole discipline leaks: what is stored is a tendency (an inga-fact, third-personal); the *arrogation itself* is an act that occurs, or does not, at act-time, and Row 2 reads the act's drive, never the tendency. A seed frozen into a bearer is a soul by another name — the tradition's own worry about the ālaya, and this grid's soul-guard, are the same guard.

So the facts sort exhaustively into three registers:

| Register | What it holds | Instances |
|---|---|---|
| **Field-facts** (inga) | Everything diachronic; index-free in configuration; relabelling-invariant; carried | the causal series; *delivery* — which fruits arrive at which configuration; seeds — conditioning-facts about the series, including the re-pitched configuration the next deed reads; the tendency to arrogate |
| **Weld-facts** (shu) | Everything indexed; made at act-time, spent at act-time; never carried | the agent-index of each deed; for-me-ness; the reception-weld's reach-back (below) |
| **Stated** (Row 2) | Neither carried nor made; stated per-call | the placement of *this* act's index at *this* call — an occurrence-fact about the weld, field-describable via the composition of its drive; indexical in content, third-personal in register; the adverb on Row 3's verb |

This is the answer, in one place, to *what does the next deed read?* — it reads a field-fact. The arrow does all the diachronic work, and does it index-free in the stated sense. Delivery is still a relation on welds, and welds expose agent role readings; `SameAgentDelivery` is field vocabulary on purpose. "Index-free" means that no index is stored in the configuration and that field relations transport invariantly under whole-carrier relabelling, not that those relations are agent-blind. The apparent contradiction ("re-pitched configuration" vs. "nothing stored") dissolves into the typing: the configuration is carried *as* an inga-fact, and what was never stored was only ever the index *as index*. And the table sorts registers of speech and role, not kinds of fact: a Row 2 statement states a field-describable fact (the composition above), and only the middle register holds what is no fact at all — the welding itself, an act.

#### The arrow retyped: direction as display

The fourth generator-verdict's third exercise — and, like the second, forced by the system's own clauses rather than chosen. [Glossary.md](Glossary.md) now records the arrow as *inga's directedness*: primitive furniture, blind but pointed. The retype empties the pointing one more level. What the field holds is correlational structure — which welds condition which, the delivery-lines, the web — and *direction* is a reading of that structure, never its own property. The reading has a mechanism, and the mechanism is thermodynamic: a gradient-embedded being — evolved to ratchet, or built of gates whose erasures are entropy-priced — takes the slope it sits on as a direction-fact and projects it into the field. That projection is **the ratchet** ([Glossary.md](Glossary.md)). The physicists' microreversibility is the same point in their register, consumed here as display only: the grid leans on no physics, exactly as it leans on no history at Huichang. What the retype leaves untouched is everything any theorem ever consumed — delivery-facts, conditioning, the lines along which the reach-back fills its second place. What changes register is the *before/after* alone: from carried fact to stated reading, the same demotion desert underwent on the first pass. (Where gradients thin — the deep cold — nothing there reads a direction: correlations persist, and causal talk loses its footing; not noise, but relation without a privileged direction of explanation.)

The retype generates its own error pair, one per violation, nothing added by hand. The **freeze**: before/after held as a floor-claim — *time really flows* — the direction reified into furniture; the retrospective soul was this freeze in psychological dress, and the flowing container is its cosmological one. The **collapse**: the distinction fused under act-time diagnosis — *there is no time, so nothing happens, no one acts* — the fox's sentence transposed to time, not-fall spoken where not-obscure was called for. The deflationary reading is therefore not an objection the retype must survive; it is a cell the retype produces.

And the positive account was in the source-text all along. Firewood abides in its dharma-position with its own before and after; ash in its own — 前後ありといへども、前後際断せり (Genjōkōan): before and after exist, yet before and after are cut off. Before/after is per-weld display, exactly as mineness is: the reach-back welds *pastness* — *this fruit as return of that deed*, a two-place index across time — the aimed call welds futurity at sowing, and each is spent at its own act-time, carried by nothing. Local time, welded per act; no flowing container anywhere — Dōgen's uji, with Huayan's ten times (十世隔法異成門) as the wider family. So the answer to *nothing is happening* is: happening is all there is; only the container was dropped — the same shape as anātman, where dropping the owner deleted no acts.

One tension, written down rather than hidden, because the separate/fuse rule pivots on act-time and this retype conventionalizes time itself. There is no circle: act-time is a tier *within* the thermodynamic convention — precisely the convention beings live in, which is why diagnosis happens there — and the floor rule was always licensed to eat its own levels ("the two truths themselves are conventional"). Floor-fusion now explicitly includes fusing before/after, which makes the fox's question — *does he fall into cause and effect?* — even more literally the question the whole grid answers.

### The being-convention

The same demotion now applies to the macro being. A being, at this scale, is a conventional truth downstream of the words: anything nameable can be designated. The universe, its makeup evolved from a dense hot gas cloud; the stone; the buddha; the gerrymander; the hare's horn; the impossible ātman — all are legal designations as designations. Nothing licenses one as more legitimately a being. The constraint enters later, at realization and use, not at naming. Squeamishness about this is itself one of the beings-row errors: the collapse says "there are no beings"; the freeze picks one partition and mistakes it for ontology.

The ordering is ontological, not chronological. The floor/genjō vocabulary sits outside all conventions. The bare signature supplies words-level tags. The directed convention reads a slope as before/after. Inside that, the being-convention reads fine tags as macro beings, and inside both sits the grid-lens that diagnoses collapse and freeze. Names track what their *reading* presupposes, not what their definition consumes: `DeliveredTo` already used this rule, since it consumes `conditions` but its name reads the arrow. Likewise the new `Grid.DirectedConvention.BeingConvention` names read a tag as a being even when their definiens is direction-free.

Lean makes the demotion explicit with `BeingCoarsening`: a diagnosis-time projection from fine tags to macro tags, never a field in the signature. Relative to a supplied reading `S`, `SentientTag S b` means that some actual weld in the fiber is marked. `StoneTag S b` requires an inhabited actual fiber whose every actual weld is an unmarked pole act, while `Intermittent S b` records fibers containing both marked and unmarked acts. There is no tag-level sentience scalar and no recovery from the fiber's visible behavior. 無情説法 therefore needs no hidden successor layer: an unmarked stone act is already a response and already stands on the object-axis. Only the phenomenal mark remains unassertable from the grid.

The spectrum is fiber-level and per-weld. `FiberAtPole` says every actual weld in the fiber reads at the pole-class: the 84,000 pores each a responsive dharma-gate. `SelfAptTag` says every actual weld in the fiber still carries a live self-pole index: the hell-dweller's monolithic convention, where "self" is apt if it is apt anywhere. `Patchy` names the irreducible middle. No aggregate fiber-share is defined, on purpose: Row 2 is a partial ordering, not a measure, so a mixed fiber is not a middling scalar.

Coherence stays a grade, not a type. Evolution's contribution is display over the run — skin-bags usually score high at coordination, an adaptive register-clock can implement stable internal registers — but no theorem may condition legitimacy on coherence. The three registers need the same care: the swan is named, the naming is enacted as a weld, and the proneness to name is a seed. Thoughts are not "just seeds"; naming is a deed when it occurs.

The soul-guard survives the new vocabulary. `selfAptTag_indices_are_per_weld_only` says that even where the self-convention is apt, the live index is only the per-weld agent tag. The macro self is the image of those spent tags under a coarsening. Holding it as more is the fiber version of the old soul-freeze.

#### The reception-weld: loop-closure as theorem

"The same being" across sowing and reaping is loop-closure — but closure must now be earned, not helped to. Here is how it is earned.

A reception is intrinsically a reception-*of*: its content is *this-fruit-as-return-of-that-deed*. So the reception-deed's token-reflexive index is **two-place** — the weld makes mine both the receiving and, retrospectively, the deed received-from. This is **upādāna**, appropriation, the canonical partner of ahaṃkāra: the reach-back. Sameness of sower and reaper is not *tracked* across the gap — nothing indexed is there to track — but *made at reception*, each time, by an act of appropriation reaching back along the arrow. The loop is closed *by the reception-weld*, retrospectively; closure is enacted, not tracked, which is the same act-not-state discipline the rest of the grid runs on. So "the sower reaps" wears two faces and must be split along them. Its report-face — *an appropriation occurred at this reception, reaching back along that delivery-line* — is true simpliciter, an occurrence-fact the field carries like any other. Its ownership-face is not true or false but **done** — enacted whenever a return is received, full or vacuous (just below), never a standing diachronic fact persisting between acts. Held as a standing backward relation it would be a *retrospective soul*, and the soul-guard fires on it exactly as on the forward-facing kind: the reach-back, like every weld, is spent at its own act-time.

Two consequences discharge two objections at once. First, appropriation cannot poach — and the block is typed, not decreed. The reach-back's index is two-place: *this fruit as return of that deed*. Whether that deed conditioned this fruit is a delivery-fact, inga's business, settled index-free — and where delivery drew no line, the index's **second place stands unfilled**. A reach-back along an undrawn line is therefore not false — it stated nothing, having never been in the stating business — but **vacuous**: an appropriating with nothing arrived to appropriate. (Austin's word for this shape, *misfire*, is legal here only as display — over the pattern, never as mechanism — since nothing here is a speech act: the conditions the field owns are not conventions but delivery-facts, and what they settle is whether there is anything to weld.) So there is no welding at a distance, not by decree but by typing: inga settles the **delivery-question** (which fruits arrive at this configuration — causal, index-free, hard in the ordinary way), the weld answers only the **index-question** over what arrives, and the field owns the reach-back's conditions in exactly that deflated sense. Second, the diachronic *whose*-question decomposes **exhaustively**: a delivery-fact (field) plus a fresh appropriation (weld), with no third fact left over for a cross-gap convention to fix. A series-account owns the delivery-half, which was ceded to the field from the opening page — *na ca so na ca añño*, the reaper neither the sower nor another, is the tradition itself declining the robust diachronic identity-fact that would do more. The loop is *individuated* by inga (a series-fact, granted) and *closed* at each reception by the reach-back (a weld-fact, made). Nothing about ownership crosses the gap, because there is no cross-gap *whose*. If *ownership*, as the tradition's convention uses the word, is located in the continuity-fact instead, the remaining dispute is where the soteriology's load sits; this paper's answer is the object's own usage — the offices-spine stated in the identification file (Identification).

#### The weld's two faces

The karma-agent has no own-being: mere-designation, floating free of any base like the chariot. Its charter is **MMK 8** (kāraka: the doer proceeds dependent on the deed, the deed on the doer — neither prior, neither based), flanked by **MMK 17** (act and fruit — the loop) and **MMK 18** (self). With no fixed base, soteriological direction can never be *read off* the facts — only *enacted*. So dependence and enactment are one fact seen twice: no-substrate on one side *is* the necessity of welding on the other. This is **the weld** — Dōgen's shushō, practice-realization — and it wears two faces, each true at its own tier:

The same MMK 8 charter now has a checked interior form: even inside the weld, call→response order is a display reading, not before-and-after furniture recovered from unordered pair-content (`InteriorDirectionNegative.no_interior_direction_recovery`). The charter verse now has generated cells at both joints: the intra-weld arrow row for the face-order convention, and the doer/deed row for priority read as floor furniture. The occurrence reading keeps the role names `call` and `response` because the display is useful; the theorem says only that the labels are not prior to the mutual dependence they name.

- **shō** (証, realization), at the floor: no own-being, so no substance is caught in the causal net — **not-fall** (不落), anātman, not escape; grammatically the being-verified (証せらるる), the act's subject-position ceded. That shō is agential — but agential *because* welded, never on its own: there is no lone shō to rest in, only shushō-ittō, the true person of no rank going in and out. So shō is necessarily agential (it never occurs unwelded) without being agential of itself (the acting is shu's, lent at act-time) — the non-attaining middle, shō its floor-face, never a still attainment.
- **shu** (修, practice), conventionally: the karmic arrow is real and inescapable, never evaded — **not-obscure** (不昧).

### The separate/fuse rule

One rule governs every distinction the grid holds: **distinctions separate under act-time diagnosis and fuse at the floor (and at genjō — the share-zero pole, no arrogation left).** The rule dissolves the fox (not-fall at the floor, not-obscure conventional), governs the two-middles distinction (genjō provisional, shō non-attaining), and applies to the grid's own verdicts, which are conventional-tier claims that dissolve, harmlessly, below — the taxonomy's own mis-feeds are scoped in the identification file (Identification). And the rule's own pivot, act-time, is a tier within the thermodynamic convention (Karma: the arrow retyped) — the floor rule eating one more level, as it is licensed to; floor-fusion includes fusing before/after. Its two possible violations — **collapse** (fusing a distinction under act-time diagnosis) and **freeze** (holding a separation as a floor-claim) — generate the error-taxonomy whole (Theorems), one pair per distinction, with nothing listed by hand.

## One act through the grid: the fox's sentence

The system has so far been stated as type-discipline; here is one case run through it whole.

**The call.** A student asks the old Hyakujō whether the person of great practice falls into cause and effect. The question is a dharma advancing — Row 2 has a placement to read: *can he listen to this?*

**The act.** He says *not fall*. The deed is self-forward — Dōgen's delusion, the *saying* — and doubly diagnosable. Grammatically (grade 1, assertable): a tier-error, a floor-truth uttered as a conventional answer, the antinomian collapse. Soteriologically (grade 2, displayable): the answer defends an attainment — a rank rested at — so the weld arrogates the act nearly whole; the question is not heard but met as a challenge to the rank — the rank's self-maintenance driving the reply, the question driving almost nothing (probe-displayed: any question grazing the rank meets the same defense) — the world of the act reduced to the rank's echo, and Row 2 reads the index pitched hard to the self-pole *at this call*. One doing, seen twice: the arrogation (Row 3) read as the placement (Row 2). *(checked: `fox_sentence_live_selfPole`, `oldMan_utterance_misfits`)*

**The weld.** The deed welds the agent-index onto the blind arrow — *this act's agent* — token-reflexive, spent at that act-time. Nothing of it is stored. *(checked: `sentenceWeld_actual`)*

**The arrow.** Inga carries the conditioning forward, index-free: no desert in flight, only delivery. What is carried between acts is a field-fact — a configuration that tends to arrogate at calls like this — a seed, a fact *about* the series. *(checked: `fox_arrow_index_free`)*

**The returns.** Five hundred fox lives arrive — fruit landing, life by life, at the configuration the field delivers it to. Not punishment; delivery. *(checked: `fox_returns_delivered`)*

**The receptions.** Each life's receiving is itself a deed. For five hundred lives the reception is arrogated — the saying-mode persists, but as a *disposition* (an inga-fact) enacted anew each time, never as a stored self; each reception's reach-back welds *this return of that deed* as mine, and each is spent. Each clenched reception carries `ClenchMismatch`; under a reading that marks it, the same witness has the dukkha gloss. The mismatch is enacted rather than appended as penalty, while whether it is suffered is supplied. Each reception re-pitches the configuration; the field carries the re-pitch to the next act *(checked: `fox_reception_clenched`, `fox_clenchMismatch_per_life`, `fox_dukkha_per_life`, `fox_config_carries_only_tendency`, `fox_rePitch_forgets`)*; the next deed reads a field-fact.

**The release.** The later Hyakujō's turning word — *not obscure* — is another call. This time the reception is *listening*: dharmas-forward, banpō susumite, the arrived word among the myriad. The reach-back appropriates the whole return — *the fox body's long fruit, mine, of that sentence, mine* — with markedly less of the act claimed: a share-ceding event, a kenshō, a rung and not a pole (the mountain of ox-herding still ahead). Not-obscure is enacted in the reception; not-fall is true at the floor of the same act; held each at its tier, non-dual — the fox lets go. And nothing is *kept*: the release is not a possession acquired but the next configuration re-pitched *(checked: `fox_release_rung_not_pole`, `fox_reachBack_full_at_release`, `fox_nothing_kept`)*, which the next call will read.

Every load-bearing piece appears once: call, arrogation, weld, arrow, seed, return, reach-back, re-pitch, rung. The loop closes at reception, retrospectively, each time — nowhere else, and nowhere is it stored. *(checked: `foxSeriesCoarsening`, `foxSeries_macro_sentient`, `foxSeries_macro_selfConditioning`, `fox_consecutive_lives_distinct`)*

And mark what the case never tests: neither utterance occurs at the pole. The koan's own question concerns 大修行底人 — a person of great practice, not a buddha; the old man answers from a defended rank, and the release is a rung with the mountain still ahead. So the fox exercises the loop entire — sowing, arrow, reception, re-pitch — without once asking what the loop is at share-zero. That question is the transposition (Theorems: the terminus). *(checked: `fox_never_tests_pole`)*
