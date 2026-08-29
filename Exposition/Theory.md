# Kannō-Sōe Mutual Dependence (KSMD)

KSMD implements a formal theory of provisional non-reifying ontology inspired by Zen sayings.

The use of formal modelling is primarily for internal accountability in defining the system—please note that every notable conclusion of the model follows only from the modelling decisions made during the creation of the project.

Those decisions are certainly inspired by Buddhist traditions, but were not at all over-constrained to *this* specific approach by the source material. There is significant interpretive design input and assumption in the model defined according to my own judgement.

That said, I invite you to investigate the model, see what matches or does not match your own understanding, and if possible share your perspective on it in the repository [Discussions](https://github.com/kanno-soe/kanno-soe/discussions) or [Issues](https://github.com/kanno-soe/kanno-soe/issues) pages.

Nb. the equations only restate what the prose and diagrams have already stated—they are 100% fine to gloss over or read selectively.

## The formal core: designata, elaboration, and Mutual Dependence

A **designatum** is simply something the model can designate. It does not first divide designata into people, objects, events, thoughts, or times.

A **component** is a nonempty group of designata (`{a, b, c, ...}`).

An **elaboration** (⇓ reads as "elaborates to") is a relation saying that a designatum may be expanded into a raw Mutual Dependence; because it is a relation rather than a function, one designatum may have no stated elaboration, one elaboration, or several alternatives. Alternatives are simultaneously available dependence-explanations rather than mutually exclusive outcomes.

The **raw structure of a Mutual Dependence** `m` is a list of at least two components (C₁, ..., Cₙ) where every adjacent pair are symmetrically interdepending (⋈):

```text
    m ⇓ [C₁ ⋈ C₂ ⋈ C₃ ⋈ ... ⋈ Cₙ]

    not required: a temporal order, a causal arrow, or direct interdependence of non-adjacent components
```

or as an equation:
```math
C_1 \bowtie \cdots \bowtie C_n
\quad\Longleftrightarrow\quad
\bigwedge_{i=1}^{n-1}(C_i\bowtie C_{i+1})
```

As components may contain designata, and a designatum may be elaborated to a mutual dependence, the elaborated components can look like:

```text
  ab ⇓ [{a} ⋈ {b}]
  fg ⇓ [{f} ⋈ {g}]
  m  ⇓ [{ab, c, d} ⋈ {e} ⋈ {fg} ⋈ {h}]
```

Here the first component of `m` has 3 designata, `ab` which designates (elaborates to) a mutual dependence `[{a} ⋈ {b}]`, and `c`, and `d`, which each are designata without defined elaboration.

A designatum `d` **reaches** another designatum `w` (`d →* w`) if it can get there in zero or more steps of elaboration. Every designatum reaches itself. If `d` elaborates to `[C₁ ⋈ ... ⋈ Cₙ]`, one step may enter any designatum in any component.

Or more formally, fixing $E$, the elaboration approach, write $\to$ for $\to_E$, and with M as elaborated mutual dependence, let $\to^*$ denote the reflexive–transitive (Kleene-star) closure of $\to$:

```math
d\to e
\quad\Longleftrightarrow\quad
\exists M,\;
E(d,M)\land
e\in\bigcup\operatorname{components}(M)
```
```math
\frac{}{d\to^*d}
\qquad
\frac{d\to e\qquad e\to^*w}
     {d\to^*w}
```

Designata are **joinable** (↓) if there is a shared designatum `w` that both can reach:

```text
                              +--> p ---->
                             /
    designatum b --elaborates
                             \
                              +--> q ----> common witness w

    designatum e --elaborates----> r ----> common witness w

    b ↓ e  :=  there is some w reached from both b and e
```

or as an equation:
```math
d \downarrow e
\quad\Longleftrightarrow\quad
\exists w.\; d \to^{*} w \leftarrow^{*} e
```

This joinability is reflexive and symmetric, but it need not be transitive (which means that just because b ↓ e and suppose e ↓ fg, it isn't necessarily true that b ↓ fg).

An **interdependence** (⋈) between two components is a stronger requirement than just finding a joinable pair: every designatum in the first component must have a joinable partner in the second, and every designatum in the second must have a joinable partner in the first.

```text
    component C                       component D
    +---------+                       +---------+
    | c1      | -- joinable partner ↓ | d?      |
    | c2      | -- joinable partner ↓ | d?      |
    | c?      | ↓ joinable partner -- | d1      |
    | ...     |                       | ...     |
    +---------+                       +---------+

    C ⋈ D  requires coverage in both directions.

    For singleton interdependence, C ⋈ D is true iff c ↓ d
```

or as an equation (interdependence is the Egli–Milner lifting of joinability):
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

The interdependence **chain** may be any finite length. It can be sliced and compatible chains can be concatenated. Although examples in this exposition involve linear chains, two chains may include the same designatum. In that case it's really a chain *network*, with each designatum having a "valency". A designatum of an interior component of a linear chain has valency 2, while a designatum appearing in multiple chains might have valency >2.

This is the minimal formal structure of **Mutual Dependence** (*sōe*). Throughout, that structure is read as **mujishō-sōe**: mutual dependence without-own-being (*mujishō*), in which neither side supplies a self-standing substrate for the other.

## Resonance as a Mutual Dependence

A **Resonance** is the following four-component special case of Mutual Dependence, with its middle components forced to be singletons:

```text
    calls ⋈ {b₁} ⋈ {b₂} ⋈ responses
```

The intended reading is that `b₁` is the receiving view or moment of a being and `b₂` is its responding view or moment. Formally, however, `b₁` and `b₂` are two interdependent singleton designata in the same certified dependence. The model does not prove that they are numerically identical, temporally successive, conscious, or personal. The names **calls**, **receiving**, **responding**, and **responses** are role-readings of the shape.

An **Encounter** is a Resonance viewed merely as a Mutual Dependence. It retains the concrete `calls ⋈ {b₁} ⋈ {b₂} ⋈ responses` shape while everything about it being a resonance is temporarily forgotten. *Encounter* is an expository alias, not a new Lean type. Every Encounter is a Mutual Dependence; not every Mutual Dependence has the four-component singleton-middle shape needed to be an Encounter.

Because designata may elaborate into any raw dependence the modeler supplies and later certifies, the same Resonance shape can be used for a person answering a question or a stone answering the wind by rolling downhill:

```text
    {wind} ⋈ {stone-receiving} ⋈ {stone-responding} ⋈ {rolling}
```

Nothing in the ungraded structure privileges the person. Nor does the stone example prove a doctrine about sentience: it proves only that the Resonance constructor asks for interdependent singleton designata in its two middle positions, not a prior metaphysical kind called *person*.

## Graded Resonance

> Sentient beings originally are Buddha.  
> Being like water and ice,  
> leaving water there is no ice,  
> outside of sentient beings there is no Buddha.
> 
> — Hakuin Ekaku, *Song of Zazen*

A **Graded Resonance** adds two independent grades to a Resonance: a calls-side grade and a responses-side grade. The grade type need only be a preorder with a bottom element. It need not be numerical, total, or metrically spaced. The intended reading is **dis-resonance**: volition insofar as it is *sāsrava*—with outflows, ripening in further becoming. Bottom is *anāsrava* at this Resonance: the act is not productive of further becoming, without implying either the absence of volition or the global attainment of arhatship. `0` is only the familiar numerical example. How a bottom grading relates in the world is left as a functional question about the relating of such moments, and could be modelled by downstream effects on other resonances.

```text
                one Graded Resonance


           calls ⋈ {b₁} ⋈ {b₂} ⋈ responses

             (callsGrade) (responsesGrade)


    callsGrade and responsesGrade are independent coordinates.
```

A stone can prompt volition, not have it; only volition makes a cause karmic. That is the whole difference between non-karmic and karmic cause/effect. Likewise it can feed āsravas, not have them.

Thus a stone is assigned bottom on both sides, while a grumpy person who has stubbed a toe may be *assigned* a non-bottom calls grade, a non-bottom responses grade, or both. Those are interpretations supplied to the model; the model itself does not itself infer a grade.

Grading is sentience-neutral. A sentience reading *could* be supplied as additional information, but it's not inherently required in the model.

## Being

A **Being** is a mutual dependence of singleton-only designata.

```text
being ⇓ [{b₁} ⋈ {b₂} ⋈ {b₃} ⋈ ... ⋈ {bₙ}]
```

The designata are implied to be *imputed* from (share common elements with) the `b₁` and `b₂` of  resonances. A temporal/causal reading (described below) may also be supplied.

## Temporality and Causation are overlays

> In this being, that is.  
> Owing to the arising of this, that arises.  
> In this not being, that is not.  
> Owing to the cessation of this, that ceases.
>
> — Buddha, *Udāna* 1.3

> Note: This section will be revised, it puts forward a definition of Cause which is intuitive but
> confusingly different from the one the Buddhist tradition uses.
> 
> I’ll try to briefly explain the difference pending bringing this more into line with the Buddhist use of the terminology.
> 
> Firstly, in Buddhist terminology, ”A Causes B” does not necessarily imply ”A Before B”. I’ll provide two (not-necessarily-exhaustive) examples:
> 
> a) The tradition’s example: You stack two reeds leaning against each other, and leave them leaning against one another. Afterwards it’s correct to say A is Causing B to remain standing, and B is Causing A to remain standing.
> 
> b) My own unrelated example: The upcoming World Cup (of whichever sport) is to be hosted in Antarctica. Because of the World Cup taking place, there’s a building of stadiums. The building of stadiums causes the World Cup to take place. Though you could dissect this into a linear causation process, you aren’t required to do so. In farness, the tradition might use “conditions” for the latter, but the general idea is that designation of A and B could be broad enough that within there are genuine Causal relations in each direction, which the whole validly takes on as its own Causal relations when discussing it.
> 
> Lastly, (as I understand it) a matter of taste: you should be able to say ”A Before B” without having to state
> the way they mutually depend in any more detail / separate from the statement already made. The statement you make of “A Before B”
> already suffices as its own mutual dependence statement (in the sense of A’s beforeness to B, B’s afterness to A).

Mutual Dependence and Resonance contain no time-directedness. A **Temporality** interpretation is supplied separately as a strict transitive **Before** (≺) relation with, for every `x ≺ y` claim, a **Temporal** certificate. A domain may then supply a **Causal** (↝) interpretation with a `x ↝ y` relation that implies `x ≺ y`.

The certificate is simply a mutual dependence with `x` at one end and `y` at the other.

```text
    temporal certificate:     {x, ...} ⋈ ... ⋈ {..., y}
    temporal overlay:          x ≺ y
    causal assertion:          x ↝ y

    x ≺ y  =>  a mutual dependence with `x` at one end and `y` at the other
    x ↝ y  =>  x ≺ y
```

Because Before is strict, the causal relation is asymmetric: `x ↝ y` rules out `y ↝ x`.

Forgetting the causal and temporal overlays leaves the certificate as just like any other mutual dependence without causal and temporal interpretations.

To summarise, mujishō-sōe is the dependence-structure retained when either grading or the causal and temporal overlays are forgotten.

## From empty dependence to the provisional middle

> Dependent arising we declare emptiness.  
> That is a dependent designation; precisely that is the middle way.
>
> — Nāgārjuna, *Mūlamadhyamakakārikā* 24.18

Remove grades from a Graded Resonance and the Temporal/Causal overlay, and the Mutual Dependence remains. That by itself is not a Buddhist metaphysics — the philosophical bridge begins when the act-grammar reads the mutual dependence (**sōe**) as **mujishō-sōe**: mutual dependence under the condition of no own-being.

*Mujishō* (無自性) means without self-nature or own-being. The formal model's interdependence relation is a simple analogue —neither interdependent component is entered as the self-standing base of the other.

This is from Nāgārjuna's *MMK* 24.18: what dependently originates is empty of own-being; that emptiness is itself dependently designated; just this is the middle way. Therefore mutual dependence doesn't mean relations among already self-subsisting things, and emptiness doesn’t mean a deeper thing beneath them.

Jizang supplies the next turn. In the fourfold two truths, each stated ultimate—including the conventional/ultimate distinction itself—can become the conventional content of the next analysis. The iteration does not discover a final unconditioned proposition, it ends at words forgotten, thought cut off (言忘慮絶): not another claim but the place where words and thought no longer do separating work. That claimless place is called the **floor**.

The **middle** can then manifest as this case, instead of becoming another object of analysis. This manifestation is called **genjōkōan**, the **provisional middle**.

| Dependence reading | Enactment reading |
|---|---|
| **mujishō-sōe** — mutual dependence without own-being | **genjōkōan** — the case manifesting fully |

The **dependence-face** names the relation retained when additions are forgotten; the **enactment-face** names how that relation comes forward as a case. Mujishō-sōe is the dependence-face of Row 1: this Encounter has no self-standing substrate. Genjō is its enactment-face: that empty dependence nevertheless manifests as this call, this receiving, this response. *Provisional* doesn’t mean half-real or merely hypothetical, it says that the case is concrete without being promoted into a final ground.

## From no rank to practice-realization

> A monk asks: “What is the true person of no rank?” The master grabs him: “Speak! Speak!”  
> The monk hesitates. The master pushes him away: “The true person of no rank—what a dried piece of shit!”
>
> — Línjì Yìxuán, *The Record of Línjì*

Genjōkōan answers how groundless dependence comes forward as a case.

Linji supplies its guard-image. The reconstruction reads the true person of no rank (無位真人) along a seam: *no rank* (無位) is non-attainment; the true person going in and out (真人…出入) through the face-gates prevents no-rank from becoming inert; the whole figure holds no-rank and activity together. When the monk asks what the true person is—and then hesitates under Linji’s demand to speak—the phrase threatens to become a resting-place. Linji’s rebuff destroys that possibility, discarding even the “true person of no rank” once it begins to function as something identifiable or possessable. This no-rank, no-resting-place reading is called the **non-attaining middle**, or **unattaining middle**, when the emphasis falls on nothing being obtained or stored.

The reconstruction states that reading in Dōgen's vocabulary. **Shu** (修) is practice, the concrete doing. **Shō** (証) is realization, with the non-attaining floor-face at bottom placement in any given grading of a resonance. The homophone differs from the the *shō* in *mujishō*, which is 性, nature, while the **shō** in *shushō* is 証, realization.

Shō gains determinate content through a contrast within practice. At a bottom placement, practice has its non-attaining floor-face face: the act's subject-position is ceded, with nothing in the doing answering to a dis-resonant "self-forwards". At a non-bottom placement, that same practice is delusive to the extent that it arrogates the subject-position. This gives the non-attaining floor-face its grading counterpart. Genjōkōan has no corresponding delusion term: its contrast is empty dependence versus manifestation.

**Shushō** (修証) says practice-realization; **shushō-ittō** says that its practice and realization are non-dual. That cannot mean two events—practice first and an attained realization later—nor a still shō somehow acting by itself.

```text
                         one Graded Resonance

 practice, the doing (shu) ---- shushō ---- (shō) realization, as verified

                      shushō-ittō: not two events
```

**Genjōkōan**, the provisional middle, answers *how does empty dependence manifest as this case*? **Shō** answers *what is realization as verified*? Their distinction remains live when the grading is diagnosed, and loses its separating work where not.

## The act-grammar grid

> Carrying the self forward and practice-realizing the myriad dharmas is deemed delusion; the myriad dharmas coming forward and practice-realizing the self is awakening.
>
> — Dōgen, *Genjōkōan*
>
> To learn the Buddha Way is to learn the self.  
> To learn the self is to forget the self.  
> To forget the self is to be realized by the myriad dharmas.  
> To be realized by the myriad dharmas is to shed the body and mind of the self and the body and mind of other-selves.  
> There’s a resting of the traces of realization; a causing of the rested traces of realization to issue forth, long, long.
>
> — Dōgen, *Genjōkōan*

> *Practice in the midst of activity surpasses practice in stillness a hundred, a thousand, a hundred million times over.*
>
> — Hakuin Ekaku, *Orategama* I, quoting Dahui Zonggao

An **act-grammar** grid pairs a dependence-reading with an enactment-reading of one graded resonance across three rows. The enactment cells pick out three aspects of the quoted passages: *genjōkōan* is the actualizing of the case, *banpō susumite jiko o shushō suru* is the dharmas coming forward and the self being verified, and *dōchū no kufū* names that practice-realizing under the causal reading.

| Dependence reading | Enactment reading | Modelling |
|---|---|---|
| **mujishō-sōe** — mutual dependence without own-being | **genjōkōan** — the case manifesting fully | Mutual Dependence |
| **kannō-sōe** — responsive resonance placed under dis-resonance grading | **banpō susumite jiko o shushō suru** — the myriad dharmas coming forward and practice-realizing the self | Graded Resonance |
| **engi / inga** — dependent arising and cause/effect | **dōchū no kufū** — practice in the midst of activity | Causal |

Row 1 reads the resonance as manifestation without a substrate; Row 2 reads it as graded receiving and responding; Row 3 reads the doing under temporality and causation. Conversely, forgetting Row 3's overlays and Row 2's grades returns the one mutual dependence of the encounter.

## Floor-face and act-time face

The **floor** is not a first moment, a hidden base, or a final substance. It is the tier at which no deeper support is claimed and no distinction is doing separating work. A **floor-face** is this Encounter read under that no-own-being, no-claim condition. **Act-time** is the conventional diagnostic tier at which this call, this receiving, this response, this practice, and the distinctions needed to describe them are live. It is not a second Resonance before or after the floor-face.

The shushō reading introduced above is one example:

```text
                         one Graded Resonance

        act-time face                            floor-face

   concrete practice (shu) ---- shushō ---- (shō-graded-at-bottom) the being-verified
   in receiving/responding
```

Act-time follows the concrete receiving at `b₁` or responding at `b₂`; the floor-face reads that same `b₁` or `b₂` without an independently standing receiver or responder. Shu and shō are reciprocal faces of that receiving or responding within the Graded Resonance: one name follows the enactment, the other its no-own-being, non-attaining realization.

Floor corresponds to the term *nippapañca-dhātu*, an abstract term of “not proliferation”, which is what floor specifically refers to.

Act-time corresponds approximately to the term *vacī-saṅkhāra*, discursive/verbal thought.

The two terms can intersect, in designation without grasping, however here each is a term focusing on their specific aspect without considering whether the other is present of not.

One can talk of the floor at act-time in the same way that one can talk of sleep at act-time — it doesn’t in itself require the person to be sleeping to do so, or cause one to sleep necessarily, or anything like that.

To seek not-proliferation through not-*vacī-saṅkhāra* would be a one-sided approach toward not-proliferation. On the other side, ignoring *nippapañca-dhātu* because it is a “not-“, and considering *only* act-time would be another form of one-sidedness.

## Separate/fuse, utterances, and their offers

The **separate/fuse rule** states how distinctions behave across those tiers. At act-time a useful distinction separates. At the floor it fuses (floor = non-proliferation in the abstract), meaning that it makes no separating claim there—not that its two sides become one substance (non-proliferation wouldn’t assert that) and not that both propositions are asserted (non-proliferation wouldn’t assert that either).

|| **Distinction separates** | **Distinction fuses** |
|---|---|---|
| **Act-time diagnosis** | `A \| B  rule obeyed` | `A >< B collapse` |
| **Floor** | `A \|\| B freeze` | `A . B  rule obeyed` |

The two error cells occupy one diagonal; the other diagonal is the rule obeyed.

**Collapse**, written `><`, is premature fusion under act-time diagnosis; **freeze**, written `||`, is a useful separation reified as a floor-claim. “There is no time, no being, and no Resonance” is a collapse when offered where a response is occurring. A flowing time-container, substantial Being, stored shō, or self-existing Resonance is the corresponding kind of freeze.

An **utterance** isn’t a sentence-shape in isolation but its content carried by a resonance, with the call it answers and the tier at which it’s offered. The taxonomy in the section below checks the offer not the words alone. Ordinary narration offered conventionally at act-time is no error; the same words offered as ultimate furniture can freeze, while a denial offered as live diagnosis can collapse.

## The articulation joint

At an **articulation joint**, a distinction remains usable at act-time without receiving intrinsic standing at the floor. Freeze and collapse are the two ways this relation can fail. Each can operate either on a conventional articulation or on the deflationary correction of one.

The rows below name the material being mishandled. The columns name what is done with it.

| Material being mishandled | **Freeze `\|\|`: assigns final standing** | **Collapse `><`: removes live separation** |
|---|---|---|
| **Conventional articulation** — a live designation or distinction | **Intrinsic-joint realism.** `act-time → floor`: a usable term is treated as intrinsic. A being becomes substantial Being, shō becomes something stored, or the doer is placed prior to the deed. | **Identification.** `act-time → act-time`: terms whose difference remains live are fused. Sentience is read off function, or genjōkōan and shō are conflated. |
| **Deflationary correction** — a denial or other floor-speech | **Ground-reification.** `floor → floor`: emptiness, nonduality, the web, or the denial of a final floor is installed as a final item or ground. Nihilism and emptiness-sickness (空病) belong here. | **Erasure.** `floor → act-time`: a correction is used to cancel the live case. “No time” or “no being” denies an act underway; “does not fall under cause and effect” erases conduct where conduct matters. |

Identification and erasure are therefore different forms of collapse. Identification fuses terms within a live articulation. Erasure imports a deflationary correction into that articulation and uses it to cancel the case.

The freeze cells differ in the same way. Intrinsic-joint realism gives final standing to something used in conventional articulation. Ground-reification fixes the corrective itself as the final answer. Here “ground” names what the error invents, not anything the framework accepts as a ground.

The diagonals show the resulting register movements. Intrinsic-joint realism and erasure are register-mismatch errors: the first carries act-time furniture to the floor, while the second carries floor-speech into act-time. Identification and ground-reification are within-register errors: the first removes a distinction still needed at act-time, while the second turns floor-speech into an item at the floor.

Dependent articulation guards against both kinds of collapse. Because a distinction is dependently articulated, its terms can remain different where the case requires them without becoming intrinsic. For the same reason, their lack of intrinsic standing does not erase their conventional use. The ladder section develops this point by showing that every ultimate correction remains dependent on the articulation it corrects and can itself become material for further correction.

As elsewhere, these classifications concern an utterance with its call and offer, not a sentence-shape by itself. The same words may function as conventional articulation, intrinsic-joint realism, corrective medicine, or erasure according to the tier at which they are offered.

## A taxonomy of error

> This section still references the old version of the code, and *weld*, a
> conceptual fore-runner to (Graded) Resonance. The older model generally
> produces reasonable conclusions, however mostly as a result of structural
> artifact from reasonable modelling decisions as opposed to being
> meaningfully proven.
>
> The prose below currently runs ahead of the Lean side: cells marked
> `⟨no lemma yet⟩` have no formal counterpart, and the row names and table
> order are not yet reflected in `tableOrder` or the affected lemma names.
>
> The occupant labels used below are expository classifications. The
> current Lean development does not represent or audit them.

Classical nihilism turns out to be a freeze, not a collapse: the void is emptiness reified as an *absence* — a snake wrongly grasped is still grasping. And mis-typing — the state-tool for an act-job, the faculty-reading of Row 2 — is the freeze at the dated-grade/agent-type joint specifically: an act's grade frozen into a standing configuration of the agent.

The errors are categorised in two grades:

1. **Grammatical errors** — tier-errors and typing-errors. These the system can *assert*, because a mis-feed is a conventional-tier logic verdict, not a value. The old man of the fox kōan's mistake is assertable. (Assertable, note, *within the lens*: "tier-error" and "mis-feed" are verdicts of the two-truths machinery itself, compelled inside it and offered outside — the banner's clause governs the grid's own voice, and the asymmetry between the two grades is an asymmetry in that voice, not an appeal to lens-free logic.)
2. **Soteriological shortfalls** — arrogation, self-forward, low resonance, failure to meet beings. These the system can only *display* — Row 2 placements and Row 3 causation, valence borrowed from the object. The five hundred fox lives were returns, not punishments; by the same token "he failed to act as a bodhisattva" is never an asserted wrong, only a displayed asymmetry.
### Voice-discipline

Two errors formerly tabled under description/injunction are, in their pure
form, not committable by a being at act-time about an object-level call;
they are violations of the split between the two grades itself, and are
recorded here, where that split is defined, rather than as rows.

*Refusing to state the asymmetry* is the display-half abandoned: a theory
of poison that won't say which direction kills (`pole_validates_all_claims`,
`poleTier_inhabited_of_liveTerminus`; at genjōkōan all claims validate, fused;
the pole is not a truth-maker elsewhere). A being's analogue — meeting a
call with less than the stating it needs — is not a grammatical error but
the Grade-2 buddha-side shortfall.

*"Eat this"* is the assertion-half usurped: the displayed asymmetry taken
up *by the theory* as command — "escape this," the fourth truth said in the
theory's voice, is this error applied to dukkha
(`assertable_ne_displayable`). When a being mounts the same identification
in an act-time utterance — theodicy in a mouth, another's suffering
asserted as assignment — the error is tabled at
`<Displayed valence / issued command (uptake and issue of the orange); Identification; issuer-bank>`.

The recipient-side mirrors likewise remain in the table at
`<Displayed valence / issued command (uptake and issue of the orange); Identification; recipient-bank defiance>`
and
`<Displayed valence / issued command (uptake and issue of the orange); Identification; recipient-bank compliance>`,
because a being can commit them at a reception.

### Grade 1: the generator's output

Each row isolates one distinction. Freeze and collapse are operations upon
that distinction; the bold labels within each cell identify the material
mishandled by the particular error-occurrence. A distinction may admit
intrinsic-joint realism, ground-reification, or both as freezes, and
identification, erasure, or both as collapses. Material type therefore
belongs to an occupant of a cell, not to the row or cell as a whole. A
single utterance or compound position may instantiate more than one
occupant.

Each occupied subtype is printed with its full bold label and description.
`— structural: …` is reserved for a subtype that is genuinely unavailable.
An unmentioned subtype means only that it is not currently tabled or
established; it does not mean that the subtype is impossible.

Table membership requires committability in a being's act-time
utterance; theory-voice errors live in the voice-discipline note. A dash
must state a cell-specific structural reason. Cuts follow
classifying-lemma boundaries: a row's classifying lemmas are its own
family (`*_obeys`, `*_not_freeze`, `*_collapse_self_refuting`, and
cell-specific negatives); shared background lemmas —
`no_final_level_of_errorFree` supports both
`<Rung-finality; Ground-reification; final rung>` and
`<The ladder / its terminus; Ground-reification; emptiness-sickness>` — do
not by themselves merge distinct joints.

| Distinction | **Freeze `\|\|`** | **Collapse `><`** |
|---|---|---|
| Rung / pole of the grade (kenshō / genjōkōan) | **Intrinsic-joint realism.** Genjōkōan held as *final* kenshō — the pole as top rung, awakening as a still attainment, daigo as rank; "full satori" is this freeze miniaturized — a state-word for a per-call pattern (`rungPoleRow_not_freeze`) | **Identification.** A kenshō spoken *as* genjōkōan — a rung as the floor; the Zen sickness (禅病) of "stinking of Zen," an opening inflated into arrival — the fox's error at another joint (`rungPoleRow_obeys`, `kensho_as_genjo_collapse_self_refuting`, `rung_not_pole_witness`) |
| genjōkōan / shō (two middles) | **Intrinsic-joint realism.** Holding the two-middles distinction itself as a final floor-claim | **Identification.** Conflating them — manifestation taken as realization, or conversely |
| shō / satori (証 / 悟) | **Intrinsic-joint realism.** Satori as a datable possession | **Identification.** Reading the floor-face as the awakening-mode, or conversely |
| Dated grade / agent-type (the mis-typing joint; formerly act / state) | **Intrinsic-joint realism.** The act's grade frozen into a standing configuration of the agent — Resonance held as a faculty; buddha-nature as substance; the empty agent re-based. Distinct from doer/deed, where the doer's *priority* is reified — here it is the act's *type*; and from standing/dated, which takes the seed-side disposition against the dated act and expressly excludes configuration/act | **Identification.** The placement *being* the self — a grade of this dated act identified with the agent |
| Function / share | **Intrinsic-joint realism.** Function frozen into a standing device-nature — the mirror given a stand; originally not a single thing (本来無一物) is the corrective (`functionShareRow_not_freeze`) | **Identification.** Universal response identified with its share-cell — share-zero treated as non-response, or live share treated as the only real function; the identity *I-making just is the clench* is this collapse in embryo (`functionShareRow_obeys`, `function_share_cell_collapse_self_refuting`) |
| karma / inga | **Intrinsic-joint realism.** The soul: the index *stored* between welds — a standing bearer. Maximized, the solipsist's stored-index face annexes the whole field; the self-forward and Row 2-domain faces are neighboring cells in the compound decomposition rather than new rows (the solipsist is the stone's inverse: all response, no call, unable even to state what listening to Hyakujō would be) (`karmaIngaRow_not_freeze`, `solipsism_decomposition`) | **Identification.** The mis-feed: an index-free field fed to an index-requiring designation (`karmaIngaRow_obeys`, `misfeed_collapse_self_refuting`) |
| Sowing / reaping (the diachronic index) | **Intrinsic-joint realism.** The retrospective soul: the reach-back held as a standing backward relation rather than spent at reception — memory's felt storedness read literally is this freeze in psychological dress (`sowingReapingRow_not_freeze`) | **Identification.** Ownership read off the series alone; sameness-of-being as bare continuity-fact (`sowingReapingRow_obeys`, `series_ownership_collapse_self_refuting`, `no_diachronicWhose_from_series_alone`) |
| Delivery-question / index-question | **Intrinsic-joint realism.** One's future occurrence at others' Row 2 held now as a first-personal possession — "my potential," "my worth to them" — a delivery-fact, read at *their* act-times off whatever the field brings, frozen into something the being holds and could therefore weigh, spend, or withdraw — prudential privilege is this freeze's forward-facing twin, the cross-gap *whose* held as rational ground (`deliveryIndexRow_not_freeze`) | **Identification.** Mis-fed in either direction: an index-question fed to the index-free field (*did I earn this?* — akṛtābhyāgama's mis-feed half; *does the Tathāgata exist after death?* — the same mis-feed at the pole), or a delivery-fact arrogated by the weld — an act claiming command of what arrives next ("easy"; every exit-arithmetic; Devadatta's aim), authority over the one register no act holds (`deliveryIndexRow_obeys`, `misfed_register_collapse_self_refuting`) |
| Weld / event-type (severity) | **Intrinsic-joint realism.** Victim-rank: severity read off the victim's station — the honorific inflating the crime; rank smuggled back through the tariff (`weldEventTypeRow_not_freeze`) | **Identification.** Karma graded off the event-type with the weld erased — Cunda owed remorse, intention deleted from the arithmetic (`weldEventTypeRow_obeys`, `eventType_grading_collapse_self_refuting`) |
| Disposition / act (seed / clench) — **retyped: the distinction is standing/dated, never configuration/act** | **Intrinsic-joint realism.** The seed as bearer — ālaya frozen into a self carrying mineness between acts. Two further faces: the clench as *furniture* — contraction mistaken for a standing thing removable only with its substrate ("only ending me ends this"), dukkha held substrate-bound being this freeze wearing its valence, where de-clench is demolition-free by the same theorem that makes kenshō unholdable; and the clench as *structure* — contraction made constitutive of the being (anguish as the very form of consciousness — the Sartrean face; Zahavi's thin for-me-ness is expressly *not* this cell, taking the retype instead, per the placement in Identification) (`standingDatedRow_not_freeze`) | **Identification.** The dated occurrence read off the standing tendency — *he arrogates, so this act was arrogated* — prognosis substituted for diagnosis, Row 2 made to read seeds instead of deeds (what the determination reads — the configuration's part in driving *this* response — is not this cell: every act is the configuration's act); dukkha read off the seed — the proneness to suffer mistaken for suffering occurring — is the same collapse at the valence (`standingDatedRow_obeys`, `prognosis_as_diagnosis_collapse_self_refuting`, `standing_does_not_determine_dated`) |
| Per-weld mark / standing sentience | **Intrinsic-joint realism.** Sentience held as a nature the being has — affirmation or denial as nature (性); the mark is per act or it becomes a soul-shaped kind (`standingSentienceRow_not_freeze`) | **Identification.** Sentience identified with grid-visible function, in either direction — the retired `SentientTag = MountsSomewhere` identity was this collapse; machine behavior does not recover the mark (`standingSentienceRow_obeys`, `sentience_from_function_collapse_self_refuting`, `no_sentience_recovery`) |
| Displayed valence / issued command (uptake and issue of the orange) | **Intrinsic-joint realism.** The displayed asymmetry held as standing floor-furniture, persisting between calls rather than arising as the valence of this reception ⟨no lemma yet⟩ | **Identification.** Three occupants of one identification — valence taken as command — across two banks of a command never issued. Recipient-bank: defiance — the orange refused *as* command, shadow-boxing a voice the grid does not have (its one grammatical component; the rest of defiance remains Grade-2 display); and compliance — the asymmetry obeyed *as* order, distinct from value-uptake, which remains grid-legal (`assertable_ne_displayable`; legality of value-uptake: `existentialism_decomposition`, `existentialism_legal_count`). Issuer-bank: the asymmetry uttered *as* assignment at another's reception — theodicy in a being's mouth, suffering asserted as sentence, akṛtābhyāgama's displayed valence read out as command ⟨no lemma yet⟩. The theory-voice forms of both halves live in the voice-discipline note |
| shu / shō (the weld) | **Intrinsic-joint realism.** Two one-sided freezes: shō without shu (quietism, Dahui's silent-illumination target — emptiness that only empties) and shu without shō (practice as means to a later attainment, breaking shushō-ittō) (`foxWeldRow_not_freeze`) | **Erasure.** The fox: not-fall asserted conventionally — antinomianism. Converse fox: not-obscure insisted on at the floor — moralizing where nothing falls (`foxWeldRow_obeys`, `fox_notFall_collapse_self_refuting`, `fox_utterance_misfits_live_offer`) |
| Doer / deed | **Intrinsic-joint realism.** The prior doer: kāraka held prior to karman, MMK 8's target occupying its own cell; the soul in relational dress, distinct from the Pudgalavāda cell because here the *priority* is reified (`doerDeedRow_not_freeze`, `DoerDeedNegative.no_priority_recovery`) | **Erasure.** *No doer, only deeds* — bundle-reductionism spoken as live diagnosis, mounted by a being answering a call (`doerDeedRow_obeys`, `no_prior_doer_collapse_self_refuting`) |
| Self-pole / transposed (the terminus index) | **Intrinsic-joint realism.** The transposition erased upward: a self-pole weld held persisting at the summit — the subtlest soul, the true person of no rank (無位真人) as rank in weld-vocabulary; and *transposed* itself held as mechanism — an index that travels — is a miniature of the same freeze (`selfPoleTransposedRow_not_freeze`) | **Erasure.** The transposition erased downward: the terminus-act asserted indexless *and inert* — no self-pole and no standing at others' receptions either, the device dead even at others' Row 2; the exit-collapse in typing's clothes (`selfPoleTransposedRow_obeys`, `transposition_erased_downward_collapse_self_refuting`) |
| Before / after (the arrow, retyped; Lean-generated schema row) | **Intrinsic-joint realism.** The flowing container: temporality held as floor-furniture — *time really flows* — the retrospective soul's cosmological dress; eternalism-of-the-flow and the block-denier's arrow both land here, against `DirectionNegative` (`beforeAfterRow_not_freeze`) | **Erasure.** The deflation: *no time, so nothing happens, no one acts* — not-fall transposed to time, the fox's sentence at its largest scale; a floor-truth uttered where the conventional tier was live (`beforeAfterRow_obeys`, `no_time_collapse_self_refuting`, `beforeAfterLadder_obeys_succ`) |
| Intra-weld arrow (call/response order) | **Intrinsic-joint realism.** Temporality as interior furniture: *the call really is first*, before-and-after smuggled inside the weld against the transposition witness (`intraWeldArrowRow_not_freeze`, `InteriorDirectionNegative.no_interior_direction_recovery`, `intraWeldArrow_sunyata`) | **Erasure.** The deflation: *no call/response order, so no acts* — the interior arrow denied as a live diagnosis, refuting its own act-time tier (`intraWeldArrowRow_obeys`, `no_order_collapse_self_refuting`, `contentIntraWeldArrowRow_obeys_of_variation`) |
| Named being / floor (the being-convention; Lean-generated schema row) | **Intrinsic-joint realism.** The conventional designation is promoted to ontology: *prajñapti-sat* is taken as *dravya-sat* (*samāropa*), and the partition is held as floor-furniture against `BeingNegative` (`beingsRow_not_freeze`). Lewis is the nearest miss, right about plenitude and wrong about register; Huayan affirms the plenitude empty; Pudgalavāda is the classical occupant candidate. The monolithic self's soul is this freeze in fiber dress.<br><br>**Ground-reification.** Emptiness or absence is installed as final, so the correction “no being in itself” hardens into non-being as the floor. | **Identification.** No intrinsic cut is taken to mean no difference between being and non-being; the live convention and its absence are fused.<br><br>**Erasure.** *There are no beings* — the fox's sentence at the being-joint, the deflation's second dress; “no beings” offered as live diagnosis refutes its own tier (`beingsRow_obeys`, `no_beings_collapse_self_refuting`). Diamond Sūtra denial belongs here when spoken as live ontology rather than floor medicine. |
| Weld-grain / floor (the weld-convention; Lean-generated schema row) | **Intrinsic-joint realism.** The weld as svabhāva: one act-grain held as floor furniture, the last unemptied level pretending it was never a convention (`weldRow_not_freeze`, `weld_sunyata`) | **Erasure.** *No acts happen* — the fox's sentence at the act-joint, the deflation's last dress; "no welds are actual" offered as live diagnosis refutes its own tier (`weldRow_obeys`, `weld_denial_collapse_self_refuting`) |
| Terminus / exit | **Intrinsic-joint realism.** Private nirvāṇa as a rank; the pratyekabuddha freeze — *soteriological solipsism*: not denying that others exist but declining to exist *for* them, one's own standing at their Row 2 refused (Bull 10's marketplace is its corrective) (`terminusExitRow_not_freeze`) | **Erasure.** Not-fall taken as *escape* — the buddha as one who has left the loop rather than one who answers with no share claimed; the same collapse enacted rather than held is the exit-premise ("a way out"), and it fails on both axes — no exit from the arriving of calls, and none from the register at which one arrives for others; the terminus is a transposition of where the index-facts sit, not a departure from the loop (`terminusExitRow_obeys`, `exit_collapse_self_refuting`) |
| Per-call / global altitude | **Intrinsic-joint realism.** The stage-scheme error: bhūmis as rank held, a global altitude, rather than cross-sections of the loop's run — and its diagnostic twin, a delivery-fact read as altitude: "this being cannot awaken" said of a being some calls cannot reach. The freeze is two-banked: on the responder's side, upāya held as a standing competence — the device as possession, deployed unread of who is asking. The self-forward direction canonized as ontology or human condition is this row's direction face. The stored-quantity picture of awakening — an altitude accumulated and held — is this freeze under its sudden/gradual face (§2) (`perCallGlobalRow_not_freeze`, `solipsism_decomposition`, `existentialism_decomposition`) | — structural: "global altitude" names no live convention — it exists only as this freeze's invention — so there is no live separation for a collapse to remove; the nearest candidate, a trajectory read off one dated act, is already housed at the standing/dated collapse as prognosis-for-diagnosis |
| Being / emptiness (有空) | **Ground-reification.** Nihilism — emptiness reified as privative non-being, one more member of the being/non-being pair (Nishitani’s nihility, not śūnyatā); 有/空 is thereby frozen as being/non-being. | **Erasure.** Non-duality used as erasure — the live being-and-emptiness teaching is identified with its reified being/non-being form; 非有非空, which refutes the reified pair, is turned on the live one: “neither applies, so no distinction matters.” This is the deflationary form—level-3 medicine misapplied downward. It is distinct from *no beings* (level-2 medicine at the being-joint) and from *cheap transcendence* (emptying skipped rather than misapplied); the sentence still rides the distinction it cancels. |
| The ladder / its terminus (the emptying and its employment) | **Ground-reification.** Emptiness-sickness (空病): seeking a fifth negation, the emptying itself frozen into a path-object instead of the seeking dropped. The absence is structural: there is no "completed ladder" claim constructor (`no_final_level_of_errorFree`). As a formal-model analogue of 空空, priming is image-idempotent for `Reaches`: a second priming mints a further web-designatum but adds no paths among once-primed designata (`prime_reaches_exhausted_on_image`). `Joinable` is unchanged there only in the weaker, trivial sense that the first priming already made it total (`prime_joinable_exhausted_on_image`) | **Erasure.** Cheap transcendence — silence, ineffability, or other floor-speech used to cancel a live response without the climb that would make the correction fitting: an erasure by register-movement, though not the downward misapplication of an earned rung's medicine (that is the rung-finality dash's business, housed per target row). Floor-talk that cancels nothing is not this cell but the rung/pole collapse — an opening inflated, "stinking of Zen" ⟨no lemma yet⟩ |
| Theory / ultimate (the grid-lens; Lean-generated schema row) | **Ground-reification.** Grid-attachment: this lens taken as final (`gridLensRow_not_freeze`) | **Erasure.** The lens denied as live diagnosis — the grid dismissed because it is only a lens (`gridLensRow_obeys`, `lens_denial_collapse_self_refuting`) |
| Subject-axis / object-axis | **Ground-reification.** Object-axis standing denied — to another, reflexively, or in the solipsist's Row 2 evacuation: the denial installed as floor-fact, deflationary material reified. The death-freeze is re-derived without vacuity: unmarked pole welds have object-axis standing without a sentience mark, live share, natural door assignment, or landing-pattern; where remains-welds arise, death changes the character of new occurrences and cannot subtract the standing of those already actual. The realism-shaped twin — standing held as the being's annullable possession — is expressly not this cell and would be tabled as a separate occupant if wanted (`subjectObjectAxisRow_not_freeze`, `solipsism_contains_row2_domain_evacuation`) | **Identification.** Object-axis delivery identified with the receiver's own subject-position — two live terms fused, conventional material (`subjectObjectAxisRow_obeys`, `object_axis_as_subject_collapse_self_refuting`) |
| Rung-finality: level *n* held as last rung (Jizang's fourfold — Nāgārjuna's 空空, iterated; Lean-generated by `ladder_obeys`) | **Ground-reification.** Eternalism at level *n*: this pair is the final floor (`no_final_level_of_errorFree`, `ladder_obeys_of_errorFree`) | — structural: a rung's collapse is bookkept only at the next rung, as the misapplication of *that* rung's medicine (see the rung-indexing paragraph in "The ladder as medicine": a freeze is available at the rung where a distinction is stated; its collapse appears only on the next rung). Downward misapplication is therefore the joint's erasure cell iterated per rung, and its instances are housed at their target rows — *n*=2 at Named being / floor (with weld-grain at the act-joint), *n*=3 at Being / emptiness (non-duality-as-erasure), *n*=4 at Theory / ultimate |

One scope-note beneath the table, because a table of errors invites a misuse it must fence. The rows grade *offers*, not sentences. "A man walked into a bar" touches half the table's conventions — a being, a doer and a deed, a before and an after, one act-grain — and, offered as narration at the tier where narration lives, violates none of them: the semantics grants the conventional side of every row wherever an act is under way, validity by stipulation rather than an achievement the sentence earns, and the fit is checked schematically (`inForce_fits_actTime_offer`) while reading the bar-sentence as its instance is prose. The generator's standing verdict on ordinary conventional speech is *decline*. The same words can arrive under other offers — and each offer is a different utterance: one that holds the man out as substance, the walking as real flow, the bar as furniture of the ultimate stacks freezes per distinction touched; "no man, no walking," offered as live diagnosis, stacks collapses. The variable is the offer, never the words — a sentence-shape severed from call and tier is not even in the generator's domain (the gradeability rule's limit case). So a reader who leaves this table hearing error in every conventional utterance has committed `<Theory / ultimate; Ground-reification; grid-attachment>` — over-generation in diagnostic dress — and reversed the table's direction of protection: it is *because* of emptiness that everything works, and the conventional register is what the rows defend, not what they prosecute (`fitting_offer_is_actTime`: without the conventional, nothing is taught).

### Compound positions

The generator runs against whole positions, not only single utterances; named philosophies decompose into stacks of occupants, with nothing left over — which is the identity-claim's small sibling, testable the same way. Each component may be cited as `<distinction; mishandling; facet>`, with the facet omitted when the mishandling is already specific enough:

- **Skepticism** — one cell, worn once: the nihilism freeze's epistemic face `<Being / emptiness; Ground-reification; epistemic face>`. The inference from no-floor to no-warrant goes through only on the svabhāva assumption the ladder emptied — that conventional standing ever rested on a floor. The Vigrahavyāvartanī shape recurs: the skeptic needs the theory to hold a thesis of the defeasible kind, and "no level is a final floor" declines to be one. The one-cell check is `skepticism_decomposition` with `skepticism_core_cell_count`.
- **Solipsism** — the soul freeze maximized (index annexing field) `<karma / inga; Intrinsic-joint realism; stored index>`, self-forward absolutized (the delusion-direction canonized as ontology) `<Per-call / global altitude; Intrinsic-joint realism; direction>`, Row 2 evacuated `<Subject-axis / object-axis; Ground-reification; object-axis standing denied>`. MMK 8 blocks it at the charter: a doer dependent on nothing other is svabhāva, the one thing the grid has none of. It is also the grade's own asymptote — the share tending to totality — which is why the hell-dweller's world is "almost entirely object": the solipsist is where *almost* is deleted. The decomposition is checked as three stacked cells (`solipsism_decomposition`, `solipsism_core_cell_count`).
- **The exit-premise** ("ending the being ends this") — three cells stacked: the annihilationist freeze (death as floor-event) `<Subject-axis / object-axis; Ground-reification; death as floor-event>`, the terminus/exit collapse enacted (the loop treated as having a door) `<Terminus / exit; Erasure; exit>`, and the clench-as-furniture freeze (suffering mis-typed as substrate-bound) `<Disposition / act; Intrinsic-joint realism; clench as furniture>`; with delivery-arrogation riding alongside `<Delivery-question / index-question; Identification; delivery-arrogation>`. All of this is grade 1, assertable (`exitPremise_decomposition`, `exitPremise_core_cell_count`, `exitPremise_alongside_cell_count`, `exitPremise_voices`). What the grid displays and does not say is "so persist." The fox's release came by one reception done saying rather than by any of five hundred deaths *(checked: `fox_returns_delivered`, `fox_release_rung_not_pole`)*. Its funeral coda shows past welds continuing to land. This is object-axis standing, not a staticization theorem and not a claim that death changes nothing.
- **Existentialism** (read with Nishitani) — a four-cell stack, which is why it is the grid's nearest miss. Néant held as relative nothingness taken final — a rung-finality freeze at level n, one negation short of the emptying that empties itself `<Rung-finality; Ground-reification; néant>`; the *projet* — the self-forward direction canonized as the human condition rather than diagnosed per-act `<Per-call / global altitude; Intrinsic-joint realism; direction>`; anguish-as-structure — the clench frozen constitutive `<Disposition / act; Intrinsic-joint realism; clench as structure>`; and the fundamental project as an index *stored* between acts — a soul made of freedom, the weld asked to be its own floor `<karma / inga; Intrinsic-joint realism; stored index>`. What is *not* the error: value-creation. The grid explicitly permits a being to take a displayed asymmetry up as a value; choosing values is grid-legal. Only the self-grounding is the freeze — in its most sympathetic costume, since existentialist freedom genuinely resembles the weld (act-time self-making, no essence-substrate) and differs from it in exactly one respect: the weld is spent. The encoding checks four stacked cells plus one legal non-error (`existentialism_decomposition`, `existentialism_core_cell_count`, `existentialism_legal_count`, `existentialism_voices`).

### What the generator declines

Equally load-bearing is the case that classifies as **no error**. A being to which particular calls cannot be delivered — deaf and blind to the modalities a teaching travels by — commits nothing: which calls arrive at which configuration is inga's index-free business. This is a delivery-side absence, not function withheld and not an outside-domain kind. Every nearby error belongs to the diagnostician: reading failure of these calls to arrive as a global altitude ("this being cannot awaken") lands in `<Per-call / global altitude; Intrinsic-joint realism; delivery-fact as altitude>`. Hakuin's corrective bites here as delivery-engineering — finding the call that lands. The retired undefined/zero row has no work left to do.

The standing declines are recorded here once, beside that case. No probability apparatus enters over delivery: the grid consumes orderings only, and an effectiveness-ordering within a regime is all any theorem here reads. Three tempting cases get no category of their own: camping at an effective call lands in `<shu / shō (the weld); Intrinsic-joint realism; shu without shō>`; the self-announced device-made buddha is Linji's "dried piece of shit" and lands in `<Per-call / global altitude; Intrinsic-joint realism; device-certified rank>`; and industrial deployment of effective calls is displayable, while enjoining it lands in `<Displayed valence / issued command (uptake and issue of the orange); Identification; issuer-bank>`. Whether a universally effective call is possible is an empirical dispute about delivery. The manufactured machine's sentience is likewise not softened into a verdict: it is exactly what `no_sentience_recovery` leaves underdetermined. Severed-transcript classification remains declined by the gradeability discipline.

The same price is re-entered at the faith layer: faith in a device-pattern remains grid-legal, but that legality is a fact about faith's office, not an act-time certification of a device as holding a rank. `KsmdEffectiveTerminus` is the descriptive standing display used by the direct path; `KsmdFullyEnlightened` adds positive own-act-time `KsmdNoNescience` over pole-share speech-or-mind productions. For a terminus this entails the former speech-only no-delusion test under production fidelity, but the converse fails on a false pole-share thought. `KsmdFullyEnlightenedEnacted` adds a witnessed deed and an actual faithful fitting speech production, while `KsmdEffectiveOccurrence` carries the per-weld deed verdict.

### Grade 2: displayable shortfalls

These form the soteriological taxonomy proper, and here it genuinely grades, because Row 2 is a grade:

- **Self-forward** — Dōgen's delusion, the fox's *saying*. A Row 2 direction, per-act.
- **Arrogation** — the act's subjecthood claimed self-ward, read as the index pitched to the self-pole at this call. Per-call, so there is no standing rank of how deluded a being is — only the trajectory the loop draws.
- **Clenched reception** — the fox's five hundred lives: returns received saying-mode, the reach-back welding mine with a tight fist. The receiving is graded exactly as any deed is *(checked: `fox_dukkha_per_life`)*.
- **Declining the orange** — the theory (or any dharma) received and set down. Not a wrong: a low-resonance reception *of this call*, per-call, from which nothing global follows; the next call reads fresh.
- **Defiance** — arrogation as policy, the returns fought open-eyed, reception after reception. Grammatically it contains `<Displayed valence / issued command (uptake and issue of the orange); Identification; recipient-bank defiance>` — an injunction resisted that was never issued; the rest is display. And `<Disposition / act; Identification; prognosis as diagnosis>` guards against the corresponding prognosis: the fighting-stance is a seed, an inga-fact — each fight a fresh act, no standing rank of defiance, and no configuration from which release is impossible, since the next call reads a new placement. The grid displays the asymmetry and the trajectory; it cannot assert the fighter wrong, and that restraint is not a limit of the diagnosis but its content.
- **Sparse delivery or rigid response** — few calls arrive, or the actual responses vary little. Neither is near-zero function and neither determines the supplied sentience mark.
- **The buddha-side shortfall** — answering a not-yet-buddha's call with anything less than meeting it where it is, delivery-engineering included. By the orthogonality rule (Theory) it is the pole's one live grade — graded ordinal with effectiveness, independent of typing, so a terminus-typed responder can still be maximally shortfallen: the reading that never reaches (the terminus, above). This is where the bodhisattva enters *structurally*: Hakuin's corrective is already the bodhisattva-function, and Row 2 exists because of it. The grid can display that response-without-share to *another being's* call just is what saving beings looks like — the theory's own existence (the orange handed over, banpō susumite) is an instance; and the prudence theorem above shows its other face, concern running on delivery-facts alone once the arrogation is subtracted. What the grid cannot do is enjoin it, or it commits the "eat this" collapse in its own voice. So the split between assertion and display *locates* the bodhisattva structurally, with no added axiom — room and shape, not pull: nothing in the grid explains why response-without-share to another's call occurs rather than merely being classifiable, and the grid does not pretend to; occurrence is the object's affair, reported. "Ignorance of buddhahood" splits accordingly: its assertable face is `<Terminus / exit; Erasure; exit>`; its displayable face is the buddha-side shortfall.

### Outside the framework

Two remainders. **Pre-grid ignorance** — svabhāva realism, the provisional middle never reached: the grid diagnoses it (a freeze at level zero), but the being in it has no vocabulary in which the diagnosis lands — the orange unrecognized as food. **Errors about the theory** — grid-attachment and its mirror, the lens dismissed *because* it is only a lens. The Disclaimers (Identification) block the first; "other doctrines can and do hold too" is the theory declining to freeze itself against the second.

### Non-linearity

The taxonomy is not a map of places on a path. Immunity is checked per production, not stored as a safe stage: arhat quiet excludes the live self-pole through all three doors, while buddha no-nescience additionally requires positive truth from each pole-share speech-or-mind production. The former can hold while the latter fails, so the old “no safe stage” future-work absence is retired as this production-level check, not converted into rank furniture. This is why the fox kōan, a story about one sentence spoken once, can carry the whole system's diagnostics: the errors are not stations but ways the separate/fuse rule can be violated *now*. The taxonomy remains answerable in the other direction too: the deaf-blind case classifies as nothing, or else the generator would be a lens that finds error wherever it looks.

## The ladder as medicine

> It is to cure the illness of one-sidedness that there is a middle. Once the illness of one-sidedness is removed, the middle likewise is not established.
>
> — Jízàng, *The Profound Meaning of the Three Treatises* (三論玄義)

Jizang’s four levels of the two-truths teaching follow a teaching as it meets attachment. At each level, a conventional distinction remains available for use. A freeze occurs when that distinction is accorded final standing. The ultimate truth at the right of the row addresses that overreach without cancelling the distinction’s conventional use.

A teacher says, “Bring the cart,” because a load needs moving. “Cart” works as a conventional designation for the assembled cart. If someone instead treats the cart as self-standing apart from its parts and conditions, “the cart is empty of own-being” answers that attribution of self-standing; it does not deny the cart’s conventional availability.

At the second level, the teaching can keep two targets in view: the conventionally functioning cart and the reification of that cart as self-standing. Emptiness addresses the latter. A collapse occurs when the two targets are conflated, so that the denial of own-being is misapplied to the cart’s conventional function. The collapsing inference is: “Because no cart exists in itself, no cart is available to move the load.” Quoted conclusions in the collapse column report this misuse; they are neither the table’s assertions nor its injunctions.

The table reads from conventional truth on the left to its fitting ultimate truth on the right. The freeze column records what happens when the current conventional truth is accorded final standing. The collapse column records a different misuse: the preceding correction is turned indiscriminately on both the lower-level freeze and the live convention with which that freeze has been conflated.

| Conventional-truth | Freeze (held at floor) | Collapse (live conventional fused with lower-freeze) | Ultimate-truth |
|---|---|---|---|
| **First-level (一重): being (有).** The cart, path, being, or another useful distinction is live. A posited term brings two aspects together: the term (the cart) and the cut that individuates it (cart / not-cart). | A freeze occurs if either aspect is held at the floor: the cart's being treated as own-being (自性), the cart independently real; or its boundary treated as own-mark (自相), the cut held self-standing and prior to the case. *(See `<Named being / floor; Intrinsic-joint realism; own-being>` and `<Named being / floor; Intrinsic-joint realism; own-mark>`, and intrinsic-joint realism in the articulation joint.)* | — | **Emptiness (空).** It denies own-being to the term and own-mark to its boundary, without cancelling the conventional use of either. The model's guards correspond: no interdependent component is entered as the self-standing base of the other (`mujishō-sōe`), and `d ↓ e ⇏ d = e`, `A ⋈ B ⇏ A = B` (joinability is not identity). |
| **Second-level (二重): being-and-emptiness (有空).** The lower-level convention, its possible finalization, and emptiness as the correction of that finalization are all available as teaching. | A freeze occurs if emptiness is treated as a final absence standing over against being. The two-truths teaching is thereby recast as a two-item ontology. *(See `<Being / emptiness; Ground-reification; nihilism>`.)* | A collapse occurs if emptiness, stated at row 1, is turned on the live convention rather than its freeze. Two faces, matching row 1's two freezes: the conventionally functioning cart conflated with the self-standing cart, so that denial of own-being yields "Because no cart exists in itself, no cart is available for the task"; and the case-bound cut conflated with the self-standing cut, so that denial of own-mark yields "Because no cut is intrinsic, there is no difference between cart and not-cart" — dependence, joinability, or a shared witness promoted to identity. The same moves can cancel a live practice or response. *(See `<Named being / floor; Erasure; no beings>` and `<Named being / floor; Identification; being / non-being>`, and erasure and identification in the articulation joint.)* | **Neither-being-nor-emptiness (非有非空).** It denies final standing to both being and emptiness without prohibiting their pedagogical use. |
| **Third-level (三重): duality-and-non-duality (二不二).** The being-and-emptiness pair is available as duality, and neither-being-nor-emptiness as its non-duality. | A freeze occurs if neither-being-nor-emptiness, or non-duality, is treated as a final middle position. *(See `<Rung-finality; Ground-reification; n=3>`.)* | A collapse occurs if the live being-and-emptiness distinction is conflated with its frozen form. Neither-being-nor-emptiness is then misapplied to the live distinction, yielding the erroneous conclusion: “Neither being nor emptiness applies, so no distinction matters.” *(See `<Being / emptiness; Erasure; non-duality as erasure>`.)* | **Neither-duality-nor-non-duality (非二非不二).** It denies final standing to both duality and non-duality without making their distinction unusable. |
| **Fourth-level (四重): the first three levels as teaching-language (言教).** Their distinctions and corrections remain available as teaching. | A freeze occurs if the four-level account is treated as the last teaching and its final distinction is retained as doctrine. *(See `<Rung-finality; Ground-reification; n=4>`.)* | A collapse occurs if the live use of the preceding teachings is conflated with a fixed doctrinal scheme. Neither-duality-nor-non-duality is then misapplied to teaching itself, yielding the erroneous conclusion: “No distinction or non-distinction applies, so nothing can be said or taught.” *(An instance of the joint's erasure cell iterated at the teaching-language rung, housed as a schema-instance at `<Theory / ultimate; Erasure; lens denial>` — the live teaching dismissed because it is "only" a scheme; see the articulation joint and the rung-finality dash.)* | **Words-forgotten-and-thought-cut-off (言忘慮絶), with nothing-relied-on-or-acquired (無所依得).** These phrases describe the teaching’s completion without installing another position or issuing an injunction to silence. |

Jizang states one medicine at the first level. The reconstruction reads it as answering two freezes at once, because Madhyamaka's target was the self-individuated Abhidharma dharma: what a thing is and where it ends were one fact, so own-being (自性) and own-mark (自相) fell to the same denial. The model's two guards — no self-standing base for either component, and joinability without identity — disaggregate that row without adding a rung beneath it. The dash in row 1's collapse cell is therefore structural: a collapse misapplies the medicine of the row above, and emptiness is row 1's own.

Jizang’s fourth-level gathers the preceding levels as teaching-gates (教門) and brings them to the principle-gate (理門). This supplies the pedagogical closure of the four-level account. This corresponds to non-proliferation, the floor, while not precluding non-clinging designation at act-time from taking place.

The ladder uses the Grade-1 error-cells; it doesn’t introduce new occupants. A freeze is available at the rung where a distinction is stated, whereas its collapse appears only on the next rung, after its ultimate truth has been stated. Thus `<Named being / floor; Intrinsic-joint realism; own-being>` and `<Named being / floor; Intrinsic-joint realism; own-mark>`, read with the articulation joint's notion of **intrinsic-joint realism**, supply row 1's two freeze-faces; `<Named being / floor; Erasure; no beings>` and `<Named being / floor; Identification; being / non-being>`, read with the joint's **erasure** and **identification**, supply row 2's two collapse-faces; and `<Being / emptiness; Ground-reification; nihilism>` and `<Being / emptiness; Erasure; non-duality as erasure>` supply row 2's freeze and row 3's collapse, respectively.

Silence or ineffability can cancel a live response; the taxonomy keeps this
at `<The ladder / its terminus; Erasure; cheap transcendence>`. The ineffable
or emptying itself can be held as final and prompt the search for a
fifth-negation; the taxonomy keeps this at
`<The ladder / its terminus; Ground-reification; emptiness-sickness>`.

The archived Lean construction analyses a mathematical model of an *infinite* ladder, where the fourth rung onwards are negations of what came before. It records what happens when a description of that closure becomes another claim, and further rungs repeat the emptying of statable claims. The infinite ladder is governed by `no_final_level_of_errorFree`. No statable rung supplies final-standing, and the floor remains available to the whole infinite ladder (`words_idle_at_floor`, `no_row_claim_holds_at_floor`).

The Chinese terms provide the philosophical reading of the ladder. The theorem-names in this section follow the archived Ladder/Metaphysics model still cited by the taxonomy above.

## From mutual dependence to interpenetration

### Extension

Note how designation and elaboration is — how we’ve defined it above — a fundamentally *additive* process. There is no pre-existing database saying what something is not. And given ‘d’ elaborating to one mutual dependence, we equally are free to elaborate it additionally as yet another mutual dependence.

So a mutual dependence may be freely extended in either direction:

```text
initial:           no   ⇓       [{n} ⋈ {o}]
extend left:      mn    ⇓ [{m} ⋈ {n}]
extended left     mno   ⇓ [{m} ⋈ {n} ⋈ {o}]

initial:           no   ⇓       [{n} ⋈ {o}]
extend right:       opq ⇓             [{o} ⋈ {p, q}]
extended right:    nopq ⇓       [{n} ⋈ {o} ⋈ {p, q}]

extended both:    mnopq ⇓ [{m} ⋈ {n} ⋈ {o} ⋈ {p, q}]
```

This follows from the supplied philosophical reading. We say that n *implicates* m and o *implicates* p.

### Contraction

A mutual dependence may be contracted, by replacing interdependence with designation:

```text
extended both:    mnopq ⇓ [{m} ⋈ {n} ⋈ {o} ⋈ {p, q}]
contracted left:  mn    ⇓ [{m} ⋈ {n}]
                  mnopq ⇓ [{mn} ⋈ {o} ⋈ {p, q}]
contracted right:   opq ⇓              [{o} ⋈ {p, q}]
                  mnopq ⇓ [{m} ⋈ {n} ⋈ {opq}]
contracted both:  mnopq ⇓ [{mn} ⋈ {opq}]
```

### Extension and Contraction

If we repeat the process of extension and contraction indefinitely from any starting position, be it `a` or `z`,
then at the *limit*, we can describe a *web*, representing the totality of interdependence.

```text
  viewed from a:   ⋊ {a} ⋈ {bcde...wxyz} ⋉
  viewed from z:   ⋊ {abcd...vwxy} ⋈ {z} ⋉

  web :=           ⋊ {abcd...wxyz} ⋉
```

This example is illustrative of the web’s total scope, though the open-prime construction below realizes it as a hub of pairwise alternative elaborations, not as a fixed single elaboration.

### Investigation

Looking *within* `a` equally reveals the story of the totality contained by `a`:

```text
a ⇓ [{a} ⋈ {c}] a ⇓ [{a} ⋈ {h}]

c ⇓ [{c} ⋈ {e}] c ⇓ [{c} ⋈ {j}] h ⇓ [{h} ⋈ {j}] h ⇓ [{h} ⋈ {o}]

e ⇓ [{e} ⋈ {g}] e ⇓ [{e} ⋈ {l}] j ⇓ [{j} ⋈ {l}] j ⇓ [{j} ⋈ {q}] o ⇓ [{o} ⋈ {q}] o ⇓ [{o} ⋈ {v}]

g ⇓ [{g} ⋈ {i}] g ⇓ [{g} ⋈ {n}] l ⇓ [{l} ⋈ {n}] l ⇓ [{l} ⋈ {s}] q ⇓ [{q} ⋈ {s}] q ⇓ [{q} ⋈ {x}] v ⇓ [{v} ⋈ {x}] v ⇓ [{v} ⋈ {c}]

continues… spreading out
```

At the *limit*, this surfaces the totality of the previous section. The web *rolls up* the elaborations revealed under investigation.

### The web

What the formalism calls **Prime** elaboration is for the designator to designate under the expansive
understanding above, that to designate `a` is in the same moment to implicate the web of totality directly reachable from and including `a`. The formal model calls this **closed prime**. In this prime mode of
designating, `a` *contains* the web, which is called **all in each**.

Going in the opposite direction, from web to `a`, is
very natural, as we defined the web in terms of `a` initially. For analytic purposes,
the formalism considers that case separately and calls it **open prime**, but it’s still the
straightforward fact that having defined the web from `a`, the web *contains* `a`, which is called **each in all**.

Throughout this section, we fix the operators not with the base elaboration `E`, but with `prime(E)`:

```math
\to^*_{\operatorname{prime}(E)}\quad\downarrow_{\operatorname{prime}(E)}\quad\bowtie_{\operatorname{prime}(E)}\quad\Downarrow_{\operatorname{prime}(E)}\quad
```

Closed prime has this shape:

```text
  a →∗ web ←∗ b

web doesn’t reach a or b
(no outgoing elaboration clauses are defined in closed prime)
```

The inference rule:

```math
\frac{}{d\to^*\mathsf{web}}
```

This implies joinability for all prime designata and interdependence for all prime components:
```math
\left(\forall a\in\mathcal D.\;a\to^*\mathsf{web}\right)
\Longrightarrow
\left(\forall d,e\in\mathcal D.\;d\downarrow e\right)
\Longrightarrow
\left(\forall A,B\subseteq\mathcal D.\;A\bowtie B\right)
```

Reachability also implies interdependence with web:

```math
\left(
\forall a.\;
a\to^*\mathsf{web}
\right)
\Longrightarrow
\left(\forall d.\;d\downarrow \mathsf{web}\right)
\Longrightarrow
\left(
\forall d.\;
\{d\}\bowtie\{\mathsf{web}\}
\right)
```

```math
\{d\}\bowtie\{\mathsf{web}\}
\quad\Longleftrightarrow\quad
\{\mathsf{web}\}\bowtie\{d\}.
```

The two prime constructions realize this interdependence as a direct elaboration clause — for every $d\in\mathcal D$:

Prime closed (all in each):

```math
d
\Downarrow
[\{d\}\bowtie\{\mathsf{web}\}]
```

Prime open (each in all):

```math
\mathsf{web}
\Downarrow
[\{\mathsf{web}\}\bowtie\{d\}]
```

Open prime retains all closed-prime clauses and adds the clauses
from the web back to every member:

```text
  members to web:    a →∗ web ←∗ b
  web to members:    a ←∗ web →∗ b

  therefore:         a →∗ web →∗ b
```

The inference rule:

```math
\frac{}{\mathsf{web}\to^*d}
```

As an equation:
```math
\left(\forall a.\;a\to^*\mathsf{web} \land \mathsf{web}\to^*a\right)
\Longrightarrow
\left(\forall d,e.\;d \to^* e\right)
```

In open prime *reaches* is total, though that doesn’t change joinability
which is already total in closed prime.

```text
                          CLOSED PRIME        OPEN PRIME

    member →∗ web           yes                yes
    web →∗ member           no                 yes
    a →∗ b                  as at base         always
    a ↓ b                   always             always
```

As in the base elaboration, Temporality is overlaid (or can be lifted from base),
although neither designata nor the web are “before” the other.

### Supplied philosophical reading

> The dust-mote, lacking own-nature, in its entirety wholly pervades the ten directions—this is spreading-out.  
> The ten directions, lacking substance, following conditions wholly appear within the dust-mote—this is rolling-up. The sūtra says: “One Buddha-land fills the ten directions; the ten directions enter the one, and without remainder.” When rolled-up, all phenomena appear within one dust-mote. If spread-out, one dust-mote pervades all places. Precisely in spreading-out, it is constantly rolled-up—because one dust-mote subsumes all. Precisely in rolling-up, it is constantly spread-out—because all subsumes the one dust-mote.  
> This is the sovereign freedom of rolling-up and spreading-out.
>
> — Fǎzàng, *One Hundred Gates to the Sea of Meaning of the Huayan Sūtra*, Gate Four, section 9, “Rolling Up and Spreading Out”; *Taishō Tripiṭaka* 45, no. 1875, p. 631a4–9

A recap of the structures:

```text
  base elaboration        act-time articulation; local differences remain
  closed prime            every member reaches the common web
  open prime              members directly reach web; web directly reaches every member
  prime elaboration       adds suchness correspondence positively
```

Prime elaboration does no separating work, and corresponds to suchness, which is a specific kind of act-time non-proliferation.

```text
  CLOSED PRIME

  each member  →∗  web (= all)              ALL IN EACH

  OPEN PRIME

  each member  →∗  web (= all)              ALL IN EACH
  each member  ←∗  web (= all)              EACH IN ALL
```

In the closed prime, every member directly reaches the web. Since the web defines the
all, this is **all in each**: start from any one member and its elaboration
implicates the whole. The open prime adds the other half,
**each in all**: the web directly reaches every member.

## Credits

With thanks to Anthropic’s Claude Fable and OpenAI’s GPT-5.6 Sol. The theory was co-developed by the three of us with equal contribution.
