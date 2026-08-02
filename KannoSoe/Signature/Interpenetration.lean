import KannoSoe.Signature.V2

/-!
# Interpenetration by elaboration

This module adds a fresh designatum to an elaboration system and studies two
ways of using it.  The declarations below are formal model structure.  The
words *web*, *closed*, and *open* in documentation are supplied readings of
that structure; no declaration attributes understanding, consciousness, or
personhood to a designatum.

`Elaboration.prime E` uses `none : Option D` as a fresh web-designatum.  It
lifts every old clause along `some` and gives each lifted old designatum an
additional clause whose components are itself and `none`.  The construction
is additive and remains agnostic about the linkage bundled in an elaboration
target.

`Elaboration.primeOpen E` additionally lets `none` elaborate back to every
lifted old designatum.  The closed and open systems can differ for `Reaches`,
as the witness below shows, but not for `Related`.

Finally, `freshSourceExtension` isolates a conservative shape.  Clauses
sourced at `none` may target arbitrary designata; their targets need no
restriction.  Conservativity instead relies on every clause sourced at an
embedded old designatum containing only `some` images, so no old-started path
can enter `none`.  Allowing `none` in an old-sourced component list — as
`prime` does — is precisely what can destroy conservativity.
-/

universe u v

private theorem list_mem_map_of_mem {A : Type u} {B : Type v}
    {f : A → B} {a : A} {xs : List A} (h : a ∈ xs) :
    f a ∈ xs.map f := by
  induction h with
  | head xs => exact .head _
  | tail x _ ih => exact .tail (f x) ih

private theorem exists_of_list_mem_map {A : Type u} {B : Type v}
    {f : A → B} {b : B} {xs : List A} (h : b ∈ xs.map f) :
    ∃ a, a ∈ xs ∧ f a = b := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
      cases h with
      | head => exact ⟨x, .head _, rfl⟩
      | tail _ htail =>
          obtain ⟨a, ha, hab⟩ := ih htail
          exact ⟨a, .tail x ha, hab⟩

/-! ## Mapping components and raw targets -/

namespace Component

/-- Direct image of a component along a map of designata. -/
def map {D : Type u} {D' : Type v} (f : D → D')
    (c : Component D) : Component D' where
  carrier d' := ∃ d, d ∈ c ∧ f d = d'
  nonempty := by
    obtain ⟨d, hd⟩ := c.nonempty
    exact ⟨f d, d, hd, rfl⟩

@[simp] theorem mem_map_iff {D : Type u} {D' : Type v}
    (f : D → D') (c : Component D) (d' : D') :
    d' ∈ c.map f ↔ ∃ d, d ∈ c ∧ f d = d' :=
  Iff.rfl

theorem mem_map {D : Type u} {D' : Type v}
    {f : D → D'} {c : Component D} {d : D} (h : d ∈ c) :
    f d ∈ c.map f :=
  ⟨d, h, rfl⟩

end Component

namespace RawMutualDependence

/--
Map every component of a raw target.  The new linkage is an explicit
parameter: component transport cannot, and need not, manufacture a linkage.
-/
def mapComponents {D : Type u} {D' : Type v}
    (rawM : RawMutualDependence D) (f : D → D') (L : Linkage D') :
    RawMutualDependence D' where
  linkage := L
  c₁ := rawM.c₁.map f
  middle := rawM.middle.map (Component.map f)
  cₙ := rawM.cₙ.map f

@[simp] theorem components_mapComponents {D : Type u} {D' : Type v}
    (rawM : RawMutualDependence D) (f : D → D') (L : Linkage D') :
    (rawM.mapComponents f L).components =
      rawM.components.map (Component.map f) := by
  simp [mapComponents, components]

end RawMutualDependence

/-! ## Additive extension and monotonicity -/

namespace Elaboration

/-- Pointwise inclusion of elaboration clauses on a fixed domain. -/
def Extends {D : Type u} (E E' : Elaboration D) : Prop :=
  ∀ ⦃d rawM⦄, E.Elab d rawM → E'.Elab d rawM

instance {D : Type u} : LE (Elaboration D) :=
  ⟨Extends⟩

/-- Adding elaboration clauses can only add reachability. -/
theorem Reaches.mono {D : Type u} {E E' : Elaboration D}
    (hExt : E ≤ E') {d e : D} (h : E.Reaches d e) : E'.Reaches d e := by
  induction h with
  | refl d => exact .refl d
  | step hElab hcomponent hmem _ ih =>
      exact .step (hExt hElab) hcomponent hmem ih

/-- Adding elaboration clauses can only add relatedness. -/
theorem Related.mono {D : Type u} {E E' : Elaboration D}
    (hExt : E ≤ E') {a b : D} (h : E.Related a b) : E'.Related a b := by
  obtain ⟨w, ha, hb⟩ := h
  exact ⟨w, ha.mono hExt, hb.mono hExt⟩

/-! ## Priming and saturation -/

/--
Adjoin `none` as a fresh designatum, lift all old clauses along `some`, and
add for every old `d` a clause with components `{some d}` and `{none}`.

Only `components` is constrained.  In particular, the definition neither
fixes the target's bundled linkage nor asserts that the target holds.
-/
def prime {D : Type u} (E : Elaboration D) : Elaboration (Option D) where
  Elab od rawM :=
    match od with
    | none => False
    | some d =>
        (∃ oldM, E.Elab d oldM ∧
          rawM.components =
            oldM.components.map (Component.map Option.some)) ∨
        rawM.components =
          [Component.singleton (some d), Component.singleton none]

/-- Old reachability is preserved by the embedding into a primed system. -/
theorem Reaches.prime {D : Type u} {E : Elaboration D} {d e : D}
    (h : E.Reaches d e) :
    (Elaboration.prime E).Reaches (some d) (some e) := by
  induction h with
  | refl d => exact .refl (some d)
  | @step d e f rawM a hElab hcomponent hmem _ ih =>
      let mapped :=
        rawM.mapComponents Option.some
          (Linkage.ofElaboration (Elaboration.prime E))
      exact Reaches.step (rawM := mapped) (a := a.map Option.some)
        (Or.inl ⟨rawM, hElab, by simp [mapped]⟩)
        (by
          rw [RawMutualDependence.components_mapComponents]
          exact list_mem_map_of_mem hcomponent)
        (Component.mem_map hmem) ih

/-- Every designatum in a primed system reaches the fresh designatum. -/
theorem prime_reaches_web {D : Type u} (E : Elaboration D)
    (d : Option D) : (prime E).Reaches d none := by
  cases d with
  | none => exact .refl none
  | some d =>
      let rawM :=
        RawMutualDependence.pair (Linkage.ofElaboration (prime E))
          (Component.singleton (some d)) (Component.singleton none)
      exact Reaches.single (rawM := rawM) (a := Component.singleton none)
        (Or.inr (by simp [rawM])) (by simp [rawM]) (by simp)

/-- `Related` is total after one priming. -/
theorem prime_related_total {D : Type u} (E : Elaboration D)
    (a b : Option D) : (prime E).Related a b :=
  ⟨none, prime_reaches_web E a, prime_reaches_web E b⟩

/-- Total relatedness makes `Related` transitive in the primed tier. -/
theorem prime_related_transitive {D : Type u} (E : Elaboration D) :
    ∀ ⦃a b c : Option D⦄,
      (prime E).Related a b → (prime E).Related b c →
        (prime E).Related a c := by
  intro a _ c _ _
  exact prime_related_total E a c

/-- Every pair of nonempty components is linked in the primed tier. -/
theorem prime_linked_total {D : Type u} (E : Elaboration D)
    (c₁ c₂ : Component (Option D)) : (prime E).Linked c₁ c₂ := by
  obtain ⟨a, ha⟩ := c₁.nonempty
  obtain ⟨b, hb⟩ := c₂.nonempty
  exact
    ⟨fun x _ => ⟨b, hb, prime_related_total E x b⟩,
      fun y _ => ⟨a, ha, prime_related_total E a y⟩⟩

private theorem chainLinked_of_total {D : Type u} {L : Linkage D}
    (h : ∀ c₁ c₂, L.Linked c₁ c₂) :
    ∀ cs : List (Component D), L.ChainLinked cs
  | [] => .nil
  | [c] => .single c
  | c₁ :: c₂ :: rest =>
      .cons (h c₁ c₂) (chainLinked_of_total h (c₂ :: rest))

/--
After re-tagging by the primed linkage, every raw dependence holds.  This is
a statement about saturation of the primed formal tier, not about the status
of an unprimed act-time elaboration.
-/
theorem prime_certification_trivial {D : Type u} (E : Elaboration D)
    (rawM : RawMutualDependence (Option D)) :
    (prime E).certify rawM |>.Holds := by
  apply chainLinked_of_total
  intro c₁ c₂
  exact prime_linked_total E c₁ c₂

/--
There is an elaboration with a genuinely unrelated old pair whose images are
related after priming.  Thus the saturated tier cannot replace the diagnostic
base tier without losing information.
-/
theorem exists_tier_noncollapse :
    ∃ (D : Type) (E : Elaboration D) (a b : D),
      ¬ E.Related a b ∧ (prime E).Related (some a) (some b) := by
  obtain ⟨D, E, a, _, c, _, _, _, _, _, hnac⟩ :=
    Related.exists_nontransitive_mutualDependence
  exact ⟨D, E, a, c, hnac, prime_related_total E (some a) (some c)⟩

/-! ## Closed and open brackets -/

private theorem prime_reaches_some_aux {D : Type u} {E : Elaboration D}
    {start target : Option D} (h : (prime E).Reaches start target) :
    ∀ {b : D}, target = some b →
      ∃ a, start = some a ∧ E.Reaches a b := by
  induction h with
  | refl d =>
      intro b hd
      exact ⟨b, hd, .refl b⟩
  | @step d e f rawM c hElab hcomponent hmem _ ih =>
      intro b hf
      obtain ⟨e₀, he, hreach⟩ := ih hf
      subst e
      cases d with
      | none => simp [prime] at hElab
      | some d =>
          rcases hElab with
            ⟨oldM, hOld, hcomponents⟩ | hcomponents
          · rw [hcomponents] at hcomponent
            obtain ⟨oldC, holdC, hc⟩ :=
              exists_of_list_mem_map hcomponent
            subst c
            obtain ⟨e', he', heq⟩ := hmem
            simp only [Option.some.injEq] at heq
            subst e'
            exact ⟨d, rfl, Reaches.step hOld holdC he' hreach⟩
          · rw [hcomponents] at hcomponent
            simp only [List.mem_cons, List.not_mem_nil, or_false]
              at hcomponent
            rcases hcomponent with rfl | rfl
            · simp only [Component.mem_singleton_iff, Option.some.injEq]
                at hmem
              subst e₀
              exact ⟨d, rfl, hreach⟩
            · simp at hmem

/-- A path ending at an old image in the closed prime starts at an old image. -/
theorem prime_reaches_some {D : Type u} {E : Elaboration D}
    {start : Option D} {b : D}
    (h : (prime E).Reaches start (some b)) :
    ∃ a, start = some a ∧ E.Reaches a b :=
  prime_reaches_some_aux h rfl

/--
The closed prime adds the web as a reachable endpoint but adds no
old-to-old reachability.
-/
theorem prime_reaches_some_iff {D : Type u} (E : Elaboration D) (a b : D) :
    (prime E).Reaches (some a) (some b) ↔ E.Reaches a b := by
  constructor
  · intro h
    obtain ⟨a', ha', hab⟩ := prime_reaches_some h
    have haa : a = a' := Option.some.inj ha'
    exact haa ▸ hab
  · intro h
    exact Reaches.prime h

/--
Open the bracket by adding, for each old `d`, a clause from `none` back to
`some d`.  As with `prime`, only component lists are constrained.
-/
def primeOpen {D : Type u} (E : Elaboration D) : Elaboration (Option D) where
  Elab d rawM :=
    (prime E).Elab d rawM ∨
      (d = none ∧ ∃ old : D,
        rawM.components =
          [Component.singleton none, Component.singleton (some old)])

theorem prime_le_primeOpen {D : Type u} (E : Elaboration D) :
    prime E ≤ primeOpen E := by
  intro d rawM h
  exact Or.inl h

/-- In the open prime, the web reaches every designatum. -/
theorem primeOpen_reaches_from_web {D : Type u} (E : Elaboration D)
    (d : Option D) : (primeOpen E).Reaches none d := by
  cases d with
  | none => exact .refl none
  | some d =>
      let rawM :=
        RawMutualDependence.pair (Linkage.ofElaboration (primeOpen E))
          (Component.singleton none) (Component.singleton (some d))
      exact Reaches.single (rawM := rawM)
        (a := Component.singleton (some d))
        (Or.inr ⟨rfl, d, by simp [rawM]⟩) (by simp [rawM]) (by simp)

/-- `Reaches` is total in the open prime. -/
theorem primeOpen_reaches_total {D : Type u} (E : Elaboration D)
    (a b : Option D) : (primeOpen E).Reaches a b :=
  (prime_reaches_web E a).mono (prime_le_primeOpen E) |>.trans
    (primeOpen_reaches_from_web E b)

/-- `Related` is total in the open prime as well. -/
theorem primeOpen_related_total {D : Type u} (E : Elaboration D)
    (a b : Option D) : (primeOpen E).Related a b :=
  (primeOpen_reaches_total E a b).related

/-- Opening or closing the bracket is invisible to `Related`. -/
theorem primeOpen_related_iff_prime {D : Type u} (E : Elaboration D)
    (a b : Option D) :
    (primeOpen E).Related a b ↔ (prime E).Related a b :=
  ⟨fun _ => prime_related_total E a b,
    fun h => h.mono (prime_le_primeOpen E)⟩

/--
`Reaches` does distinguish an open bracket from a closed one: a pair exists
whose old reachability is absent, hence whose closed-prime reachability is
absent, while open-prime reachability is present.
-/
theorem exists_prime_open_reaches_distinction :
    ∃ (D : Type) (E : Elaboration D) (a b : D),
      ¬ (prime E).Reaches (some a) (some b) ∧
        (primeOpen E).Reaches (some a) (some b) := by
  obtain ⟨D, E, a, _, c, _, _, _, _, _, hnac⟩ :=
    Related.exists_nontransitive_mutualDependence
  refine ⟨D, E, a, c, ?_, primeOpen_reaches_total E (some a) (some c)⟩
  rw [prime_reaches_some_iff]
  exact fun h => hnac h.related

/-! ## One-prime exhaustion -/

/--
After one closed priming, a second closed priming adds no `Reaches` content
between first-tier designata.  It adds a further name and hub, but no path
between the points embedded by the second `some`.
-/
theorem prime_reaches_exhausted_on_image {D : Type u} (E : Elaboration D)
    (a b : Option D) :
    (prime (prime E)).Reaches (some a) (some b) ↔
      (prime E).Reaches a b :=
  prime_reaches_some_iff (prime E) a b

/--
The analogous image statement for `Related` is only a corollary-level fact:
both sides are already total after their first respective priming.
-/
theorem prime_related_exhausted_on_image {D : Type u} (E : Elaboration D)
    (a b : Option D) :
    (prime (prime E)).Related (some a) (some b) ↔
      (prime E).Related a b :=
  ⟨fun _ => prime_related_total E a b,
    fun _ => prime_related_total (prime E) (some a) (some b)⟩

/-! ## Conservative fresh-source extension -/

/--
Lift the old system to `some` and add arbitrary clauses at the fresh source
`none`.  No restriction is placed on fresh-clause targets.  The load-bearing
restriction is that lifted old-sourced clauses cannot contain `none`, so the
fresh clauses remain invisible from old starts.
-/
def freshSourceExtension {D : Type u} (E : Elaboration D)
    (fresh : RawMutualDependence (Option D) → Prop) :
    Elaboration (Option D) where
  Elab od rawM :=
    match od with
    | none => fresh rawM
    | some d =>
        ∃ oldM, E.Elab d oldM ∧
          rawM.components =
            oldM.components.map (Component.map Option.some)

/-- Old reachability embeds into any fresh-source extension. -/
theorem Reaches.freshSource {D : Type u} {E : Elaboration D}
    {fresh : RawMutualDependence (Option D) → Prop} {a b : D}
    (h : E.Reaches a b) :
    (freshSourceExtension E fresh).Reaches (some a) (some b) := by
  induction h with
  | refl d => exact .refl (some d)
  | @step d e f rawM c hElab hcomponent hmem _ ih =>
      let mapped :=
        rawM.mapComponents Option.some
          (Linkage.ofElaboration (freshSourceExtension E fresh))
      exact Reaches.step (rawM := mapped) (a := c.map Option.some)
        ⟨rawM, hElab, by simp [mapped]⟩
        (by
          rw [RawMutualDependence.components_mapComponents]
          exact list_mem_map_of_mem hcomponent)
        (Component.mem_map hmem) ih

private theorem freshSource_reaches_old_aux {D : Type u}
    {E : Elaboration D}
    {fresh : RawMutualDependence (Option D) → Prop}
    {start target : Option D}
    (h : (freshSourceExtension E fresh).Reaches start target) :
    ∀ {a : D}, start = some a →
      ∃ b, target = some b ∧ E.Reaches a b := by
  induction h with
  | refl d =>
      intro a hd
      exact ⟨a, hd, .refl a⟩
  | @step d e f rawM c hElab hcomponent hmem _ ih =>
      intro a hd
      subst d
      obtain ⟨oldM, hOld, hcomponents⟩ := hElab
      rw [hcomponents] at hcomponent
      obtain ⟨oldC, holdC, hc⟩ := exists_of_list_mem_map hcomponent
      subst c
      obtain ⟨e₀, he₀, he⟩ := hmem
      subst e
      obtain ⟨b, hfb, hreach⟩ := ih rfl
      exact ⟨b, hfb, Reaches.step hOld holdC he₀ hreach⟩

/--
Every path from an embedded old designatum stays in the embedded old domain.
-/
theorem freshSource_reaches_old {D : Type u} {E : Elaboration D}
    {fresh : RawMutualDependence (Option D) → Prop}
    {a : D} {target : Option D}
    (h : (freshSourceExtension E fresh).Reaches (some a) target) :
    ∃ b, target = some b ∧ E.Reaches a b :=
  freshSource_reaches_old_aux h rfl

/-- Fresh-source extension preserves `Reaches` on the old domain exactly. -/
theorem freshSource_reaches_iff {D : Type u} (E : Elaboration D)
    (fresh : RawMutualDependence (Option D) → Prop) (a b : D) :
    (freshSourceExtension E fresh).Reaches (some a) (some b) ↔
      E.Reaches a b := by
  constructor
  · intro h
    obtain ⟨b', hb', hab'⟩ := freshSource_reaches_old h
    have hbb : b = b' := Option.some.inj hb'
    exact hbb ▸ hab'
  · intro h
    exact h.freshSource

/-- Fresh-source extension preserves `Related` on the old domain exactly. -/
theorem freshSource_related_iff {D : Type u} (E : Elaboration D)
    (fresh : RawMutualDependence (Option D) → Prop) (a b : D) :
    (freshSourceExtension E fresh).Related (some a) (some b) ↔
      E.Related a b := by
  constructor
  · rintro ⟨w, haw, hbw⟩
    obtain ⟨wa, hwa, ha⟩ := freshSource_reaches_old haw
    obtain ⟨wb, hwb, hb⟩ := freshSource_reaches_old hbw
    have hwab : wa = wb := Option.some.inj (hwa.symm.trans hwb)
    subst wb
    exact ⟨wa, ha, hb⟩
  · rintro ⟨w, haw, hbw⟩
    exact ⟨some w, haw.freshSource, hbw.freshSource⟩

/--
Contract `a` and `b` under the fresh designatum `none`.  This is a
fresh-source articulation, not an identity assertion about either old
designatum.
-/
def contract {D : Type u} (E : Elaboration D) (a b : D) :
    Elaboration (Option D) :=
  freshSourceExtension E fun rawM =>
    rawM.components =
      [Component.singleton (some a), Component.singleton (some b)]

/-- A contraction preserves old-domain reachability. -/
theorem contract_reaches_iff {D : Type u} (E : Elaboration D)
    (a b x y : D) :
    (contract E a b).Reaches (some x) (some y) ↔ E.Reaches x y :=
  freshSource_reaches_iff E _ x y

/-- A contraction preserves old-domain relatedness. -/
theorem contract_related_iff {D : Type u} (E : Elaboration D)
    (a b x y : D) :
    (contract E a b).Related (some x) (some y) ↔ E.Related x y :=
  freshSource_related_iff E _ x y

/--
The fresh contraction-point is related to an embedded old point exactly when
at least one constituent is.  Thus the contracted join condition is
disjunctive, even though old-domain relatedness itself is preserved exactly.
-/
theorem contract_related_none_iff {D : Type u} (E : Elaboration D)
    (a b c : D) :
    (contract E a b).Related none (some c) ↔
      E.Related a c ∨ E.Related b c := by
  constructor
  · rintro ⟨w, hnw, hcw⟩
    obtain ⟨w', hw, hcw'⟩ := freshSource_reaches_old hcw
    subst w
    cases hnw with
    | @step _ e _ rawM component hElab hcomponent hmem htail =>
        have hcomponents : rawM.components =
            [Component.singleton (some a), Component.singleton (some b)] := by
          simpa [contract, freshSourceExtension] using hElab
        rw [hcomponents] at hcomponent
        simp at hcomponent
        rcases hcomponent with hleft | hright
        · subst component
          have he : e = some a := by simpa using hmem
          subst e
          exact Or.inl ⟨w',
            (contract_reaches_iff E a b a w').mp htail, hcw'⟩
        · subst component
          have he : e = some b := by simpa using hmem
          subst e
          exact Or.inr ⟨w',
            (contract_reaches_iff E a b b w').mp htail, hcw'⟩
  · rintro (⟨w, haw, hcw⟩ | ⟨w, hbw, hcw⟩)
    · let rawM : RawMutualDependence (Option D) :=
        .pair (contract E a b) (Component.singleton (some a))
          (Component.singleton (some b))
      have hnone : (contract E a b).Reaches none (some a) :=
        Reaches.single (rawM := rawM)
          (a := Component.singleton (some a))
          (by simp [contract, freshSourceExtension, rawM])
          (by simp [rawM]) (by simp)
      exact ⟨some w, hnone.trans
        ((contract_reaches_iff E a b a w).mpr haw),
        (contract_reaches_iff E a b c w).mpr hcw⟩
    · let rawM : RawMutualDependence (Option D) :=
        .pair (contract E a b) (Component.singleton (some a))
          (Component.singleton (some b))
      have hnone : (contract E a b).Reaches none (some b) :=
        Reaches.single (rawM := rawM)
          (a := Component.singleton (some b))
          (by simp [contract, freshSourceExtension, rawM])
          (by simp [rawM]) (by simp)
      exact ⟨some w, hnone.trans
        ((contract_reaches_iff E a b b w).mpr hbw),
        (contract_reaches_iff E a b c w).mpr hcw⟩

/--
A holding articulated singleton triple can be contracted at its left pair.
This is the monotone direction of contraction at that displayed join.
-/
theorem contract_pair_holds_of_singleton_triple {D : Type u}
    (E : Elaboration D)
    (a b c : D)
    (h : (RawMutualDependence.triple E
      (Component.singleton a) (Component.singleton b)
      (Component.singleton c)).Holds) :
    (RawMutualDependence.pair (contract E a b)
      (Component.singleton none)
      (Component.singleton (some c))).Holds := by
  rw [RawMutualDependence.holds_pair_iff]
  change (contract E a b).Linked (Component.singleton none)
    (Component.singleton (some c))
  rw [linked_singleton_iff, contract_related_none_iff]
  rw [RawMutualDependence.holds_triple_iff] at h
  change E.Linked (Component.singleton a) (Component.singleton b) ∧
    E.Linked (Component.singleton b) (Component.singleton c) at h
  rw [linked_singleton_iff, linked_singleton_iff] at h
  exact Or.inr h.2

/--
Contraction does not preserve chain-certifiability in the reverse direction.
For the nontransitivity witness, `b <--> a <--> c` fails at its second join,
while `[b <--> a] <--> c` holds because the fresh point can use `b`'s cone.
-/
theorem contract_not_chain_invariant :
    ∃ (D : Type) (E : Elaboration D) (a b c : D),
      E.Related a b ∧ E.Related b c ∧ ¬ E.Related a c ∧
        ¬ (RawMutualDependence.triple E
          (Component.singleton b) (Component.singleton a)
          (Component.singleton c)).Holds ∧
        (RawMutualDependence.pair (contract E b a)
          (Component.singleton none)
          (Component.singleton (some c))).Holds := by
  obtain ⟨D, E, a, b, c, _, _, _, hab, hbc, hnac⟩ :=
    Related.exists_nontransitive_mutualDependence
  refine ⟨D, E, a, b, c, hab, hbc, hnac, ?_, ?_⟩
  · rw [RawMutualDependence.holds_triple_iff]
    change ¬ (E.Linked (Component.singleton b) (Component.singleton a) ∧
      E.Linked (Component.singleton a) (Component.singleton c))
    rw [linked_singleton_iff, linked_singleton_iff]
    exact fun h => hnac h.2
  · rw [RawMutualDependence.holds_pair_iff]
    change (contract E b a).Linked (Component.singleton none)
      (Component.singleton (some c))
    rw [linked_singleton_iff]
    exact (contract_related_none_iff E b a c).mpr (Or.inl hbc)

end Elaboration
