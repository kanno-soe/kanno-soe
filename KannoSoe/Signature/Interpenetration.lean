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
is additive and remains agnostic about the interdependence bundled in an elaboration
target.

`Elaboration.primeOpen E` additionally lets `none` elaborate back to every
lifted old designatum.  The closed and open systems can differ for `Reaches`,
as the witness below shows, but not for `Joinable`.

`Temporality.liftOption T` separately preserves a supplied `Before` relation
between embedded old designata, transports their temporal certificates, and
leaves `none` outside that relation.  It is an optional temporal overlay on the
primed carrier, not temporality derived by priming.
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

namespace Interdependence

/-- Transport an interdependence along a map of designata. -/
def map {D : Type u} {D' : Type v} (L : Interdependence D) (f : D → D') :
    Interdependence D' where
  Interdependent c₁' c₂' :=
    ∃ c₁ c₂, L.Interdependent c₁ c₂ ∧
      c₁' = c₁.map f ∧ c₂' = c₂.map f
  symm := by
    rintro c₁' c₂' ⟨c₁, c₂, h₁₂, hc₁, hc₂⟩
    exact ⟨c₂, c₁, L.symm h₁₂, hc₂, hc₁⟩

theorem Chained.map {D : Type u} {D' : Type v}
    {L : Interdependence D} {components : List (Component D)}
    (f : D → D') (h : L.Chained components) :
    (L.map f).Chained (components.map (Component.map f)) := by
  induction h with
  | nil => exact .nil
  | single c₁ => exact .single (c₁.map f)
  | cons h₁₂ _ ih =>
      exact .cons ⟨_, _, h₁₂, rfl, rfl⟩ ih

end Interdependence

namespace RawMutualDependence

/--
Map every component of a raw target.  The new interdependence is an explicit
parameter: component transport cannot, and need not, manufacture an
interdependence.
-/
def mapComponents {D : Type u} {D' : Type v}
    (rawM : RawMutualDependence D) (f : D → D') (L : Interdependence D') :
    RawMutualDependence D' where
  interdependence := L
  c₁ := rawM.c₁.map f
  middle := rawM.middle.map (Component.map f)
  cₙ := rawM.cₙ.map f

@[simp] theorem components_mapComponents {D : Type u} {D' : Type v}
    (rawM : RawMutualDependence D) (f : D → D') (L : Interdependence D') :
    (rawM.mapComponents f L).components =
      rawM.components.map (Component.map f) := by
  simp [mapComponents, components]

end RawMutualDependence

namespace MutualDependence

/-- Transport a certified mutual dependence along a map of designata. -/
def map {D : Type u} {D' : Type v} (m : MutualDependence D) (f : D → D') :
    MutualDependence D' where
  toRaw := m.toRaw.mapComponents f (m.interdependence.map f)
  holds := by
    rw [RawMutualDependence.Holds,
      RawMutualDependence.components_mapComponents]
    exact m.holds.map f

@[simp] theorem c₁_map {D : Type u} {D' : Type v}
    (m : MutualDependence D) (f : D → D') :
    (m.map f).c₁ = m.c₁.map f :=
  rfl

@[simp] theorem cₙ_map {D : Type u} {D' : Type v}
    (m : MutualDependence D) (f : D → D') :
    (m.map f).cₙ = m.cₙ.map f :=
  rfl

end MutualDependence

namespace Temporal

/-- Transport a temporal certificate along a map of designata. -/
def map {D : Type u} {D' : Type v} {x y : D}
    (h : Temporal D x y) (f : D → D') : Temporal D' (f x) (f y) := by
  obtain ⟨m, hx, hy⟩ := h
  exact .ofMutualDependence (m.map f) (Component.mem_map hx)
    (Component.mem_map hy)

end Temporal

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

/-- Adding elaboration clauses can only add joinability. -/
theorem Joinable.mono {D : Type u} {E E' : Elaboration D}
    (hExt : E ≤ E') {a b : D} (h : E.Joinable a b) : E'.Joinable a b := by
  obtain ⟨w, ha, hb⟩ := h
  exact ⟨w, ha.mono hExt, hb.mono hExt⟩

/-! ## Priming and saturation -/

/--
Adjoin `none` as a fresh designatum, lift all old clauses along `some`, and
add for every old `d` a clause with components `{some d}` and `{none}`.
The lifted worldly bodies and bracket body are intentionally simultaneous
alternatives for one source: their plurality is the content, not slack.

Only `components` is constrained.  In particular, the definition neither
fixes the target's bundled interdependence nor asserts that the target holds.
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
          (Interdependence.ofElaboration (Elaboration.prime E))
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
        RawMutualDependence.pair (Interdependence.ofElaboration (prime E))
          (Component.singleton (some d)) (Component.singleton none)
      exact Reaches.single (rawM := rawM) (a := Component.singleton none)
        (Or.inr (by simp [rawM])) (by simp [rawM]) (by simp)

/-- `Joinable` is total after one priming. -/
theorem prime_joinable_total {D : Type u} (E : Elaboration D)
    (a b : Option D) : (prime E).Joinable a b :=
  ⟨none, prime_reaches_web E a, prime_reaches_web E b⟩

/-- Total joinability makes `Joinable` transitive in the primed tier. -/
theorem prime_joinable_transitive {D : Type u} (E : Elaboration D) :
    ∀ ⦃a b c : Option D⦄,
      (prime E).Joinable a b → (prime E).Joinable b c →
        (prime E).Joinable a c := by
  intro a _ c _ _
  exact prime_joinable_total E a c

/-- Every pair of nonempty components is interdependent in the primed tier. -/
theorem prime_interdependent_total {D : Type u} (E : Elaboration D)
    (c₁ c₂ : Component (Option D)) : (prime E).Interdependent c₁ c₂ := by
  obtain ⟨a, ha⟩ := c₁.nonempty
  obtain ⟨b, hb⟩ := c₂.nonempty
  exact
    ⟨fun x _ => ⟨b, hb, prime_joinable_total E x b⟩,
      fun y _ => ⟨a, ha, prime_joinable_total E a y⟩⟩

private theorem chained_of_total {D : Type u} {L : Interdependence D}
    (h : ∀ c₁ c₂, L.Interdependent c₁ c₂) :
    ∀ cs : List (Component D), L.Chained cs
  | [] => .nil
  | [c] => .single c
  | c₁ :: c₂ :: rest =>
      .cons (h c₁ c₂) (chained_of_total h (c₂ :: rest))

/--
After re-tagging by the primed interdependence, every raw dependence holds.  This is
a statement about saturation of the primed formal tier, not about the status
of an unprimed act-time elaboration.
-/
theorem prime_certification_trivial {D : Type u} (E : Elaboration D)
    (rawM : RawMutualDependence (Option D)) :
    (prime E).certify rawM |>.Holds := by
  apply chained_of_total
  intro c₁ c₂
  exact prime_interdependent_total E c₁ c₂

/--
There is an elaboration with a genuinely non-joinable old pair whose images are
joinable after priming.  Thus the saturated tier cannot replace the diagnostic
base tier without losing information.
-/
theorem exists_tier_noncollapse :
    ∃ (D : Type) (E : Elaboration D) (a b : D),
      ¬ E.Joinable a b ∧ (prime E).Joinable (some a) (some b) := by
  obtain ⟨D, E, a, _, c, _, _, _, _, _, hnac⟩ :=
    Joinable.exists_nontransitive_mutualDependence
  exact ⟨D, E, a, c, hnac, prime_joinable_total E (some a) (some c)⟩

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
`some d`. The web intentionally has one two-component body per old designatum;
this plurality is the hub encoding. As with `prime`, only component lists are
constrained.
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
        RawMutualDependence.pair (Interdependence.ofElaboration (primeOpen E))
          (Component.singleton none) (Component.singleton (some d))
      exact Reaches.single (rawM := rawM)
        (a := Component.singleton (some d))
        (Or.inr ⟨rfl, d, by simp [rawM]⟩) (by simp [rawM]) (by simp)

theorem primeOpen_reaches_total {D : Type u} (E : Elaboration D)
    (a b : Option D) : (primeOpen E).Reaches a b :=
  (prime_reaches_web E a).mono (prime_le_primeOpen E) |>.trans
    (primeOpen_reaches_from_web E b)

theorem primeOpen_joinable_total {D : Type u} (E : Elaboration D)
    (a b : Option D) : (primeOpen E).Joinable a b :=
  (primeOpen_reaches_total E a b).joinable

/-- Opening or closing the bracket is invisible to `Joinable`. -/
theorem primeOpen_joinable_iff_prime {D : Type u} (E : Elaboration D)
    (a b : Option D) :
    (primeOpen E).Joinable a b ↔ (prime E).Joinable a b :=
  ⟨fun _ => prime_joinable_total E a b,
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
    Joinable.exists_nontransitive_mutualDependence
  refine ⟨D, E, a, c, ?_, primeOpen_reaches_total E (some a) (some c)⟩
  rw [prime_reaches_some_iff]
  exact fun h => hnac h.joinable

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
The analogous image statement for `Joinable` is only a corollary-level fact:
both sides are already total after their first respective priming.
-/
theorem prime_joinable_exhausted_on_image {D : Type u} (E : Elaboration D)
    (a b : Option D) :
    (prime (prime E)).Joinable (some a) (some b) ↔
      (prime E).Joinable a b :=
  ⟨fun _ => prime_joinable_total E a b,
    fun _ => prime_joinable_total (prime E) (some a) (some b)⟩

end Elaboration

/-! ## Conservative temporality on a primed carrier -/

namespace Temporality

/--
Preserve a base `Before` relation between `some` images while leaving the fresh
`none` designatum temporally isolated.  This is an optional overlay for the
carrier used by priming; `Elaboration.prime` itself supplies no temporality.
-/
def liftOption {D : Type u} (T : Temporality D) : Temporality (Option D) where
  Before
    | some x, some y => T.Before x y
    | _, _ => False
  trans := by
    intro x y z hxy hyz
    cases x with
    | none => exact False.elim hxy
    | some x =>
        cases y with
        | none => exact False.elim hxy
        | some y =>
            cases z with
            | none => exact False.elim hyz
            | some z => exact T.trans hxy hyz
  irrefl := by
    intro x
    cases x with
    | none => exact fun h => h
    | some x => exact T.irrefl x
  certify := by
    intro x y h
    cases x with
    | none => exact False.elim h
    | some x =>
        cases y with
        | none => exact False.elim h
        | some y => exact (T.certify h).map Option.some

/-- The lifted `Before` relation agrees with the base relation on old images. -/
@[simp] theorem liftOption_before_some_some_iff {D : Type u}
    (T : Temporality D) {x y : D} :
    (liftOption T).Before (some x) (some y) ↔ T.Before x y :=
  Iff.rfl

@[simp] theorem liftOption_not_before_none {D : Type u}
    (T : Temporality D) (x : Option D) :
    ¬ (liftOption T).Before x none := by
  cases x <;> exact fun h => h

@[simp] theorem liftOption_not_none_before {D : Type u}
    (T : Temporality D) (y : Option D) :
    ¬ (liftOption T).Before none y := by
  cases y <;> exact fun h => h

end Temporality
