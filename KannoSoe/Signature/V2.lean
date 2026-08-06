import Std

/-!
# Mutual dependence, resonance, and direction

Raw types describe component structures without asserting that their
interdependences hold. Certified types pair those descriptions with proofs, while
`Elaboration` targets raw mutual dependences so it can remain agnostic about
the validity of its targets.

A interdependence derived from an elaboration (`Interdependence.ofElaboration E`) cannot
appear inside the targets of `E`'s own definition; see
`Elaboration.certify` and `Elaboration.SelfCertified`.

Direction/causality is an additional interpretation a domain may carry,
not something mutual dependence or resonance asserts or requires.
-/

universe u v

/-! ## Components -/

structure Component (D : Type u) where
  carrier : D → Prop
  nonempty : ∃ d, carrier d

instance {D : Type u} : Membership D (Component D) :=
  ⟨fun a d => a.carrier d⟩

instance {D : Type u} : CoeFun (Component D) (fun _ => D → Prop) :=
  ⟨Component.carrier⟩

namespace Component

def ofDesignata {D : Type u} (designata : List D)
    (nonempty : designata ≠ []) : Component D where
  carrier := fun d => d ∈ designata
  nonempty := by
    cases designata with
    | nil => exact (nonempty rfl).elim
    | cons d rest => exact ⟨d, by simp⟩

@[simp] theorem mem_ofDesignata_iff {D : Type u} {designata : List D}
    {nonempty : designata ≠ []} {d : D} :
    d ∈ ofDesignata designata nonempty ↔ d ∈ designata :=
  Iff.rfl

def singleton {D : Type u} (d : D) : Component D :=
  ofDesignata [d] (by simp)

@[simp] theorem mem_singleton_iff {D : Type u} {d x : D} :
    x ∈ singleton d ↔ x = d := by
  simp [singleton]

def pair {D : Type u} (d₁ d₂ : D) : Component D :=
  ofDesignata [d₁, d₂] (by simp)

@[simp] theorem mem_pair_iff {D : Type u} {d₁ d₂ x : D} :
    x ∈ pair d₁ d₂ ↔ x = d₁ ∨ x = d₂ := by
  simp [pair]

theorem exists_mem {D : Type u} (a : Component D) : ∃ d, d ∈ a :=
  a.nonempty

/-- Components are equal when they have exactly the same members. -/
theorem ext {D : Type u} {a b : Component D}
    (h : ∀ d, d ∈ a ↔ d ∈ b) : a = b := by
  cases a with
  | mk carrierA nonemptyA =>
      cases b with
      | mk carrierB nonemptyB =>
          have hcarrier : carrierA = carrierB :=
            by
              ext d
              exact h d
          cases hcarrier
          rfl

end Component

/-! ## Interdependence -/

structure Interdependence (D : Type u) where
  Interdependent : Component D → Component D → Prop
  symm : ∀ {c₁ c₂}, Interdependent c₁ c₂ → Interdependent c₂ c₁

namespace Interdependence

inductive Chained {D : Type u} (L : Interdependence D) :
    List (Component D) → Prop where
  | nil : Chained L []
  | single (c₁ : Component D) : Chained L [c₁]
  | cons {c₁ c₂ : Component D} {rest : List (Component D)}
      (h₁₂ : L.Interdependent c₁ c₂) (h : Chained L (c₂ :: rest)) :
      Chained L (c₁ :: c₂ :: rest)

theorem Chained.tail {D : Type u} {L : Interdependence D}
    {c₁ : Component D} {l : List (Component D)}
    (h : L.Chained (c₁ :: l)) : L.Chained l := by
  cases h with
  | single _ => exact Chained.nil
  | cons _ h => exact h

theorem Chained.of_append_right {D : Type u} {L : Interdependence D} :
    ∀ (l₁ : List (Component D)) {l₂ : List (Component D)},
      L.Chained (l₁ ++ l₂) → L.Chained l₂
  | [], _, h => h
  | c₁ :: rest, l₂, h => by
      rw [List.cons_append] at h
      exact Chained.of_append_right rest h.tail

theorem Chained.of_append_left {D : Type u} {L : Interdependence D} :
    ∀ (l₁ l₂ : List (Component D)),
      L.Chained (l₁ ++ l₂) → L.Chained l₁
  | [], _, _ => Chained.nil
  | [c₁], _, _ => Chained.single c₁
  | c₁ :: c₂ :: rest, l₂, h => by
      rw [List.cons_append, List.cons_append] at h
      cases h with
      | cons h₁₂ h =>
          refine Chained.cons h₁₂
            (Chained.of_append_left (c₂ :: rest) l₂ ?_)
          rw [List.cons_append]
          exact h

theorem Chained.glue {D : Type u} {L : Interdependence D} :
    ∀ {l₁ : List (Component D)} {cₙ : Component D}
        {l₂ : List (Component D)},
      L.Chained (l₁ ++ [cₙ]) → L.Chained (cₙ :: l₂) →
      L.Chained (l₁ ++ cₙ :: l₂) := by
  intro l₁ cₙ l₂ hleft hright
  induction l₁ with
  | nil => exact hright
  | cons c₁ rest ih =>
      cases rest with
      | nil =>
          change L.Chained [c₁, cₙ] at hleft
          cases hleft with
          | cons h₁ₙ _ => exact .cons h₁ₙ hright
      | cons c₂ rest =>
          change L.Chained (c₁ :: c₂ :: rest ++ [cₙ]) at hleft
          cases hleft with
          | cons h₁₂ htail =>
              exact .cons h₁₂ (ih htail)

/-- Catenate two nonempty chains whose exposed endpoints are interdependent. -/
theorem Chained.catenate {D : Type u} {L : Interdependence D}
    {l₁ l₂ : List (Component D)} {c₁ c₂ : Component D}
    (h₁ : L.Chained (l₁ ++ [c₁]))
    (h₂ : L.Chained (c₂ :: l₂))
    (h₁₂ : L.Interdependent c₁ c₂) :
    L.Chained ((l₁ ++ [c₁]) ++ c₂ :: l₂) := by
  have hthrough :
      L.Chained ((l₁ ++ [c₁]) ++ [c₂]) := by
    simpa [List.append_assoc] using
      (Chained.glue (l₁ := l₁) (cₙ := c₁) (l₂ := [c₂])
        h₁ (.cons h₁₂ (.single c₂)))
  exact Chained.glue (l₁ := l₁ ++ [c₁]) (cₙ := c₂)
    (l₂ := l₂) hthrough h₂

/-- Reversing a chain preserves it under a symmetric interdependence. -/
theorem Chained.reverse {D : Type u} {L : Interdependence D}
    {components : List (Component D)}
    (h : L.Chained components) :
    L.Chained components.reverse := by
  induction h with
  | nil => exact .nil
  | single c => exact .single c
  | @cons c₁ c₂ rest h₁₂ htail ih =>
      have htail' :
          L.Chained (rest.reverse ++ [c₂]) := by
        simpa using ih
      simpa [List.reverse_cons, List.append_assoc] using
        (Chained.glue (l₁ := rest.reverse) (cₙ := c₂)
          (l₂ := [c₁]) htail'
          (.cons (L.symm h₁₂) (.single c₁)))

end Interdependence

/-! ## Raw mutual dependence: data only -/

/--
Components plus their interdependence, as pure data (1:1: each value carries
exactly one interdependence). At least two components by construction. This type
makes no assertion; `RawMutualDependence.Holds` states it, and
`MutualDependence` below bundles the proof.
-/
structure RawMutualDependence (D : Type u) where
  interdependence : Interdependence D
  c₁ : Component D
  middle : List (Component D)
  cₙ : Component D

namespace RawMutualDependence

def components {D : Type u} (rawM : RawMutualDependence D) :
    List (Component D) :=
  rawM.c₁ :: rawM.middle ++ [rawM.cₙ]

@[simp] theorem c₁_mem_components {D : Type u}
    (rawM : RawMutualDependence D) : rawM.c₁ ∈ rawM.components := by
  simp [components]

@[simp] theorem cₙ_mem_components {D : Type u}
    (rawM : RawMutualDependence D) : rawM.cₙ ∈ rawM.components := by
  simp [components]

/-- The assertion: every two adjacent components are accepted by the
bundled interdependence. -/
def Holds {D : Type u} (rawM : RawMutualDependence D) : Prop :=
  rawM.interdependence.Chained rawM.components

def pair {D : Type u} (L : Interdependence D) (c₁ c₂ : Component D) :
    RawMutualDependence D :=
  ⟨L, c₁, [], c₂⟩

def triple {D : Type u} (L : Interdependence D) (c₁ c₂ c₃ : Component D) :
    RawMutualDependence D :=
  ⟨L, c₁, [c₂], c₃⟩

def quad {D : Type u} (L : Interdependence D) (c₁ c₂ c₃ c₄ : Component D) :
    RawMutualDependence D :=
  ⟨L, c₁, [c₂, c₃], c₄⟩

/-- Build raw dependence data from an explicitly nontrivial component list. -/
def ofComponents {D : Type u} (L : Interdependence D)
    (c₁ c₂ : Component D) :
    List (Component D) → RawMutualDependence D
  | [] => pair L c₁ c₂
  | c₃ :: rest =>
      let rawM := ofComponents L c₂ c₃ rest
      ⟨L, c₁, c₂ :: rawM.middle, rawM.cₙ⟩

@[simp] theorem interdependence_ofComponents {D : Type u} (L : Interdependence D)
    (c₁ c₂ : Component D) (rest : List (Component D)) :
    (ofComponents L c₁ c₂ rest).interdependence = L := by
  cases rest <;> rfl

@[simp] theorem c₁_ofComponents {D : Type u} (L : Interdependence D)
    (c₁ c₂ : Component D) (rest : List (Component D)) :
    (ofComponents L c₁ c₂ rest).c₁ = c₁ := by
  cases rest <;> rfl

@[simp] theorem components_ofComponents {D : Type u} (L : Interdependence D)
    (c₁ c₂ : Component D) (rest : List (Component D)) :
    (ofComponents L c₁ c₂ rest).components = c₁ :: c₂ :: rest := by
  induction rest generalizing c₁ c₂ with
  | nil => rfl
  | cons c₃ rest ih =>
      change
        c₁ ::
            (c₂ :: (ofComponents L c₂ c₃ rest).middle) ++
              [(ofComponents L c₂ c₃ rest).cₙ] =
          c₁ :: c₂ :: c₃ :: rest
      have tailComponents :
          (c₂ :: (ofComponents L c₂ c₃ rest).middle) ++
              [(ofComponents L c₂ c₃ rest).cₙ] =
            c₂ :: c₃ :: rest := by
        calc
          _ =
              (ofComponents L c₂ c₃ rest).c₁ ::
                  (ofComponents L c₂ c₃ rest).middle ++
                    [(ofComponents L c₂ c₃ rest).cₙ] := by
                exact congrArg
                  (fun c =>
                    (c :: (ofComponents L c₂ c₃ rest).middle) ++
                      [(ofComponents L c₂ c₃ rest).cₙ])
                  (c₁_ofComponents L c₂ c₃ rest).symm
          _ = (ofComponents L c₂ c₃ rest).components := rfl
          _ = c₂ :: c₃ :: rest := ih c₂ c₃
      exact congrArg (List.cons c₁) tailComponents

@[simp] theorem interdependence_pair {D : Type u} (L : Interdependence D)
    (c₁ c₂ : Component D) : (pair L c₁ c₂).interdependence = L :=
  rfl

@[simp] theorem components_pair {D : Type u} (L : Interdependence D)
    (c₁ c₂ : Component D) : (pair L c₁ c₂).components = [c₁, c₂] :=
  rfl

@[simp] theorem components_triple {D : Type u} (L : Interdependence D)
    (c₁ c₂ c₃ : Component D) :
    (triple L c₁ c₂ c₃).components = [c₁, c₂, c₃] :=
  rfl

@[simp] theorem components_quad {D : Type u} (L : Interdependence D)
    (c₁ c₂ c₃ c₄ : Component D) :
    (quad L c₁ c₂ c₃ c₄).components = [c₁, c₂, c₃, c₄] :=
  rfl

@[simp] theorem holds_pair_iff {D : Type u} {L : Interdependence D}
    {c₁ c₂ : Component D} :
    (pair L c₁ c₂).Holds ↔ L.Interdependent c₁ c₂ := by
  constructor
  · intro h
    have h : L.Chained [c₁, c₂] := h
    cases h with
    | cons h₁₂ _ => exact h₁₂
  · intro h
    show L.Chained [c₁, c₂]
    exact .cons h (.single c₂)

@[simp] theorem holds_triple_iff {D : Type u} {L : Interdependence D}
    {c₁ c₂ c₃ : Component D} :
    (triple L c₁ c₂ c₃).Holds ↔
      L.Interdependent c₁ c₂ ∧ L.Interdependent c₂ c₃ := by
  constructor
  · intro h
    have h : L.Chained [c₁, c₂, c₃] := h
    cases h with
    | cons h₁₂ h =>
        cases h with
        | cons h₂₃ _ => exact ⟨h₁₂, h₂₃⟩
  · intro h
    show L.Chained [c₁, c₂, c₃]
    exact .cons h.1 (.cons h.2 (.single c₃))

@[simp] theorem holds_quad_iff {D : Type u} {L : Interdependence D}
    {c₁ c₂ c₃ c₄ : Component D} :
    (quad L c₁ c₂ c₃ c₄).Holds ↔
      L.Interdependent c₁ c₂ ∧ L.Interdependent c₂ c₃ ∧ L.Interdependent c₃ c₄ := by
  constructor
  · intro h
    have h : L.Chained [c₁, c₂, c₃, c₄] := h
    cases h with
    | cons h₁₂ h =>
        cases h with
        | cons h₂₃ h =>
            cases h with
            | cons h₃₄ _ => exact ⟨h₁₂, h₂₃, h₃₄⟩
  · intro h
    show L.Chained [c₁, c₂, c₃, c₄]
    exact .cons h.1 (.cons h.2.1 (.cons h.2.2 (.single c₄)))

/-- Reverse the displayed order while retaining the same symmetric interdependence. -/
def reverse {D : Type u} (rawM : RawMutualDependence D) :
    RawMutualDependence D where
  interdependence := rawM.interdependence
  c₁ := rawM.cₙ
  middle := rawM.middle.reverse
  cₙ := rawM.c₁

@[simp] theorem interdependence_reverse {D : Type u}
    (rawM : RawMutualDependence D) : rawM.reverse.interdependence = rawM.interdependence :=
  rfl

@[simp] theorem c₁_reverse {D : Type u} (rawM : RawMutualDependence D) :
    rawM.reverse.c₁ = rawM.cₙ :=
  rfl

@[simp] theorem middle_reverse {D : Type u}
    (rawM : RawMutualDependence D) :
    rawM.reverse.middle = rawM.middle.reverse :=
  rfl

@[simp] theorem cₙ_reverse {D : Type u} (rawM : RawMutualDependence D) :
    rawM.reverse.cₙ = rawM.c₁ :=
  rfl

@[simp] theorem components_reverse {D : Type u}
    (rawM : RawMutualDependence D) :
    rawM.reverse.components = rawM.components.reverse := by
  simp [reverse, components, List.reverse_append]

@[simp] theorem reverse_reverse {D : Type u}
    (rawM : RawMutualDependence D) : rawM.reverse.reverse = rawM := by
  cases rawM
  simp [reverse]

/-- A certified raw chain remains certified when its display is reversed. -/
theorem Holds.reverse {D : Type u} {rawM : RawMutualDependence D}
    (h : rawM.Holds) : rawM.reverse.Holds := by
  change rawM.interdependence.Chained rawM.reverse.components
  rw [components_reverse]
  exact Interdependence.Chained.reverse h

theorem holds_of_contiguous {D : Type u}
    {whole sub : RawMutualDependence D} {pre suf : List (Component D)}
    (hL : sub.interdependence = whole.interdependence)
    (hdecomp : whole.components = pre ++ sub.components ++ suf)
    (hw : whole.Holds) : sub.Holds := by
  have h : whole.interdependence.Chained (pre ++ sub.components ++ suf) := by
    rw [← hdecomp]
    exact hw
  show sub.interdependence.Chained sub.components
  rw [hL]
  exact Interdependence.Chained.of_append_right pre
    (Interdependence.Chained.of_append_left _ suf h)

def IsResonance {D : Type u} (rawM : RawMutualDependence D) : Prop :=
  ∃ b₁ b₂ : D,
    rawM.middle = [Component.singleton b₁, Component.singleton b₂]

theorem isResonance_quad {D : Type u} (L : Interdependence D) (c₁ : Component D)
    (b₁ b₂ : D) (c₄ : Component D) :
    (quad L c₁ (Component.singleton b₁)
      (Component.singleton b₂) c₄).IsResonance :=
  ⟨b₁, b₂, rfl⟩

end RawMutualDependence

/-! ## Mutual dependence: data plus proof -/

/--
The certified type downstream code should use: a raw mutual dependence
together with the proof that it holds under its own interdependence.

If most of your interdependence proofs are dischargeable by a tactic, give the
`holds` field a default (`holds : toRaw.Holds := by your_tactic`) so
construction feels field-free at most sites.
-/
structure MutualDependence (D : Type u) where
  toRaw : RawMutualDependence D
  holds : toRaw.Holds

namespace MutualDependence

def interdependence {D : Type u} (m : MutualDependence D) : Interdependence D :=
  m.toRaw.interdependence

def c₁ {D : Type u} (m : MutualDependence D) : Component D :=
  m.toRaw.c₁

def middle {D : Type u} (m : MutualDependence D) : List (Component D) :=
  m.toRaw.middle

def cₙ {D : Type u} (m : MutualDependence D) : Component D :=
  m.toRaw.cₙ

def components {D : Type u} (m : MutualDependence D) :
    List (Component D) :=
  m.toRaw.components

/-- Proof irrelevance: equality of certified dependences reduces to
equality of the underlying data. -/
theorem ext {D : Type u} {a b : MutualDependence D}
    (h : a.toRaw = b.toRaw) : a = b := by
  cases a
  cases b
  cases h
  rfl

def reverse {D : Type u} (m : MutualDependence D) : MutualDependence D :=
  ⟨m.toRaw.reverse, m.holds.reverse⟩

@[simp] theorem toRaw_reverse {D : Type u} (m : MutualDependence D) :
    m.reverse.toRaw = m.toRaw.reverse :=
  rfl

@[simp] theorem interdependence_reverse {D : Type u} (m : MutualDependence D) :
    m.reverse.interdependence = m.interdependence :=
  rfl

@[simp] theorem c₁_reverse {D : Type u} (m : MutualDependence D) :
    m.reverse.c₁ = m.cₙ :=
  rfl

@[simp] theorem middle_reverse {D : Type u} (m : MutualDependence D) :
    m.reverse.middle = m.middle.reverse :=
  rfl

@[simp] theorem cₙ_reverse {D : Type u} (m : MutualDependence D) :
    m.reverse.cₙ = m.c₁ :=
  rfl

@[simp] theorem components_reverse {D : Type u} (m : MutualDependence D) :
    m.reverse.components = m.components.reverse :=
  RawMutualDependence.components_reverse m.toRaw

@[simp] theorem reverse_reverse {D : Type u} (m : MutualDependence D) :
    m.reverse.reverse = m :=
  ext (RawMutualDependence.reverse_reverse m.toRaw)

def pair {D : Type u} (L : Interdependence D) (c₁ c₂ : Component D)
    (h : L.Interdependent c₁ c₂) : MutualDependence D :=
  ⟨RawMutualDependence.pair L c₁ c₂,
    RawMutualDependence.holds_pair_iff.mpr h⟩

def triple {D : Type u} (L : Interdependence D) (c₁ c₂ c₃ : Component D)
    (h₁₂ : L.Interdependent c₁ c₂) (h₂₃ : L.Interdependent c₂ c₃) :
    MutualDependence D :=
  ⟨RawMutualDependence.triple L c₁ c₂ c₃,
    RawMutualDependence.holds_triple_iff.mpr ⟨h₁₂, h₂₃⟩⟩

def quad {D : Type u} (L : Interdependence D) (c₁ c₂ c₃ c₄ : Component D)
    (h₁₂ : L.Interdependent c₁ c₂) (h₂₃ : L.Interdependent c₂ c₃)
    (h₃₄ : L.Interdependent c₃ c₄) :
    MutualDependence D :=
  ⟨RawMutualDependence.quad L c₁ c₂ c₃ c₄,
    RawMutualDependence.holds_quad_iff.mpr ⟨h₁₂, h₂₃, h₃₄⟩⟩

/-- Certify an explicitly nontrivial chained list of components. -/
def ofComponents {D : Type u} (L : Interdependence D)
    (c₁ c₂ : Component D) (rest : List (Component D))
    (holds : L.Chained (c₁ :: c₂ :: rest)) :
    MutualDependence D := by
  refine ⟨RawMutualDependence.ofComponents L c₁ c₂ rest, ?_⟩
  change
    (RawMutualDependence.ofComponents L c₁ c₂ rest).interdependence.Chained
      (RawMutualDependence.ofComponents L c₁ c₂ rest).components
  rw [RawMutualDependence.interdependence_ofComponents,
    RawMutualDependence.components_ofComponents]
  exact holds

/-- `holds_of_contiguous` as a slicing function: the sub-tuple copies the
whole's interdependence, so it comes back certified with no side conditions. -/
def slice {D : Type u} (whole : MutualDependence D)
    (c₁ : Component D) (middle : List (Component D))
    (cₙ : Component D) (pre suf : List (Component D))
    (hdecomp : whole.toRaw.components =
      pre ++ (c₁ :: middle ++ [cₙ]) ++ suf) : MutualDependence D :=
  ⟨⟨whole.toRaw.interdependence, c₁, middle, cₙ⟩,
    RawMutualDependence.holds_of_contiguous
      (whole := whole.toRaw)
      (sub := ⟨whole.toRaw.interdependence, c₁, middle, cₙ⟩)
      (pre := pre) (suf := suf) rfl hdecomp whole.holds⟩

/-- Concatenate two dependences by identifying an equal shared endpoint. -/
def concatenateSharedEndpoint {D : Type u} (m₁ m₂ : MutualDependence D)
    (hL : m₁.interdependence = m₂.interdependence) (hShared : m₁.cₙ = m₂.c₁) :
    MutualDependence D := by
  refine
    ⟨⟨m₁.interdependence, m₁.c₁, m₁.middle ++ m₁.cₙ :: m₂.middle, m₂.cₙ⟩, ?_⟩
  have h₂ :
      m₁.interdependence.Chained (m₁.cₙ :: m₂.middle ++ [m₂.cₙ]) := by
    rw [hL, hShared]
    exact m₂.holds
  have h := Interdependence.Chained.glue
    (l₁ := m₁.c₁ :: m₁.middle) (cₙ := m₁.cₙ)
    (l₂ := m₂.middle ++ [m₂.cₙ]) m₁.holds h₂
  simpa [MutualDependence.interdependence, MutualDependence.c₁,
    MutualDependence.middle, MutualDependence.cₙ,
    RawMutualDependence.Holds, RawMutualDependence.components,
    List.append_assoc] using h

/-- Concatenate two dependences while retaining both interdependent endpoints. -/
def concatenateInterdependentEndpoints {D : Type u} (m₁ m₂ : MutualDependence D)
    (hL : m₁.interdependence = m₂.interdependence)
    (hInterdependent : m₁.interdependence.Interdependent m₁.cₙ m₂.c₁) :
    MutualDependence D := by
  refine
    ⟨⟨m₁.interdependence, m₁.c₁,
      m₁.middle ++ [m₁.cₙ, m₂.c₁] ++ m₂.middle, m₂.cₙ⟩, ?_⟩
  have h₁₂ :
      m₁.interdependence.Chained
        (((m₁.c₁ :: m₁.middle) ++ [m₁.cₙ]) ++ [m₂.c₁]) := by
    simpa [MutualDependence.interdependence, MutualDependence.c₁,
      MutualDependence.middle, MutualDependence.cₙ,
      List.append_assoc] using
      (Interdependence.Chained.glue
        (l₁ := m₁.c₁ :: m₁.middle) (cₙ := m₁.cₙ) (l₂ := [m₂.c₁])
        m₁.holds (.cons hInterdependent (.single m₂.c₁)))
  have h₂ :
      m₁.interdependence.Chained (m₂.c₁ :: m₂.middle ++ [m₂.cₙ]) := by
    rw [hL]
    exact m₂.holds
  have h := Interdependence.Chained.glue
    (l₁ := (m₁.c₁ :: m₁.middle) ++ [m₁.cₙ]) (cₙ := m₂.c₁)
    (l₂ := m₂.middle ++ [m₂.cₙ]) h₁₂ h₂
  simpa [MutualDependence.interdependence, MutualDependence.c₁,
    MutualDependence.middle, MutualDependence.cₙ,
    RawMutualDependence.Holds, RawMutualDependence.components,
    List.append_assoc] using h

@[simp] theorem components_concatenateInterdependentEndpoints {D : Type u}
    (m₁ m₂ : MutualDependence D) (hL : m₁.interdependence = m₂.interdependence)
    (hInterdependent : m₁.interdependence.Interdependent m₁.cₙ m₂.c₁) :
    (concatenateInterdependentEndpoints m₁ m₂ hL hInterdependent).components =
      m₁.components ++ m₂.components := by
  simp [concatenateInterdependentEndpoints, MutualDependence.components,
    MutualDependence.c₁, MutualDependence.middle, MutualDependence.cₙ,
    RawMutualDependence.components, List.append_assoc]

def IsResonance {D : Type u} (m : MutualDependence D) : Prop :=
  m.toRaw.IsResonance

end MutualDependence

/-! ## Elaboration and joinability -/

/--
An elaboration system. `Elab d rawM` asserts that `rawM` is one of the
simultaneously true dependence-explanations of designatum `d`. Alternatives
are plural routes through those facts, not exclusive outcomes: selecting one
to witness a pair does not resolve, exclude, or collapse the others. A
unique-elaboration function would instead reify the unique constitution that
this relation deliberately leaves open in every case.

`Elaboration` must target `RawMutualDependence`: it constrains the
components of its targets and stays agnostic about both the bundled
interdependence and whether the tuple holds. Requiring targets to carry
`Interdependence.ofElaboration` of this same elaboration — let alone proofs under
it — inside the elaboration's own definition is value-level
self-reference; see `certify` and `SelfCertified`.
-/
structure Elaboration (D : Type u) where
  Elab : D → RawMutualDependence D → Prop

namespace Elaboration

inductive Reaches {D : Type u} (E : Elaboration D) : D → D → Prop where
  | refl (d : D) : Reaches E d d
  | step {d e f : D} {rawM : RawMutualDependence D}
      {a : Component D}
      (hE : E.Elab d rawM) (ha : a ∈ rawM.components) (he : e ∈ a)
      (h : Reaches E e f) : Reaches E d f

theorem Reaches.trans {D : Type u} {E : Elaboration D} {d e f : D}
    (h₁ : E.Reaches d e) : E.Reaches e f → E.Reaches d f := by
  induction h₁ with
  | refl _ => exact id
  | step hE ha he _ ih =>
      exact fun h₂ => Reaches.step hE ha he (ih h₂)

theorem Reaches.single {D : Type u} {E : Elaboration D} {d e : D}
    {rawM : RawMutualDependence D} {a : Component D}
    (hE : E.Elab d rawM) (ha : a ∈ rawM.components) (he : e ∈ a) :
    E.Reaches d e :=
  Reaches.step hE ha he (Reaches.refl e)

def Joinable {D : Type u} (E : Elaboration D) (a b : D) : Prop :=
  ∃ w, E.Reaches a w ∧ E.Reaches b w

theorem Joinable.refl {D : Type u} (E : Elaboration D) (a : D) :
    E.Joinable a a :=
  ⟨a, Reaches.refl a, Reaches.refl a⟩

theorem Joinable.symm {D : Type u} {E : Elaboration D} {a b : D}
    (h : E.Joinable a b) : E.Joinable b a := by
  obtain ⟨w, ha, hb⟩ := h
  exact ⟨w, hb, ha⟩

/-- Reachability into one side of joinability transports joinability back. -/
theorem Joinable.of_reaches {D : Type u} {E : Elaboration D} {d y x : D}
    (hdy : E.Reaches d y) (hyx : E.Joinable y x) : E.Joinable d x := by
  obtain ⟨w, hyw, hxw⟩ := hyx
  exact ⟨w, hdy.trans hyw, hxw⟩

theorem Reaches.joinable {D : Type u} {E : Elaboration D} {a b : D}
    (h : E.Reaches a b) : E.Joinable a b :=
  ⟨b, h, Reaches.refl b⟩

theorem Reaches.joinable_symm {D : Type u} {E : Elaboration D} {a b : D}
    (h : E.Reaches a b) : E.Joinable b a :=
  h.joinable.symm

/--
The Egli–Milner lifting of joinability to components: every designatum on
either side has a joinable partner on the other.
-/
def Interdependent {D : Type u} (E : Elaboration D)
    (c₁ c₂ : Component D) : Prop :=
  (∀ a ∈ c₁, ∃ b ∈ c₂, E.Joinable a b) ∧
    (∀ b ∈ c₂, ∃ a ∈ c₁, E.Joinable a b)

theorem Interdependent.symm {D : Type u} {E : Elaboration D}
    {c₁ c₂ : Component D} (h : E.Interdependent c₁ c₂) : E.Interdependent c₂ c₁ := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨fun b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨a, ha, hr⟩ := h₂ b hb
    exact ⟨a, ha, hr.symm⟩
  · obtain ⟨b, hb, hr⟩ := h₁ a ha
    exact ⟨b, hb, hr.symm⟩

@[simp] theorem interdependent_singleton_iff {D : Type u} {E : Elaboration D}
    {a b : D} :
    E.Interdependent (Component.singleton a) (Component.singleton b) ↔
      E.Joinable a b := by
  constructor
  · intro h
    obtain ⟨b', hb', hr⟩ := h.1 a (by simp)
    have hb : b' = b := by simpa using hb'
    subst hb
    exact hr
  · intro h
    refine ⟨fun a' ha' => ?_, fun b' hb' => ?_⟩
    · have ha : a' = a := by simpa using ha'
      subst ha
      exact ⟨b, by simp, h⟩
    · have hb : b' = b := by simpa using hb'
      subst hb
      exact ⟨a, by simp, h⟩

end Elaboration

namespace Interdependence

def ofElaboration {D : Type u} (E : Elaboration D) : Interdependence D where
  Interdependent := E.Interdependent
  symm := Elaboration.Interdependent.symm

instance {D : Type u} : Coe (Elaboration D) (Interdependence D) :=
  ⟨ofElaboration⟩

end Interdependence

namespace Elaboration

/-- Re-tag a raw dependence with the interdependence derived from `E` — the
sanctioned route around the self-reference restriction. Certifying (i.e.
producing a `MutualDependence`) additionally requires proving `Holds`
under the derived interdependence, which is genuine work per system. -/
def certify {D : Type u} (E : Elaboration D)
    (rawM : RawMutualDependence D) : RawMutualDependence D :=
  { rawM with interdependence := Interdependence.ofElaboration E }

@[simp] theorem interdependence_certify {D : Type u} (E : Elaboration D)
    (rawM : RawMutualDependence D) :
    (E.certify rawM).interdependence = Interdependence.ofElaboration E :=
  rfl

@[simp] theorem components_certify {D : Type u} (E : Elaboration D)
    (rawM : RawMutualDependence D) :
    (E.certify rawM).components = rawM.components :=
  rfl

@[simp] theorem certify_pair {D : Type u} (E : Elaboration D)
    (L : Interdependence D) (c₁ c₂ : Component D) :
    E.certify (RawMutualDependence.pair L c₁ c₂) =
      RawMutualDependence.pair (Interdependence.ofElaboration E) c₁ c₂ :=
  rfl

@[simp] theorem certify_triple {D : Type u} (E : Elaboration D)
    (L : Interdependence D) (c₁ c₂ c₃ : Component D) :
    E.certify (RawMutualDependence.triple L c₁ c₂ c₃) =
      RawMutualDependence.triple (Interdependence.ofElaboration E) c₁ c₂ c₃ :=
  rfl

@[simp] theorem certify_quad {D : Type u} (E : Elaboration D)
    (L : Interdependence D) (c₁ c₂ c₃ c₄ : Component D) :
    E.certify (RawMutualDependence.quad L c₁ c₂ c₃ c₄) =
      RawMutualDependence.quad (Interdependence.ofElaboration E) c₁ c₂ c₃ c₄ :=
  rfl

@[simp] theorem certify_reverse {D : Type u} (E : Elaboration D)
    (rawM : RawMutualDependence D) :
    E.certify rawM.reverse = (E.certify rawM).reverse :=
  rfl

/-- Well-formedness of a completed system: every emitted raw dependence
carries the interdependence derived from the elaboration itself. Provable about a
finished `E`; not expressible inside `E`'s own definition. -/
def SelfCertified {D : Type u} (E : Elaboration D) : Prop :=
  ∀ d rawM, E.Elab d rawM → rawM.interdependence = Interdependence.ofElaboration E

/-- An elaboration system accepts the reversed display of every target. -/
def ReversalClosed {D : Type u} (E : Elaboration D) : Prop :=
  ∀ d rawM, E.Elab d rawM → E.Elab d rawM.reverse

theorem ReversalClosed.elab_reverse_iff {D : Type u}
    {E : Elaboration D} (hrc : E.ReversalClosed) {d : D}
    {rawM : RawMutualDependence D} :
    E.Elab d rawM.reverse ↔ E.Elab d rawM := by
  constructor
  · intro h
    simpa using hrc d rawM.reverse h
  · exact hrc d rawM

/-- Close an elaboration under reversal of the displayed bodies. -/
def reversalClosure {D : Type u} (E : Elaboration D) : Elaboration D where
  Elab d rawM := E.Elab d rawM ∨ E.Elab d rawM.reverse

/-- The closure construction accepts the reverse of every accepted body. -/
theorem reversalClosure_reversalClosed {D : Type u} (E : Elaboration D) :
    (reversalClosure E).ReversalClosed := by
  intro d rawM h
  rcases h with h | h
  · exact Or.inr (by simpa using h)
  · exact Or.inl h

/-- Reachability cannot observe reversal of displayed bodies. -/
theorem Reaches.reversalClosure_iff {D : Type u} (E : Elaboration D)
    {d e : D} :
    (reversalClosure E).Reaches d e ↔ E.Reaches d e := by
  constructor
  · intro h
    induction h with
    | refl d => exact .refl d
    | @step d e f rawM a hElab hcomponent hmem _ ih =>
        rcases hElab with hElab | hElab
        · exact .step hElab hcomponent hmem ih
        · exact .step (rawM := rawM.reverse) hElab
            (by simpa using hcomponent)
            hmem ih
  · intro h
    induction h with
    | refl d => exact .refl d
    | step hElab hcomponent hmem _ ih =>
        exact .step (Or.inl hElab) hcomponent hmem ih

/-- Reversal-closing an elaboration leaves its reach relation unchanged. -/
theorem reaches_reversalClosure {D : Type u} (E : Elaboration D) :
    (reversalClosure E).Reaches = E.Reaches := by
  ext d e
  exact Reaches.reversalClosure_iff E

private inductive JoinabilityNotTransitiveCase where
  | a
  | b
  | c
  | moreA
  | abWitness
  | moreB
  | bcWitness
  | moreC
  deriving DecidableEq

/-- A certified mutual dependence can exhibit the failure of transitivity of
`Joinable`. Here `a` and `b` share `abWitness`, while `b` and `c` share the
distinct `bcWitness`; the reachable sets of `a` and `c` are disjoint. Thus the
singleton triple `[{a}, {b}, {c}]` genuinely holds under
`Interdependence.ofElaboration E`, although its endpoint designata are not joinable. -/
theorem Joinable.exists_nontransitive_mutualDependence :
    ∃ (D : Type) (E : Elaboration D) (a b c : D)
        (m : MutualDependence D),
      m.interdependence = Interdependence.ofElaboration E ∧
        m.components =
          [Component.singleton a, Component.singleton b,
            Component.singleton c] ∧
        E.Joinable a b ∧ E.Joinable b c ∧ ¬ E.Joinable a c := by
  let E : Elaboration JoinabilityNotTransitiveCase :=
    ⟨fun d rawM =>
      (d = .a ∧
        rawM.components =
          [Component.singleton .moreA,
            Component.singleton .abWitness]) ∨
      (d = .b ∧
        rawM.components =
          [Component.singleton .abWitness,
            Component.singleton .moreB,
            Component.singleton .bcWitness]) ∨
      (d = .c ∧
        rawM.components =
          [Component.singleton .bcWitness,
            Component.singleton .moreC])⟩
  let mA : RawMutualDependence JoinabilityNotTransitiveCase :=
    .pair E (Component.singleton .moreA)
      (Component.singleton .abWitness)
  let mB : RawMutualDependence JoinabilityNotTransitiveCase :=
    .triple E (Component.singleton .abWitness)
      (Component.singleton .moreB) (Component.singleton .bcWitness)
  let mC : RawMutualDependence JoinabilityNotTransitiveCase :=
    .pair E (Component.singleton .bcWitness)
      (Component.singleton .moreC)
  have hEa : E.Elab .a mA := by
    simp [E, mA]
  have hEb : E.Elab .b mB := by
    simp [E, mB]
  have hEc : E.Elab .c mC := by
    simp [E, mC]
  have haab : E.Reaches .a .abWitness :=
    Reaches.single (rawM := mA) (a := Component.singleton .abWitness)
      hEa (by simp [mA]) (by simp)
  have hbab : E.Reaches .b .abWitness :=
    Reaches.single (rawM := mB) (a := Component.singleton .abWitness)
      hEb (by simp [mB]) (by simp)
  have hbbc : E.Reaches .b .bcWitness :=
    Reaches.single (rawM := mB) (a := Component.singleton .bcWitness)
      hEb (by simp [mB]) (by simp)
  have hcbc : E.Reaches .c .bcWitness :=
    Reaches.single (rawM := mC) (a := Component.singleton .bcWitness)
      hEc (by simp [mC]) (by simp)
  have hab : E.Joinable .a .b :=
    ⟨JoinabilityNotTransitiveCase.abWitness, haab, hbab⟩
  have hbc' : E.Joinable .b .c :=
    ⟨JoinabilityNotTransitiveCase.bcWitness, hbbc, hcbc⟩
  have reachesA {w : JoinabilityNotTransitiveCase} (h : E.Reaches .a w) :
      w = .a ∨ w = .moreA ∨ w = .abWitness := by
    cases h with
    | refl _ => simp
    | step hE hcomponent he htail =>
        simp [E] at hE
        simp [hE] at hcomponent
        rcases hcomponent with rfl | rfl
        · simp at he
          cases he
          cases htail with
          | refl _ => simp
          | step hE' _ _ _ => simp [E] at hE'
        · simp at he
          cases he
          cases htail with
          | refl _ => simp
          | step hE' _ _ _ => simp [E] at hE'
  have reachesC {w : JoinabilityNotTransitiveCase} (h : E.Reaches .c w) :
      w = .c ∨ w = .bcWitness ∨ w = .moreC := by
    cases h with
    | refl _ => simp
    | step hE hcomponent he htail =>
        simp [E] at hE
        simp [hE] at hcomponent
        rcases hcomponent with rfl | rfl
        · simp at he
          cases he
          cases htail with
          | refl _ => simp
          | step hE' _ _ _ => simp [E] at hE'
        · simp at he
          cases he
          cases htail with
          | refl _ => simp
          | step hE' _ _ _ => simp [E] at hE'
  have hnac : ¬ E.Joinable .a .c := by
    rintro ⟨w, haw, hcw⟩
    rcases reachesA haw with hwa | hwa | hwa <;>
      rcases reachesC hcw with hwc | hwc | hwc <;>
      simp_all
  let m : MutualDependence JoinabilityNotTransitiveCase :=
    MutualDependence.triple E
      (Component.singleton .a) (Component.singleton .b)
      (Component.singleton .c)
      (interdependent_singleton_iff.mpr hab) (interdependent_singleton_iff.mpr hbc')
  exact ⟨JoinabilityNotTransitiveCase, E, .a, .b, .c, m,
    rfl, rfl, hab, hbc', hnac⟩

/-- `Joinable` is not transitive, even among the components of a certified
mutual dependence carrying the interdependence derived from its elaboration. -/
theorem Joinable.not_transitive :
    ∃ (D : Type) (E : Elaboration D),
      ¬ ∀ ⦃a b c⦄, E.Joinable a b → E.Joinable b c → E.Joinable a c := by
  obtain ⟨D, E, _, _, _, _, _, _, hab, hbc, hnac⟩ :=
    Joinable.exists_nontransitive_mutualDependence
  refine ⟨D, E, ?_⟩
  intro htrans
  exact hnac (htrans hab hbc)

end Elaboration

/-! ## Resonance, raw and certified -/

/--
Resonance data whose two middle components are forced to be singletons.

b₁ is the being receiving calls; b₂ is the "same" being responding. The being's
receiving-stage and responding-stage share interdependence despite the change.
-/
structure RawResonance (D : Type u) where
  interdependence : Interdependence D
  calls : Component D
  b₁ : D
  b₂ : D
  responses : Component D

namespace RawResonance

def middle {D : Type u} (rawR : RawResonance D) : List (Component D) :=
  [Component.singleton rawR.b₁, Component.singleton rawR.b₂]

def toRawMutualDependence {D : Type u} (rawR : RawResonance D) :
    RawMutualDependence D :=
  RawMutualDependence.quad rawR.interdependence rawR.calls
    (Component.singleton rawR.b₁)
    (Component.singleton rawR.b₂) rawR.responses

def components {D : Type u} (rawR : RawResonance D) :
    List (Component D) :=
  rawR.toRawMutualDependence.components

@[simp] theorem interdependence_toRawMutualDependence {D : Type u}
    (rawR : RawResonance D) :
    rawR.toRawMutualDependence.interdependence = rawR.interdependence :=
  rfl

@[simp] theorem middle_toRawMutualDependence {D : Type u}
    (rawR : RawResonance D) :
    rawR.toRawMutualDependence.middle = rawR.middle :=
  rfl

@[simp] theorem components_eq {D : Type u} (rawR : RawResonance D) :
    rawR.components =
      [rawR.calls, Component.singleton rawR.b₁,
        Component.singleton rawR.b₂, rawR.responses] :=
  rfl

theorem isResonance {D : Type u} (rawR : RawResonance D) :
    rawR.toRawMutualDependence.IsResonance :=
  ⟨rawR.b₁, rawR.b₂, rfl⟩

def Holds {D : Type u} (rawR : RawResonance D) : Prop :=
  rawR.toRawMutualDependence.Holds

@[simp] theorem holds_iff {D : Type u} {rawR : RawResonance D} :
    rawR.Holds ↔
      rawR.interdependence.Interdependent rawR.calls (Component.singleton rawR.b₁) ∧
        rawR.interdependence.Interdependent (Component.singleton rawR.b₁)
          (Component.singleton rawR.b₂) ∧
          rawR.interdependence.Interdependent (Component.singleton rawR.b₂)
            rawR.responses := by
  change
    (RawMutualDependence.quad rawR.interdependence rawR.calls
      (Component.singleton rawR.b₁)
      (Component.singleton rawR.b₂) rawR.responses).Holds ↔ _
  exact RawMutualDependence.holds_quad_iff

end RawResonance

/-- Completeness at the raw level: every raw mutual dependence satisfying
`IsResonance` is represented by some `RawResonance`. -/
theorem RawMutualDependence.IsResonance.exists_rawResonance
    {D : Type u} {rawM : RawMutualDependence D}
    (h : rawM.IsResonance) :
    ∃ rawR : RawResonance D, rawR.toRawMutualDependence = rawM := by
  cases rawM with
  | mk interdependence c₁ middle cₙ =>
      obtain ⟨b₁, b₂, hmiddle⟩ := h
      change middle = [Component.singleton b₁, Component.singleton b₂]
        at hmiddle
      subst middle
      exact ⟨⟨interdependence, c₁, b₁, b₂, cₙ⟩, rfl⟩

/-- The certified counterpart to `RawResonance`, following the same
raw/certified boundary as mutual dependence. -/
structure Resonance (D : Type u) where
  toRawResonance : RawResonance D
  holds : toRawResonance.Holds

namespace Resonance

def interdependence {D : Type u} (r : Resonance D) : Interdependence D :=
  r.toRawResonance.interdependence

def calls {D : Type u} (r : Resonance D) : Component D :=
  r.toRawResonance.calls

def b₁ {D : Type u} (r : Resonance D) : D :=
  r.toRawResonance.b₁

def b₂ {D : Type u} (r : Resonance D) : D :=
  r.toRawResonance.b₂

def responses {D : Type u} (r : Resonance D) : Component D :=
  r.toRawResonance.responses

def middleComponents {D : Type u} (r : Resonance D) :
    List (Component D) :=
  [Component.singleton r.b₁, Component.singleton r.b₂]

def toMutualDependence {D : Type u} (r : Resonance D) :
    MutualDependence D :=
  ⟨r.toRawResonance.toRawMutualDependence, r.holds⟩

instance {D : Type u} : Coe (Resonance D) (MutualDependence D) :=
  ⟨toMutualDependence⟩

theorem isResonance {D : Type u} (r : Resonance D) :
    r.toMutualDependence.IsResonance :=
  r.toRawResonance.isResonance

def mk' {D : Type u} (L : Interdependence D) (calls : Component D) (b₁ b₂ : D)
    (responses : Component D)
    (h₁ : L.Interdependent calls (Component.singleton b₁))
    (h₂ : L.Interdependent (Component.singleton b₁) (Component.singleton b₂))
    (h₃ : L.Interdependent (Component.singleton b₂) responses) : Resonance D :=
  ⟨⟨L, calls, b₁, b₂, responses⟩,
    RawResonance.holds_iff.mpr ⟨h₁, h₂, h₃⟩⟩

end Resonance

/-- Completeness at the certified level: every certified mutual dependence
satisfying `IsResonance` comes from a certified `Resonance`; the proof is
transported along the raw representation. -/
theorem MutualDependence.IsResonance.exists_resonance
    {D : Type u} {m : MutualDependence D} (h : m.IsResonance) :
    ∃ r : Resonance D, r.toMutualDependence = m := by
  obtain ⟨rawR, hrawR⟩ :=
    RawMutualDependence.IsResonance.exists_rawResonance h
  exact ⟨⟨rawR, (show rawR.toRawMutualDependence.Holds from
    hrawR.symm ▸ m.holds)⟩, MutualDependence.ext hrawR⟩

/-! ## Being -/

/--
A certified mutual dependence all of whose components are singletons.
-/
structure Being (D : Type u) where
  toMutualDependence : MutualDependence D
  singleton_components :
    ∀ c ∈ toMutualDependence.components,
      ∃ d : D, c = Component.singleton d

namespace Being

/--
Regard a certified mutual dependence as a being when every one of its
components is a singleton.
-/
def ofMutualDependence {D : Type u} (m : MutualDependence D)
    (singleton_components :
      ∀ c ∈ m.components, ∃ d : D, c = Component.singleton d) :
    Being D :=
  ⟨m, singleton_components⟩

instance {D : Type u} : Coe (Being D) (MutualDependence D) :=
  ⟨toMutualDependence⟩

end Being

/-! ## Grading -/

structure PreorderBot (Grade : Type v) where
  le : Grade → Grade → Prop
  bot : Grade
  leRefl : ∀ grade, le grade grade
  leTrans : ∀ {a b c}, le a b → le b c → le a c
  botLeast : ∀ grade, le bot grade

/-- Grade can be thought of as a "dis-resonance". Bot = no dis-resonance. -/
structure GradedResonance (D : Type u) {Grade : Type v}
    (PB : PreorderBot Grade) extends Resonance D where
  callsGrade : Grade
  responsesGrade : Grade

namespace GradedResonance

def toMutualDependence {D : Type u} {Grade : Type v}
    {PB : PreorderBot Grade} (r : GradedResonance D PB) :
    MutualDependence D :=
  r.toResonance.toMutualDependence

instance {D : Type u} {Grade : Type v} {PB : PreorderBot Grade} :
    CoeOut (GradedResonance D PB) (Resonance D) :=
  ⟨GradedResonance.toResonance⟩

theorem isResonance {D : Type u} {Grade : Type v}
    {PB : PreorderBot Grade} (r : GradedResonance D PB) :
    r.toMutualDependence.IsResonance :=
  r.toResonance.isResonance

def ofResonance {D : Type u} {Grade : Type v} {PB : PreorderBot Grade}
    (r : Resonance D) (callsGrade responsesGrade : Grade) :
    GradedResonance D PB where
  toResonance := r
  callsGrade := callsGrade
  responsesGrade := responsesGrade

@[simp] theorem callsGrade_ofResonance {D : Type u} {Grade : Type v}
    {PB : PreorderBot Grade} (r : Resonance D)
    (callsGrade responsesGrade : Grade) :
    (ofResonance (PB := PB) r callsGrade responsesGrade).callsGrade =
      callsGrade :=
  rfl

@[simp] theorem responsesGrade_ofResonance {D : Type u} {Grade : Type v}
    {PB : PreorderBot Grade} (r : Resonance D)
    (callsGrade responsesGrade : Grade) :
    (ofResonance (PB := PB) r callsGrade responsesGrade).responsesGrade =
      responsesGrade :=
  rfl

def ungraded {D : Type u} {Grade : Type v} {PB : PreorderBot Grade}
    (r : Resonance D) : GradedResonance D PB :=
  ofResonance r PB.bot PB.bot

@[simp] theorem callsGrade_ungraded {D : Type u} {Grade : Type v}
    {PB : PreorderBot Grade} (r : Resonance D) :
    (ungraded (PB := PB) r).callsGrade = PB.bot :=
  rfl

@[simp] theorem responsesGrade_ungraded {D : Type u} {Grade : Type v}
    {PB : PreorderBot Grade} (r : Resonance D) :
    (ungraded (PB := PB) r).responsesGrade = PB.bot :=
  rfl

def IsUngraded {D : Type u} {Grade : Type v} {PB : PreorderBot Grade}
    (r : GradedResonance D PB) : Prop :=
  r.callsGrade = PB.bot ∧ r.responsesGrade = PB.bot

def le {D : Type u} {Grade : Type v} {PB : PreorderBot Grade}
    (a b : GradedResonance D PB) : Prop :=
  PB.le a.callsGrade b.callsGrade ∧
    PB.le a.responsesGrade b.responsesGrade

end GradedResonance

/-! ## Direction and causality -/

/--
Directed is not derived from the MutualDependence or Resonance,
instead it's a fact among those - it just turns out that when thermodynamic gradient
is possible, some designata sit at lower entropy than others; Directed specifies which.

Causal comes with an assertion that there's a
mutual dependence chain with x at one side and y at another.
-/
structure Directed (D : Type u) where
  Before : D → D → Prop
  trans : ∀ {x y z : D}, Before x y → Before y z → Before x z
  irrefl : ∀ x : D, ¬ Before x x

namespace Directed

theorem asymm {D : Type u} (DA : Directed D) {x y : D}
    (h : DA.Before x y) : ¬ DA.Before y x :=
  fun h' => DA.irrefl x (DA.trans h h')

def ofBase {D : Type u} (base : D → D → Prop)
    (acyclic : ∀ x, ¬ Relation.TransGen base x x) : Directed D where
  Before := Relation.TransGen base
  trans := Relation.TransGen.trans
  irrefl := acyclic

theorem rank_lt_of_transGen {D : Type u} {base : D → D → Prop}
    {rank : D → Nat}
    (step_lt : ∀ {x y}, base x y → rank x < rank y)
    {x y : D} (h : Relation.TransGen base x y) : rank x < rank y := by
  induction h with
  | single hxy => exact step_lt hxy
  | tail _ hyz ih => exact Nat.lt_trans ih (step_lt hyz)

def ofBaseRank {D : Type u} (base : D → D → Prop) (rank : D → Nat)
    (step_lt : ∀ {x y}, base x y → rank x < rank y) : Directed D :=
  ofBase base fun x h =>
    Nat.lt_irrefl (rank x)
      (rank_lt_of_transGen (base := base) (rank := rank) step_lt h)

end Directed

/--
The undirected dependence certificate carried by a causal claim.  It singles
out `x` in the first component and `y` in the last; the certified mutual
dependence does not itself assert that either designatum is before the other.
-/
inductive Causation (D : Type u) (x y : D) : Prop where
  | ofMutualDependence (m : MutualDependence D)
      (mem_c₁ : x ∈ m.c₁) (mem_cₙ : y ∈ m.cₙ)

namespace Causation

theorem symm {D : Type u} {x y : D} (h : Causation D x y) :
    Causation D y x := by
  obtain ⟨m, hx, hy⟩ := h
  exact .ofMutualDependence m.reverse hy hx

end Causation

structure Causal (D : Type u) extends Directed D where
  Causes : D → D → Prop
  causes_before : ∀ {x y : D}, Causes x y → Before x y
  certify : ∀ {x y : D}, Causes x y → Causation D x y

namespace Causal

/-- Causal claims inherit asymmetry from their strict `Before` overlay. -/
theorem causes_asymm {D : Type u} (C : Causal D) {x y : D}
    (h : C.Causes x y) : ¬ C.Causes y x :=
  fun h' => C.toDirected.asymm (C.causes_before h) (C.causes_before h')

end Causal
