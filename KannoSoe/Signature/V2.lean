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

/--
Replace each member of a component by a nonempty component and take their
indexed union.  The subtype argument identifies the source slot while the
union is built; the enclosing `Segment.Shell` retains the slot presentation.
-/
def bind {D : Type u} (source : Component D)
    (part : (d : {d // d ∈ source}) → Component D) : Component D where
  carrier := fun x => ∃ d, x ∈ part d
  nonempty := by
    obtain ⟨d, hd⟩ := source.nonempty
    obtain ⟨x, hx⟩ := (part ⟨d, hd⟩).nonempty
    exact ⟨x, ⟨⟨d, hd⟩, hx⟩⟩

@[simp] theorem mem_bind_iff {D : Type u} {source : Component D}
    {part : (d : {d // d ∈ source}) → Component D} {x : D} :
    x ∈ source.bind part ↔ ∃ d, x ∈ part d :=
  Iff.rfl

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

/-- Reverse a certified dependence together with its holding proof. -/
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
An elaboration system. `Elab d rawM` asserts that designatum `d` *may be
elaborated as* the raw mutual dependence `rawM`.

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

/--
A chosen elaboration body together with the proof that it certifies under the
interdependence derived from the same elaboration system.

The raw target is retained because `Elab` may inspect its original interdependence;
`certify` is the sanctioned operation which retags that target with
`Interdependence.ofElaboration E`.
-/
structure Resolution {D : Type u} (E : Elaboration D) (d : D) where
  raw : RawMutualDependence D
  isElaboration : E.Elab d raw
  holds : (E.certify raw).Holds

namespace Resolution

/-- Proof irrelevance reduces resolution equality to equality of raw bodies. -/
theorem ext {D : Type u} {E : Elaboration D} {d : D}
    {r₁ r₂ : Resolution E d} (h : r₁.raw = r₂.raw) : r₁ = r₂ := by
  cases r₁
  cases r₂
  cases h
  rfl

/-- The certified mutual dependence selected by a resolution. -/
def toMutualDependence {D : Type u} {E : Elaboration D} {d : D}
    (r : Resolution E d) : MutualDependence D :=
  ⟨E.certify r.raw, r.holds⟩

@[simp] theorem toMutualDependence_toRaw {D : Type u}
    {E : Elaboration D} {d : D} (r : Resolution E d) :
    r.toMutualDependence.toRaw = E.certify r.raw :=
  rfl

@[simp] theorem toMutualDependence_interdependence {D : Type u}
    {E : Elaboration D} {d : D} (r : Resolution E d) :
    r.toMutualDependence.interdependence = Interdependence.ofElaboration E :=
  rfl

@[simp] theorem toMutualDependence_c₁ {D : Type u}
    {E : Elaboration D} {d : D} (r : Resolution E d) :
    r.toMutualDependence.c₁ = r.raw.c₁ :=
  rfl

@[simp] theorem toMutualDependence_cₙ {D : Type u}
    {E : Elaboration D} {d : D} (r : Resolution E d) :
    r.toMutualDependence.cₙ = r.raw.cₙ :=
  rfl

/-- Reverse a selected body when the elaboration accepts reversed targets. -/
def reverse {D : Type u} {E : Elaboration D} {d : D}
    (r : Resolution E d) (hrc : E.ReversalClosed) : Resolution E d where
  raw := r.raw.reverse
  isElaboration := hrc d r.raw r.isElaboration
  holds := by
    rw [Elaboration.certify_reverse]
    exact r.holds.reverse

@[simp] theorem raw_reverse {D : Type u} {E : Elaboration D} {d : D}
    (r : Resolution E d) (hrc : E.ReversalClosed) :
    (r.reverse hrc).raw = r.raw.reverse :=
  rfl

@[simp] theorem toMutualDependence_reverse {D : Type u}
    {E : Elaboration D} {d : D} (r : Resolution E d)
    (hrc : E.ReversalClosed) :
    (r.reverse hrc).toMutualDependence = r.toMutualDependence.reverse :=
  MutualDependence.ext rfl

@[simp] theorem reverse_reverse {D : Type u} {E : Elaboration D} {d : D}
    (r : Resolution E d) (hrc : E.ReversalClosed) :
    (r.reverse hrc).reverse hrc = r :=
  ext (RawMutualDependence.reverse_reverse r.raw)

end Resolution

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
A nonempty collection of resonances whose singleton middle components form
one certified mutual dependence.
-/
structure Being (D : Type u) where
  resonances : List (Resonance D)
  nonempty : resonances ≠ []
  toMutualDependence : MutualDependence D
  components_eq :
    toMutualDependence.components =
      resonances.flatMap Resonance.middleComponents

namespace Being

/--
Certify a nonempty list of resonances as a being. Each resonance contributes
its two singleton middle components, and `holds` certifies the resulting
chain, including the interdependence between every pair of consecutive
resonances.
-/
def ofResonances {D : Type u}
    (L : Interdependence D)
    (resonances : List (Resonance D))
    (nonempty : resonances ≠ [])
    (holds :
      L.Chained
        (resonances.flatMap Resonance.middleComponents)) :
    Being D := by
  cases resonances with
  | nil => exact (nonempty rfl).elim
  | cons r rest =>
      have chain :
          L.Chained
            (Component.singleton r.b₁ :: Component.singleton r.b₂ ::
              rest.flatMap Resonance.middleComponents) := by
        simpa [Resonance.middleComponents] using holds
      refine
        ⟨r :: rest, by simp,
          MutualDependence.ofComponents L
            (Component.singleton r.b₁) (Component.singleton r.b₂)
            (rest.flatMap Resonance.middleComponents) chain, ?_⟩
      simp [MutualDependence.ofComponents, MutualDependence.components,
        Resonance.middleComponents]

instance {D : Type u} : Coe (Being D) (MutualDependence D) :=
  ⟨toMutualDependence⟩

end Being

/-! ## Segments

`Component` remains the unit placed at each position of an ordinary mutual
dependence.  A segment is a presentation layer in which a designatum in a
component may be opened as one certified mutual dependence.  The opened body
is retained, and its first and last components become that slot's left and
right interfaces.  Slots in a multi-member component are combined in
parallel; adjacent segments continue to use `Elaboration.Interdependent`.

Opening is one level deep and local to an occurrence.  In particular, a leaf
means "not opened here", not "provably has no elaboration".  This keeps every
component immediately usable and does not demand a recursive normal form from
possibly cyclic elaboration systems.
-/

namespace Segment

/-! ## Component shells -/

/--
One designatum-slot in a component presentation.  A resolved slot stores one
complete certified body, so its two interfaces cannot be selected from
different elaboration alternatives.
-/
inductive Slot {D : Type u} (E : Elaboration D) (d : D) where
  | leaf
  | resolved (resolution : Elaboration.Resolution E d)

namespace Slot

/-- The interface exposed by a slot to its left. -/
def left {D : Type u} {E : Elaboration D} {d : D} :
    Slot E d → Component D
  | .leaf => Component.singleton d
  | .resolved r => r.toMutualDependence.c₁

/-- The interface exposed by a slot to its right. -/
def right {D : Type u} {E : Elaboration D} {d : D} :
    Slot E d → Component D
  | .leaf => Component.singleton d
  | .resolved r => r.toMutualDependence.cₙ

@[simp] theorem left_leaf {D : Type u} {E : Elaboration D} {d : D} :
    (Slot.leaf : Slot E d).left = Component.singleton d :=
  rfl

@[simp] theorem right_leaf {D : Type u} {E : Elaboration D} {d : D} :
    (Slot.leaf : Slot E d).right = Component.singleton d :=
  rfl

@[simp] theorem left_resolved {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (Slot.resolved r).left = r.raw.c₁ :=
  rfl

@[simp] theorem right_resolved {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (Slot.resolved r).right = r.raw.cₙ :=
  rfl

/-- Every member of a slot's right interface is reachable from its source. -/
theorem reaches_of_mem_right {D : Type u} {E : Elaboration D} {d x : D}
    (s : Slot E d) (hx : x ∈ s.right) : E.Reaches d x := by
  cases s with
  | leaf =>
      have hxd : x = d := by simpa using hx
      subst x
      exact Elaboration.Reaches.refl d
  | resolved r =>
      exact Elaboration.Reaches.single r.isElaboration
        r.raw.cₙ_mem_components hx

/-- Every member of a slot's left interface is reachable from its source. -/
theorem reaches_of_mem_left {D : Type u} {E : Elaboration D} {d x : D}
    (s : Slot E d) (hx : x ∈ s.left) : E.Reaches d x := by
  cases s with
  | leaf =>
      have hxd : x = d := by simpa using hx
      subst x
      exact Elaboration.Reaches.refl d
  | resolved r =>
      exact Elaboration.Reaches.single r.isElaboration
        r.raw.c₁_mem_components hx

/-- Reverse a slot's retained body and exchange its two interfaces. -/
def reverse {D : Type u} {E : Elaboration D} {d : D}
    (s : Slot E d) (hrc : E.ReversalClosed) : Slot E d :=
  match s with
  | .leaf => .leaf
  | .resolved r => .resolved (r.reverse hrc)

@[simp] theorem left_reverse {D : Type u} {E : Elaboration D} {d : D}
    (s : Slot E d) (hrc : E.ReversalClosed) :
    (s.reverse hrc).left = s.right := by
  cases s <;> rfl

@[simp] theorem right_reverse {D : Type u} {E : Elaboration D} {d : D}
    (s : Slot E d) (hrc : E.ReversalClosed) :
    (s.reverse hrc).right = s.left := by
  cases s <;> rfl

@[simp] theorem reverse_reverse {D : Type u} {E : Elaboration D} {d : D}
    (s : Slot E d) (hrc : E.ReversalClosed) :
    (s.reverse hrc).reverse hrc = s := by
  cases s <;> simp [reverse]

end Slot

/--
A component position with a finite, occurrence-local presentation.  The
specialized `component` and `resolution` cases make their interfaces reduce
definitionally; `slots` opens the members of a multi-member source in
parallel.
-/
inductive Shell {D : Type u} (E : Elaboration D) where
  | component (source : Component D)
  | slots (source : Component D)
      (slot : (d : {d // d ∈ source}) → Slot E d.1)
  | resolution {d : D} (value : Elaboration.Resolution E d)

namespace Shell

/-- The source component retained by a shell. -/
def source {D : Type u} {E : Elaboration D} : Shell E → Component D
  | .component c => c
  | .slots c _ => c
  | .resolution (d := d) _ => Component.singleton d

/-- The parallel union of all left slot-interfaces. -/
def left {D : Type u} {E : Elaboration D} : Shell E → Component D
  | .component c => c
  | .slots c slot => c.bind fun d => (slot d).left
  | .resolution r => r.toMutualDependence.c₁

/-- The parallel union of all right slot-interfaces. -/
def right {D : Type u} {E : Elaboration D} : Shell E → Component D
  | .component c => c
  | .slots c slot => c.bind fun d => (slot d).right
  | .resolution r => r.toMutualDependence.cₙ

/-- A component used without opening any of its occurrences. -/
def ofComponent {D : Type u} (E : Elaboration D)
    (source : Component D) : Shell E :=
  .component source

/-- Open source slots with a total designatum-indexed presentation. -/
def ofSlots {D : Type u} {E : Elaboration D} (source : Component D)
    (slot : (d : D) → Slot E d) : Shell E :=
  .slots source fun d => slot d.1

/-- A singleton component used without opening its designatum. -/
def ofDesignatum {D : Type u} (E : Elaboration D) (d : D) : Shell E :=
  ofComponent E (Component.singleton d)

/--
Place a designatum in its singleton source component and open that occurrence
as the selected certified body.
-/
def ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) : Shell E :=
  .resolution r

@[simp] theorem source_ofComponent {D : Type u} (E : Elaboration D)
    (source : Component D) : (ofComponent E source).source = source :=
  rfl

@[simp] theorem left_ofComponent {D : Type u} (E : Elaboration D)
    (source : Component D) : (ofComponent E source).left = source :=
  rfl

@[simp] theorem right_ofComponent {D : Type u} (E : Elaboration D)
    (source : Component D) : (ofComponent E source).right = source :=
  rfl

@[simp] theorem source_ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (ofResolution r).source = Component.singleton d :=
  rfl

@[simp] theorem left_ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (ofResolution r).left = r.raw.c₁ :=
  rfl

@[simp] theorem right_ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (ofResolution r).right = r.raw.cₙ :=
  rfl

@[simp] theorem mem_left_slots_iff {D : Type u} {E : Elaboration D}
    {source : Component D}
    {slot : (d : {d // d ∈ source}) → Slot E d.1} {x : D} :
    x ∈ (Shell.slots source slot).left ↔
      ∃ d, x ∈ (slot d).left :=
  Iff.rfl

@[simp] theorem mem_right_slots_iff {D : Type u} {E : Elaboration D}
    {source : Component D}
    {slot : (d : {d // d ∈ source}) → Slot E d.1} {x : D} :
    x ∈ (Shell.slots source slot).right ↔
      ∃ d, x ∈ (slot d).right :=
  Iff.rfl

/-- A right-interface member is reachable from some retained source member. -/
theorem reaches_of_mem_right {D : Type u} {E : Elaboration D}
    (s : Shell E) {x : D} (hx : x ∈ s.right) :
    ∃ d, d ∈ s.source ∧ E.Reaches d x := by
  cases s with
  | component source =>
      exact ⟨x, hx, Elaboration.Reaches.refl x⟩
  | slots source slot =>
      obtain ⟨d, hdx⟩ := hx
      exact ⟨d.1, d.2, (slot d).reaches_of_mem_right hdx⟩
  | resolution r =>
      rename_i d
      exact ⟨d, (show d ∈ Component.singleton d by simp),
        Elaboration.Reaches.single r.isElaboration
        r.raw.cₙ_mem_components hx⟩

/-- Every retained source member reaches some right-interface member. -/
theorem exists_mem_right_reaches {D : Type u} {E : Elaboration D}
    (s : Shell E) {d : D} (hd : d ∈ s.source) :
    ∃ x, x ∈ s.right ∧ E.Reaches d x := by
  cases s with
  | component source =>
      exact ⟨d, hd, Elaboration.Reaches.refl d⟩
  | slots source slot =>
      let sourceMember : {x // x ∈ source} := ⟨d, hd⟩
      obtain ⟨x, hx⟩ := (slot sourceMember).right.exists_mem
      exact ⟨x, ⟨sourceMember, hx⟩,
        (slot sourceMember).reaches_of_mem_right hx⟩
  | resolution r =>
      rename_i sourceD
      change d ∈ Component.singleton sourceD at hd
      have hsource : d = sourceD := by simpa using hd
      subst d
      obtain ⟨x, hx⟩ := r.raw.cₙ.exists_mem
      exact ⟨x, hx, Elaboration.Reaches.single r.isElaboration
        r.raw.cₙ_mem_components hx⟩

/-- A left-interface member is reachable from some retained source member. -/
theorem reaches_of_mem_left {D : Type u} {E : Elaboration D}
    (s : Shell E) {x : D} (hx : x ∈ s.left) :
    ∃ d, d ∈ s.source ∧ E.Reaches d x := by
  cases s with
  | component source =>
      exact ⟨x, hx, Elaboration.Reaches.refl x⟩
  | slots source slot =>
      obtain ⟨d, hdx⟩ := hx
      exact ⟨d.1, d.2, (slot d).reaches_of_mem_left hdx⟩
  | resolution r =>
      rename_i d
      exact ⟨d, (show d ∈ Component.singleton d by simp),
        Elaboration.Reaches.single r.isElaboration
        r.raw.c₁_mem_components hx⟩

/-- Every retained source member reaches some left-interface member. -/
theorem exists_mem_left_reaches {D : Type u} {E : Elaboration D}
    (s : Shell E) {d : D} (hd : d ∈ s.source) :
    ∃ x, x ∈ s.left ∧ E.Reaches d x := by
  cases s with
  | component source =>
      exact ⟨d, hd, Elaboration.Reaches.refl d⟩
  | slots source slot =>
      let sourceMember : {x // x ∈ source} := ⟨d, hd⟩
      obtain ⟨x, hx⟩ := (slot sourceMember).left.exists_mem
      exact ⟨x, ⟨sourceMember, hx⟩,
        (slot sourceMember).reaches_of_mem_left hx⟩
  | resolution r =>
      rename_i sourceD
      change d ∈ Component.singleton sourceD at hd
      have hsource : d = sourceD := by simpa using hd
      subst d
      obtain ⟨x, hx⟩ := r.raw.c₁.exists_mem
      exact ⟨x, hx, Elaboration.Reaches.single r.isElaboration
        r.raw.c₁_mem_components hx⟩

/-- Interdependence from the right interface is sound for the retained source. -/
theorem interdependent_of_interdependent_right {D : Type u} {E : Elaboration D}
    (s : Shell E) {c : Component D} (h : E.Interdependent s.right c) :
    E.Interdependent s.source c := by
  constructor
  · intro d hd
    obtain ⟨x, hx, hdx⟩ := s.exists_mem_right_reaches hd
    obtain ⟨y, hy, hxy⟩ := h.1 x hx
    exact ⟨y, hy, Elaboration.Joinable.of_reaches hdx hxy⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := h.2 y hy
    obtain ⟨d, hd, hdx⟩ := s.reaches_of_mem_right hx
    exact ⟨d, hd, Elaboration.Joinable.of_reaches hdx hxy⟩

/-- Interdependence from the left interface is sound for the retained source. -/
theorem interdependent_of_interdependent_left {D : Type u} {E : Elaboration D}
    (s : Shell E) {c : Component D} (h : E.Interdependent s.left c) :
    E.Interdependent s.source c := by
  constructor
  · intro d hd
    obtain ⟨x, hx, hdx⟩ := s.exists_mem_left_reaches hd
    obtain ⟨y, hy, hxy⟩ := h.1 x hx
    exact ⟨y, hy, Elaboration.Joinable.of_reaches hdx hxy⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := h.2 y hy
    obtain ⟨d, hd, hdx⟩ := s.reaches_of_mem_left hx
    exact ⟨d, hd, Elaboration.Joinable.of_reaches hdx hxy⟩

/-- Opening every source member as a leaf preserves the left component. -/
@[simp] theorem left_slots_all_leaf {D : Type u} {E : Elaboration D}
    (c : Component D) :
    (Shell.slots c fun _ => (Slot.leaf : Slot E _)).left = c := by
  apply Component.ext
  intro x
  constructor
  · rintro ⟨member, hx⟩
    have hxm : x = member.1 := by simpa using hx
    rw [hxm]
    exact member.2
  · intro hx
    exact ⟨⟨x, hx⟩, by simp⟩

/-- Opening every source member as a leaf preserves the right component. -/
@[simp] theorem right_slots_all_leaf {D : Type u} {E : Elaboration D}
    (c : Component D) :
    (Shell.slots c fun _ => (Slot.leaf : Slot E _)).right = c := by
  apply Component.ext
  intro x
  constructor
  · rintro ⟨member, hx⟩
    have hxm : x = member.1 := by simpa using hx
    rw [hxm]
    exact member.2
  · intro hx
    exact ⟨⟨x, hx⟩, by simp⟩

/-- A singleton shell's left interface is its sole slot's left interface. -/
@[simp] theorem left_slots_singleton {D : Type u} {E : Elaboration D}
    (d : D)
    (slot : (x : {x // x ∈ Component.singleton d}) → Slot E x.1) :
    (Shell.slots (Component.singleton d) slot).left =
      (slot ⟨d, by simp⟩).left := by
  apply Component.ext
  intro x
  constructor
  · rintro ⟨member, hx⟩
    have hmember : member = (⟨d, by simp⟩ :
        {x // x ∈ Component.singleton d}) := by
      apply Subtype.ext
      simpa using member.2
    subst member
    exact hx
  · intro hx
    exact ⟨⟨d, by simp⟩, hx⟩

/-- A singleton shell's right interface is its sole slot's right interface. -/
@[simp] theorem right_slots_singleton {D : Type u} {E : Elaboration D}
    (d : D)
    (slot : (x : {x // x ∈ Component.singleton d}) → Slot E x.1) :
    (Shell.slots (Component.singleton d) slot).right =
      (slot ⟨d, by simp⟩).right := by
  apply Component.ext
  intro x
  constructor
  · rintro ⟨member, hx⟩
    have hmember : member = (⟨d, by simp⟩ :
        {x // x ∈ Component.singleton d}) := by
      apply Subtype.ext
      simpa using member.2
    subst member
    exact hx
  · intro hx
    exact ⟨⟨d, by simp⟩, hx⟩

/-- The general `slots` encoding of one resolved singleton occurrence. -/
def singleResolvedSlot {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) : Shell E :=
  .slots (Component.singleton d) fun member =>
    have hmember : member.1 = d := by simpa using member.2
    hmember.symm ▸ Slot.resolved r

@[simp] theorem source_singleResolvedSlot {D : Type u}
    {E : Elaboration D} {d : D} (r : Elaboration.Resolution E d) :
    (singleResolvedSlot r).source = Component.singleton d :=
  rfl

@[simp] theorem left_singleResolvedSlot {D : Type u}
    {E : Elaboration D} {d : D} (r : Elaboration.Resolution E d) :
    (singleResolvedSlot r).left = (ofResolution r).left := by
  rw [singleResolvedSlot, left_slots_singleton]
  rfl

@[simp] theorem right_singleResolvedSlot {D : Type u}
    {E : Elaboration D} {d : D} (r : Elaboration.Resolution E d) :
    (singleResolvedSlot r).right = (ofResolution r).right := by
  rw [singleResolvedSlot, right_slots_singleton]
  rfl

/-- The general and specialized encodings agree on source and interfaces. -/
theorem singleResolvedSlot_ofResolution {D : Type u}
    {E : Elaboration D} {d : D} (r : Elaboration.Resolution E d) :
    (singleResolvedSlot r).source = (ofResolution r).source ∧
      (singleResolvedSlot r).left = (ofResolution r).left ∧
        (singleResolvedSlot r).right = (ofResolution r).right := by
  simp

/-- Reverse every opened body in a shell while retaining its source. -/
def reverse {D : Type u} {E : Elaboration D}
    (s : Shell E) (hrc : E.ReversalClosed) : Shell E :=
  match s with
  | .component c => .component c
  | .slots c slot => .slots c fun d => (slot d).reverse hrc
  | .resolution r => .resolution (r.reverse hrc)

@[simp] theorem source_reverse {D : Type u} {E : Elaboration D}
    (s : Shell E) (hrc : E.ReversalClosed) :
    (s.reverse hrc).source = s.source := by
  cases s <;> rfl

@[simp] theorem left_reverse {D : Type u} {E : Elaboration D}
    (s : Shell E) (hrc : E.ReversalClosed) :
    (s.reverse hrc).left = s.right := by
  cases s <;> simp [reverse, Shell.left, Shell.right]

@[simp] theorem right_reverse {D : Type u} {E : Elaboration D}
    (s : Shell E) (hrc : E.ReversalClosed) :
    (s.reverse hrc).right = s.left := by
  cases s <;> simp [reverse, Shell.left, Shell.right]

@[simp] theorem reverse_reverse {D : Type u} {E : Elaboration D}
    (s : Shell E) (hrc : E.ReversalClosed) :
    (s.reverse hrc).reverse hrc = s := by
  cases s <;> simp [reverse]

end Shell

/-! ## Serial segment presentations -/

/--
The retained shape of a segment.  `catenated` records serial composition without
discarding either side; a direct mutual dependence may also occupy a segment
position when its interdependence is the one induced by `E`.
-/
inductive Shape {D : Type u} (E : Elaboration D) where
  | shell (value : Shell E)
  | dependence (value : MutualDependence D)
      (compatible : value.interdependence = Interdependence.ofElaboration E)
  | catenated (left right : Shape E)

namespace Shape

/-- The left interface of a retained segment shape. -/
def left {D : Type u} {E : Elaboration D} : Shape E → Component D
  | .shell s => s.left
  | .dependence m _ => m.c₁
  | .catenated l _ => l.left

/-- The right interface of a retained segment shape. -/
def right {D : Type u} {E : Elaboration D} : Shape E → Component D
  | .shell s => s.right
  | .dependence m _ => m.cₙ
  | .catenated _ r => r.right

@[simp] theorem left_shell {D : Type u} {E : Elaboration D}
    (s : Shell E) : (Shape.shell s).left = s.left :=
  rfl

@[simp] theorem right_shell {D : Type u} {E : Elaboration D}
    (s : Shell E) : (Shape.shell s).right = s.right :=
  rfl

@[simp] theorem left_dependence {D : Type u} {E : Elaboration D}
    (m : MutualDependence D)
    (compatible : m.interdependence = Interdependence.ofElaboration E) :
    (Shape.dependence m compatible).left = m.c₁ :=
  rfl

@[simp] theorem right_dependence {D : Type u} {E : Elaboration D}
    (m : MutualDependence D)
    (compatible : m.interdependence = Interdependence.ofElaboration E) :
    (Shape.dependence m compatible).right = m.cₙ :=
  rfl

@[simp] theorem left_catenated {D : Type u} {E : Elaboration D}
    (s₁ s₂ : Shape E) : (Shape.catenated s₁ s₂).left = s₁.left :=
  rfl

@[simp] theorem right_catenated {D : Type u} {E : Elaboration D}
    (s₁ s₂ : Shape E) : (Shape.catenated s₁ s₂).right = s₂.right :=
  rfl

/--
Internal validity of a shape.  Shells contain only leaves or certified
resolutions, and compatible mutual dependences are already certified.  An
catenation adds exactly the interdependence between the exposed adjacent
interfaces.
-/
def Holds {D : Type u} {E : Elaboration D} : Shape E → Prop
  | .shell _ => True
  | .dependence _ _ => True
  | .catenated l r => l.Holds ∧ r.Holds ∧ E.Interdependent l.right r.left

@[simp] theorem holds_catenated_iff {D : Type u} {E : Elaboration D}
    (s₁ s₂ : Shape E) :
    (Shape.catenated s₁ s₂).Holds ↔
      s₁.Holds ∧ s₂.Holds ∧ E.Interdependent s₁.right s₂.left :=
  Iff.rfl

/-- The retained source components, in serial display order. -/
def sourceComponents {D : Type u} {E : Elaboration D} :
    Shape E → List (Component D)
  | .shell s => [s.source]
  | .dependence m _ => m.components
  | .catenated s₁ s₂ => s₁.sourceComponents ++ s₂.sourceComponents

@[simp] theorem sourceComponents_shell {D : Type u} {E : Elaboration D}
    (s : Shell E) : (Shape.shell s).sourceComponents = [s.source] :=
  rfl

@[simp] theorem sourceComponents_dependence {D : Type u}
    {E : Elaboration D} (m : MutualDependence D)
    (compatible : m.interdependence = Interdependence.ofElaboration E) :
    (Shape.dependence m compatible).sourceComponents = m.components :=
  rfl

@[simp] theorem sourceComponents_catenated {D : Type u}
    {E : Elaboration D} (s₁ s₂ : Shape E) :
    (Shape.catenated s₁ s₂).sourceComponents =
      s₁.sourceComponents ++ s₂.sourceComponents :=
  rfl

theorem sourceComponents_ne_nil {D : Type u} {E : Elaboration D}
    (sh : Shape E) : sh.sourceComponents ≠ [] := by
  induction sh with
  | shell s => simp
  | dependence m compatible =>
      simp [MutualDependence.components, RawMutualDependence.components]
  | catenated s₁ s₂ ih₁ ih₂ =>
      cases hsource : s₁.sourceComponents with
      | nil => exact (ih₁ hsource).elim
      | cons c rest => simp [hsource]

/--
Decompose the retained sources at the right edge and transport any
interdependence from the exposed interface back to that last source component.
-/
theorem exists_last_source {D : Type u} {E : Elaboration D}
    (sh : Shape E) :
    ∃ before last,
      sh.sourceComponents = before ++ [last] ∧
        ∀ c, E.Interdependent sh.right c → E.Interdependent last c := by
  induction sh with
  | shell s =>
      exact ⟨[], s.source, rfl, fun _ h => s.interdependent_of_interdependent_right h⟩
  | dependence m compatible =>
      exact ⟨m.c₁ :: m.middle, m.cₙ, rfl, fun _ h => h⟩
  | catenated s₁ s₂ ih₁ ih₂ =>
      obtain ⟨before, last, hsources, htransport⟩ := ih₂
      refine ⟨s₁.sourceComponents ++ before, last, ?_, ?_⟩
      · simp [hsources]
      · exact htransport

/--
Decompose the retained sources at the left edge and transport any
interdependence from the exposed interface back to that first source component.
-/
theorem exists_head_source {D : Type u} {E : Elaboration D}
    (sh : Shape E) :
    ∃ first after,
      sh.sourceComponents = first :: after ∧
        ∀ c, E.Interdependent c sh.left → E.Interdependent c first := by
  induction sh with
  | shell s =>
      exact ⟨s.source, [], rfl,
        fun _ h => (s.interdependent_of_interdependent_left h.symm).symm⟩
  | dependence m compatible =>
      exact ⟨m.c₁, m.middle ++ [m.cₙ], rfl, fun _ h => h⟩
  | catenated s₁ s₂ ih₁ ih₂ =>
      obtain ⟨first, after, hsources, htransport⟩ := ih₁
      refine ⟨first, after ++ s₂.sourceComponents, ?_, ?_⟩
      · simp [hsources]
      · exact htransport

/-- Every holding retained shape flattens to a chained source-component list. -/
theorem chained_sourceComponents {D : Type u} {E : Elaboration D}
    (sh : Shape E) (h : sh.Holds) :
    (Interdependence.ofElaboration E).Chained sh.sourceComponents := by
  induction sh with
  | shell s => exact .single s.source
  | dependence m compatible =>
      change (Interdependence.ofElaboration E).Chained m.components
      rw [← compatible]
      exact m.holds
  | catenated s₁ s₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂, hinterdependent⟩ := h
      have hchain₁ := ih₁ h₁
      have hchain₂ := ih₂ h₂
      obtain ⟨before, last, hsources₁, hlast⟩ :=
        exists_last_source s₁
      obtain ⟨first, after, hsources₂, hfirst⟩ :=
        exists_head_source s₂
      have hlastFirst : E.Interdependent last first :=
        hfirst last (hlast s₂.left hinterdependent)
      rw [hsources₁] at hchain₁
      rw [hsources₂] at hchain₂
      rw [sourceComponents_catenated, hsources₁, hsources₂]
      exact Interdependence.Chained.catenate
        hchain₁ hchain₂ hlastFirst

/-- Reverse retained bodies and reverse the order of serial composition. -/
def reverse {D : Type u} {E : Elaboration D}
    (sh : Shape E) (hrc : E.ReversalClosed) : Shape E :=
  match sh with
  | .shell s => .shell (s.reverse hrc)
  | .dependence m compatible =>
      .dependence m.reverse (by simpa using compatible)
  | .catenated s₁ s₂ => .catenated (s₂.reverse hrc) (s₁.reverse hrc)

@[simp] theorem left_reverse {D : Type u} {E : Elaboration D}
    (sh : Shape E) (hrc : E.ReversalClosed) :
    (sh.reverse hrc).left = sh.right := by
  induction sh <;> simp [reverse, *]

@[simp] theorem right_reverse {D : Type u} {E : Elaboration D}
    (sh : Shape E) (hrc : E.ReversalClosed) :
    (sh.reverse hrc).right = sh.left := by
  induction sh <;> simp [reverse, *]

@[simp] theorem sourceComponents_reverse {D : Type u}
    {E : Elaboration D} (sh : Shape E) (hrc : E.ReversalClosed) :
    (sh.reverse hrc).sourceComponents = sh.sourceComponents.reverse := by
  induction sh <;> simp [reverse, *, List.reverse_append]

/-- Internal validity is preserved by reversing the complete retained shape. -/
theorem Holds.reverse {D : Type u} {E : Elaboration D} {sh : Shape E}
    (h : sh.Holds) (hrc : E.ReversalClosed) : (sh.reverse hrc).Holds := by
  induction sh with
  | shell s => trivial
  | dependence m compatible => trivial
  | catenated s₁ s₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂, hinterdependent⟩ := h
      exact ⟨ih₂ h₂, ih₁ h₁, by simpa using hinterdependent.symm⟩

@[simp] theorem reverse_reverse {D : Type u} {E : Elaboration D}
    (sh : Shape E) (hrc : E.ReversalClosed) :
    (sh.reverse hrc).reverse hrc = sh := by
  induction sh <;> simp [reverse, *]

end Shape

end Segment

/-- A retained endpoint-sensitive shape with its interdependence proofs. -/
structure Segment {D : Type u} (E : Elaboration D) where
  shape : Segment.Shape E
  holds : shape.Holds

namespace Segment

/-- Proof irrelevance reduces segment equality to equality of retained shapes. -/
theorem ext {D : Type u} {E : Elaboration D} {s₁ s₂ : Segment E}
    (h : s₁.shape = s₂.shape) : s₁ = s₂ := by
  cases s₁
  cases s₂
  cases h
  rfl

/-- The component exposed at the left edge of a segment. -/
def left {D : Type u} {E : Elaboration D} (s : Segment E) : Component D :=
  s.shape.left

/-- The component exposed at the right edge of a segment. -/
def right {D : Type u} {E : Elaboration D} (s : Segment E) : Component D :=
  s.shape.right

/-- A component shell is already a valid one-position segment. -/
def ofShell {D : Type u} {E : Elaboration D} (s : Shell E) : Segment E :=
  ⟨.shell s, trivial⟩

/-- Every component becomes a segment immediately, with equal interfaces. -/
def ofComponent {D : Type u} (E : Elaboration D)
    (c : Component D) : Segment E :=
  ofShell (Shell.ofComponent E c)

/-- Every designatum first becomes a singleton-component segment. -/
def ofDesignatum {D : Type u} (E : Elaboration D) (d : D) : Segment E :=
  ofComponent E (Component.singleton d)

/-- Open one singleton occurrence as its selected certified resolution. -/
def ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) : Segment E :=
  ofShell (Shell.ofResolution r)

/-- A compatible certified mutual dependence used directly as a segment. -/
def ofMutualDependence {D : Type u} {E : Elaboration D}
    (m : MutualDependence D)
    (compatible : m.interdependence = Interdependence.ofElaboration E) : Segment E :=
  ⟨.dependence m compatible, trivial⟩

/-- Two oriented segments are catenable when their facing endpoints interdepend. -/
def Catenable {D : Type u} (E : Elaboration D)
    (s₁ s₂ : Segment E) : Prop :=
  E.Interdependent s₁.right s₂.left

/--
Catenate two segments while retaining both shapes.  Only the left segment's
right interface and the right segment's left interface are checked.
-/
def catenate {D : Type u} {E : Elaboration D} (s₁ s₂ : Segment E)
    (catenable : Catenable E s₁ s₂) : Segment E :=
  ⟨.catenated s₁.shape s₂.shape, ⟨s₁.holds, s₂.holds, catenable⟩⟩

/-- Flatten a segment with at least two retained sources to a certified chain. -/
def toMutualDependence {D : Type u} {E : Elaboration D}
    (s : Segment E) {c₁ c₂ : Component D}
    {rest : List (Component D)}
    (hdecomp : s.shape.sourceComponents = c₁ :: c₂ :: rest) :
    MutualDependence D := by
  apply MutualDependence.ofComponents (Interdependence.ofElaboration E) c₁ c₂ rest
  rw [← hdecomp]
  exact s.shape.chained_sourceComponents s.holds

@[simp] theorem components_toMutualDependence {D : Type u}
    {E : Elaboration D} (s : Segment E) {c₁ c₂ : Component D}
    {rest : List (Component D)}
    (hdecomp : s.shape.sourceComponents = c₁ :: c₂ :: rest) :
    (s.toMutualDependence hdecomp).components = c₁ :: c₂ :: rest := by
  simp [toMutualDependence, MutualDependence.ofComponents,
    MutualDependence.components]

/-- Reverse the complete retained segment and its validity proof. -/
def reverse {D : Type u} {E : Elaboration D}
    (s : Segment E) (hrc : E.ReversalClosed) : Segment E :=
  ⟨s.shape.reverse hrc, s.holds.reverse hrc⟩

@[simp] theorem left_reverse {D : Type u} {E : Elaboration D}
    (s : Segment E) (hrc : E.ReversalClosed) :
    (s.reverse hrc).left = s.right :=
  Shape.left_reverse s.shape hrc

@[simp] theorem right_reverse {D : Type u} {E : Elaboration D}
    (s : Segment E) (hrc : E.ReversalClosed) :
    (s.reverse hrc).right = s.left :=
  Shape.right_reverse s.shape hrc

@[simp] theorem reverse_reverse {D : Type u} {E : Elaboration D}
    (s : Segment E) (hrc : E.ReversalClosed) :
    (s.reverse hrc).reverse hrc = s :=
  ext (Shape.reverse_reverse s.shape hrc)

/-- A catenable display reverses by reversing and exchanging both sides. -/
theorem Catenable.reverse {D : Type u} {E : Elaboration D}
    {s₁ s₂ : Segment E} (h : Catenable E s₁ s₂)
    (hrc : E.ReversalClosed) :
    Catenable E (s₂.reverse hrc) (s₁.reverse hrc) := by
  simpa [Catenable] using h.symm

@[simp] theorem reverse_catenate {D : Type u} {E : Elaboration D}
    (s₁ s₂ : Segment E) (h : Catenable E s₁ s₂)
    (hrc : E.ReversalClosed) :
    (catenate s₁ s₂ h).reverse hrc =
      catenate (s₂.reverse hrc) (s₁.reverse hrc) (h.reverse hrc) :=
  ext rfl

/-- Interface interdependence at a left shell transports to its source. -/
theorem interdependent_source_of_catenable_left {D : Type u} {E : Elaboration D}
    (s₁ : Shell E) (s₂ : Segment E) (h : Catenable E (ofShell s₁) s₂) :
    E.Interdependent s₁.source s₂.left :=
  s₁.interdependent_of_interdependent_right h

/-- Interface interdependence at a right shell transports to its source. -/
theorem interdependent_source_of_catenable_right {D : Type u} {E : Elaboration D}
    (s₁ : Segment E) (s₂ : Shell E) (h : Catenable E s₁ (ofShell s₂)) :
    E.Interdependent s₁.right s₂.source :=
  (s₂.interdependent_of_interdependent_left h.symm).symm

/-- Catenable shells have interdependent source components. -/
theorem interdependent_sources_of_catenable {D : Type u} {E : Elaboration D}
    (s₁ s₂ : Shell E) (h : Catenable E (ofShell s₁) (ofShell s₂)) :
    E.Interdependent s₁.source s₂.source := by
  have hleft : E.Interdependent s₁.source s₂.left :=
    interdependent_source_of_catenable_left s₁ (ofShell s₂) h
  exact (s₂.interdependent_of_interdependent_left hleft.symm).symm

@[simp] theorem left_ofShell {D : Type u} {E : Elaboration D}
    (s : Shell E) : (ofShell s).left = s.left :=
  rfl

@[simp] theorem right_ofShell {D : Type u} {E : Elaboration D}
    (s : Shell E) : (ofShell s).right = s.right :=
  rfl

@[simp] theorem left_ofComponent {D : Type u} (E : Elaboration D)
    (c : Component D) : (ofComponent E c).left = c := by
  simp [ofComponent]

@[simp] theorem right_ofComponent {D : Type u} (E : Elaboration D)
    (c : Component D) : (ofComponent E c).right = c := by
  simp [ofComponent]

@[simp] theorem left_ofDesignatum {D : Type u} (E : Elaboration D) (d : D) :
    (ofDesignatum E d).left = Component.singleton d := by
  simp [ofDesignatum]

@[simp] theorem right_ofDesignatum {D : Type u} (E : Elaboration D) (d : D) :
    (ofDesignatum E d).right = Component.singleton d := by
  simp [ofDesignatum]

@[simp] theorem left_ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (ofResolution r).left = r.raw.c₁ := by
  simp [ofResolution]

@[simp] theorem right_ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (ofResolution r).right = r.raw.cₙ := by
  simp [ofResolution]

@[simp] theorem left_ofMutualDependence {D : Type u}
    {E : Elaboration D} (m : MutualDependence D)
    (compatible : m.interdependence = Interdependence.ofElaboration E) :
    (ofMutualDependence m compatible).left = m.c₁ :=
  rfl

@[simp] theorem right_ofMutualDependence {D : Type u}
    {E : Elaboration D} (m : MutualDependence D)
    (compatible : m.interdependence = Interdependence.ofElaboration E) :
    (ofMutualDependence m compatible).right = m.cₙ :=
  rfl

@[simp] theorem left_catenate {D : Type u} {E : Elaboration D}
    (l r : Segment E) (h : Catenable E l r) :
    (catenate l r h).left = l.left :=
  rfl

@[simp] theorem right_catenate {D : Type u} {E : Elaboration D}
    (l r : Segment E) (h : Catenable E l r) :
    (catenate l r h).right = r.right :=
  rfl

@[simp] theorem catenable_resolution_component_iff {D : Type u}
    {E : Elaboration D} {d : D} (r : Elaboration.Resolution E d)
    (c : Component D) :
    Catenable E (ofResolution r) (ofComponent E c) ↔
      E.Interdependent r.raw.cₙ c := by
  simp [Catenable]

@[simp] theorem catenable_component_resolution_iff {D : Type u}
    {E : Elaboration D} (c : Component D) {d : D}
    (r : Elaboration.Resolution E d) :
    Catenable E (ofComponent E c) (ofResolution r) ↔
      E.Interdependent c r.raw.c₁ := by
  simp [Catenable]

/--
For singleton interfaces, a resolved `[a <--> b] <--> c` occurrence checks
only whether `b` and `c` are joinable; the stored `a <--> b` body remains
internal to its shell.
-/
theorem catenable_resolution_designatum_iff {D : Type u}
    {E : Elaboration D} {d b : D}
    (r : Elaboration.Resolution E d)
    (hright : r.raw.cₙ = Component.singleton b) (c : D) :
    Catenable E (ofResolution r) (ofDesignatum E c) ↔ E.Joinable b c := by
  rw [Catenable, right_ofResolution, left_ofDesignatum, hright]
  exact Elaboration.interdependent_singleton_iff

/--
The left mirror of `catenable_resolution_designatum_iff`: a designatum is
catenable with an opened body exactly when it passes the body's exposed left
endpoint check.
-/
theorem catenable_designatum_resolution_iff {D : Type u}
    {E : Elaboration D} {d a : D}
    (r : Elaboration.Resolution E d)
    (hleft : r.raw.c₁ = Component.singleton a) (c : D) :
    Catenable E (ofDesignatum E c) (ofResolution r) ↔ E.Joinable c a := by
  rw [Catenable, right_ofDesignatum, left_ofResolution, hleft]
  exact Elaboration.interdependent_singleton_iff

end Segment

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
