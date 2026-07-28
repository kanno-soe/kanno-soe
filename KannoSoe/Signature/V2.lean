import Std

/-!
# Mutual dependence, resonance, and direction

Raw types describe component structures without asserting that their
linkages hold. Certified types pair those descriptions with proofs, while
`Elaboration` targets raw mutual dependences so it can remain agnostic about
the validity of its targets.

A linkage derived from an elaboration (`Linkage.ofElaboration E`) cannot
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
  ⟨fun A d => A.carrier d⟩

instance {D : Type u} : CoeFun (Component D) (fun _ => D → Prop) :=
  ⟨Component.carrier⟩

namespace Component

def singleton {D : Type u} (d : D) : Component D where
  carrier := fun x => x = d
  nonempty := ⟨d, rfl⟩

@[simp] theorem mem_singleton_iff {D : Type u} {d x : D} :
    x ∈ singleton d ↔ x = d :=
  Iff.rfl

theorem exists_mem {D : Type u} (A : Component D) : ∃ d, d ∈ A :=
  A.nonempty

end Component

/-! ## Linkage -/

structure Linkage (D : Type u) where
  Linked : Component D → Component D → Prop
  symm : ∀ {A B}, Linked A B → Linked B A

namespace Linkage

inductive ChainLinked {D : Type u} (L : Linkage D) :
    List (Component D) → Prop where
  | nil : ChainLinked L []
  | single (A : Component D) : ChainLinked L [A]
  | cons {A B : Component D} {rest : List (Component D)}
      (hAB : L.Linked A B) (h : ChainLinked L (B :: rest)) :
      ChainLinked L (A :: B :: rest)

theorem ChainLinked.tail {D : Type u} {L : Linkage D}
    {A : Component D} {l : List (Component D)}
    (h : L.ChainLinked (A :: l)) : L.ChainLinked l := by
  cases h with
  | single _ => exact ChainLinked.nil
  | cons _ h => exact h

theorem ChainLinked.of_append_right {D : Type u} {L : Linkage D} :
    ∀ (l₁ : List (Component D)) {l₂ : List (Component D)},
      L.ChainLinked (l₁ ++ l₂) → L.ChainLinked l₂
  | [], _, h => h
  | A :: rest, l₂, h => by
      rw [List.cons_append] at h
      exact ChainLinked.of_append_right rest h.tail

theorem ChainLinked.of_append_left {D : Type u} {L : Linkage D} :
    ∀ (l₁ l₂ : List (Component D)),
      L.ChainLinked (l₁ ++ l₂) → L.ChainLinked l₁
  | [], _, _ => ChainLinked.nil
  | [A], _, _ => ChainLinked.single A
  | A :: B :: rest, l₂, h => by
      rw [List.cons_append, List.cons_append] at h
      cases h with
      | cons hAB h =>
          refine ChainLinked.cons hAB
            (ChainLinked.of_append_left (B :: rest) l₂ ?_)
          rw [List.cons_append]
          exact h

theorem ChainLinked.glue {D : Type u} {L : Linkage D} :
    ∀ {l₁ : List (Component D)} {X : Component D}
        {l₂ : List (Component D)},
      L.ChainLinked (l₁ ++ [X]) → L.ChainLinked (X :: l₂) →
      L.ChainLinked (l₁ ++ X :: l₂) := by
  intro l₁ X l₂ hleft hright
  induction l₁ with
  | nil => exact hright
  | cons A rest ih =>
      cases rest with
      | nil =>
          change L.ChainLinked [A, X] at hleft
          cases hleft with
          | cons hAX _ => exact .cons hAX hright
      | cons B rest =>
          change L.ChainLinked (A :: B :: rest ++ [X]) at hleft
          cases hleft with
          | cons hAB htail =>
              exact .cons hAB (ih htail)

end Linkage

/-! ## Raw mutual dependence: data only -/

/--
Components plus their linkage, as pure data (1:1: each value carries
exactly one linkage). At least two components by construction. This type
makes no assertion; `RawMutualDependence.Holds` states it, and
`MutualDependence` below bundles the proof.
-/
structure RawMutualDependence (D : Type u) where
  linkage : Linkage D
  first : Component D
  middle : List (Component D)
  last : Component D

namespace RawMutualDependence

def components {D : Type u} (m : RawMutualDependence D) :
    List (Component D) :=
  m.first :: m.middle ++ [m.last]

/-- The assertion: every two adjacent components are accepted by the
bundled linkage. -/
def Holds {D : Type u} (m : RawMutualDependence D) : Prop :=
  m.linkage.ChainLinked m.components

def pair {D : Type u} (L : Linkage D) (A B : Component D) :
    RawMutualDependence D :=
  ⟨L, A, [], B⟩

def triple {D : Type u} (L : Linkage D) (A B C : Component D) :
    RawMutualDependence D :=
  ⟨L, A, [B], C⟩

def quad {D : Type u} (L : Linkage D) (A B C R : Component D) :
    RawMutualDependence D :=
  ⟨L, A, [B, C], R⟩

@[simp] theorem linkage_pair {D : Type u} (L : Linkage D)
    (A B : Component D) : (pair L A B).linkage = L :=
  rfl

@[simp] theorem components_pair {D : Type u} (L : Linkage D)
    (A B : Component D) : (pair L A B).components = [A, B] :=
  rfl

@[simp] theorem components_triple {D : Type u} (L : Linkage D)
    (A B C : Component D) : (triple L A B C).components = [A, B, C] :=
  rfl

@[simp] theorem components_quad {D : Type u} (L : Linkage D)
    (A B C R : Component D) :
    (quad L A B C R).components = [A, B, C, R] :=
  rfl

@[simp] theorem holds_pair_iff {D : Type u} {L : Linkage D}
    {A B : Component D} :
    (pair L A B).Holds ↔ L.Linked A B := by
  constructor
  · intro h
    have h : L.ChainLinked [A, B] := h
    cases h with
    | cons hAB _ => exact hAB
  · intro h
    show L.ChainLinked [A, B]
    exact .cons h (.single B)

@[simp] theorem holds_triple_iff {D : Type u} {L : Linkage D}
    {A B C : Component D} :
    (triple L A B C).Holds ↔ L.Linked A B ∧ L.Linked B C := by
  constructor
  · intro h
    have h : L.ChainLinked [A, B, C] := h
    cases h with
    | cons hAB h =>
        cases h with
        | cons hBC _ => exact ⟨hAB, hBC⟩
  · intro h
    show L.ChainLinked [A, B, C]
    exact .cons h.1 (.cons h.2 (.single C))

@[simp] theorem holds_quad_iff {D : Type u} {L : Linkage D}
    {A B C R : Component D} :
    (quad L A B C R).Holds ↔
      L.Linked A B ∧ L.Linked B C ∧ L.Linked C R := by
  constructor
  · intro h
    have h : L.ChainLinked [A, B, C, R] := h
    cases h with
    | cons hAB h =>
        cases h with
        | cons hBC h =>
            cases h with
            | cons hCR _ => exact ⟨hAB, hBC, hCR⟩
  · intro h
    show L.ChainLinked [A, B, C, R]
    exact .cons h.1 (.cons h.2.1 (.cons h.2.2 (.single R)))

theorem holds_of_contiguous {D : Type u}
    {whole sub : RawMutualDependence D} {pre suf : List (Component D)}
    (hL : sub.linkage = whole.linkage)
    (hdecomp : whole.components = pre ++ sub.components ++ suf)
    (hw : whole.Holds) : sub.Holds := by
  have h : whole.linkage.ChainLinked (pre ++ sub.components ++ suf) := by
    rw [← hdecomp]
    exact hw
  show sub.linkage.ChainLinked sub.components
  rw [hL]
  exact Linkage.ChainLinked.of_append_right pre
    (Linkage.ChainLinked.of_append_left _ suf h)

def IsResonance {D : Type u} (m : RawMutualDependence D) : Prop :=
  ∃ b₁ b₂ : D,
    m.middle = [Component.singleton b₁, Component.singleton b₂]

theorem isResonance_quad {D : Type u} (L : Linkage D) (C : Component D)
    (b₁ b₂ : D) (R : Component D) :
    (quad L C (Component.singleton b₁)
      (Component.singleton b₂) R).IsResonance :=
  ⟨b₁, b₂, rfl⟩

end RawMutualDependence

/-! ## Mutual dependence: data plus proof -/

/--
The certified type downstream code should use: a raw mutual dependence
together with the proof that it holds under its own linkage.

If most of your linkage proofs are dischargeable by a tactic, give the
`holds` field a default (`holds : toRaw.Holds := by your_tactic`) so
construction feels field-free at most sites.
-/
structure MutualDependence (D : Type u) where
  toRaw : RawMutualDependence D
  holds : toRaw.Holds

namespace MutualDependence

def linkage {D : Type u} (m : MutualDependence D) : Linkage D :=
  m.toRaw.linkage

def first {D : Type u} (m : MutualDependence D) : Component D :=
  m.toRaw.first

def middle {D : Type u} (m : MutualDependence D) : List (Component D) :=
  m.toRaw.middle

def last {D : Type u} (m : MutualDependence D) : Component D :=
  m.toRaw.last

def components {D : Type u} (m : MutualDependence D) :
    List (Component D) :=
  m.toRaw.components

/-- Proof irrelevance: equality of certified dependences reduces to
equality of the underlying data. -/
theorem ext {D : Type u} {m₁ m₂ : MutualDependence D}
    (h : m₁.toRaw = m₂.toRaw) : m₁ = m₂ := by
  cases m₁
  cases m₂
  cases h
  rfl

def pair {D : Type u} (L : Linkage D) (A B : Component D)
    (h : L.Linked A B) : MutualDependence D :=
  ⟨RawMutualDependence.pair L A B,
    RawMutualDependence.holds_pair_iff.mpr h⟩

def triple {D : Type u} (L : Linkage D) (A B C : Component D)
    (hAB : L.Linked A B) (hBC : L.Linked B C) : MutualDependence D :=
  ⟨RawMutualDependence.triple L A B C,
    RawMutualDependence.holds_triple_iff.mpr ⟨hAB, hBC⟩⟩

def quad {D : Type u} (L : Linkage D) (A B C R : Component D)
    (hAB : L.Linked A B) (hBC : L.Linked B C) (hCR : L.Linked C R) :
    MutualDependence D :=
  ⟨RawMutualDependence.quad L A B C R,
    RawMutualDependence.holds_quad_iff.mpr ⟨hAB, hBC, hCR⟩⟩

/-- `holds_of_contiguous` as a slicing function: the sub-tuple copies the
whole's linkage, so it comes back certified with no side conditions. -/
def slice {D : Type u} (whole : MutualDependence D)
    (first : Component D) (middle : List (Component D))
    (last : Component D) (pre suf : List (Component D))
    (hdecomp : whole.toRaw.components =
      pre ++ (first :: middle ++ [last]) ++ suf) : MutualDependence D :=
  ⟨⟨whole.toRaw.linkage, first, middle, last⟩,
    RawMutualDependence.holds_of_contiguous
      (whole := whole.toRaw)
      (sub := ⟨whole.toRaw.linkage, first, middle, last⟩)
      (pre := pre) (suf := suf) rfl hdecomp whole.holds⟩

def mergeSharedEndpoint {D : Type u} (A B : MutualDependence D)
    (hL : A.linkage = B.linkage) (hX : A.last = B.first) :
    MutualDependence D := by
  refine ⟨⟨A.linkage, A.first, A.middle ++ A.last :: B.middle, B.last⟩, ?_⟩
  have hB :
      A.linkage.ChainLinked (A.last :: B.middle ++ [B.last]) := by
    rw [hL, hX]
    exact B.holds
  have h := Linkage.ChainLinked.glue
    (l₁ := A.first :: A.middle) (X := A.last)
    (l₂ := B.middle ++ [B.last]) A.holds hB
  simpa [MutualDependence.linkage, MutualDependence.first,
    MutualDependence.middle, MutualDependence.last,
    RawMutualDependence.Holds, RawMutualDependence.components,
    List.append_assoc] using h

def mergeLinkedEndpoints {D : Type u} (A B : MutualDependence D)
    (hL : A.linkage = B.linkage)
    (hJoin : A.linkage.Linked A.last B.first) : MutualDependence D := by
  refine
    ⟨⟨A.linkage, A.first,
      A.middle ++ [A.last, B.first] ++ B.middle, B.last⟩, ?_⟩
  have hAB :
      A.linkage.ChainLinked
        (((A.first :: A.middle) ++ [A.last]) ++ [B.first]) := by
    simpa [MutualDependence.linkage, MutualDependence.first,
      MutualDependence.middle, MutualDependence.last,
      List.append_assoc] using
      (Linkage.ChainLinked.glue
        (l₁ := A.first :: A.middle) (X := A.last) (l₂ := [B.first])
        A.holds (.cons hJoin (.single B.first)))
  have hB :
      A.linkage.ChainLinked (B.first :: B.middle ++ [B.last]) := by
    rw [hL]
    exact B.holds
  have h := Linkage.ChainLinked.glue
    (l₁ := (A.first :: A.middle) ++ [A.last]) (X := B.first)
    (l₂ := B.middle ++ [B.last]) hAB hB
  simpa [MutualDependence.linkage, MutualDependence.first,
    MutualDependence.middle, MutualDependence.last,
    RawMutualDependence.Holds, RawMutualDependence.components,
    List.append_assoc] using h

def IsResonance {D : Type u} (m : MutualDependence D) : Prop :=
  m.toRaw.IsResonance

end MutualDependence

/-! ## Elaboration and relatedness -/

/--
An elaboration system. `Elab d m` asserts that designatum `d` *may be
elaborated as* the raw mutual dependence `m`.

`Elaboration` must target `RawMutualDependence`: it constrains the
components of its targets and stays agnostic about both the bundled
linkage and whether the tuple holds. Requiring targets to carry
`Linkage.ofElaboration` of this same elaboration — let alone proofs under
it — inside the elaboration's own definition is value-level
self-reference; see `certify` and `SelfCertified`.
-/
structure Elaboration (D : Type u) where
  Elab : D → RawMutualDependence D → Prop

namespace Elaboration

inductive Reaches {D : Type u} (E : Elaboration D) : D → D → Prop where
  | refl (d : D) : Reaches E d d
  | step {d e f : D} {m : RawMutualDependence D} {A : Component D}
      (hE : E.Elab d m) (hA : A ∈ m.components) (he : e ∈ A)
      (h : Reaches E e f) : Reaches E d f

theorem Reaches.trans {D : Type u} {E : Elaboration D} {d e f : D}
    (h₁ : E.Reaches d e) : E.Reaches e f → E.Reaches d f := by
  induction h₁ with
  | refl _ => exact id
  | step hE hA he _ ih => exact fun h₂ => Reaches.step hE hA he (ih h₂)

theorem Reaches.single {D : Type u} {E : Elaboration D} {d e : D}
    {m : RawMutualDependence D} {A : Component D}
    (hE : E.Elab d m) (hA : A ∈ m.components) (he : e ∈ A) :
    E.Reaches d e :=
  Reaches.step hE hA he (Reaches.refl e)

def Related {D : Type u} (E : Elaboration D) (a b : D) : Prop :=
  ∃ w, E.Reaches a w ∧ E.Reaches b w

theorem Related.refl {D : Type u} (E : Elaboration D) (a : D) :
    E.Related a a :=
  ⟨a, Reaches.refl a, Reaches.refl a⟩

theorem Related.symm {D : Type u} {E : Elaboration D} {a b : D}
    (h : E.Related a b) : E.Related b a := by
  obtain ⟨w, ha, hb⟩ := h
  exact ⟨w, hb, ha⟩

private inductive RelatedNotTransitiveCase where
  | a
  | b
  | c
  deriving DecidableEq

theorem Related.not_transitive :
    ∃ (D : Type) (E : Elaboration D),
      ¬ ∀ ⦃a b c⦄, E.Related a b → E.Related b c → E.Related a c := by
  let L : Linkage RelatedNotTransitiveCase := {
    Linked := fun _ _ => True
    symm := fun _ => trivial }
  let m : RawMutualDependence RelatedNotTransitiveCase :=
    .pair L (Component.singleton .a) (Component.singleton .c)
  let E : Elaboration RelatedNotTransitiveCase :=
    ⟨fun d m' => d = .b ∧ m' = m⟩
  refine ⟨RelatedNotTransitiveCase, E, ?_⟩
  intro htrans
  have hba : E.Reaches .b .a :=
    Reaches.single (m := m) (A := Component.singleton .a)
      ⟨rfl, rfl⟩ (by simp [m]) rfl
  have hbc : E.Reaches .b .c :=
    Reaches.single (m := m) (A := Component.singleton .c)
      ⟨rfl, rfl⟩ (by simp [m]) rfl
  have hab : E.Related .a .b :=
    ⟨RelatedNotTransitiveCase.a,
      Reaches.refl RelatedNotTransitiveCase.a, hba⟩
  have hbc' : E.Related .b .c :=
    ⟨RelatedNotTransitiveCase.c, hbc,
      Reaches.refl RelatedNotTransitiveCase.c⟩
  obtain ⟨w, haw, hcw⟩ := htrans hab hbc'
  have hwa : w = .a := by
    cases haw with
    | refl _ => rfl
    | step hE _ _ _ => simp [E] at hE
  have hwc : w = .c := by
    cases hcw with
    | refl _ => rfl
    | step hE _ _ _ => simp [E] at hE
  exact (by decide : RelatedNotTransitiveCase.a ≠ .c) (hwa.symm.trans hwc)

def Linked {D : Type u} (E : Elaboration D) (A B : Component D) : Prop :=
  (∀ a ∈ A, ∃ b ∈ B, E.Related a b) ∧
    (∀ b ∈ B, ∃ a ∈ A, E.Related a b)

theorem Linked.symm {D : Type u} {E : Elaboration D}
    {A B : Component D} (h : E.Linked A B) : E.Linked B A := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨fun b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨a, ha, hr⟩ := h₂ b hb
    exact ⟨a, ha, hr.symm⟩
  · obtain ⟨b, hb, hr⟩ := h₁ a ha
    exact ⟨b, hb, hr.symm⟩

@[simp] theorem linked_singleton_iff {D : Type u} {E : Elaboration D}
    {a b : D} :
    E.Linked (Component.singleton a) (Component.singleton b) ↔
      E.Related a b := by
  constructor
  · intro h
    obtain ⟨b', hb', hr⟩ := h.1 a rfl
    have hb : b' = b := hb'
    subst hb
    exact hr
  · intro h
    refine ⟨fun a' ha' => ?_, fun b' hb' => ?_⟩
    · have ha : a' = a := ha'
      subst ha
      exact ⟨b, rfl, h⟩
    · have hb : b' = b := hb'
      subst hb
      exact ⟨a, rfl, h⟩

end Elaboration

namespace Linkage

def ofElaboration {D : Type u} (E : Elaboration D) : Linkage D where
  Linked := E.Linked
  symm := Elaboration.Linked.symm

instance {D : Type u} : Coe (Elaboration D) (Linkage D) :=
  ⟨ofElaboration⟩

end Linkage

namespace Elaboration

/-- Re-tag a raw dependence with the linkage derived from `E` — the
sanctioned route around the self-reference restriction. Certifying (i.e.
producing a `MutualDependence`) additionally requires proving `Holds`
under the derived linkage, which is genuine work per system. -/
def certify {D : Type u} (E : Elaboration D)
    (m : RawMutualDependence D) : RawMutualDependence D :=
  { m with linkage := Linkage.ofElaboration E }

@[simp] theorem linkage_certify {D : Type u} (E : Elaboration D)
    (m : RawMutualDependence D) :
    (E.certify m).linkage = Linkage.ofElaboration E :=
  rfl

@[simp] theorem components_certify {D : Type u} (E : Elaboration D)
    (m : RawMutualDependence D) :
    (E.certify m).components = m.components :=
  rfl

/-- Well-formedness of a completed system: every emitted raw dependence
carries the linkage derived from the elaboration itself. Provable about a
finished `E`; not expressible inside `E`'s own definition. -/
def SelfCertified {D : Type u} (E : Elaboration D) : Prop :=
  ∀ d m, E.Elab d m → m.linkage = Linkage.ofElaboration E

end Elaboration

/-! ## Resonance, raw and certified -/

/--
Resonance data whose two middle components are forced to be singletons.

b₁ is the being receiving calls; b₂ is the "same" being responding. The being's
receiving-stage and responding-stage share linkage despite the change.
-/
structure RawResonance (D : Type u) where
  linkage : Linkage D
  calls : Component D
  b₁ : D
  b₂ : D
  responses : Component D

namespace RawResonance

def middle {D : Type u} (r : RawResonance D) : List (Component D) :=
  [Component.singleton r.b₁, Component.singleton r.b₂]

def toRawMutualDependence {D : Type u} (r : RawResonance D) :
    RawMutualDependence D :=
  RawMutualDependence.quad r.linkage r.calls (Component.singleton r.b₁)
    (Component.singleton r.b₂) r.responses

def components {D : Type u} (r : RawResonance D) : List (Component D) :=
  r.toRawMutualDependence.components

@[simp] theorem linkage_toRawMutualDependence {D : Type u}
    (r : RawResonance D) :
    r.toRawMutualDependence.linkage = r.linkage :=
  rfl

@[simp] theorem middle_toRawMutualDependence {D : Type u}
    (r : RawResonance D) :
    r.toRawMutualDependence.middle = r.middle :=
  rfl

@[simp] theorem components_eq {D : Type u} (r : RawResonance D) :
    r.components =
      [r.calls, Component.singleton r.b₁, Component.singleton r.b₂, r.responses] :=
  rfl

theorem isResonance {D : Type u} (r : RawResonance D) :
    r.toRawMutualDependence.IsResonance :=
  ⟨r.b₁, r.b₂, rfl⟩

def Holds {D : Type u} (r : RawResonance D) : Prop :=
  r.toRawMutualDependence.Holds

@[simp] theorem holds_iff {D : Type u} {r : RawResonance D} :
    r.Holds ↔
      r.linkage.Linked r.calls (Component.singleton r.b₁) ∧
        r.linkage.Linked (Component.singleton r.b₁)
          (Component.singleton r.b₂) ∧
          r.linkage.Linked (Component.singleton r.b₂) r.responses := by
  change
    (RawMutualDependence.quad r.linkage r.calls (Component.singleton r.b₁)
      (Component.singleton r.b₂) r.responses).Holds ↔ _
  exact RawMutualDependence.holds_quad_iff

end RawResonance

/-- Completeness at the raw level: every raw mutual dependence satisfying
`IsResonance` is represented by some `RawResonance`. -/
theorem RawMutualDependence.IsResonance.exists_rawResonance
    {D : Type u} {m : RawMutualDependence D} (h : m.IsResonance) :
    ∃ r : RawResonance D, r.toRawMutualDependence = m := by
  cases m with
  | mk linkage first middle last =>
      obtain ⟨b₁, b₂, hmiddle⟩ := h
      change middle = [Component.singleton b₁, Component.singleton b₂]
        at hmiddle
      subst middle
      exact ⟨⟨linkage, first, b₁, b₂, last⟩, rfl⟩

/-- The certified counterpart to `RawResonance`, following the same
raw/certified boundary as mutual dependence. -/
structure Resonance (D : Type u) where
  toRawResonance : RawResonance D
  holds : toRawResonance.Holds

namespace Resonance

def linkage {D : Type u} (r : Resonance D) : Linkage D :=
  r.toRawResonance.linkage

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

def mk' {D : Type u} (L : Linkage D) (calls : Component D) (b₁ b₂ : D)
    (responses : Component D)
    (h₁ : L.Linked calls (Component.singleton b₁))
    (h₂ : L.Linked (Component.singleton b₁) (Component.singleton b₂))
    (h₃ : L.Linked (Component.singleton b₂) responses) : Resonance D :=
  ⟨⟨L, calls, b₁, b₂, responses⟩,
    RawResonance.holds_iff.mpr ⟨h₁, h₂, h₃⟩⟩

end Resonance

/-- Completeness at the certified level: every certified mutual dependence
satisfying `IsResonance` comes from a certified `Resonance`; the proof is
transported along the raw representation. -/
theorem MutualDependence.IsResonance.exists_resonance
    {D : Type u} {m : MutualDependence D} (h : m.IsResonance) :
    ∃ r : Resonance D, r.toMutualDependence = m := by
  obtain ⟨rr, hrr⟩ :=
    RawMutualDependence.IsResonance.exists_rawResonance h
  exact ⟨⟨rr, (show rr.toRawMutualDependence.Holds from
    hrr.symm ▸ m.holds)⟩, MutualDependence.ext hrr⟩

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

private def rawOfComponents {D : Type u} (L : Linkage D)
    (first second : Component D) :
    List (Component D) → RawMutualDependence D
  | [] => RawMutualDependence.pair L first second
  | third :: rest =>
      let tail := rawOfComponents L second third rest
      ⟨L, first, second :: tail.middle, tail.last⟩

private theorem linkage_rawOfComponents {D : Type u} (L : Linkage D)
    (first second : Component D) (rest : List (Component D)) :
    (rawOfComponents L first second rest).linkage = L := by
  cases rest <;> rfl

private theorem first_rawOfComponents {D : Type u} (L : Linkage D)
    (first second : Component D) (rest : List (Component D)) :
    (rawOfComponents L first second rest).first = first := by
  cases rest <;> rfl

private theorem components_rawOfComponents {D : Type u} (L : Linkage D)
    (first second : Component D) (rest : List (Component D)) :
    (rawOfComponents L first second rest).components =
      first :: second :: rest := by
  induction rest generalizing first second with
  | nil => rfl
  | cons third rest ih =>
      change
        first ::
            (second :: (rawOfComponents L second third rest).middle) ++
              [(rawOfComponents L second third rest).last] =
          first :: second :: third :: rest
      have tailComponents :
          (second :: (rawOfComponents L second third rest).middle) ++
              [(rawOfComponents L second third rest).last] =
            second :: third :: rest := by
        calc
          _ =
              (rawOfComponents L second third rest).first ::
                  (rawOfComponents L second third rest).middle ++
                    [(rawOfComponents L second third rest).last] := by
                exact congrArg
                  (fun component =>
                    (component ::
                      (rawOfComponents L second third rest).middle) ++
                        [(rawOfComponents L second third rest).last])
                  (first_rawOfComponents L second third rest).symm
          _ = (rawOfComponents L second third rest).components := rfl
          _ = second :: third :: rest := ih second third
      exact congrArg (List.cons first) tailComponents

private def mutualDependenceOfComponents {D : Type u} (L : Linkage D)
    (first second : Component D) (rest : List (Component D))
    (holds : L.ChainLinked (first :: second :: rest)) :
    MutualDependence D := by
  refine ⟨rawOfComponents L first second rest, ?_⟩
  change
    (rawOfComponents L first second rest).linkage.ChainLinked
      (rawOfComponents L first second rest).components
  rw [linkage_rawOfComponents, components_rawOfComponents]
  exact holds

/--
Certify a nonempty list of resonances as a being. Each resonance contributes
its two singleton middle components, and `holds` certifies the resulting
chain, including every join between consecutive resonances.
-/
def ofResonances {D : Type u}
    (L : Linkage D)
    (resonances : List (Resonance D))
    (nonempty : resonances ≠ [])
    (holds :
      L.ChainLinked
        (resonances.flatMap Resonance.middleComponents)) :
    Being D := by
  cases resonances with
  | nil => exact (nonempty rfl).elim
  | cons r rest =>
      have chain :
          L.ChainLinked
            (Component.singleton r.b₁ :: Component.singleton r.b₂ ::
              rest.flatMap Resonance.middleComponents) := by
        simpa [Resonance.middleComponents] using holds
      refine
        ⟨r :: rest, by simp,
          mutualDependenceOfComponents L
            (Component.singleton r.b₁) (Component.singleton r.b₂)
            (rest.flatMap Resonance.middleComponents) chain, ?_⟩
      simpa [mutualDependenceOfComponents, MutualDependence.components,
        Resonance.middleComponents] using
        (components_rawOfComponents L
          (Component.singleton r.b₁) (Component.singleton r.b₂)
          (rest.flatMap Resonance.middleComponents))

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
    (r₁ r₂ : GradedResonance D PB) : Prop :=
  PB.le r₁.callsGrade r₂.callsGrade ∧
    PB.le r₁.responsesGrade r₂.responsesGrade

end GradedResonance

/-! ## Direction and causality -/

/--
Directed is not derived from the MutualDependence or Resonance,
instead it's a fact among those - it just turns out that when thermodynamic gradient
is possible, some designata sit at lower entropy than others; Directed specifies which.
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

structure Causal (D : Type u) extends Directed D where
  Causes : D → D → Prop
  causes_before : ∀ {x y : D}, Causes x y → Before x y
