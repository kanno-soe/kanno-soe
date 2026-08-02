import KannoSoe.Signature.V2

/-!
# Endpoint-sensitive segments

`Component` remains the unit placed at each position of an ordinary mutual
dependence.  This module adds a presentation layer in which a designatum in a
component may be opened as one certified mutual dependence.  The opened body
is retained, and its first and last components become that slot's left and
right interfaces.  Slots in a multi-member component are combined in
parallel; adjacent segments continue to use the existing bilateral
`Elaboration.Linked` relation.

Opening is finite and local to an occurrence.  In particular, a leaf means
"not opened here", not "provably has no elaboration".  This keeps every
component immediately usable and does not demand a recursive normal form from
possibly cyclic elaboration systems.
-/

universe u

namespace Component

/--
Replace each member of a component by a nonempty component and take their
parallel union.  The subtype argument identifies the source slot while the
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

namespace Elaboration

/--
A chosen elaboration body together with the proof that it certifies under the
linkage derived from the same elaboration system.

The raw target is retained because `Elab` may inspect its original linkage;
`certify` is the sanctioned operation which retags that target with
`Linkage.ofElaboration E`.
-/
structure Resolution {D : Type u} (E : Elaboration D) (d : D) where
  raw : RawMutualDependence D
  isElaboration : E.Elab d raw
  holds : (E.certify raw).Holds

namespace Resolution

/-- The certified mutual dependence selected by a resolution. -/
def toMutualDependence {D : Type u} {E : Elaboration D} {d : D}
    (r : Resolution E d) : MutualDependence D :=
  ⟨E.certify r.raw, r.holds⟩

@[simp] theorem toMutualDependence_toRaw {D : Type u}
    {E : Elaboration D} {d : D} (r : Resolution E d) :
    r.toMutualDependence.toRaw = E.certify r.raw :=
  rfl

@[simp] theorem toMutualDependence_linkage {D : Type u}
    {E : Elaboration D} {d : D} (r : Resolution E d) :
    r.toMutualDependence.linkage = Linkage.ofElaboration E :=
  rfl

@[simp] theorem toMutualDependence_c₁ {D : Type u}
    {E : Elaboration D} {d : D} (r : Resolution E d) :
    r.toMutualDependence.c₁ = r.raw.c₁ :=
  rfl

@[simp] theorem toMutualDependence_cₙ {D : Type u}
    {E : Elaboration D} {d : D} (r : Resolution E d) :
    r.toMutualDependence.cₙ = r.raw.cₙ :=
  rfl

end Resolution

end Elaboration

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
    (Slot.resolved r).left = r.toMutualDependence.c₁ :=
  rfl

@[simp] theorem right_resolved {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (Slot.resolved r).right = r.toMutualDependence.cₙ :=
  rfl

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
  | resolution {d : D} (source : Component D)
      (isSingleton : source = Component.singleton d)
      (value : Elaboration.Resolution E d)

namespace Shell

/-- The source component retained by a shell. -/
def source {D : Type u} {E : Elaboration D} : Shell E → Component D
  | .component c => c
  | .slots c _ => c
  | .resolution source _ _ => source

/-- The parallel union of all left slot-interfaces. -/
def left {D : Type u} {E : Elaboration D} : Shell E → Component D
  | .component c => c
  | .slots c slot => c.bind fun d => (slot d).left
  | .resolution _ _ r => r.toMutualDependence.c₁

/-- The parallel union of all right slot-interfaces. -/
def right {D : Type u} {E : Elaboration D} : Shell E → Component D
  | .component c => c
  | .slots c slot => c.bind fun d => (slot d).right
  | .resolution _ _ r => r.toMutualDependence.cₙ

/-- A component used without opening any of its occurrences. -/
def ofComponent {D : Type u} (E : Elaboration D)
    (source : Component D) : Shell E :=
  .component source

/-- A singleton component used without opening its designatum. -/
def ofDesignatum {D : Type u} (E : Elaboration D) (d : D) : Shell E :=
  ofComponent E (Component.singleton d)

/--
Place a designatum in its singleton source component and open that occurrence
as the selected certified body.
-/
def ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) : Shell E :=
  .resolution (Component.singleton d) rfl r

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
    (ofResolution r).left = r.toMutualDependence.c₁ :=
  rfl

@[simp] theorem right_ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (ofResolution r).right = r.toMutualDependence.cₙ :=
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

end Shell

/-! ## Serial segment presentations -/

/--
The retained shape of a segment.  `append` records serial composition without
discarding either side; a direct mutual dependence may also occupy a segment
position when its linkage is the one induced by `E`.
-/
inductive Shape {D : Type u} (E : Elaboration D) where
  | shell (value : Shell E)
  | dependence (value : MutualDependence D)
      (compatible : value.linkage = Linkage.ofElaboration E)
  | append (left right : Shape E)

namespace Shape

/-- The left interface of a retained segment shape. -/
def left {D : Type u} {E : Elaboration D} : Shape E → Component D
  | .shell s => s.left
  | .dependence m _ => m.c₁
  | .append l _ => l.left

/-- The right interface of a retained segment shape. -/
def right {D : Type u} {E : Elaboration D} : Shape E → Component D
  | .shell s => s.right
  | .dependence m _ => m.cₙ
  | .append _ r => r.right

/--
Internal validity of a shape.  Shells contain only leaves or certified
resolutions, and compatible mutual dependences are already certified.  An
append adds exactly the strong join between the exposed adjacent interfaces.
-/
def Holds {D : Type u} {E : Elaboration D} : Shape E → Prop
  | .shell _ => True
  | .dependence _ _ => True
  | .append l r => l.Holds ∧ r.Holds ∧ E.Linked l.right r.left

end Shape

end Segment

/-- A retained endpoint-sensitive shape together with all of its joins. -/
structure Segment {D : Type u} (E : Elaboration D) where
  shape : Segment.Shape E
  holds : shape.Holds

namespace Segment

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
    (compatible : m.linkage = Linkage.ofElaboration E) : Segment E :=
  ⟨.dependence m compatible, trivial⟩

/-- The endpoint-sensitive join required between two oriented segments. -/
def Joined {D : Type u} (E : Elaboration D)
    (left right : Segment E) : Prop :=
  E.Linked left.right right.left

/--
Compose two segments while retaining both shapes.  Only the left segment's
right interface and the right segment's left interface are checked.
-/
def append {D : Type u} {E : Elaboration D} (left right : Segment E)
    (joined : Joined E left right) : Segment E :=
  ⟨.append left.shape right.shape, ⟨left.holds, right.holds, joined⟩⟩

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
    (ofResolution r).left = r.toMutualDependence.c₁ := by
  simp [ofResolution]

@[simp] theorem right_ofResolution {D : Type u} {E : Elaboration D} {d : D}
    (r : Elaboration.Resolution E d) :
    (ofResolution r).right = r.toMutualDependence.cₙ := by
  simp [ofResolution]

@[simp] theorem left_ofMutualDependence {D : Type u}
    {E : Elaboration D} (m : MutualDependence D)
    (compatible : m.linkage = Linkage.ofElaboration E) :
    (ofMutualDependence m compatible).left = m.c₁ :=
  rfl

@[simp] theorem right_ofMutualDependence {D : Type u}
    {E : Elaboration D} (m : MutualDependence D)
    (compatible : m.linkage = Linkage.ofElaboration E) :
    (ofMutualDependence m compatible).right = m.cₙ :=
  rfl

@[simp] theorem left_append {D : Type u} {E : Elaboration D}
    (l r : Segment E) (h : Joined E l r) :
    (append l r h).left = l.left :=
  rfl

@[simp] theorem right_append {D : Type u} {E : Elaboration D}
    (l r : Segment E) (h : Joined E l r) :
    (append l r h).right = r.right :=
  rfl

@[simp] theorem joined_resolution_component_iff {D : Type u}
    {E : Elaboration D} {d : D} (r : Elaboration.Resolution E d)
    (c : Component D) :
    Joined E (ofResolution r) (ofComponent E c) ↔
      E.Linked r.toMutualDependence.cₙ c := by
  simp [Joined]

@[simp] theorem joined_component_resolution_iff {D : Type u}
    {E : Elaboration D} (c : Component D) {d : D}
    (r : Elaboration.Resolution E d) :
    Joined E (ofComponent E c) (ofResolution r) ↔
      E.Linked c r.toMutualDependence.c₁ := by
  simp [Joined]

/--
For singleton interfaces, a resolved `[a <--> b] <--> c` occurrence checks
only `b Related c`; the stored `a <--> b` body remains internal to its shell.
-/
theorem joined_resolution_designatum_iff {D : Type u}
    {E : Elaboration D} {name b : D}
    (r : Elaboration.Resolution E name)
    (hright : r.toMutualDependence.cₙ = Component.singleton b) (c : D) :
    Joined E (ofResolution r) (ofDesignatum E c) ↔ E.Related b c := by
  rw [Joined, right_ofResolution, left_ofDesignatum, hright]
  exact Elaboration.linked_singleton_iff

end Segment
