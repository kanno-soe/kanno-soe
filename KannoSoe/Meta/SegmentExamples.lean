import KannoSoe.Signature.V2

/-!
# Endpoint-sensitive segment examples

These examples exercise the two distinctions introduced by `Segment`:
members of one source component open in parallel, while serial composition
checks only the exposed boundary of each retained segment.
-/

namespace SegmentExamples

/-! ## Parallel opening inside one component -/

inductive ParallelDesignatum where
  | a
  | b
  | c
  | ab
  | x
  deriving DecidableEq

/-- A small elaboration used only to make every example linkage immediate. -/
def parallelElaboration : Elaboration ParallelDesignatum where
  Elab := fun _ _ => True

theorem parallel_related_total (p q : ParallelDesignatum) :
    parallelElaboration.Related p q := by
  let raw : RawMutualDependence ParallelDesignatum :=
    .pair parallelElaboration (Component.singleton q)
      (Component.singleton q)
  have hpq : parallelElaboration.Reaches p q :=
    Elaboration.Reaches.single (rawM := raw)
      (a := Component.singleton q) trivial (by simp [raw]) (by simp)
  exact hpq.related

def rawAB : RawMutualDependence ParallelDesignatum :=
  .pair parallelElaboration
    (Component.singleton .a) (Component.singleton .b)

def resolutionAB :
    Elaboration.Resolution parallelElaboration ParallelDesignatum.ab where
  raw := rawAB
  isElaboration := trivial
  holds := by
    simp only [rawAB, Elaboration.certify_pair,
      RawMutualDependence.holds_pair_iff]
    exact Elaboration.linked_singleton_iff.mpr
      (parallel_related_total .a .b)

/--
The total slot presentation opens `ab` as `[a <--> b]` and leaves every other
designatum unopened.
-/
def parallelSlot :
    (d : ParallelDesignatum) → Segment.Slot parallelElaboration d
  | .ab => .resolved resolutionAB
  | _ => .leaf

/-- The source component selects the `ab` and `x` cases in parallel. -/
def parallelShell : Segment.Shell parallelElaboration :=
  Segment.Shell.ofSlots (Component.pair .ab .x) parallelSlot

@[simp] theorem parallelShell_source :
    parallelShell.source = Component.pair ParallelDesignatum.ab
      ParallelDesignatum.x :=
  rfl

/-- Opening the two source slots in parallel exposes `{a,x}` on the left. -/
theorem mem_parallelShell_left_iff (d : ParallelDesignatum) :
    d ∈ parallelShell.left ↔
      d = ParallelDesignatum.a ∨ d = ParallelDesignatum.x := by
  constructor
  · rintro ⟨⟨source, hsource⟩, hd⟩
    have hsource' : source = ParallelDesignatum.ab ∨
        source = ParallelDesignatum.x := by
      simpa using hsource
    rcases hsource' with rfl | rfl
    · left
      change d ∈ Component.singleton ParallelDesignatum.a at hd
      simpa using hd
    · right
      simpa [parallelShell, parallelSlot] using hd
  · rintro (rfl | rfl)
    · exact ⟨⟨ParallelDesignatum.ab, by simp⟩,
        by
          change ParallelDesignatum.a ∈
            Component.singleton ParallelDesignatum.a
          simp⟩
    · exact ⟨⟨ParallelDesignatum.x, by simp⟩,
        by simp [parallelSlot]⟩

/-- Opening the two source slots in parallel exposes `{b,x}` on the right. -/
theorem mem_parallelShell_right_iff (d : ParallelDesignatum) :
    d ∈ parallelShell.right ↔
      d = ParallelDesignatum.b ∨ d = ParallelDesignatum.x := by
  constructor
  · rintro ⟨⟨source, hsource⟩, hd⟩
    have hsource' : source = ParallelDesignatum.ab ∨
        source = ParallelDesignatum.x := by
      simpa using hsource
    rcases hsource' with rfl | rfl
    · left
      change d ∈ Component.singleton ParallelDesignatum.b at hd
      simpa using hd
    · right
      simpa [parallelShell, parallelSlot] using hd
  · rintro (rfl | rfl)
    · exact ⟨⟨ParallelDesignatum.ab, by simp⟩,
        by
          change ParallelDesignatum.b ∈
            Component.singleton ParallelDesignatum.b
          simp⟩
    · exact ⟨⟨ParallelDesignatum.x, by simp⟩,
        by simp [parallelSlot]⟩

/-- A selected resolution keeps one body and exposes that body's endpoints. -/
theorem resolvedAB_interfaces :
    (Segment.ofResolution resolutionAB).left =
        Component.singleton ParallelDesignatum.a ∧
      (Segment.ofResolution resolutionAB).right =
        Component.singleton ParallelDesignatum.b := by
  constructor
  · rw [Segment.left_ofResolution]
    rfl
  · rw [Segment.right_ofResolution]
    rfl

/-- Opening the slot retains its original singleton source component. -/
theorem resolvedAB_source :
    (Segment.Shell.ofResolution resolutionAB).source =
      Component.singleton ParallelDesignatum.ab :=
  rfl

/-- The right-hand join of `[a <--> b] <--> c` is the `b`/`c` join. -/
theorem resolvedAB_join_c :
    Segment.Joined parallelElaboration
      (Segment.ofResolution resolutionAB)
      (Segment.ofDesignatum parallelElaboration ParallelDesignatum.c) := by
  apply (Segment.joined_resolution_designatum_iff resolutionAB
    rfl ParallelDesignatum.c).mpr
  exact parallel_related_total .b .c

/-- The retained nested segment denoted by `[a <--> b] <--> c`. -/
def resolvedABThenC : Segment parallelElaboration :=
  Segment.append (Segment.ofResolution resolutionAB)
    (Segment.ofDesignatum parallelElaboration ParallelDesignatum.c)
    resolvedAB_join_c

/-- Composition retains the inner left edge and the outer right edge. -/
theorem resolvedABThenC_interfaces :
    resolvedABThenC.left = Component.singleton ParallelDesignatum.a ∧
      resolvedABThenC.right = Component.singleton ParallelDesignatum.c := by
  constructor
  · rw [resolvedABThenC, Segment.left_append,
      Segment.left_ofResolution]
    rfl
  · rw [resolvedABThenC, Segment.right_append,
      Segment.right_ofDesignatum]

/-! ## Endpoint sensitivity over a non-total elaboration -/

namespace EndpointSensitivity

inductive EndpointDesignatum where
  | a
  | b
  | c
  | ab
  | moreA
  | abWitness
  | moreB
  | bcWitness
  | moreC
  deriving DecidableEq

/--
`a` and `b` meet at `abWitness`, while `b` and `c` meet separately at
`bcWitness`.  The extra source `ab` elaborates specifically as `[a,b]`.
-/
def endpointElaboration : Elaboration EndpointDesignatum where
  Elab d rawM :=
    (d = .ab ∧
      rawM.components =
        [Component.singleton .a, Component.singleton .b]) ∨
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
          Component.singleton .moreC])

def endpointRawA : RawMutualDependence EndpointDesignatum :=
  .pair endpointElaboration (Component.singleton .moreA)
    (Component.singleton .abWitness)

def endpointRawB : RawMutualDependence EndpointDesignatum :=
  .triple endpointElaboration (Component.singleton .abWitness)
    (Component.singleton .moreB) (Component.singleton .bcWitness)

def endpointRawC : RawMutualDependence EndpointDesignatum :=
  .pair endpointElaboration (Component.singleton .bcWitness)
    (Component.singleton .moreC)

def endpointRawAB : RawMutualDependence EndpointDesignatum :=
  .pair endpointElaboration (Component.singleton .a)
    (Component.singleton .b)

theorem endpoint_elaborates_a : endpointElaboration.Elab .a endpointRawA := by
  simp [endpointElaboration, endpointRawA]

theorem endpoint_elaborates_b : endpointElaboration.Elab .b endpointRawB := by
  simp [endpointElaboration, endpointRawB]

theorem endpoint_elaborates_c : endpointElaboration.Elab .c endpointRawC := by
  simp [endpointElaboration, endpointRawC]

theorem endpoint_elaborates_ab :
    endpointElaboration.Elab .ab endpointRawAB := by
  simp [endpointElaboration, endpointRawAB]

theorem endpoint_related_a_b : endpointElaboration.Related .a .b := by
  have ha : endpointElaboration.Reaches .a .abWitness :=
    Elaboration.Reaches.single (rawM := endpointRawA)
      (a := Component.singleton .abWitness) endpoint_elaborates_a
      (by simp [endpointRawA]) (by simp)
  have hb : endpointElaboration.Reaches .b .abWitness :=
    Elaboration.Reaches.single (rawM := endpointRawB)
      (a := Component.singleton .abWitness) endpoint_elaborates_b
      (by simp [endpointRawB]) (by simp)
  exact ⟨.abWitness, ha, hb⟩

theorem endpoint_related_b_c : endpointElaboration.Related .b .c := by
  have hb : endpointElaboration.Reaches .b .bcWitness :=
    Elaboration.Reaches.single (rawM := endpointRawB)
      (a := Component.singleton .bcWitness) endpoint_elaborates_b
      (by simp [endpointRawB]) (by simp)
  have hc : endpointElaboration.Reaches .c .bcWitness :=
    Elaboration.Reaches.single (rawM := endpointRawC)
      (a := Component.singleton .bcWitness) endpoint_elaborates_c
      (by simp [endpointRawC]) (by simp)
  exact ⟨.bcWitness, hb, hc⟩

private theorem reaches_a {w : EndpointDesignatum}
    (h : endpointElaboration.Reaches .a w) :
    w = .a ∨ w = .moreA ∨ w = .abWitness := by
  cases h with
  | refl _ => simp
  | step hE hcomponent he htail =>
      simp [endpointElaboration] at hE
      simp [hE] at hcomponent
      rcases hcomponent with rfl | rfl
      · simp at he
        cases he
        cases htail with
        | refl _ => simp
        | step hE' _ _ _ => simp [endpointElaboration] at hE'
      · simp at he
        cases he
        cases htail with
        | refl _ => simp
        | step hE' _ _ _ => simp [endpointElaboration] at hE'

private theorem reaches_c {w : EndpointDesignatum}
    (h : endpointElaboration.Reaches .c w) :
    w = .c ∨ w = .bcWitness ∨ w = .moreC := by
  cases h with
  | refl _ => simp
  | step hE hcomponent he htail =>
      simp [endpointElaboration] at hE
      simp [hE] at hcomponent
      rcases hcomponent with rfl | rfl
      · simp at he
        cases he
        cases htail with
        | refl _ => simp
        | step hE' _ _ _ => simp [endpointElaboration] at hE'
      · simp at he
        cases he
        cases htail with
        | refl _ => simp
        | step hE' _ _ _ => simp [endpointElaboration] at hE'

theorem endpoint_not_related_a_c : ¬ endpointElaboration.Related .a .c := by
  rintro ⟨w, haw, hcw⟩
  rcases reaches_a haw with hwa | hwa | hwa <;>
    rcases reaches_c hcw with hwc | hwc | hwc <;>
    simp_all

def endpointResolutionAB :
    Elaboration.Resolution endpointElaboration EndpointDesignatum.ab where
  raw := endpointRawAB
  isElaboration := endpoint_elaborates_ab
  holds := by
    simp only [endpointRawAB, Elaboration.certify_pair,
      RawMutualDependence.holds_pair_iff]
    exact Elaboration.linked_singleton_iff.mpr endpoint_related_a_b

/-- The selected body exposes `b`, so `[a,b] <--> c` succeeds. -/
theorem endpoint_resolution_join_c :
    Segment.Joined endpointElaboration
      (Segment.ofResolution endpointResolutionAB)
      (Segment.ofDesignatum endpointElaboration .c) := by
  exact (Segment.joined_resolution_designatum_iff endpointResolutionAB
    rfl .c).mpr endpoint_related_b_c

/-- The retained nested segment denoted by `[a <--> b] <--> c`. -/
def endpointResolvedABThenC : Segment endpointElaboration :=
  Segment.append (Segment.ofResolution endpointResolutionAB)
    (Segment.ofDesignatum endpointElaboration .c)
    endpoint_resolution_join_c

@[simp] theorem endpointResolvedABThenC_sourceComponents :
    endpointResolvedABThenC.shape.sourceComponents =
      [Component.singleton EndpointDesignatum.ab,
        Component.singleton EndpointDesignatum.c] := by
  rfl

/-- Flattening retains the source designata, not the opened body's endpoints. -/
def endpointNestedMutualDependence : MutualDependence EndpointDesignatum :=
  endpointResolvedABThenC.toMutualDependence
    endpointResolvedABThenC_sourceComponents

@[simp] theorem endpointNestedMutualDependence_components :
    endpointNestedMutualDependence.components =
      [Component.singleton EndpointDesignatum.ab,
        Component.singleton EndpointDesignatum.c] := by
  simp [endpointNestedMutualDependence]

/-- Reversing only the outer order tests `c` against `a` and therefore fails. -/
theorem endpoint_c_not_join_resolution :
    ¬ Segment.Joined endpointElaboration
      (Segment.ofDesignatum endpointElaboration .c)
      (Segment.ofResolution endpointResolutionAB) := by
  intro hjoined
  have hca : endpointElaboration.Related .c .a :=
    (Segment.joined_designatum_resolution_iff endpointResolutionAB
      rfl .c).mp hjoined
  exact endpoint_not_related_a_c hca.symm

/-- The same certified `a <--> b <--> c` chain can occupy one Segment slot. -/
def endpointMutualDependence : MutualDependence EndpointDesignatum :=
  MutualDependence.triple (Linkage.ofElaboration endpointElaboration)
    (Component.singleton .a) (Component.singleton .b)
    (Component.singleton .c)
    (Elaboration.linked_singleton_iff.mpr endpoint_related_a_b)
    (Elaboration.linked_singleton_iff.mpr endpoint_related_b_c)

def endpointDirectSegment : Segment endpointElaboration :=
  Segment.ofMutualDependence endpointMutualDependence rfl

@[simp] theorem endpointDirectSegment_interfaces :
    endpointDirectSegment.left = Component.singleton EndpointDesignatum.a ∧
      endpointDirectSegment.right =
        Component.singleton EndpointDesignatum.c := by
  constructor <;> rfl

end EndpointSensitivity

end SegmentExamples
