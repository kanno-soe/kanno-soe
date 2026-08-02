import KannoSoe.Signature.Segment

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
    change (RawMutualDependence.pair
      (Linkage.ofElaboration parallelElaboration)
      (Component.singleton ParallelDesignatum.a)
      (Component.singleton ParallelDesignatum.b)).Holds
    rw [RawMutualDependence.holds_pair_iff]
    change parallelElaboration.Linked
      (Component.singleton ParallelDesignatum.a)
      (Component.singleton ParallelDesignatum.b)
    rw [Elaboration.linked_singleton_iff]
    exact parallel_related_total .a .b

/--
The source has two slots.  `ab` opens as `[a <--> b]`, while `x` remains a
leaf.  Pattern branches impossible under the source predicate still return a
leaf, keeping the definition constructive.
-/
def parallelShell : Segment.Shell parallelElaboration :=
  .slots (Component.pair .ab .x) fun member =>
    if h : member.1 = ParallelDesignatum.ab then
      h.symm ▸ Segment.Slot.resolved resolutionAB
    else
      .leaf

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
      simpa [parallelShell] using hd
  · rintro (rfl | rfl)
    · exact ⟨⟨ParallelDesignatum.ab, by simp⟩,
        by
          change ParallelDesignatum.a ∈
            Component.singleton ParallelDesignatum.a
          simp⟩
    · exact ⟨⟨ParallelDesignatum.x, by simp⟩,
        by simp⟩

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
      simpa [parallelShell] using hd
  · rintro (rfl | rfl)
    · exact ⟨⟨ParallelDesignatum.ab, by simp⟩,
        by
          change ParallelDesignatum.b ∈
            Component.singleton ParallelDesignatum.b
          simp⟩
    · exact ⟨⟨ParallelDesignatum.x, by simp⟩,
        by simp⟩

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

end SegmentExamples
