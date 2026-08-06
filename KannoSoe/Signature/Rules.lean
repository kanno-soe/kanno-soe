import KannoSoe.Signature.V2

/-!
# Finite elaboration rules and verified decision procedures

`ElabRule` is a finite presentation of an elaboration clause.  The decision
procedures below compute the reach closure through every component, using
structural fuel,
and are connected back to the relational signature by iff theorems.  They use
ordinary `decide`; no native-code evaluator participates in the proofs.
-/

universe u

/-- A finite elaboration clause with at least two nonempty components. -/
structure ElabRule (D : Type u) where
  source : D
  components : List (List D)
  two_le : 2 ≤ components.length := by decide
  nonempty : ∀ c ∈ components, c ≠ [] := by decide

namespace Component

/-- Turn a list of nonempty designatum lists into components. -/
def ofDesignataList {D : Type u} (components : List (List D))
    (nonempty : ∀ c ∈ components, c ≠ []) : List (Component D) :=
  components.pmap
    (fun c hc => Component.ofDesignata c hc) nonempty

@[simp] theorem ofDesignataList_nil {D : Type u}
    (nonempty : ∀ c ∈ ([] : List (List D)), c ≠ []) :
    ofDesignataList [] nonempty = [] :=
  rfl

@[simp] theorem ofDesignataList_cons {D : Type u} (c : List D)
    (components : List (List D))
    (nonempty : ∀ c' ∈ c :: components, c' ≠ []) :
    ofDesignataList (c :: components) nonempty =
      Component.ofDesignata c (nonempty c (by simp)) ::
        ofDesignataList components
          (fun c' hc' => nonempty c' (by simp [hc'])) := by
  simp [ofDesignataList]

end Component

namespace ElabRule

theorem components_ne_nil {D : Type u} (rule : ElabRule D) :
    rule.components ≠ [] := by
  intro h
  have htwo := rule.two_le
  simp [h] at htwo

/-- The first component list of a rule. -/
def first {D : Type u} (rule : ElabRule D) : List D :=
  rule.components.head rule.components_ne_nil

/-- The last component list of a rule. -/
def last {D : Type u} (rule : ElabRule D) : List D :=
  rule.components.getLast rule.components_ne_nil

@[simp] theorem first_mem {D : Type u} (rule : ElabRule D) :
    rule.first ∈ rule.components := by
  exact List.head_mem rule.components_ne_nil

@[simp] theorem last_mem {D : Type u} (rule : ElabRule D) :
    rule.last ∈ rule.components := by
  exact List.getLast_mem rule.components_ne_nil

theorem first_ne_nil {D : Type u} (rule : ElabRule D) :
    rule.first ≠ [] :=
  rule.nonempty rule.first rule.first_mem

theorem last_ne_nil {D : Type u} (rule : ElabRule D) :
    rule.last ≠ [] :=
  rule.nonempty rule.last rule.last_mem

/-- Component lists strictly between the first and last lists. -/
def middle {D : Type u} (rule : ElabRule D) : List (List D) :=
  rule.components.tail.dropLast

theorem middle_nonempty {D : Type u} (rule : ElabRule D) :
    ∀ c ∈ rule.middle, c ≠ [] := by
  intro c hc
  apply rule.nonempty c
  exact List.mem_of_mem_tail (List.dropLast_subset _ hc)

def firstComponent {D : Type u} (rule : ElabRule D) : Component D :=
  Component.ofDesignata rule.first rule.first_ne_nil

def lastComponent {D : Type u} (rule : ElabRule D) : Component D :=
  Component.ofDesignata rule.last rule.last_ne_nil

def middleComponents {D : Type u} (rule : ElabRule D) :
    List (Component D) :=
  Component.ofDesignataList rule.middle rule.middle_nonempty

/-- The canonical raw body represented by a rule for a supplied interdependence. -/
def toRaw {D : Type u} (rule : ElabRule D) (L : Interdependence D) :
    RawMutualDependence D where
  interdependence := L
  c₁ := rule.firstComponent
  middle := rule.middleComponents
  cₙ := rule.lastComponent

@[simp] theorem c₁_toRaw {D : Type u} (rule : ElabRule D)
    (L : Interdependence D) : (rule.toRaw L).c₁ = rule.firstComponent :=
  rfl

@[simp] theorem cₙ_toRaw {D : Type u} (rule : ElabRule D)
    (L : Interdependence D) : (rule.toRaw L).cₙ = rule.lastComponent :=
  rfl

@[simp] theorem components_toRaw {D : Type u} (rule : ElabRule D)
    (L : Interdependence D) :
    (rule.toRaw L).components =
      rule.firstComponent :: rule.middleComponents ++ [rule.lastComponent] :=
  rfl

/-- The rule's component lists decomposed into first, middle, and last. -/
def displayedComponents {D : Type u} (rule : ElabRule D) : List (List D) :=
  rule.first :: rule.middle ++ [rule.last]

theorem tail_ne_nil {D : Type u} (rule : ElabRule D) :
    rule.components.tail ≠ [] := by
  cases hcomponents : rule.components with
  | nil =>
      have htwo := rule.two_le
      simp [hcomponents] at htwo
  | cons first rest =>
      cases rest with
      | nil =>
          have htwo := rule.two_le
          simp [hcomponents] at htwo
      | cons second rest => simp

/-- The displayed decomposition contains exactly the supplied component lists. -/
theorem displayedComponents_eq_components {D : Type u}
    (rule : ElabRule D) : rule.displayedComponents = rule.components := by
  simp only [displayedComponents, first, middle, last]
  rw [← List.getLast_tail rule.tail_ne_nil,
    List.cons_append,
    List.dropLast_concat_getLast rule.tail_ne_nil]
  exact List.cons_head_tail rule.components_ne_nil

/-- Every designatum occurring in any component of a rule. -/
def designata {D : Type u} (rule : ElabRule D) : List D :=
  rule.components.flatten

theorem displayedComponents_nonempty {D : Type u} (rule : ElabRule D) :
    ∀ c ∈ rule.displayedComponents, c ≠ [] := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact rule.first_ne_nil
  · rcases List.mem_append.mp hc with hc | hc
    · exact rule.middle_nonempty c hc
    · have hc' : c = rule.last := by simpa using hc
      subst c
      exact rule.last_ne_nil

theorem components_toRaw_eq_ofDesignataList {D : Type u}
    (rule : ElabRule D) (L : Interdependence D) :
    (rule.toRaw L).components =
    Component.ofDesignataList rule.displayedComponents
        rule.displayedComponents_nonempty := by
  simp [displayedComponents, toRaw, RawMutualDependence.components,
    firstComponent, middleComponents, lastComponent,
    Component.ofDesignataList]

theorem components_toRaw_eq_ofComponents {D : Type u}
    (rule : ElabRule D) (L : Interdependence D) :
    (rule.toRaw L).components =
      Component.ofDesignataList rule.components rule.nonempty := by
  simpa only [displayedComponents_eq_components] using
    rule.components_toRaw_eq_ofDesignataList L

end ElabRule

namespace Elaboration

/-- Present an elaboration relation by a finite list of rules. -/
def ofRules {D : Type u} (rules : List (ElabRule D)) : Elaboration D where
  Elab d rawM :=
    ∃ rule ∈ rules,
      d = rule.source ∧
        rawM.components = (rule.toRaw rawM.interdependence).components

namespace Rules

variable {D : Type u} [DecidableEq D]

/-- Immediate component successors of a designatum in a finite rule system. -/
def succs (rules : List (ElabRule D)) (d : D) : List D :=
  rules.flatMap fun rule =>
    if rule.source = d then rule.designata else []

/-- Every designatum mentioned as a source or component member. -/
def mentionedDesignata (rules : List (ElabRule D)) : List D :=
  (rules.flatMap fun rule => rule.source :: rule.designata).eraseDups

/-- Add all immediate successors of the current reached set. -/
def expand (rules : List (ElabRule D)) (reached : List D) : List D :=
  (reached ++ reached.flatMap (succs rules)).eraseDups

/-- Structurally fuelled saturation, stopping early at a fixed point. -/
def saturate (rules : List (ElabRule D)) : Nat → List D → List D
  | 0, reached => reached
  | fuel + 1, reached =>
      let expanded := expand rules reached
      if expanded ⊆ reached then reached
      else saturate rules fuel expanded

/-- Designata in the finite universe not yet present in a reached set. -/
def unseen (rules : List (ElabRule D)) (reached : List D) : List D :=
  (mentionedDesignata rules).filter fun d => decide (d ∉ reached)

/-- The verified finite reach closure of a seed. -/
def reachSet (rules : List (ElabRule D)) (seed : D) : List D :=
  saturate rules (mentionedDesignata rules).length [seed]

theorem mem_succs_iff {rules : List (ElabRule D)} {d x : D} :
    x ∈ succs rules d ↔
      ∃ rule ∈ rules, rule.source = d ∧ x ∈ rule.designata := by
  simp only [succs, List.mem_flatMap]
  constructor
  · rintro ⟨rule, hrule, hx⟩
    by_cases hsource : rule.source = d
    · exact ⟨rule, hrule, hsource, by simpa [hsource] using hx⟩
    · simp [hsource] at hx
  · rintro ⟨rule, hrule, hsource, hx⟩
    exact ⟨rule, hrule, by simpa [hsource] using hx⟩

theorem mem_universe_of_mem_designata {rules : List (ElabRule D)}
    {rule : ElabRule D} (hrule : rule ∈ rules) {x : D}
    (hx : x ∈ rule.designata) : x ∈ mentionedDesignata rules := by
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  exact ⟨rule, hrule, List.Mem.tail _ hx⟩

theorem mem_universe_of_mem_succs {rules : List (ElabRule D)}
    {d x : D} (hx : x ∈ succs rules d) :
    x ∈ mentionedDesignata rules := by
  obtain ⟨rule, hrule, _, hxdesignata⟩ := mem_succs_iff.mp hx
  exact mem_universe_of_mem_designata hrule hxdesignata

theorem reaches_of_mem_succs {rules : List (ElabRule D)}
    {d x : D} (hx : x ∈ succs rules d) :
    (ofRules rules).Reaches d x := by
  obtain ⟨rule, hrule, hsource, hxdesignata⟩ := mem_succs_iff.mp hx
  let rawM :=
    rule.toRaw (Interdependence.ofElaboration (ofRules rules))
  have hElab : (ofRules rules).Elab d rawM := by
    exact ⟨rule, hrule, hsource.symm, rfl⟩
  obtain ⟨component, hcomponent, hx⟩ :=
    List.mem_flatten.mp hxdesignata
  let a := Component.ofDesignata component (rule.nonempty component hcomponent)
  exact Reaches.single (rawM := rawM) (a := a) hElab
    (by
      rw [ElabRule.components_toRaw_eq_ofComponents]
      exact List.mem_pmap_of_mem hcomponent)
    (by simpa [a] using hx)

theorem mem_succs_of_elab_component {rules : List (ElabRule D)}
    {d x : D} {rawM : RawMutualDependence D} {a : Component D}
    (hElab : (ofRules rules).Elab d rawM)
    (hcomponent : a ∈ rawM.components)
    (hx : x ∈ a) : x ∈ succs rules d := by
  obtain ⟨rule, hrule, hsource, hcomponents⟩ := hElab
  apply mem_succs_iff.mpr
  refine ⟨rule, hrule, hsource.symm, ?_⟩
  have ha : a ∈ Component.ofDesignataList rule.components rule.nonempty := by
    rw [← ElabRule.components_toRaw_eq_ofComponents,
      ← hcomponents]
    exact hcomponent
  obtain ⟨component, hcomponent', haeq⟩ := List.mem_pmap.mp ha
  rw [← haeq] at hx
  exact List.mem_flatten.mpr
    ⟨component, hcomponent', by simpa using hx⟩

@[simp] theorem mem_expand_iff {rules : List (ElabRule D)}
    {reached : List D} {x : D} :
    x ∈ expand rules reached ↔
      x ∈ reached ∨ ∃ d ∈ reached, x ∈ succs rules d := by
  simp [expand]

theorem subset_expand (rules : List (ElabRule D)) (reached : List D) :
    reached ⊆ expand rules reached := by
  intro x hx
  exact mem_expand_iff.mpr (Or.inl hx)

theorem mem_universe_of_mem_expand_not_mem {rules : List (ElabRule D)}
    {reached : List D} {x : D} (hx : x ∈ expand rules reached)
    (hnot : x ∉ reached) : x ∈ mentionedDesignata rules := by
  rcases mem_expand_iff.mp hx with hx | ⟨d, _, hsucc⟩
  · exact (hnot hx).elim
  · exact mem_universe_of_mem_succs hsucc

private theorem exists_mem_not_mem_of_not_subset {xs ys : List D}
    (h : ¬xs ⊆ ys) : ∃ x, x ∈ xs ∧ x ∉ ys := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : x ∈ ys
      · have htail : ¬xs ⊆ ys := by
          intro hsubset
          exact h (List.cons_subset.mpr ⟨hx, hsubset⟩)
        obtain ⟨y, hyxs, hy⟩ := ih htail
        exact ⟨y, List.Mem.tail x hyxs, hy⟩
      · exact ⟨x, List.Mem.head xs, hx⟩

private theorem length_filter_le_of_imp {α : Type u} {l : List α}
    {p q : α → Bool} (himp : ∀ x, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have ih' := ih
      cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

private theorem length_filter_lt_of_imp_of_exists {α : Type u}
    {l : List α} {p q : α → Bool}
    (himp : ∀ x, p x = true → q x = true)
    (hexists : ∃ x ∈ l, q x = true ∧ p x = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hexists
  | cons x xs ih =>
      have hle := length_filter_le_of_imp (l := xs) himp
      rcases hexists with ⟨y, hy, hqy, hpy⟩
      rcases List.mem_cons.mp hy with hy | hy
      · subst y
        cases hp : p x <;> cases hq : q x <;> simp_all <;> omega
      · have ihExists : ∃ y ∈ xs, q y = true ∧ p y = false :=
          ⟨y, hy, hqy, hpy⟩
        have ih' := ih ihExists
        cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem unseen_expand_lt {rules : List (ElabRule D)} {reached : List D}
    (hnot : ¬expand rules reached ⊆ reached) :
    (unseen rules (expand rules reached)).length <
      (unseen rules reached).length := by
  obtain ⟨x, hxexpanded, hxnot⟩ :=
    exists_mem_not_mem_of_not_subset hnot
  have hxuniverse := mem_universe_of_mem_expand_not_mem hxexpanded hxnot
  apply length_filter_lt_of_imp_of_exists
  · intro y hy
    simp only [decide_eq_true_eq] at hy ⊢
    intro hyreached
    exact hy (subset_expand rules reached hyreached)
  · exact ⟨x, hxuniverse, by simp [hxnot, hxexpanded]⟩

theorem expand_subset_of_unseen_eq_zero {rules : List (ElabRule D)}
    {reached : List D} (hzero : (unseen rules reached).length = 0) :
    expand rules reached ⊆ reached := by
  intro x hxexpanded
  by_cases hx : x ∈ reached
  · exact hx
  · have hxuniverse := mem_universe_of_mem_expand_not_mem hxexpanded hx
    have hxunseen : x ∈ unseen rules reached := by
      simp [unseen, hxuniverse, hx]
    have hpos := List.length_pos_of_mem hxunseen
    omega

theorem saturate_stable (rules : List (ElabRule D)) (fuel : Nat)
    (reached : List D) (hbound : (unseen rules reached).length ≤ fuel) :
    expand rules (saturate rules fuel reached) ⊆
      saturate rules fuel reached := by
  induction fuel generalizing reached with
  | zero =>
      simp only [saturate]
      apply expand_subset_of_unseen_eq_zero
      omega
  | succ fuel ih =>
      simp only [saturate]
      let expanded := expand rules reached
      by_cases hstable : expanded ⊆ reached
      · simp [expanded, hstable]
      · simp [expanded, hstable]
        apply ih
        have hprogress := unseen_expand_lt (rules := rules) hstable
        omega

theorem reachSet_stable (rules : List (ElabRule D)) (seed : D) :
    expand rules (reachSet rules seed) ⊆ reachSet rules seed := by
  unfold reachSet
  apply saturate_stable
  exact List.length_filter_le _ _

theorem expand_reaches {rules : List (ElabRule D)} {seed : D}
    {reached : List D}
    (hreach : ∀ x ∈ reached, (ofRules rules).Reaches seed x) :
    ∀ x ∈ expand rules reached, (ofRules rules).Reaches seed x := by
  intro x hx
  rcases mem_expand_iff.mp hx with hx | ⟨d, hd, hsucc⟩
  · exact hreach x hx
  · exact (hreach d hd).trans (reaches_of_mem_succs hsucc)

theorem mem_saturate_reaches {rules : List (ElabRule D)} {seed : D}
    (fuel : Nat) (reached : List D)
    (hreach : ∀ x ∈ reached, (ofRules rules).Reaches seed x) :
    ∀ x ∈ saturate rules fuel reached,
      (ofRules rules).Reaches seed x := by
  induction fuel generalizing reached with
  | zero => simpa [saturate] using hreach
  | succ fuel ih =>
      simp only [saturate]
      let expanded := expand rules reached
      by_cases hstable : expanded ⊆ reached
      · simp [expanded, hstable]
        exact hreach
      · simp [expanded, hstable]
        exact ih expanded (expand_reaches hreach)

theorem mem_reachSet_reaches {rules : List (ElabRule D)} {seed x : D}
    (hx : x ∈ reachSet rules seed) : (ofRules rules).Reaches seed x := by
  unfold reachSet at hx
  exact mem_saturate_reaches (rules := rules)
    (mentionedDesignata rules).length [seed]
    (by
      intro y hy
      have hy' : y = seed := by simpa using hy
      subst y
      exact .refl seed)
    x hx

theorem subset_saturate (rules : List (ElabRule D)) (fuel : Nat)
    (reached : List D) : reached ⊆ saturate rules fuel reached := by
  induction fuel generalizing reached with
  | zero => exact List.Subset.refl reached
  | succ fuel ih =>
      simp only [saturate]
      let expanded := expand rules reached
      by_cases hstable : expanded ⊆ reached
      · simp [expanded, hstable]
      · simp [expanded, hstable]
        exact (subset_expand rules reached).trans (ih expanded)

theorem seed_mem_reachSet (rules : List (ElabRule D)) (seed : D) :
    seed ∈ reachSet rules seed := by
  unfold reachSet
  exact subset_saturate rules (mentionedDesignata rules).length [seed] (by simp)

theorem reachSet_closed {rules : List (ElabRule D)} {seed d x : D}
    (hd : d ∈ reachSet rules seed) (hx : x ∈ succs rules d) :
    x ∈ reachSet rules seed := by
  apply reachSet_stable rules seed
  exact mem_expand_iff.mpr (Or.inr ⟨d, hd, hx⟩)

theorem reaches_mem_of_succ_closed {rules : List (ElabRule D)}
    {start target : D} (h : (ofRules rules).Reaches start target)
    {reached : List D} (hstart : start ∈ reached)
    (hclosed : ∀ {d x}, d ∈ reached → x ∈ succs rules d → x ∈ reached) :
    target ∈ reached := by
  induction h with
  | refl _ => exact hstart
  | step hElab hcomponent hmem _ ih =>
      apply ih
      exact hclosed hstart
        (mem_succs_of_elab_component hElab hcomponent hmem)

theorem reaches_mem_reachSet {rules : List (ElabRule D)} {seed x : D}
    (hx : (ofRules rules).Reaches seed x) : x ∈ reachSet rules seed := by
  apply reaches_mem_of_succ_closed hx (seed_mem_reachSet rules seed)
  intro d x hd hsucc
  exact reachSet_closed hd hsucc

/-- The computed closure and relational reachability coincide. -/
@[simp] theorem mem_reachSet_iff {rules : List (ElabRule D)} {seed x : D} :
    x ∈ reachSet rules seed ↔ (ofRules rules).Reaches seed x :=
  ⟨mem_reachSet_reaches, reaches_mem_reachSet⟩

/-- Boolean nonempty intersection of two computed reach sets. -/
def joinableB (rules : List (ElabRule D)) (a b : D) : Bool :=
  (reachSet rules a).any fun w => decide (w ∈ reachSet rules b)

@[simp] theorem joinableB_eq_true_iff {rules : List (ElabRule D)} {a b : D} :
    joinableB rules a b = true ↔ (ofRules rules).Joinable a b := by
  simp [joinableB, Elaboration.Joinable]

/-- Egli–Milner interdependence on finite designatum lists. -/
def interdependentB (rules : List (ElabRule D)) (c₁ c₂ : List D) : Bool :=
  (c₁.all fun a => c₂.any fun b => joinableB rules a b) &&
    (c₂.all fun b => c₁.any fun a => joinableB rules a b)

@[simp] theorem interdependent_ofDesignata_iff
    {rules : List (ElabRule D)} {c₁ c₂ : List D}
    {h₁ : c₁ ≠ []} {h₂ : c₂ ≠ []} :
    interdependentB rules c₁ c₂ = true ↔
      (ofRules rules).Interdependent
        (Component.ofDesignata c₁ h₁) (Component.ofDesignata c₂ h₂) := by
  simp [interdependentB, Elaboration.Interdependent]

@[simp] theorem interdependent_singleton_iff
    {rules : List (ElabRule D)} {a b : D} :
    joinableB rules a b = true ↔
      (ofRules rules).Interdependent
        (Component.singleton a) (Component.singleton b) := by
  rw [joinableB_eq_true_iff]
  exact Elaboration.interdependent_singleton_iff.symm

/-- Pairwise chaining on finite component lists. -/
def chainedB (rules : List (ElabRule D)) : List (List D) → Bool
  | [] => true
  | [_] => true
  | c₁ :: c₂ :: rest =>
      interdependentB rules c₁ c₂ && chainedB rules (c₂ :: rest)

omit [DecidableEq D] in
private theorem chained_cons_cons_iff {L : Interdependence D}
    {c₁ c₂ : Component D} {rest : List (Component D)} :
    L.Chained (c₁ :: c₂ :: rest) ↔
      L.Interdependent c₁ c₂ ∧ L.Chained (c₂ :: rest) := by
  constructor
  · intro h
    cases h with
    | cons h₁₂ htail => exact ⟨h₁₂, htail⟩
  · rintro ⟨h₁₂, htail⟩
    exact .cons h₁₂ htail

@[simp] theorem chained_map_ofDesignata_iff
    {rules : List (ElabRule D)} (components : List (List D))
    (nonempty : ∀ c ∈ components, c ≠ []) :
    chainedB rules components = true ↔
      (Interdependence.ofElaboration (ofRules rules)).Chained
        (Component.ofDesignataList components nonempty) := by
  induction components with
  | nil =>
      constructor
      · intro _
        exact .nil
      · intro _
        rfl
  | cons c components ih =>
      cases components with
      | nil =>
          constructor
          · intro _
            exact .single _
          · intro _
            rfl
      | cons c₂ rest =>
          rw [chainedB]
          rw [Bool.and_eq_true]
          rw [interdependent_ofDesignata_iff]
          rw [ih (fun c' hc' => nonempty c' (by simp [hc']))]
          simp only [Component.ofDesignataList_cons]
          rw [chained_cons_cons_iff]
          rfl

@[simp] theorem chainedB_displayedComponents_iff_holds
    {rules : List (ElabRule D)} (rule : ElabRule D) :
    chainedB rules rule.displayedComponents = true ↔
      (rule.toRaw (Interdependence.ofElaboration (ofRules rules))).Holds := by
  change chainedB rules rule.displayedComponents = true ↔
    (Interdependence.ofElaboration (ofRules rules)).Chained
      (rule.toRaw (Interdependence.ofElaboration (ofRules rules))).components
  rw [rule.components_toRaw_eq_ofDesignataList]
  exact chained_map_ofDesignata_iff _ _

instance instDecidableJoinableOfRules (rules : List (ElabRule D))
    (a b : D) : Decidable ((ofRules rules).Joinable a b) :=
  decidable_of_iff (joinableB rules a b = true) joinableB_eq_true_iff

instance instDecidableInterdependentOfRules (rules : List (ElabRule D))
    (c₁ c₂ : List D) (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ []) :
    Decidable ((ofRules rules).Interdependent
      (Component.ofDesignata c₁ h₁) (Component.ofDesignata c₂ h₂)) :=
  decidable_of_iff (interdependentB rules c₁ c₂ = true)
    interdependent_ofDesignata_iff

instance instDecidableInterdependentSingletonOfRules
    (rules : List (ElabRule D)) (a b : D) :
    Decidable ((ofRules rules).Interdependent
      (Component.singleton a) (Component.singleton b)) :=
  decidable_of_iff (joinableB rules a b = true)
    interdependent_singleton_iff

instance instDecidableChainedOfRules (rules : List (ElabRule D))
    (components : List (List D))
    (nonempty : ∀ c ∈ components, c ≠ []) :
    Decidable ((Interdependence.ofElaboration (ofRules rules)).Chained
      (Component.ofDesignataList components nonempty)) :=
  decidable_of_iff (chainedB rules components = true)
    (chained_map_ofDesignata_iff components nonempty)

instance instDecidableRuleHolds (rules : List (ElabRule D))
    (rule : ElabRule D) :
    Decidable
      ((rule.toRaw (Interdependence.ofElaboration (ofRules rules))).Holds) :=
  decidable_of_iff (chainedB rules rule.displayedComponents = true)
    (chainedB_displayedComponents_iff_holds rule)

end Rules
end Elaboration

namespace RulesSmoke

inductive Point where
  | a
  | b
  | middle
  | c
  deriving DecidableEq, Repr

abbrev rules : List (ElabRule Point) := [
  { source := .a, components := [[.b], [.middle], [.c]] }
]

abbrev elaboration : Elaboration Point :=
  Elaboration.ofRules rules

theorem positive : elaboration.Joinable .a .b := by decide

theorem middle_component : elaboration.Joinable .a .middle := by decide

theorem negative : ¬elaboration.Joinable .b .c := by decide

theorem chained :
    (Interdependence.ofElaboration elaboration).Chained
      (Component.ofDesignataList [[.a], [.b]] (by decide)) := by
  decide

end RulesSmoke
