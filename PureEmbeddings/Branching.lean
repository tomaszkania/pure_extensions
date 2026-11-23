import Std

namespace PureEmbeddings.Branching

universe u v w

/--
`same i x y` means that `x` and `y` are in the same coset of the subgroup
with index `i`. A choice at coordinate `i` is invisible modulo the other
subgroups, and two choices at `i` are distinguished modulo its own subgroup.
Only the laws of addition used in the finite-sum argument are required.
-/
structure IndependentFamily (I : Type u) (K : Type v) (F : Type w) where
  zero : F
  add : F → F → F
  zero_add : ∀ x, add zero x = x
  add_zero : ∀ x, add x zero = x
  same : I → F → F → Prop
  refl : ∀ i x, same i x x
  symm : ∀ i x y, same i x y → same i y x
  trans : ∀ i x y z, same i x y → same i y z → same i x z
  add_congr : ∀ i a b x y, same i a b → same i x y →
    same i (add a x) (add b y)
  entry : I → K → F
  off_coordinate : ∀ i j k, i ≠ j → same i (entry j k) zero
  separate : ∀ i k l, same i (entry i k) (entry i l) → k = l

variable {I : Type u} {K : Type v} {F : Type w}

/-- Finite sums meet the prescribed cosets and are zero modulo every
subgroup whose index is outside the sum. -/
theorem finiteWitness (d : IndependentFamily I K F) (η : I → K)
    (indices : List I) (once : indices.Nodup) :
    ∃ x : F, (∀ i, i ∈ indices → d.same i x (d.entry i (η i))) ∧
             (∀ i, i ∉ indices → d.same i x d.zero) := by
  classical
  induction indices with
  | nil =>
    refine ⟨d.zero, ?_, ?_⟩
    · intro i hi
      simp at hi
    · intro i _
      exact d.refl i d.zero
  | cons j js ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp once
    obtain ⟨x, inside, outside⟩ := ih rest
    refine ⟨d.add (d.entry j (η j)) x, ?_, ?_⟩
    · intro i hi
      by_cases h : i = j
      · subst i
        simpa only [d.add_zero] using
          d.add_congr j _ _ _ _ (d.refl j (d.entry j (η j))) (outside j fresh)
      · have hj : i ∈ js := (List.mem_cons.mp hi).resolve_left h
        simpa only [d.zero_add] using
          d.add_congr i _ _ _ _ (d.off_coordinate i j (η j) h) (inside i hj)
    · intro i hi
      have h : i ≠ j := fun hij => hi (List.mem_cons.mpr (Or.inl hij))
      have h' : i ∉ js := fun hij => hi (List.mem_cons.mpr (Or.inr hij))
      simpa only [d.zero_add] using
        d.add_congr i _ _ _ _ (d.off_coordinate i j (η j) h) (outside i h')

/-- The independent-family bound stated without cardinal arithmetic. The
compactness assumption concerns finitely compatible cosets, and the
conclusion supplies an actual injective function on all assignments. -/
theorem independentInjection (d : IndependentFamily I K F)
    (compact : ∀ centres : I → F,
      (∀ js : List I, js.Nodup → ∃ x : F, ∀ i, i ∈ js → d.same i x (centres i)) →
      ∃ x : F, ∀ i, d.same i x (centres i)) :
    ∃ point : (I → K) → F, ∀ η ν, point η = point ν → η = ν := by
  classical
  have realises (η : I → K) : ∃ x : F, ∀ i, d.same i x (d.entry i (η i)) := by
    apply compact
    intro js hjs
    obtain ⟨x, inside, _⟩ := finiteWitness d η js hjs
    exact ⟨x, inside⟩
  let point := fun η => Classical.choose (realises η)
  have atCentre (η : I → K) (i : I) : d.same i (point η) (d.entry i (η i)) :=
    Classical.choose_spec (realises η) i
  refine ⟨point, ?_⟩
  intro η ν heq
  funext i
  apply d.separate i
  have hν : d.same i (point η) (d.entry i (ν i)) := heq ▸ atCentre ν i
  exact d.trans i _ _ _ (d.symm i _ _ (atCentre η i)) hν

/-- A branch prefix is stored newest entry first, so `k :: s` is the child
obtained by appending the next choice to the chronological prefix. -/
def branchPrefix (η : Nat → K) : Nat → List K
  | 0 => []
  | n + 1 => η n :: branchPrefix η n

/-- Combinatorial data of the cosets in a tree of depth `ω`. -/
structure CosetTree (K : Type v) (F : Type w) where
  inside : List K → F → Prop
  inhabitedNode : ∀ s, ∃ x, inside s x
  nested : ∀ s k x, inside (k :: s) x → inside s x
  separatedChildren : ∀ s k l x, inside (k :: s) x → inside (l :: s) x → k = l

private theorem ancestor (d : CosetTree K F) (η : Nat → K) (x : F) (m : Nat) :
    ∀ n, n ≤ m → d.inside (branchPrefix η m) x → d.inside (branchPrefix η n) x := by
  induction m with
  | zero =>
    intro n h hx
    have hn : n = 0 := by omega
    simpa only [hn] using hx
  | succ m ih =>
    intro n h hx
    by_cases hn : n = m + 1
    · simpa only [hn] using hx
    · exact ih n (by omega) (d.nested (branchPrefix η m) (η m) x hx)

private theorem commonDepth (levels : List Nat) : ∃ m, ∀ n ∈ levels, n ≤ m := by
  induction levels with
  | nil => exact ⟨0, by simp⟩
  | cons n ns ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨max n m, ?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with h | h
    · subst k
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (hm k h) (Nat.le_max_right _ _)

/-- Nested non-empty cosets meet every finite selection of levels. Under
compactness, one can choose a point for each infinite branch. Points for
distinct branches differ because two distinct children are disjoint. -/
theorem infiniteBranchInjection (d : CosetTree K F)
    (compact : ∀ nodes : Nat → List K,
      (∀ levels : List Nat, ∃ x : F, ∀ n ∈ levels, d.inside (nodes n) x) →
      ∃ x : F, ∀ n, d.inside (nodes n) x) :
    ∃ point : (Nat → K) → F, ∀ η ν, point η = point ν → η = ν := by
  classical
  have realises (η : Nat → K) : ∃ x : F, ∀ n, d.inside (branchPrefix η n) x := by
    apply compact (branchPrefix η)
    intro levels
    obtain ⟨m, hm⟩ := commonDepth levels
    obtain ⟨x, hx⟩ := d.inhabitedNode (branchPrefix η m)
    exact ⟨x, fun n hn => ancestor d η x m n (hm n hn) hx⟩
  let point := fun η => Classical.choose (realises η)
  have along (η : Nat → K) (n : Nat) : d.inside (branchPrefix η n) (point η) :=
    Classical.choose_spec (realises η) n
  refine ⟨point, ?_⟩
  intro η ν heq
  have eqPrefix : ∀ n, branchPrefix η n = branchPrefix ν n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have left : d.inside (η n :: branchPrefix η n) (point η) := along η (n + 1)
      have right : d.inside (ν n :: branchPrefix η n) (point η) := by
        rw [ih, heq]
        exact along ν (n + 1)
      have hk := d.separatedChildren (branchPrefix η n) (η n) (ν n) (point η) left right
      simp only [branchPrefix, hk, ih]
  funext n
  exact (List.cons.inj (eqPrefix (n + 1))).1

end PureEmbeddings.Branching
