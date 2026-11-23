import PureEmbeddings.ModuleTheory
import Mathlib.ModelTheory.Substructures
import Mathlib.Data.List.GetD
import Mathlib.Data.Fin.VecNotation

/-!
# Small pure submodules

We choose a solution of each soluble finite system in the ambient module.
Closing a set under the coordinates of these choices, addition, zero and
scalar multiplication gives a pure submodule. Mathlib's cardinal bound for
the closure under finitary operations counts the elements thus obtained.
-/

namespace PureEmbeddings

open Cardinal FirstOrder
open scoped BigOperators

universe u
variable {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]

namespace HullConstruction

private def coordinate {A : Type*} [Zero A] {n : Nat}
    (a : Fin n → A) (j : Nat) : A :=
  if h : j < n then a ⟨j, h⟩ else 0

private def rowsOf {m n : Nat} (r : Fin m → Fin n → R) : List (List R) :=
  List.ofFn (fun i => List.ofFn (r i))

private def matrixOf (rows : List (List R)) {m n : Nat} :
    Fin m → Fin n → R :=
  fun i j => (rows.getD i.val []).getD j.val 0

private theorem matrixOf_rowsOf {m n : Nat} (r : Fin m → Fin n → R) :
    matrixOf (rowsOf r) = r := by
  funext i j
  simp [matrixOf, rowsOf, i.isLt, j.isLt]

private noncomputable def chosen {m n : Nat} (r : Fin m → Fin n → R)
    (a : Fin m → M) : Fin n → M := by
  classical
  exact if h : Soluble r a then Classical.choose h else fun _ => 0

private theorem chosen_spec {m n : Nat} {r : Fin m → Fin n → R} {a : Fin m → M}
    (h : Soluble r a) (i : Fin m) : ∑ j, r i j • chosen r a j = a i := by
  simpa only [chosen, dif_pos h] using Classical.choose_spec h i

/-- The three alternatives encode zero/addition, multiplication by a
scalar, and one coordinate of a solution of a matrix with recorded rows. -/
private abbrev Symbol (R : Type u) :=
  Nat ⊕ (R ⊕ (Nat × List (List R) × Nat))

private def language (R : Type u) : Language.{u, 0} where
  Functions _ := Symbol R
  Relations _ := Empty

private noncomputable instance interpretation :
    (language R).Structure M where
  funMap := fun {m} op (a : Fin m → M) =>
    match (op : Symbol R) with
    | .inl 0 => 0
    | .inl (_ + 1) => coordinate a 0 + coordinate a 1
    | .inr (.inl r) => r • coordinate a 0
    | .inr (.inr (n, rows, j)) =>
        coordinate (chosen (matrixOf (m := m) (n := n) rows) a) j
  RelMap := fun h => nomatch h

private noncomputable abbrev closureOf (R : Type u) [Ring R] [Module R M]
    (s : Set M) := FirstOrder.Language.Substructure.closure (language R) s

private theorem zero_mem (s : Set M) : (0 : M) ∈ closureOf R s := by
  exact (closureOf R s).fun_mem (n := 0) (.inl 0 : Symbol R)
    Fin.elim0 (fun i => Fin.elim0 i)

private theorem add_mem (s : Set M) {x y : M}
    (hx : x ∈ closureOf R s) (hy : y ∈ closureOf R s) :
    x + y ∈ closureOf R s := by
  exact (closureOf R s).fun_mem (n := 2) (.inl 1 : Symbol R)
    ![x,y] (Fin.forall_fin_two.mpr ⟨hx, hy⟩)

private theorem smul_mem (s : Set M) (r : R) {x : M}
    (hx : x ∈ closureOf R s) : r • x ∈ closureOf R s := by
  exact (closureOf R s).fun_mem (n := 1) (.inr (.inl r) : Symbol R)
    ![x] (Fin.forall_fin_one.mpr hx)

private theorem chosen_mem (s : Set M) {m n : Nat} (r : Fin m → Fin n → R)
    (a : Fin m → M) (ha : ∀ i, a i ∈ closureOf R s) (j : Fin n) :
    chosen r a j ∈ closureOf R s := by
  have h := (closureOf R s).fun_mem (n := m)
    (.inr (.inr (n, rowsOf r, j.val)) : Symbol R) a ha
  change coordinate (chosen (matrixOf (m := m) (n := n) (rowsOf r)) a) j.val ∈ _ at h
  simpa only [matrixOf_rowsOf, coordinate, dif_pos j.isLt] using h

omit [Ring R] in
private theorem symbol_bound :
    Cardinal.mk (Σ i, (language R).Functions i) ≤ max ℵ₀ (Cardinal.mk R) := by
  let b : Cardinal := max ℵ₀ (Cardinal.mk R)
  have hω : ℵ₀ ≤ b := le_max_left _ _
  have hR : Cardinal.mk R ≤ b := le_max_right _ _
  have hL : Cardinal.mk (List (List R)) ≤ b :=
    (Cardinal.mk_list_le_max _).trans
      (max_le hω ((Cardinal.mk_list_le_max R).trans (max_le hω hR)))
  have mulBound {x y : Cardinal.{u}} (hx : x ≤ b) (hy : y ≤ b) : x * y ≤ b :=
    (mul_le_mul' hx hy).trans (Cardinal.mul_eq_self hω).le
  change Cardinal.mk (Σ _ : Nat, Symbol R) ≤ b
  simp only [Cardinal.mk_sigma, Cardinal.sum_const, Symbol, Cardinal.mk_sum, Cardinal.mk_prod,
    Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_id, Cardinal.lift_uzero]
  exact mulBound hω (Cardinal.add_le_of_le hω hω
    (Cardinal.add_le_of_le hω hR (mulBound hω (mulBound hL hω))))

end HullConstruction

open HullConstruction

/-- A monotone choice of a small pure submodule containing the given set.
It depends on the chosen solutions in the ambient module. -/
noncomputable def pureHull (R : Type u) [Ring R] [Module R M] (s : Set M) :
    Submodule R M where
  carrier := (closureOf R s : Set M)
  zero_mem' := zero_mem s
  add_mem' := add_mem s
  smul_mem' := smul_mem s

theorem subset_pureHull (s : Set M) : s ⊆ (pureHull R s : Set M) :=
  FirstOrder.Language.Substructure.subset_closure

theorem pureHull_mono {s t : Set M} (h : s ⊆ t) : pureHull R s ≤ pureHull R t :=
  FirstOrder.Language.Substructure.closure_mono h

/-- The kernel checks purity for the exact solvability predicate used in
the definition of the extension property. -/
theorem pureHull_isPureMap (s : Set M) : IsPureMap (pureHull R s).subtype := by
  refine ⟨Subtype.val_injective, ?_⟩
  intro m n r a h
  let b : Fin m → M := (pureHull R s).subtype ∘ a
  have hmem (j : Fin n) : chosen r b j ∈ pureHull R s :=
    chosen_mem s r b (fun i => (a i).property) j
  refine ⟨fun j => ⟨chosen r b j, hmem j⟩, fun i => ?_⟩
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using chosen_spec h i

theorem mk_pureHull_le (s : Set M) :
    Cardinal.mk (pureHull R s) ≤ max ℵ₀ (max (Cardinal.mk R) (Cardinal.mk s)) := by
  let b := max ℵ₀ (max (Cardinal.mk R) (Cardinal.mk s))
  have hω : ℵ₀ ≤ b := le_max_left _ _
  have hR : Cardinal.mk R ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hs : Cardinal.mk s ≤ b := (le_max_right _ _).trans (le_max_right _ _)
  change Cardinal.mk (closureOf R s) ≤ b
  have h := FirstOrder.Language.Substructure.lift_card_closure_le (L := language R) (s := s)
  simp only [Cardinal.lift_id] at h
  exact h.trans (max_le hω (Cardinal.add_le_of_le hω hs
    (symbol_bound (R := R) |>.trans (max_le hω hR))))

theorem exists_small_pureHull (s : Set M) :
    ∃ N : Submodule R M, s ⊆ (N : Set M) ∧ IsPureMap N.subtype ∧
      Cardinal.mk N ≤ max ℵ₀ (max (Cardinal.mk R) (Cardinal.mk s)) :=
  ⟨pureHull R s, subset_pureHull s, pureHull_isPureMap s, mk_pureHull_le s⟩

/-- Small submodule closed under any countably indexed choice of
matrix-dependent solution operations. No algebraic law for the operations
is required. This also permits simultaneous choices inside a submodule
and modulo that submodule. -/
theorem exists_small_closedOperations (s : Set M)
    (op : Nat → {m n : Nat} → (Fin m → Fin n → R) → (Fin m → M) → Fin n → M) :
    ∃ U : Submodule R M, s ⊆ (U : Set M) ∧
      Cardinal.mk U ≤ max ℵ₀ (max (Cardinal.mk R) (Cardinal.mk s)) ∧
      ∀ idx {m n} (r : Fin m → Fin n → R) (a : Fin m → M),
        (∀ i, a i ∈ U) → ∀ j, op idx r a j ∈ U := by
  classical
  let L := language R
  letI : L.Structure M := {
    funMap := fun {m} sym (a : Fin m → M) => match (sym : Symbol R) with
      | .inl 0 => 0
      | .inl (_ + 1) => coordinate a 0 + coordinate a 1
      | .inr (.inl r) => r • coordinate a 0
      | .inr (.inr (n, rows, code)) =>
        coordinate (op code.unpair.1 (matrixOf (m := m) (n := n) rows) a) code.unpair.2
    RelMap := fun h => nomatch h }
  let T := FirstOrder.Language.Substructure.closure L s
  let U : Submodule R M := {
    carrier := (T : Set M)
    zero_mem' := T.fun_mem (n := 0) (.inl 0 : Symbol R) Fin.elim0 (fun i => Fin.elim0 i)
    add_mem' := fun {x y} hx hy => T.fun_mem (n := 2) (.inl 1 : Symbol R)
      ![x,y] (Fin.forall_fin_two.mpr ⟨hx,hy⟩)
    smul_mem' := fun r x hx => T.fun_mem (n := 1) (.inr (.inl r) : Symbol R)
      ![x] (Fin.forall_fin_one.mpr hx) }
  refine ⟨U, FirstOrder.Language.Substructure.subset_closure, ?_, ?_⟩
  · let b := max ℵ₀ (max (Cardinal.mk R) (Cardinal.mk s))
    have hω : ℵ₀ ≤ b := le_max_left _ _
    have hr : Cardinal.mk R ≤ b := (le_max_left _ _).trans (le_max_right _ _)
    have hs : Cardinal.mk s ≤ b := (le_max_right _ _).trans (le_max_right _ _)
    have h := FirstOrder.Language.Substructure.lift_card_closure_le (L := L) (s := s)
    simp only [Cardinal.lift_id] at h
    exact h.trans (max_le hω (Cardinal.add_le_of_le hω hs
      ((symbol_bound (R := R)).trans (max_le hω hr))))
  · intro idx m n r a ha j
    have h := T.fun_mem (n := m)
      (.inr (.inr (n, rowsOf r, Nat.pair idx j.val)) : Symbol R) a ha
    change coordinate (op (Nat.pair idx j.val).unpair.1
      (matrixOf (m := m) (n := n) (rowsOf r)) a) (Nat.pair idx j.val).unpair.2 ∈ U at h
    simpa only [Nat.unpair_pair, matrixOf_rowsOf r, coordinate, dif_pos j.isLt] using h

end PureEmbeddings
