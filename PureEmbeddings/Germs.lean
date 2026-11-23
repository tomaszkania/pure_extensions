import PureEmbeddings.ModuleTheory
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.AtTopBot.Finset

/-! A reduced power construction for algebraic compactness. Arbitrary systems
are presented as families of equations, each with finitely many terms. -/
namespace PureEmbeddings.Germs

open Filter
open scoped BigOperators

universe u
variable {R M ι E V : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- Passing from functions to germs is linear. -/
def ofFunLinear (l : Filter ι) : (ι → M) →ₗ[R] Germ l M where
  toFun := Germ.ofFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The constant-germ diagonal. -/
def diagonal (l : Filter ι) : M →ₗ[R] Germ l M where
  toFun := Germ.const
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem ofFun_sum {n : ℕ} (l : Filter ι) (r : Fin n → R)
    (y : Fin n → ι → M) :
    (ofFunLinear (R := R) l) (fun i => ∑ j, r j • y j i) =
      ∑ j, r j • ofFunLinear (R := R) l (y j) := by
  have hf : (fun i => ∑ j, r j • y j i) = ∑ j, r j • y j := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [hf, map_sum]
  simp only [map_smul]

theorem diagonal_pure (l : Filter ι) [l.NeBot] :
    IsPureMap (diagonal (R := R) (M := M) l) := by
  constructor
  · intro x y h
    have he : (fun _ : ι => x) =ᶠ[l] (fun _ => y) := Germ.coe_eq.mp h
    exact he.exists.choose_spec
  · intro m n r a hs
    obtain ⟨g, hg⟩ := hs
    have reps (j : Fin n) : ∃ f : ι → M, ofFunLinear (R := R) l f = g j :=
      Germ.inductionOn (p := fun z => ∃ f : ι → M, ofFunLinear (R := R) l f = z)
        (g j) fun f => ⟨f, rfl⟩
    choose f hf using reps
    have he (i : Fin m) : ∀ᶠ d in l, ∑ j, r i j • f j d = a i := by
      apply Germ.coe_eq.mp
      change ofFunLinear (R := R) l (fun d => ∑ j, r i j • f j d) = _
      rw [ofFun_sum]
      simpa only [hf] using hg i
    have hh : ∀ᶠ d in l, ∀ i, ∑ j, r i j • f j d = a i :=
      Filter.eventually_all.mpr he
    obtain ⟨d, hd⟩ := hh.exists
    exact ⟨fun j => f j d, hd⟩

/-- A row-finite system of linear equations. Coordinates may occur repeatedly
in a row. -/
structure System (R M E V : Type u) where
  width : E → ℕ
  coeff : (i : E) → Fin (width i) → R
  var : (i : E) → Fin (width i) → V
  rhs : E → M

def System.Holds (s : System R M E V) (x : V → M) (i : E) : Prop :=
  ∑ j, s.coeff i j • x (s.var i j) = s.rhs i

def System.FinitelySoluble (s : System R M E V) : Prop :=
  ∀ a : Finset E, ∃ x : V → M, ∀ i ∈ a, s.Holds x i

/-- A simultaneous solution in the germs along finite sets of equations. -/
theorem in_germs (s : System R M E V) (hs : s.FinitelySoluble) :
    ∃ x : V → Germ (atTop : Filter (Finset E)) M, ∀ i,
      ∑ j, s.coeff i j • x (s.var i j) =
        diagonal (R := R) (atTop : Filter (Finset E)) (s.rhs i) := by
  classical
  choose localSol hlocal using hs
  let l : Filter (Finset E) := atTop
  refine ⟨fun v => ofFunLinear (R := R) l (fun a => localSol a v), ?_⟩
  intro i
  rw [← ofFun_sum]
  apply Germ.coe_eq.mpr
  apply (eventually_ge_atTop ({i} : Finset E)).mono
  intro a h
  exact hlocal a i (h (Finset.mem_singleton_self i))

/-- Pure-injectivity gives simultaneous solutions of all finitely soluble
systems, even when the equation and variable sets are infinite. -/
theorem algebraically_compact {F : ModuleCat.{u} R} (hF : IsPureInjective F)
    (s : System R F E V) (hs : s.FinitelySoluble) :
    ∃ x : V → F, ∀ i, s.Holds x i := by
  classical
  let l : Filter (Finset E) := atTop
  have hp := diagonal_pure (R := R) (M := F) l
  obtain ⟨ret, hret⟩ := hF F (ModuleCat.of R (Germ l F)) (diagonal l) LinearMap.id hp
  obtain ⟨x, hx⟩ := in_germs s hs
  refine ⟨fun v => ret (x v), ?_⟩
  intro i
  have he := congrArg ret (hx i)
  have hr : ret (diagonal l (s.rhs i)) = s.rhs i :=
    DFunLike.congr_fun hret (s.rhs i)
  change ∑ j, s.coeff i j • ret (x (s.var i j)) = _
  exact (by simpa only [map_sum, map_smul] using he : _ = ret (diagonal l (s.rhs i))).trans hr

/-- The one-variable cosets of the images of specified finite coefficient
rows meet whenever each finite subfamily meets. Private variables for
different equations are independent. -/
theorem coefficient_cosets_of_solver {F : ModuleCat.{u} R}
    (n : E → ℕ) (r : (i : E) → Fin (n i) → R) (c : E → F)
    (solve : ∀ s : System R F E (Option ((i : E) × Fin (n i))),
      s.FinitelySoluble → ∃ x, ∀ i, s.Holds x i)
    (hs : ∀ a : Finset E, ∃ z : F, ∀ i ∈ a,
      ∃ y : Fin (n i) → F, z - c i = ∑ j, r i j • y j) :
    ∃ z : F, ∀ i, ∃ y : Fin (n i) → F, z - c i = ∑ j, r i j • y j := by
  classical
  let Var := Option ((i : E) × Fin (n i))
  let s : System R F E Var :=
    { width := fun i => n i + 1
      coeff := fun i => Fin.cases 1 (fun j => -r i j)
      var := fun i => Fin.cases none (fun j => some ⟨i,j⟩)
      rhs := c }
  have row (v : Var → F) (i : E) : s.Holds v i ↔
      v none - c i = ∑ j, r i j • v (some ⟨i,j⟩) := by
    simp only [s, System.Holds, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      one_smul, neg_smul, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_iff_eq_add]
    rw [add_comm]
  have finiteRows : s.FinitelySoluble := by
    intro a
    obtain ⟨z, hz⟩ := hs a
    let privateVars (i : E) : Fin (n i) → F :=
      if h : i ∈ a then Classical.choose (hz i h) else 0
    let v : Var → F
      | none => z
      | some ⟨i,j⟩ => privateVars i j
    refine ⟨v, fun i hi => (row v i).2 ?_⟩
    simpa only [v, privateVars, dif_pos hi] using Classical.choose_spec (hz i hi)
  obtain ⟨v, hv⟩ := solve s finiteRows
  exact ⟨v none, fun i => ⟨_, (row v i).1 (hv i)⟩⟩

theorem coefficient_cosets {F : ModuleCat.{u} R} (hF : IsPureInjective F)
    (n : E → ℕ) (r : (i : E) → Fin (n i) → R) (c : E → F)
    (hs : ∀ a : Finset E, ∃ z : F, ∀ i ∈ a,
      ∃ y : Fin (n i) → F, z - c i = ∑ j, r i j • y j) :
    ∃ z : F, ∀ i, ∃ y : Fin (n i) → F, z - c i = ∑ j, r i j • y j :=
  coefficient_cosets_of_solver n r c (algebraically_compact hF) hs

end PureEmbeddings.Germs
