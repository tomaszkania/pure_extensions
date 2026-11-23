import PureEmbeddings.CriterionMathlib
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The minimum over a left pure-semisimple ring

We give a presentation of a single module that maps by a pure quotient onto
every module of size at most κ. Its generators consist of κ copies of each
finite homogeneous matrix presentation. Splitting the pure kernel then gives
a split embedding in the opposite direction.
-/

noncomputable section

namespace PureEmbeddings.PureSemisimple
open Cardinal Function
open scoped BigOperators

universe u
variable {R : Type u} [Ring R]

private abbrev Code (R : Type u) := EquationCriterion.EquationCode R R
private abbrev Atom (R I : Type u) := Code R × I × ℕ
private abbrev Free (R I : Type u) [Ring R] := Atom R I →₀ R

private def row {I : Type u} (t : Code R) (k : I) (i : Fin t.1) : Free R I :=
  ∑ j : Fin t.2.1, t.2.2.1 i j • Finsupp.single (t,k,j.val) (1 : R)

private def relations (R I : Type u) [Ring R] : Submodule R (Free R I) :=
  Submodule.span R {v | ∃ (t : Code R) (k : I) (i : Fin t.1), v = row t k i}

private abbrev Target (R I : Type u) [Ring R] := Free R I ⧸ relations R I

private def generator {I : Type u} (t : Code R) (k : I) (j : Fin t.2.1) : Target R I :=
  (relations R I).mkQ (Finsupp.single (t,k,j.val) (1 : R))

private theorem generator_relation {I : Type u} (t : Code R) (k : I) (i : Fin t.1) :
    ∑ j : Fin t.2.1, t.2.2.1 i j • generator t k j = 0 := by
  have hz : (relations R I).mkQ (row t k i) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨t,k,i,rfl⟩
  simpa only [row, map_sum, map_smul, generator] using hz

private theorem target_size (κ : Cardinal.{u}) (hω : ℵ₀ ≤ κ) (hr : Cardinal.mk R ≤ κ) :
    Cardinal.mk (Target R κ.out) ≤ κ := by
  classical
  letI : Infinite κ.out := Cardinal.aleph0_le_mk_iff.mp ((Cardinal.mk_out κ).symm ▸ hω)
  letI : Nonempty (Code R) := ⟨⟨0, 0, fun _ _ => 0, fun _ => 0⟩⟩
  have hc : Cardinal.mk (Code R) ≤ κ := EquationCriterion.systemCardinal_le κ hω hr hr
  have hi : Cardinal.mk (κ.out × ℕ) ≤ κ := by
    simp only [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_out, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact (mul_le_mul' le_rfl hω).trans_eq (Cardinal.mul_eq_self hω)
  have ha : Cardinal.mk (Atom R κ.out) ≤ κ := by
    change Cardinal.mk (Code R × (κ.out × ℕ)) ≤ κ
    simp only [Cardinal.mk_prod, Cardinal.lift_id] at *
    exact (mul_le_mul' hc hi).trans_eq (Cardinal.mul_eq_self hω)
  have hfree : Cardinal.mk (Free R κ.out) ≤ κ := by
    calc
      _ ≤ Cardinal.mk (Finset (Atom R κ.out × R)) :=
        Cardinal.mk_le_of_injective (Finsupp.graph_injective _ _)
      _ = Cardinal.mk (Atom R κ.out × R) := Cardinal.mk_finset_of_infinite _
      _ ≤ κ := by
        rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
        exact (mul_le_mul' ha hr).trans_eq (Cardinal.mul_eq_self hω)
  exact (Cardinal.mk_le_of_surjective (relations R κ.out).mkQ_surjective).trans hfree

/-- Every homogeneous finite system can be lifted together with its solution. -/
private def HomogeneousLifting {P M : ModuleCat.{u} R} (p : P →ₗ[R] M) : Prop :=
  ∀ {m n : ℕ} (r : Fin m → Fin n → R) (y : Fin n → M),
    (∀ i, ∑ j, r i j • y j = 0) →
      ∃ z : Fin n → P, (∀ i, ∑ j, r i j • z j = 0) ∧ ∀ j, p (z j) = y j

private abbrev Solutions (t : Code R) (M : ModuleCat.{u} R) :=
  {y : Fin t.2.1 → M // ∀ i : Fin t.1, ∑ j, t.2.2.1 i j • y j = 0}

private theorem quotientOnto (κ : Cardinal.{u}) (hω : ℵ₀ ≤ κ)
    (M : ModuleCat.{u} R) (hm : Cardinal.mk M ≤ κ) :
    ∃ p : Target R κ.out →ₗ[R] M,
      HomogeneousLifting (P := ModuleCat.of R (Target R κ.out)) (M := M) p := by
  classical
  have numbered (t : Code R) : ∃ f : κ.out → Solutions t M, Surjective f := by
    have hsize : Cardinal.mk (Solutions t M) ≤ Cardinal.mk κ.out := by
      rw [Cardinal.mk_out]
      apply (Cardinal.mk_le_of_injective Subtype.val_injective).trans
      rw [Cardinal.mk_arrow, Cardinal.lift_mk_fin, Cardinal.lift_uzero]
      exact (Cardinal.power_le_power_right hm).trans (Cardinal.power_nat_le hω)
    obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hsize
    letI : Nonempty (Solutions t M) := ⟨⟨fun _ => 0, fun _ => by simp⟩⟩
    exact ⟨invFun e, (leftInverse_invFun e.injective).surjective⟩
  choose enum onto using numbered
  let value : Atom R κ.out → M := fun a =>
    if h : a.2.2 < a.1.2.1 then (enum a.1 a.2.1).1 ⟨a.2.2,h⟩ else 0
  let f := Finsupp.linearCombination R value
  have annihilates : relations R κ.out ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,k,i,rfl⟩
    change f (row t k i) = 0
    simpa [row, f, value, map_sum, Finsupp.linearCombination_single] using (enum t k).2 i
  let p := (relations R κ.out).liftQ f annihilates
  refine ⟨p, ?_⟩
  intro m n r y hy
  let t : Code R := ⟨m,n,r,fun _ => 0⟩
  let b : Solutions t M := ⟨y,hy⟩
  obtain ⟨k,hk⟩ := onto t b
  refine ⟨generator t k, generator_relation t k, fun j => ?_⟩
  have he : (enum t k).1 j = y j := congrArg (fun w : Solutions t M => w.1 j) hk
  change f (Finsupp.single (t,k,j.val) 1) = y j
  have hj : (j : ℕ) < t.2.1 := j.isLt
  simpa [f, Finsupp.linearCombination_single, value, hj] using he

private theorem kernelPure {P M : ModuleCat.{u} R} (p : P →ₗ[R] M)
    (h : HomogeneousLifting p) : IsPureMap (LinearMap.ker p).subtype := by
  refine ⟨Subtype.val_injective, ?_⟩
  intro m n r a sol
  obtain ⟨x,hx⟩ := sol
  have zeroImage (i : Fin m) : ∑ j, r i j • p (x j) = 0 := by
    simpa [map_sum] using (congrArg p (hx i)).trans (a i).property
  obtain ⟨z,hz,hp⟩ := h r (fun j => p (x j)) zeroImage
  let k (j : Fin n) : LinearMap.ker p := ⟨x j - z j, by simp [LinearMap.mem_ker, hp j]⟩
  refine ⟨k, fun i => Subtype.ext ?_⟩
  change (LinearMap.ker p).subtype (∑ j, r i j • k j) = (a i).val
  simp only [map_sum, map_smul, Submodule.subtype_apply, k, smul_sub,
    Finset.sum_sub_distrib, hx, hz, sub_zero]
  rfl

/-- A fixed module of size at most κ contains every module of size at most κ
as a direct summand over a left pure-semisimple ring. -/
theorem splitUniversal (κ : Cardinal.{u}) (hω : ℵ₀ ≤ κ) (hr : Cardinal.mk R ≤ κ)
    (hs : LeftPureSemisimple.{u} R) :
    ∃ P : ModuleCat.{u} R, Cardinal.mk P ≤ κ ∧
      ∀ M : ModuleCat.{u} R, Cardinal.mk M ≤ κ →
        ∃ (s : M →ₗ[R] P) (p : P →ₗ[R] M), LeftInverse p s := by
  let P := ModuleCat.of R (Target R κ.out)
  refine ⟨P, target_size κ hω hr, ?_⟩
  intro M hm
  obtain ⟨p,h⟩ := quotientOnto κ hω M hm
  have onto : Surjective p := by
    intro b
    obtain ⟨z,_,hz⟩ := h (m := 0) (n := 1) (fun i _ => Fin.elim0 i) (fun _ => b) (fun i => Fin.elim0 i)
    exact ⟨z 0, hz 0⟩
  obtain ⟨r,hr⟩ := hs (ModuleCat.of R (LinearMap.ker p)) P _ (kernelPure (P := P) (M := M) p h)
  let ex := p.exact_subtype_ker_map
  let split := ex.splitInjectiveEquiv onto ⟨r, LinearMap.ext hr⟩
  let sec := (ex.splitSurjectiveEquiv (LinearMap.ker p).injective_subtype).symm split
  exact ⟨sec.1,p,LinearMap.congr_fun sec.2⟩

/-- The least possible cardinality in the pure-semisimple branch of Theorem A. -/
theorem minimum [Nontrivial R] (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hr : Cardinal.mk R < κ)
    (hs : LeftPureSemisimple.{u} R) : HasMinimum (R := R) κ κ := by
  apply hasMinimum_of_bounds (fun _ h => h.lower hω.le hr)
  obtain ⟨P,size,universal⟩ := splitUniversal κ hω.le hr.le hs
  refine ⟨P, ?_, size⟩
  apply EquationCriterion.extension_of_pureInjective_and_universal κ hω hr P (leftPureSemisimple_iff.mp hs P)
  intro M hm
  obtain ⟨s,p,h⟩ := universal M hm
  exact ⟨s,isPureMap_of_retraction s p h⟩

end PureEmbeddings.PureSemisimple
