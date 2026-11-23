import PureEmbeddings.CountableCompactness
import PureEmbeddings.CriterionMathlib
import Mathlib.SetTheory.Cardinal.Regular

/-! A generalisation of the pure-injectivity part of the supported-product
calculation. The index set may have any cardinality, and the scalar ring may
be noncommutative or uncountable. -/
namespace PureEmbeddings.SupportedModules
open Cardinal Set
universe u
variable {R I : Type u} [Ring R] (C : I → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]

/-- Every element is zero away from a set of fewer than κ coordinates. -/
def supported (κ : Cardinal.{u}) (hk : ℵ₀ ≤ κ) : Submodule R ((i : I) → C i) where
  carrier := {x | #({i : I | x i ≠ 0} : Set I) < κ}
  zero_mem' := by simpa using aleph0_pos.trans_le hk
  add_mem' := by
    intro x y hx hy
    have h : {i : I | x i + y i ≠ 0} ⊆ {i : I | x i ≠ 0} ∪ {i : I | y i ≠ 0} := by
      intro i hi
      by_contra hn
      have hx0 : x i = 0 := by simpa using fun h => hn (Or.inl h)
      have hy0 : y i = 0 := by simpa using fun h => hn (Or.inr h)
      exact hi (by simp [hx0,hy0])
    exact (mk_le_mk_of_subset h).trans_lt ((mk_union_le _ _).trans_lt (add_lt_of_lt hk hx hy))
  smul_mem' r x hx := by
    have h : {i : I | r • x i ≠ 0} ⊆ {i : I | x i ≠ 0} := by
      intro i hi he
      exact hi (by simp [he])
    exact (mk_le_mk_of_subset h).trans_lt hx

private theorem solve_on_support {κ : Cardinal.{u}} (hk : ℵ₀ ≤ κ)
    (hp : ∀ i, IsPureInjective (ModuleCat.of R (C i))) {E V : Type u} (hE : #E < κ.ord.cof)
    (s : Germs.System R (supported (R := R) C κ hk) E V) (hs : s.FinitelySoluble) :
    ∃ x, ∀ e, s.Holds x e := by
  classical
  let P := supported (R := R) C κ hk
  let ev (i : I) : P →ₗ[R] C i := (LinearMap.proj i).comp P.subtype
  let t (i : I) : Germs.System R (C i) E V :=
    { width := s.width, coeff := s.coeff, var := s.var, rhs := fun e => ev i (s.rhs e) }
  have solvable (i : I) : (t i).FinitelySoluble := by
    intro a
    obtain ⟨z,hz⟩ := hs a
    refine ⟨fun v => ev i (z v), fun e he => ?_⟩
    simpa only [t,Germs.System.Holds,map_sum,map_smul] using congrArg (ev i) (hz e he)
  choose y hy using fun i => Germs.algebraically_compact (hp i) (t i) (solvable i)
  let S (e : E) : Set I := {i | ev i (s.rhs e) ≠ 0}
  have small (e : E) : #(S e) < κ := (s.rhs e).property
  let J := ⋃ e, S e
  have hJ : #J < κ := (mk_iUnion_le S).trans_lt <| mul_lt_of_lt hk
    (hE.trans_le (Ordinal.cof_ord_le κ)) (Ordinal.iSup_lt hE small)
  let z (v : V) := fun i => if i ∈ J then y i v else 0
  let x (v : V) : P := ⟨z v,(mk_le_mk_of_subset (show {i : I | z v i ≠ 0} ⊆ J from by
    intro i hi; by_contra off; exact hi (by simp [z,off]))).trans_lt hJ⟩
  refine ⟨x, fun e => Subtype.ext (funext fun i => ?_)⟩
  change (ev i) (∑ j, s.coeff e j • x (s.var e j)) = ev i (s.rhs e)
  simp only [map_sum,map_smul]
  have entry (v : V) : ev i (x v) = (if i ∈ J then y i v else 0) := rfl
  by_cases mem : i ∈ J
  · simpa only [entry,if_pos mem] using (show ∑ j, s.coeff e j • y i (s.var e j) = ev i (s.rhs e) from hy i e)
  · have zero : ev i (s.rhs e) = 0 := by
      by_contra hn; exact mem (Set.mem_iUnion.mpr ⟨e,hn⟩)
    simp [entry,mem,zero]

/-- A product with supports of size less than κ of pure-injective left R-modules
is pure-injective whenever `max ℵ₀ |R| < cf κ`. -/
theorem supported_pureInjective (κ : Cardinal.{u}) (hk : ℵ₀ ≤ κ)
    (hcof : max ℵ₀ (#R) < κ.ord.cof) (hp : ∀ i, IsPureInjective (ModuleCat.of R (C i))) :
    IsPureInjective (ModuleCat.of R (supported (R := R) C κ hk)) := by
  apply pureInjective_of_solver
  intro E V s hs
  apply MatrixDCC.solve_of_cosets _ s hs
  intro J codes c fip
  apply MatrixDCC.cosets_of_code_solver _ codes c fip
  intro K t ht
  apply solve_on_support C hk hp _ t ht
  let μ := max ℵ₀ (#R)
  have hω : ℵ₀ ≤ μ := le_max_left _ _
  have hR : #R ≤ μ := le_max_right _ _
  let pack (q : MatrixDCC.Code R) : EquationCriterion.EquationCode R R :=
    ⟨q.rows,q.cols,q.coeff,q.lead⟩
  let unpack : EquationCriterion.EquationCode R R → MatrixDCC.Code R :=
    fun ⟨m,n,a,b⟩ => ⟨m,n,b,a⟩
  have hCode : #(MatrixDCC.Code R) ≤ μ := (mk_le_of_injective
    (show Function.LeftInverse unpack pack from fun _ => rfl).injective).trans
      (EquationCriterion.systemCardinal_le μ hω hR hR)
  have hK : #K ≤ μ := (mk_subtype_le _).trans hCode
  have hrow : #((k : K) × Fin k.val.rows) ≤ μ := by
    let pair (a : (k : K) × Fin k.val.rows) : K × ℕ := (a.1,a.2.val)
    have inj : Function.Injective pair := by
      rintro ⟨k,r⟩ ⟨k',r'⟩ h
      have e : k = k' := congrArg Prod.fst h
      subst k'
      have d : r = r' := Fin.ext (congrArg Prod.snd h)
      cases d
      rfl
    apply (Cardinal.mk_le_of_injective inj).trans
    simpa only [Cardinal.mk_prod,Cardinal.mk_nat,Cardinal.lift_aleph0,Cardinal.lift_uzero] using
      (mul_le_mul' hK hω).trans_eq (Cardinal.mul_eq_self hω)
  exact hrow.trans_lt hcof

end PureEmbeddings.SupportedModules
