import PureEmbeddings.GroupFactors
import PureEmbeddings.AlgebraicCompactness
import PureEmbeddings.PureInjectivity
import PureEmbeddings.CountableCompactness
import PureEmbeddings.MatrixCompact

/-! The countable congruences in the supported group preclude the extension property. -/
namespace PureEmbeddings.Groups
open Cardinal

/-- On a family with fewer than `cf κ` equations, solutions in the factor
groups can be assembled inside the supported product. The number of variables
is unrestricted. -/
theorem solve_in_supported_product {I E V : Type} (κ : Cardinal.{0}) (hκ : ℵ₀ ≤ κ)
    (C : I → Type) [∀ i, AddCommGroup (C i)] (hE : #E < κ.ord.cof)
    (solve : ∀ (i : I) (s : Germs.System ℤ (C i) E V), s.FinitelySoluble →
      ∃ x, ∀ e, s.Holds x e)
    (s : Germs.System ℤ (supportedProduct κ hκ C) E V) (hs : s.FinitelySoluble) :
    ∃ x, ∀ e, s.Holds x e := by
  classical
  let P := supportedProduct κ hκ C
  let ev (i : I) : P →ₗ[ℤ] C i :=
    AddMonoidHom.toIntLinearMap { toFun := fun x => x.val i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let t (i : I) : Germs.System ℤ (C i) E V :=
    {width := s.width, coeff := s.coeff, var := s.var, rhs := fun e => ev i (s.rhs e)}
  have localSol (i : I) : (t i).FinitelySoluble := by
    intro K
    obtain ⟨z,hz⟩ := hs K
    refine ⟨fun v => ev i (z v), fun j hj => ?_⟩
    simpa only [t, Germs.System.Holds, map_sum, map_smul] using congrArg (ev i) (hz j hj)
  choose y hy using fun i => solve i (t i) (localSol i)
  obtain ⟨J,hJ,cover⟩ := common_support_below_cofinality κ hκ C E hE s.rhs
  let x (v : V) : P := extendBlock κ hκ C J hJ (fun j => y j.val v)
  have eval_x (v : V) (j : J) : ev j.val (x v) = y j.val v := by
    exact congrFun (full_coordinate_product_splits κ hκ C J hJ (fun k => y k.val v)) j
  have eval_off (v : V) (i : I) (hi : i ∉ J) : ev i (x v) = 0 := by
    exact extendBlock_off κ hκ C J hJ (fun j => y j.val v) hi
  refine ⟨x, fun e => ?_⟩
  change (∑ j, s.coeff e j • x (s.var e j)) = s.rhs e
  apply Subtype.ext
  funext i
  change ev i _ = ev i _
  rw [map_sum]
  simp only [map_smul]
  by_cases hi : i ∈ J
  · have on (v : V) := eval_x v ⟨i,hi⟩
    simp only [on]
    exact hy i e
  · have rhs0 : ev i (s.rhs e) = 0 := by
      by_contra h
      exact hi (cover e h)
    simp [fun v => eval_off v i hi, rhs0]

/-- The positive half at the level of small systems. Over the integers all
countable systems qualify as soon as κ has uncountable cofinality. -/
theorem kostana_solves_below_cofinality {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) {E V : Type}
    (hE : #E < κ.ord.cof) (s : Germs.System ℤ (kostanaGroup κ hκ) E V)
    (hs : s.FinitelySoluble) : ∃ x, ∀ e, s.Holds x e :=
  solve_in_supported_product κ hκ (fun i : κ.ord.toType × FactorIndex => factor i.2) hE
    (fun i => factor_solves i.2) s hs

/-- On an unrestricted product each system is solved independently at each coordinate. -/
theorem factors_product_pureInjective {I : Type} (t : I → FactorIndex) :
    IsPureInjective (ModuleCat.of ℤ ((i : I) → factor (t i))) := by
  apply pureInjective_of_solver
  intro E V s hs
  let P := (i : I) → factor (t i)
  let ev (i : I) : P →ₗ[ℤ] factor (t i) := LinearMap.proj i
  let U (i : I) : Germs.System ℤ (factor (t i)) E V :=
    { width := s.width, coeff := s.coeff, var := s.var, rhs := fun e => ev i (s.rhs e) }
  have fip (i : I) : (U i).FinitelySoluble := by
    intro K
    obtain ⟨x,hx⟩ := hs K
    refine ⟨fun v => ev i (x v), fun e he => ?_⟩
    simpa only [U, Germs.System.Holds, map_sum, map_smul] using congrArg (ev i) (hx e he)
  choose y hy using fun i => factor_solves (t i) (U i) (fip i)
  refine ⟨fun v i => y i v, fun e => ?_⟩
  change ∑ j, s.coeff e j • (fun i => y i (s.var e j)) = _
  funext i
  simpa only [Finset.sum_apply, Pi.smul_apply] using hy i e

/-- Kostana's supported group is pure-injective exactly at uncountable cofinality. -/
theorem kostana_pureInjective_iff {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) :
    IsPureInjective (ModuleCat.of ℤ (kostanaGroup κ hκ)) ↔ ℵ₀ < κ.ord.cof := by
  constructor
  · intro hpi
    apply lt_of_le_of_ne (Ordinal.aleph0_le_cof.mpr (Cardinal.isSuccLimit_ord hκ))
    intro hc
    obtain ⟨s,fin,bad⟩ := kostana_unsolvable_congruences κ hκ hc.symm
    let n (_ : ℕ) := 1
    let r (m : ℕ) (_ : Fin (n m)) := ((2^m : ℕ) : ℤ)
    obtain ⟨x,hx⟩ := Germs.coefficient_cosets hpi n r s (by
      intro t
      obtain ⟨z,hz⟩ := fin t
      refine ⟨z, fun i hi => ?_⟩
      obtain ⟨y,hy⟩ := hz i hi
      refine ⟨fun _ => y, ?_⟩
      simpa only [n,r,Fin.sum_univ_one,natCast_zsmul,sub_eq_iff_eq_add,add_comm] using hy)
    apply bad
    refine ⟨x, fun i => ?_⟩
    obtain ⟨y,hy⟩ := hx i
    exact ⟨y 0, by simpa only [n,r,Fin.sum_univ_one,natCast_zsmul,sub_eq_iff_eq_add,add_comm] using hy⟩
  · intro hc
    apply MatrixDCC.pureInjective_iff_countable_solver.mpr
    intro E V _ _ t ht
    exact kostana_solves_below_cofinality hκ (Cardinal.mk_le_aleph0.trans_lt hc) t ht

theorem kostana_extension_cofinality {κ : Cardinal.{0}} (hκ : ℵ₀ < κ)
    (hE : HasExtension (R := ℤ) κ (ModuleCat.of ℤ (kostanaGroup κ hκ.le))) :
    ℵ₀ < κ.ord.cof :=
  (kostana_pureInjective_iff hκ.le).mp (hE.pureInjective hκ (Cardinal.mk_le_aleph0.trans_lt hκ))

/-- At an uncountable cardinal of countable cofinality, Kostana's group fails (Eκ). -/
theorem kostana_not_extension {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) (hc : κ.ord.cof = ℵ₀) :
    ¬ HasExtension (R := ℤ) κ (ModuleCat.of ℤ (kostanaGroup κ hκ.le)) :=
  fun hE => (kostana_extension_cofinality hκ hE).ne' hc

end PureEmbeddings.Groups
