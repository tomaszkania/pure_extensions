import PureEmbeddings.GeneralLower
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Arbitrary well-ordered branching

The direct sum embeds purely into the full product. After extending its map
to the product, two different branches can be distinguished at their first
different coordinate. This also treats branches with limit-length prefixes.
-/
namespace PureEmbeddings.TransfiniteBranching
open Cardinal Function MatrixDCC GeneralLower
open scoped BigOperators
universe u
variable {R I K W : Type u} [Ring R] [AddCommGroup W] [Module R W]

/-- Finitely many constants involve only finitely many coordinates. Solutions
in the full product can be truncated to those coordinates. -/
theorem sum_to_product_pure (J : Type u) :
    IsPureMap (Finsupp.lcoeFun : (J →₀ W) →ₗ[R] (J → W)) := by
  classical
  refine ⟨DFunLike.coe_injective, ?_⟩
  rintro m n r a ⟨y,hy⟩
  let s := Finset.univ.biUnion fun i => (a i).support
  let z (j : Fin n) := Finsupp.onFinset s (fun t => if t ∈ s then y j t else 0)
    (fun t h => by by_contra hn; exact h (if_neg hn))
  refine ⟨z,fun i => Finsupp.ext fun t => ?_⟩
  have h := congrFun (hy i) t
  by_cases ht : t ∈ s
  · simpa [z,Finsupp.onFinset_apply,Finsupp.finset_sum_apply,Finset.sum_apply,ht] using h
  · have hzero : a i t = 0 := by
      apply Finsupp.notMem_support_iff.mp
      exact fun hv => ht (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩)
    simp [z,Finsupp.finset_sum_apply,ht,hzero]

private theorem product_mem {J : Type u} (L : List (Code R)) (v : J → W)
    (h : ∀ j, v j ∈ groupList L W) : v ∈ groupList L (J → W) := by
  apply (mem_groupList _).2
  intro c hc
  have localMem (j : J) : ∃ y : Fin c.cols → W,
      ∀ k, c.lead k • v j + ∑ l, c.coeff k l • y l = 0 := (mem_groupList _).1 (h j) c hc
  choose y hy using localMem
  exact ⟨fun l j => y j l, fun k => funext fun j => by
    simpa only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,Pi.zero_apply] using hy j k⟩

/-- Each witness is excluded by its own matrix conditions and belongs to
all earlier conditions. No assumption on its relation to later conditions
is required. -/
theorem branch_bound [LinearOrder I] [WellFoundedLT I] (F : ModuleCat.{u} R)
    (inj : IsPureInjective F) (L : I → List (Code R)) (w : I → W)
    (off : ∀ i j, i < j → w j ∈ groupList (L i) W)
    (out : ∀ i, w i ∉ groupList (L i) W)
    (e : ((I × K) →₀ W) →ₗ[R] F) (hp : IsPureMap e) :
    Cardinal.mk K ^ Cardinal.mk I ≤ Cardinal.mk F := by
  classical
  let J := I × K
  let incl : (J →₀ W) →ₗ[R] (J → W) := Finsupp.lcoeFun
  obtain ⟨g,hg⟩ := inj (ModuleCat.of R (J →₀ W)) (ModuleCat.of R (J → W)) incl e
    (sum_to_product_pure J)
  let path (η : I → K) : J → W := fun t => if t.2 = η t.1 then w t.1 else 0
  let point (η : I → K) := g (path η)
  have separate : Injective point := by
    intro η ν he
    by_contra hn
    have diff : {i | η i ≠ ν i}.Nonempty := by
      by_contra hempty
      apply hn
      exact funext fun j => Classical.byContradiction fun hj => hempty ⟨j,hj⟩
    obtain ⟨i,hi,earlier⟩ := wellFounded_lt.has_min _ diff
    have prior (a : I) (h : a < i) : η a = ν a := by by_contra ha; exact earlier a ha h
    let delta : J →₀ W := Finsupp.single (i,η i) (w i) - Finsupp.single (i,ν i) (w i)
    let residual := path η - path ν - incl delta
    have membrane (t : J) : residual t ∈ groupList (L i) W := by
      obtain ⟨a,k⟩ := t
      rcases lt_trichotomy a i with h | eqai | h
      · have eq := prior a h
        have hne : i ≠ a := ne_of_gt h
        simp [residual, path, incl, delta, J, Prod.mk.injEq, hne, eq]
      · subst a
        simp [residual,path,incl,delta,J,Finsupp.single_apply,Prod.mk.injEq,eq_comm]
      · have hne : i ≠ a := ne_of_lt h
        have hh := off i a h
        have hh' (v : K) : (if k = v then w a else 0) ∈ groupList (L i) W :=
          by split <;> first | exact hh | exact (groupList (L i) W).zero_mem
        simpa [residual,path,incl,delta,J,Finsupp.single_apply,Prod.mk.injEq,hne] using
          (groupList (L i) W).sub_mem (hh' (η a)) (hh' (ν a))
    have hmap := map_groupList (L i) g (product_mem (L i) residual membrane)
    have gdelta : g (incl delta) = e delta := LinearMap.congr_fun hg delta
    have same : g (path η) = g (path ν) := he
    have hdelta : e delta ∈ groupList (L i) F := by
      have hz : -(e delta) ∈ groupList (L i) F := by
        simpa only [residual,map_sub,same,sub_self,zero_sub,gdelta] using hmap
      simpa using (groupList (L i) F).neg_mem hz
    have hsource := reflect_groupList (L i) e hp hdelta
    have hproj := map_groupList (L i) (Finsupp.lapply (i,η i) : (J →₀ W) →ₗ[R] W) hsource
    exact out i (by simpa [delta,J,Finsupp.single_apply,Prod.mk.injEq,Ne.symm hi] using hproj)
  rw [Cardinal.power_def]
  exact Cardinal.mk_le_of_injective separate

/-- The extension property gives the transfinite lower bound for triangular
matrix witnesses in a module of arbitrary cardinality. -/
theorem lower [LinearOrder I] [WellFoundedLT I] (κ : Cardinal.{u})
    (hk : ℵ₀ < κ) (hr : Cardinal.mk R < κ) (hi : Cardinal.mk I ≤ κ)
    (F M : ModuleCat.{u} R) (hF : HasExtension κ F) (L : I → List (Code R)) (a : I → M)
    (earlier : ∀ i j, i < j → a j ∈ groupList (L i) M)
    (outside : ∀ i, a i ∉ groupList (L i) M) : κ ^ Cardinal.mk I ≤ Cardinal.mk F := by
  classical
  obtain ⟨W,contains,pureW,sizeW⟩ := exists_small_pureHull (R := R) (Set.range a)
  let w (i : I) : W := ⟨a i,contains ⟨i,rfl⟩⟩
  have hW : Cardinal.mk W ≤ κ := sizeW.trans (max_le hk.le (max_le hr.le (Cardinal.mk_range_le.trans hi)))
  let J := I × κ.out
  have hj : Cardinal.mk J ≤ κ := by
    rw [show Cardinal.mk J = Cardinal.mk I * κ by simp [J,Cardinal.mk_prod]]
    exact (mul_le_mul' hi le_rfl).trans_eq (Cardinal.mul_eq_self hk.le)
  have hs : Cardinal.mk (J →₀ W) ≤ κ := by
    calc
      _ ≤ Cardinal.mk (Finset (J × W)) := Cardinal.mk_le_of_injective (Finsupp.graph_injective _ _)
      _ ≤ Cardinal.mk (List (J × W)) := Cardinal.mk_le_of_surjective List.toFinset_surjective
      _ ≤ max ℵ₀ (Cardinal.mk (J × W)) := Cardinal.mk_list_le_max _
      _ ≤ κ := max_le hk.le (by
        rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id]
        exact (mul_le_mul' hj hW).trans_eq (Cardinal.mul_eq_self hk.le))
  obtain ⟨e,he⟩ := hF.universal_le hk hr (ModuleCat.of R (J →₀ W)) hs
  have h := branch_bound F (hF.pureInjective hk hr) L w
    (fun i j h => reflect_groupList _ W.subtype pureW (earlier i j h))
    (fun i hm => outside i (map_groupList _ W.subtype hm)) e he
  simpa only [Cardinal.mk_out] using h

end PureEmbeddings.TransfiniteBranching
