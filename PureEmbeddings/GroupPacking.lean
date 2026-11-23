import PureEmbeddings.GroupExtension
import PureEmbeddings.CriterionMathlib

/-! Copies of a small pure embedding can be placed on disjoint coordinate blocks. -/
namespace PureEmbeddings.Groups
open Cardinal Set

private noncomputable def reindexZero {T I : Type} (e : T ↪ I) (C : I → Type) [∀ i, Zero (C i)]
    (x : (t : T) → C (e t)) (i : I) : C i := by
  classical
  exact if h : i ∈ Set.range e then (h.choose_spec ▸ x h.choose) else 0

private theorem reindex_at {T I : Type} (e : T ↪ I) (C : I → Type) [∀ i, Zero (C i)]
    (x : (t : T) → C (e t)) (t : T) : reindexZero e C x (e t) = x t := by
  have h : e t ∈ Set.range e := Set.mem_range_self t
  have eq : h.choose = t := e.injective h.choose_spec
  simp only [reindexZero, dif_pos h]
  exact eq_of_heq ((eqRec_heq _ _).trans (by rw [eq]))

private theorem reindex_out {T I : Type} (e : T ↪ I) (C : I → Type) [∀ i, Zero (C i)]
    (x : (t : T) → C (e t)) (i : I) (h : i ∉ Set.range e) : reindexZero e C x i = 0 := by
  simp [reindexZero, h]

/-- Replicate a pure embedding in a product on fewer than κ coordinates.
The resulting direct sum of κ copies is pure in the supported product. -/
theorem pack_pure_copies {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) {M : ModuleCat.{0} ℤ}
    {T : Type} (t : T → FactorIndex) (ht : #T < κ)
    (f : M →ₗ[ℤ] ((j : T) → factor (t j))) (hf : IsPureMap f) :
    ∃ g : (κ.ord.toType →₀ M) →ₗ[ℤ] kostanaGroup κ hκ, IsPureMap g := by
  classical
  let W := κ.ord.toType
  let I := W × FactorIndex
  let C (i : I) := factor i.2
  have hb : #(W × T) ≤ #W := by
    simp only [W,Cardinal.mk_prod,Cardinal.lift_id,Cardinal.mk_ord_toType]
    exact (Cardinal.mul_le_max_of_aleph0_le_left hκ).trans (max_le le_rfl ht.le)
  obtain ⟨pair⟩ := hb
  let e : W × T ↪ I := ⟨fun wt => (pair wt,t wt.2), fun _ _ h => pair.injective (congrArg Prod.fst h)⟩
  let fill (x : W →₀ M) := reindexZero e C (fun wt => f (x wt.1) wt.2)
  have get (x : W →₀ M) (w : W) (j : T) : fill x (e (w,j)) = f (x w) j :=
    reindex_at e C _ (w,j)
  have off (x : W →₀ M) (i : I) (hi : i ∉ Set.range e) : fill x i = 0 := reindex_out e C _ i hi
  have small (x : W →₀ M) : #(support (fill x)) < κ := by
    let J := (x.support : Set W) ×ˢ (Set.univ : Set T)
    have incl : support (fill x) ⊆ e '' J := by
      intro i hi
      by_cases im : i ∈ Set.range e
      · obtain ⟨⟨w,j⟩,rfl⟩ := im
        refine ⟨(w,j), ⟨Finsupp.mem_support_iff.mpr ?_, Set.mem_univ _⟩, rfl⟩
        intro hz
        exact hi (by rw [get, hz, map_zero]; rfl)
      · exact False.elim (hi (off x i im))
    refine (Cardinal.mk_le_mk_of_subset incl).trans_lt (Cardinal.mk_image_le.trans_lt ?_)
    rw [Cardinal.mk_setProd, Cardinal.mk_univ]
    exact Cardinal.mul_lt_of_lt hκ ((Cardinal.lt_aleph0_of_finite (↑x.support : Type)).trans_le hκ) ht
  let g : (W →₀ M) →ₗ[ℤ] kostanaGroup κ hκ :=
    { toFun := fun x => ⟨fill x,small x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        funext i
        change fill (x+y) i = fill x i + fill y i
        by_cases im : i ∈ Set.range e
        · obtain ⟨⟨w,j⟩,rfl⟩ := im; simp only [get,Finsupp.add_apply,map_add,Pi.add_apply]
        · simp [off, im]
      map_smul' := by
        intro r x
        apply Subtype.ext
        funext i
        change fill (r • x) i = r • fill x i
        by_cases im : i ∈ Set.range e
        · obtain ⟨⟨w,j⟩,rfl⟩ := im; simp only [get,Finsupp.smul_apply,map_smul,Pi.smul_apply]
        · simp [off, im] }
  have evaluates (w : W) : ∃ l : kostanaGroup κ hκ →ₗ[ℤ] ((j:T) → factor (t j)),
      ∀ x, l (g x) = f (x w) := by
    let l : kostanaGroup κ hκ →ₗ[ℤ] ((j:T) → factor (t j)) :=
      AddMonoidHom.toIntLinearMap { toFun := fun x j => x.val (e (w,j)), map_zero' := rfl, map_add' := fun _ _ => rfl }
    exact ⟨l, fun x => funext fun j => get x w j⟩
  choose l hl using evaluates
  refine ⟨g, ⟨fun x y h => Finsupp.ext (fun w => hf.1 ((hl w x).symm.trans ((congrArg (l w) h).trans (hl w y)))), ?_⟩⟩
  intro m n r a sol
  have localSol (w : W) : Soluble r (fun i => a i w) := by
    apply hf.2
    have same : (l w) ∘ (g ∘ a) = f ∘ (fun i => a i w) := funext fun i => hl w (a i)
    exact same ▸ sol.map (l w)
  choose y hy using localSol
  let S : Finset W := Finset.univ.biUnion fun i => (a i).support
  let z (j : Fin n) : W →₀ M :=
    Finsupp.onFinset S (fun w => if w ∈ S then y w j else 0) (by intro w h; by_contra hn; simp [hn] at h)
  refine ⟨z, fun i => Finsupp.ext (fun w => ?_)⟩
  change (Finsupp.lapply (R := ℤ) w) (∑ j, r i j • z j) = a i w
  simp only [map_sum, map_smul, Finsupp.lapply_apply, z, Finsupp.onFinset_apply]
  by_cases hw : w ∈ S
  · simpa [hw] using hy w i
  · have ha : a i w = 0 := Finsupp.notMem_support_iff.mp (fun h => hw
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,h⟩))
    simp [hw,ha]

/-- Only embeddings of individual smaller groups are needed here. Replicating
them on disjoint blocks supplies the copies required by the extension argument. -/
theorem kostana_extension_of_cocyclic_embeddings {κ : Cardinal.{0}} (hκ : ℵ₀ < κ)
    (hc : ℵ₀ < κ.ord.cof)
    (embed : ∀ M : ModuleCat.{0} ℤ, #M < κ → ∃ (T : Type) (t : T → FactorIndex),
      #T < κ ∧ ∃ f : M →ₗ[ℤ] ((j : T) → factor (t j)), IsPureMap f) :
    HasExtension (R := ℤ) κ (ModuleCat.of ℤ (kostanaGroup κ hκ.le)) := by
  intro A B i f hB hi hf
  letI : Module ℤ A := A.isModule
  letI : Module ℤ B := B.isModule
  obtain ⟨g,hg⟩ := (kostana_pureInjective_iff hκ.le).mpr hc A B i f hi
  let C := B ⧸ LinearMap.range i
  let q : B →ₗ[ℤ] C := (LinearMap.range i).mkQ
  have onto : Function.Surjective q := (LinearMap.range i).mkQ_surjective
  obtain ⟨T,t,ht,j,hj⟩ := embed (ModuleCat.of ℤ C) ((Cardinal.mk_le_of_surjective onto).trans_lt hB)
  obtain ⟨into,hin⟩ := pack_pure_copies hκ.le t ht j hj
  let μ := max ℵ₀ (#B)
  have hμ : μ < #(κ.ord.toType) := by simpa [μ] using max_lt hκ hB
  exact EquationCriterion.uniformEquationExtension μ (le_max_left _ _)
    (Cardinal.mk_le_aleph0.trans (le_max_left _ _)) (le_max_right _ _) hμ
    i q f g into (LinearMap.exact_map_mkQ_range i) onto hg hf hin

end PureEmbeddings.Groups
