import PureEmbeddings.OrdinaryBounds
import Mathlib.SetTheory.Cardinal.Regular

/-! Closing under Baer extensions at a cardinal fixed by raising to the
number of generators needed for a left ideal. -/
noncomputable section
namespace PureEmbeddings.Ordinary
open Cardinal Submodule LinearMap Function Set
universe u
variable (R : Type u) [Ring R]

private theorem ideal_maps_bound (I : Ideal R) (N : ModuleCat.{u} R)
    (τ μ : Cardinal.{u}) (hm : Cardinal.mk N ≤ μ) (hμ : μ ^ τ = μ)
    (hgen : ∃ s : Set R, Cardinal.mk s ≤ τ ∧ Submodule.span R s = I) :
    Cardinal.mk (I →ₗ[R] N) ≤ μ := by
  obtain ⟨s, hs, he⟩ := hgen
  let ins (x : s) : I := ⟨x, he ▸ subset_span x.property⟩
  let restrict (f : I →ₗ[R] N) (x : s) := f (ins x)
  have hi : Injective restrict := by
    intro f g h
    apply LinearMap.ext
    intro x
    have eqon (a : R) (ha : a ∈ Submodule.span R s) : f ⟨a,he ▸ ha⟩ = g ⟨a,he ▸ ha⟩ := by
      induction ha using Submodule.span_induction with
      | mem a ha => exact congrFun h ⟨a,ha⟩
      | zero => exact f.map_zero.trans g.map_zero.symm
      | add a b _ _ h₁ h₂ =>
        exact (f.map_add _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans (g.map_add _ _).symm)
      | smul b a _ hi =>
        exact (f.map_smul b _).trans ((congrArg (b • ·) hi).trans (g.map_smul b _).symm)
    exact eqon x (he.symm ▸ x.property)
  apply (Cardinal.mk_le_of_injective hi).trans
  rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id, ← hμ]
  apply (Cardinal.power_le_power_right hm).trans
  apply Cardinal.power_le_power_left _ hs
  
  have : 1 ≤ Cardinal.mk N := Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero_iff.mpr inferInstance)
  exact (zero_lt_one.trans_le (this.trans hm)).ne'

private theorem union_bound {A T : Type u} (s : T → Set A) {μ : Cardinal.{u}}
    (hω : ℵ₀ ≤ μ) (ht : Cardinal.mk T ≤ μ) (hs : ∀ t, Cardinal.mk (s t) ≤ μ) :
    Cardinal.mk (⋃ t, s t) ≤ μ := by
  apply Cardinal.mk_iUnion_le_sum_mk.trans
  exact (Cardinal.sum_le_sum _ _ hs).trans ((Cardinal.sum_const' T μ).le.trans
    ((mul_le_mul' ht le_rfl).trans_eq (Cardinal.mul_eq_self hω)))

/-- A bounded submodule of an injective can be enlarged, at the same bound,
to supply extensions of all maps from left ideals into that submodule. -/
private theorem grow {E : ModuleCat.{u} R} (hE : Module.Injective R E)
    (τ μ : Cardinal.{u}) (hω : ℵ₀ ≤ μ) (hr : Cardinal.mk R ≤ μ)
    (hids : Cardinal.mk (Ideal R) ≤ μ) (hpow : μ ^ τ = μ)
    (hgen : ∀ I : Ideal R, ∃ s : Set R, Cardinal.mk s ≤ τ ∧ Submodule.span R s = I)
    (P : Submodule R E) (hs : Cardinal.mk P ≤ μ) :
    ∃ Q : Submodule R E, Cardinal.mk Q ≤ μ ∧ P ≤ Q ∧
      ∀ (I : Ideal R) (g : I →ₗ[R] P), ∃ v : Q, ∀ a : I, (a : R) • (v : E) = (g a : E) := by
  classical
  let T := (I : Ideal R) × (I →ₗ[R] P)
  have lift' (t : T) := hE.out t.1.subtype Subtype.val_injective (P.subtype.comp t.2)
  let choose' (t : T) : R →ₗ[R] E := (lift' t).choose
  let val (t : T) := choose' t 1
  let s : Set E := (P : Set E) ∪ Set.range val
  let Q := pureHull R s
  have hT : Cardinal.mk T ≤ μ := by
    rw [Cardinal.mk_sigma]
    apply (Cardinal.sum_le_sum _ _ (fun I => ideal_maps_bound R I (ModuleCat.of R P) τ μ hs hpow (hgen I))).trans
    rw [Cardinal.sum_const']
    exact (mul_le_mul' hids le_rfl).trans_eq (Cardinal.mul_eq_self hω)
  have hsize : Cardinal.mk s ≤ μ := (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le hω hs (Cardinal.mk_range_le.trans hT))
  refine ⟨Q, (mk_pureHull_le (R := R) s).trans (max_le hω (max_le hr hsize)),
    fun _ hx => subset_pureHull s (Or.inl hx), fun I g => ?_⟩
  let t : T := ⟨I,g⟩
  refine ⟨⟨val t, subset_pureHull s (Or.inr (Set.mem_range_self t))⟩, fun a => ?_⟩
  have h := (lift' t).choose_spec a
  change (a : R) • choose' t 1 = (g a : E)
  rw [← map_smul, smul_eq_mul, mul_one]
  exact h

/-- A small injective submodule containing a prescribed set. Successive
stages supply extensions of all previously seen maps from an ideal. -/
theorem bounded_injective_submodule {E : ModuleCat.{u} R} (hE : Module.Injective R E)
    (τ μ : Cardinal.{u}) (hτ : ℵ₀ ≤ τ) (htm : τ < μ) (hr : Cardinal.mk R ≤ μ)
    (hids : Cardinal.mk (Ideal R) ≤ μ) (hpow : μ ^ τ = μ)
    (hgen : ∀ I : Ideal R, ∃ s : Set R, Cardinal.mk s ≤ τ ∧ Submodule.span R s = I)
    (seed : Set E) (hs : Cardinal.mk seed ≤ μ) :
    ∃ P : Submodule R E, seed ⊆ P ∧ Cardinal.mk P ≤ μ ∧ Module.Injective R P := by
  classical
  let θ := Order.succ τ
  let T := θ.ord.toType
  have hω := hτ.trans htm.le
  have hθ : θ ≤ μ := Order.succ_le_of_lt htm
  have hT : Cardinal.mk T ≤ μ := (Cardinal.mk_ord_toType θ).le.trans hθ
  have reg : Cardinal.IsRegular θ := Cardinal.isRegular_succ hτ
  have bound {A : Type u} (hA : Cardinal.mk A ≤ τ) (v : A → T) : ∃ j, ∀ a, v a < j := by
    have hsmall : Cardinal.mk (Set.range v) < Ordinal.cof (Ordinal.type ((· < ·) : T → T → Prop)) := by
      rw [Ordinal.type_toType, reg.cof_eq]
      exact (Cardinal.mk_range_le.trans hA).trans_lt (Order.lt_succ τ)
    obtain ⟨j,hj⟩ := Ordinal.lt_cof_type (r := (· < ·)) hsmall
    exact ⟨j,fun a => hj _ (Set.mem_range_self a)⟩
  haveI : Nonempty T := Ordinal.toType_nonempty_iff_ne_zero.mpr reg.ord_pos.ne'
  let Small := {P : Submodule R E // Cardinal.mk P ≤ μ}
  let next (P : Small) := grow R hE τ μ hω hr hids hpow hgen P.val P.property
  let step (P : Small) : Small := ⟨(next P).choose,(next P).choose_spec.1⟩
  have step_le (P : Small) : P.val ≤ (step P).val := (next P).choose_spec.2.1
  let growSet (i : T) (prev : ∀ j : T, j < i → Small) : Set E :=
    seed ∪ ⋃ j : Set.Iio i, ((step (prev j j.property)).val : Set E)
  have gs (i : T) (prev : ∀ j : T, j < i → Small) : Cardinal.mk (growSet i prev) ≤ μ := by
    apply (Cardinal.mk_union_le _ _).trans
    exact Cardinal.add_le_of_le hω hs (union_bound _ hω
      ((Cardinal.mk_le_of_injective (f := fun j : Set.Iio i => (j : T)) Subtype.val_injective).trans hT)
      (fun j => (step (prev j j.property)).property))
  let make (i : T) (prev : ∀ j : T, j < i → Small) : Small :=
    ⟨pureHull R (growSet i prev), (mk_pureHull_le (R := R) _).trans (max_le hω (max_le hr (gs i prev)))⟩
  let p := wellFounded_lt.fix make
  have pe (i : T) : p i = make i (fun j _ => p j) := wellFounded_lt.fix_eq make i
  have prev_le (i j : T) (h : i < j) : (step (p i)).val ≤ (p j).val := by
    rw [pe j]
    exact fun _ hx => subset_pureHull _ (Or.inr (Set.mem_iUnion.mpr ⟨⟨i,h⟩,hx⟩))
  have mono : Monotone (fun i : T => (p i).val) := by
    intro i j hij
    rcases lt_or_eq_of_le hij with h|rfl
    · exact (step_le _).trans (prev_le _ _ h)
    · rfl
  let P := ⨆ i : T, (p i).val
  have pc : (P : Set E) = ⋃ i, ((p i).val : Set E) :=
    Submodule.coe_iSup_of_directed _ mono.directed_le
  have ps : seed ⊆ P := by
    let i := Classical.ofNonempty (α := T)
    apply Set.Subset.trans _ (show ((p i).val : Set E) ⊆ P from le_iSup (fun j => (p j).val) i)
    rw [pe i]
    exact fun _ hx => subset_pureHull _ (Or.inl hx)
  have psize : Cardinal.mk P ≤ μ := by
    change Cardinal.mk (P : Set E) ≤ μ
    rw [pc]
    exact union_bound _ hω hT (fun i => (p i).property)
  refine ⟨P,ps,psize,Module.Baer.injective ?_⟩
  intro I g
  obtain ⟨s,hsmall,he⟩ := hgen I
  let ins (x : s) : I := ⟨x, he ▸ Submodule.subset_span x.property⟩
  have mem (x : s) : ∃ i : T, (g (ins x) : E) ∈ (p i).val := by
    apply Set.mem_iUnion.mp
    rw [← pc]
    exact (g (ins x)).property
  obtain ⟨i,hi⟩ := bound hsmall (fun x => (mem x).choose)
  have lands (a : R) (ha : a ∈ Submodule.span R s) : (g ⟨a,he ▸ ha⟩ : E) ∈ (p i).val := by
    induction ha using Submodule.span_induction with
    | mem x hx => exact mono (hi ⟨x,hx⟩).le ((mem ⟨x,hx⟩).choose_spec)
    | zero =>
      change (P.subtype.comp g) 0 ∈ _
      simpa only [map_zero] using (p i).val.zero_mem
    | add x y h₁ h₂ hx hy =>
      change (P.subtype.comp g) (⟨x,he ▸ h₁⟩ + ⟨y,he ▸ h₂⟩) ∈ _
      rw [map_add]
      exact (p i).val.add_mem hx hy
    | smul r x h₁ hx =>
      change (P.subtype.comp g) (r • ⟨x,he ▸ h₁⟩) ∈ _
      rw [map_smul]
      exact (p i).val.smul_mem r hx
  let f := (P.subtype.comp g).codRestrict (p i).val (fun x => lands x (he.symm ▸ x.property))
  obtain ⟨v,hv⟩ := (next (p i)).choose_spec.2.2 I f
  obtain ⟨j,hj⟩ := bound (A := PUnit.{u+1}) (by simpa using Cardinal.one_le_aleph0.trans hτ) (fun _ => i)
  have hvP : (v : E) ∈ P := le_iSup (fun t => (p t).val) j (prev_le i j (hj PUnit.unit) v.property)
  refine ⟨LinearMap.toSpanSingleton R P ⟨v,hvP⟩,fun x hx => Subtype.ext (hv ⟨x,hx⟩)⟩

theorem exists_universal_fixed (κ τ μ : Cardinal.{u}) (hτ : ℵ₀ ≤ τ)
    (htk : τ < κ) (hkm : κ ≤ μ) (hr : Cardinal.mk R ≤ μ)
    (hids : Cardinal.mk (Ideal R) ≤ μ) (hpow : μ ^ τ = μ)
    (hgen : ∀ I : Ideal R, ∃ s : Set R, Cardinal.mk s ≤ τ ∧ Submodule.span R s = I) :
    ∃ D : ModuleCat.{u} R, Cardinal.mk D ≤ μ ∧ Module.Injective R D ∧
      ∀ M : ModuleCat.{u} R, Cardinal.mk M ≤ κ → ∃ f : M →ₗ[R] D, Function.Injective f := by
  classical
  let C := ModuleCat.of R (CyclicSum R)
  let X := ModuleCat.of R (κ.out →₀ C)
  let E := CategoryTheory.Injective.under X
  let j : X →ₗ[R] E := (CategoryTheory.Injective.ι X).hom
  have hj : Function.Injective j := (ModuleCat.mono_iff_injective _).mp inferInstance
  haveI : CategoryTheory.Injective (ModuleCat.of R E) :=
    inferInstanceAs (CategoryTheory.Injective (CategoryTheory.Injective.under X))
  have hE := Module.injective_module_of_injective_object R E
  have hω := hτ.trans htk.le
  have hC : Cardinal.mk C ≤ μ := cyclicSum_size R μ (hω.trans hkm) hr hids
  have hX := copies_size R C κ μ hω hkm hC
  obtain ⟨P,hsub,hP,hp⟩ := bounded_injective_submodule R hE τ μ hτ (htk.trans_le hkm)
    hr hids hpow hgen (Set.range j) (Cardinal.mk_range_le.trans hX)
  let j' := j.codRestrict P (fun x => hsub (Set.mem_range_self x))
  have hj' : Function.Injective j' := fun _ _ h => hj (congrArg Subtype.val h)
  refine ⟨ModuleCat.of R P, hP, hp, fun M hm => ?_⟩
  exact universal_of_cyclic_copies (C := C) (D := ModuleCat.of R P) (cyclicSum_universal R)
    hp j' hj' M (by simpa using hm)

end PureEmbeddings.Ordinary
