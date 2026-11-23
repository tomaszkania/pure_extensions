import PureEmbeddings.Ordinary
import Mathlib.RingTheory.Noetherian.Basic

/-! Bounded ordinary injectives over left Noetherian rings. -/
noncomputable section
namespace PureEmbeddings.Ordinary
open Cardinal Submodule LinearMap
universe u
variable (R : Type u) [Ring R]

abbrev CyclicSum := DirectSum (Ideal R) (fun I => R ⧸ (I : Submodule R R))

theorem cyclicSum_universal : CyclicUniversal (ModuleCat.of R (CyclicSum R)) := by
  classical
  intro M y
  let f := LinearMap.toSpanSingleton R M y
  let e := f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton y))
  exact ⟨(DirectSum.lof R _ _ (LinearMap.ker f)).comp e.symm.toLinearMap,
    (DirectSum.of_injective (LinearMap.ker f)).comp e.symm.injective⟩

theorem cyclicSum_size (μ : Cardinal.{u}) (hω : ℵ₀ ≤ μ) (hR : Cardinal.mk R ≤ μ)
    (hI : Cardinal.mk (Ideal R) ≤ μ) : Cardinal.mk (CyclicSum R) ≤ μ := by
  classical
  let atom (p : Ideal R × R) : CyclicSum R :=
    DirectSum.of (fun I : Ideal R => R ⧸ (I : Submodule R R)) p.1 (Submodule.Quotient.mk p.2)
  let total (l : List (Ideal R × R)) : CyclicSum R := (l.map atom).sum
  have onto : Function.Surjective total := by
    intro z
    refine DirectSum.induction_on z ?_ ?_ ?_
    · exact ⟨[], rfl⟩
    · intro i x
      obtain ⟨t,rfl⟩ := Submodule.Quotient.mk_surjective i x
      exact ⟨[(i,t)], by simp [total, atom]⟩
    · rintro x y ⟨l,rfl⟩ ⟨l',rfl⟩
      exact ⟨l++l', by simp [total]⟩
  apply (Cardinal.mk_le_of_surjective onto).trans
  apply (Cardinal.mk_list_le_max _).trans
  refine max_le hω ?_
  rw [Cardinal.mk_prod]
  simpa only [Cardinal.lift_id] using (mul_le_mul' hI hR).trans_eq (Cardinal.mul_eq_self hω)

theorem ideals_size_noetherian [IsNoetherianRing R] (κ : Cardinal.{u})
    (hω : ℵ₀ ≤ κ) (hR : Cardinal.mk R ≤ κ) : Cardinal.mk (Ideal R) ≤ κ := by
  classical
  let gen (l : List R) : Ideal R := Submodule.span R (↑l.toFinset : Set R)
  have hs : Function.Surjective gen := by
    intro I
    obtain ⟨s,hs⟩ := IsNoetherian.noetherian I
    exact ⟨s.toList, by simpa [gen] using hs⟩
  exact (Cardinal.mk_le_of_surjective hs).trans ((Cardinal.mk_list_le_max _).trans (max_le hω hR))

theorem injective_of_pure_noetherian [IsNoetherianRing R] {E : ModuleCat.{u} R}
    (hE : Module.Injective R E) (P : Submodule R E) (hp : IsPureMap P.subtype) :
    Module.Injective R P := by
  apply Module.Baer.injective
  intro I g
  obtain ⟨n,a,ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  have hmem (i : Fin n) : a i ∈ I := ha ▸ Submodule.subset_span (Set.mem_range_self i)
  let a' (i : Fin n) : I := ⟨a i,hmem i⟩
  obtain ⟨q,hq⟩ := hE.out I.subtype Subtype.val_injective (P.subtype.comp g)
  let r (i : Fin n) (_ : Fin 1) := a i
  have hsol : Soluble r (P.subtype ∘ (g ∘ a')) := by
    refine ⟨fun _ => q 1, fun i => ?_⟩
    simpa [r, Function.comp_def, a', ← q.map_smul, smul_eq_mul] using hq (a' i)
  obtain ⟨v,hv⟩ := hp.2 r (g ∘ a') hsol
  let q' := LinearMap.toSpanSingleton R P (v 0)
  refine ⟨q', ?_⟩
  have hgen (i : Fin n) : q' (a i) = g (a' i) := by simpa [q',r] using hv i
  have hall : ∀ x : R, ∀ hx : x ∈ Submodule.span R (Set.range a),
      q' x = g ⟨x,ha ▸ hx⟩ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i,rfl⟩ := hx; exact hgen i
    | zero => exact q'.map_zero.trans g.map_zero.symm
    | add x y hx hy h₁ h₂ => exact (q'.map_add _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans (g.map_add _ _).symm)
    | smul b x hx hi => exact (q'.map_smul b x).trans ((congrArg (b • ·) hi).trans (g.map_smul b _).symm)
  intro x hx
  exact hall x (ha.symm ▸ hx)

theorem copies_size (C : ModuleCat.{u} R) (κ μ : Cardinal.{u}) (hk : ℵ₀ ≤ κ)
    (hkm : κ ≤ μ) (hc : Cardinal.mk C ≤ μ) : Cardinal.mk (κ.out →₀ C) ≤ μ := by
  classical
  haveI : Infinite κ.out := Cardinal.aleph0_le_mk_iff.mp (by simpa using hk)
  cases subsingleton_or_nontrivial C with
  | inl h => exact (show Cardinal.mk (κ.out →₀ C) ≤ 1 by simp).trans (Cardinal.one_le_aleph0.trans (hk.trans hkm))
  | inr h => simpa using max_le hkm hc

theorem exists_universal_noetherian [IsNoetherianRing R] (κ : Cardinal.{u})
    (hω : ℵ₀ ≤ κ) (hr : Cardinal.mk R ≤ κ) :
    ∃ D : ModuleCat.{u} R, Cardinal.mk D ≤ κ ∧ Module.Injective R D ∧
      ∀ M : ModuleCat.{u} R, Cardinal.mk M ≤ κ → ∃ f : M →ₗ[R] D, Function.Injective f := by
  classical
  let C := ModuleCat.of R (CyclicSum R)
  let X := ModuleCat.of R (κ.out →₀ C)
  let E := CategoryTheory.Injective.under X
  let j : X →ₗ[R] E := (CategoryTheory.Injective.ι X).hom
  have hj : Function.Injective j := (ModuleCat.mono_iff_injective _).mp inferInstance
  haveI : CategoryTheory.Injective (ModuleCat.of R E) :=
    inferInstanceAs (CategoryTheory.Injective (CategoryTheory.Injective.under X))
  let P := pureHull R (Set.range j)
  have hE := Module.injective_module_of_injective_object R E
  have hp := injective_of_pure_noetherian R hE P (pureHull_isPureMap (R := R) _)
  let j' := j.codRestrict P (fun x => subset_pureHull (R := R) _ (Set.mem_range_self x))
  have hj' : Function.Injective j' := fun _ _ h => hj (congrArg Subtype.val h)
  have hC : Cardinal.mk C ≤ κ := cyclicSum_size R κ hω hr (ideals_size_noetherian R κ hω hr)
  have hX := copies_size R C κ κ hω le_rfl hC
  have hP := (mk_pureHull_le (R := R) (Set.range j)).trans
    (max_le hω (max_le hr ((Cardinal.mk_range_le (f := j)).trans hX)))
  refine ⟨ModuleCat.of R P, hP, hp, fun M hm => ?_⟩
  exact universal_of_cyclic_copies (C := C) (D := ModuleCat.of R P) (cyclicSum_universal R)
    hp j' hj' M (by simpa using hm)

end PureEmbeddings.Ordinary
