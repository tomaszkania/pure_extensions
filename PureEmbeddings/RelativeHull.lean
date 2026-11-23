import PureEmbeddings.PureHull
import Mathlib.Tactic.Abel

/-! An extension by one new element can be assembled from a small pure
inclusion. The construction adjoins solutions both inside a prescribed
pure submodule and modulo that submodule. -/
namespace PureEmbeddings
open Cardinal
open scoped BigOperators
universe u
variable {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]

private def relativeCondition (P : Submodule R M) (mode : Nat) {m n : Nat}
    (r : Fin m → Fin n → R) (a : Fin m → M) (x : Fin n → M) : Prop :=
  if mode = 0 then (∀ j, x j ∈ P) ∧ ∀ i, ∑ j, r i j • x j = a i
  else ∀ i, (∑ j, r i j • x j) - a i ∈ P

private noncomputable def relativeChoice (P : Submodule R M) (mode : Nat) {m n : Nat}
    (r : Fin m → Fin n → R) (a : Fin m → M) : Fin n → M := by
  classical
  exact if h : ∃ x, relativeCondition P mode r a x then Classical.choose h else 0

private theorem relativeChoice_spec (P : Submodule R M) (mode : Nat) {m n : Nat}
    (r : Fin m → Fin n → R) (a : Fin m → M) (h : ∃ x, relativeCondition P mode r a x) :
    relativeCondition P mode r a (relativeChoice P mode r a) := by
  simpa only [relativeChoice, dif_pos h] using Classical.choose_spec h

/-- For a pure submodule `P` and an element `b`, one can adjoin a small
submodule `U` containing `b` such that `P∩U` is pure in `U` and
`P+U` is pure in the ambient module. -/
theorem exists_small_relativeHull (P : Submodule R M) (hp : IsPureMap P.subtype) (b : M) :
    ∃ U : Submodule R M, b ∈ U ∧ Cardinal.mk U ≤ max ℵ₀ (Cardinal.mk R) ∧
      IsPureMap (P.comap U.subtype).subtype ∧ IsPureMap (P ⊔ U).subtype := by
  classical
  obtain ⟨U, hb, hsize, closed⟩ := exists_small_closedOperations (R := R)
    ({b} : Set M) (relativeChoice P)
  have hsmall : Cardinal.mk U ≤ max ℵ₀ (Cardinal.mk R) := by
    refine hsize.trans (max_le (le_max_left _ _) (max_le (le_max_right _ _) ?_))
    exact (Cardinal.mk_le_aleph0 (α := ({b} : Set M))).trans (le_max_left _ _)
  refine ⟨U, hb (Set.mem_singleton b), hsmall, ⟨Subtype.val_injective, ?_⟩,
    ⟨Subtype.val_injective, ?_⟩⟩
  · intro m n r a sol
    let c : Fin m → M := fun i => ((a i).val : M)
    let p : Fin m → P := fun i => ⟨c i, (a i).property⟩
    have ambient : Soluble r (P.subtype ∘ p) := sol.map U.subtype
    obtain ⟨z, hz⟩ := hp.2 r p ambient
    have exists_sol : ∃ x, relativeCondition P 0 r c x := by
      refine ⟨fun j => (z j : M), ?_⟩
      change (∀ j, (z j : M) ∈ P) ∧ _
      exact ⟨fun j => (z j).property, fun i => by
        simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
          congrArg Subtype.val (hz i)⟩
    let y := relativeChoice P 0 r c
    obtain ⟨hyp, hEq⟩ : (∀ j, y j ∈ P) ∧ ∀ i, ∑ j, r i j • y j = c i :=
      relativeChoice_spec P 0 r c exists_sol
    have hyu (j : Fin n) : y j ∈ U := closed 0 r c (fun i => (a i).val.property) j
    refine ⟨fun j => ⟨⟨y j, hyu j⟩, hyp j⟩, fun i => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using hEq i
  · intro m n r a sol
    obtain ⟨x, hx⟩ := sol
    have decomposes (i : Fin m) : ∃ u : U, (a i : M) - (u : M) ∈ P := by
      obtain ⟨p, hp', z, hz', ha⟩ := Submodule.mem_sup.mp (a i).property
      exact ⟨⟨z,hz'⟩, by rw [← ha, add_sub_cancel_right]; exact hp'⟩
    choose u hu using decomposes
    let c : Fin m → M := fun i => (u i : M)
    have exists_mod : ∃ y, relativeCondition P 1 r c y := by
      refine ⟨x, ?_⟩
      change ∀ i, (∑ j, r i j • x j) - c i ∈ P
      exact fun i => (hx i) ▸ hu i
    let y := relativeChoice P 1 r c
    have hy (i : Fin m) : (∑ j, r i j • y j) - c i ∈ P :=
      relativeChoice_spec P 1 r c exists_mod i
    have hyu (j : Fin n) : y j ∈ U := closed 1 r c (fun i => (u i).property) j
    have residual (i : Fin m) : (a i : M) - ∑ j, r i j • y j ∈ P := by
      convert P.sub_mem (hu i) (hy i) using 1
      dsimp [c]
      abel
    let d : Fin m → P := fun i => ⟨_, residual i⟩
    have sd : Soluble r (P.subtype ∘ d) := by
      refine ⟨fun j => x j - y j, fun i => ?_⟩
      change (∑ j, r i j • (x j - y j)) = (a i : M) - ∑ j, r i j • y j
      simp only [smul_sub, Finset.sum_sub_distrib, hx i, Function.comp_apply,
        Submodule.subtype_apply]
    obtain ⟨w, hw⟩ := hp.2 r d sd
    refine ⟨fun j => ⟨(w j : M) + y j,
      Submodule.mem_sup.mpr ⟨_, (w j).property, _, hyu j, rfl⟩⟩, fun i => ?_⟩
    apply Subtype.ext
    have hwi : (∑ j, r i j • (w j : M)) = (a i : M) - ∑ j, r i j • y j := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
        congrArg Subtype.val (hw i)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, smul_add,
      Finset.sum_add_distrib, hwi, sub_add_cancel]

end PureEmbeddings
