import PureEmbeddings.Chains
import PureEmbeddings.PureHull
import PureEmbeddings.Germs
import Mathlib.SetTheory.Ordinal.Basic

/-! The necessary universality and small-system compactness properties of an extension module. -/
namespace PureEmbeddings
open Cardinal Filter
universe u
variable {R : Type u} [Ring R] {κ : Cardinal.{u}}

theorem HasExtension.universal_le {F : ModuleCat.{u} R} (hF : HasExtension κ F)
    (hk : ℵ₀ < κ) (hR : Cardinal.mk R < κ) (M : ModuleCat.{u} R) (hM : Cardinal.mk M ≤ κ) :
    ∃ f : M →ₗ[R] F, IsPureMap f := by
  classical
  obtain ⟨e⟩ : Nonempty (M ↪ κ.ord.toType) := (show Cardinal.mk M ≤ Cardinal.mk κ.ord.toType from by simpa using hM)
  let s (j : κ.ord.toType) : Set M := e ⁻¹' Set.Iic j
  apply hF.universal_of_chain (fun j => pureHull R (s j))
  · intro i j hij
    exact pureHull_mono fun _ h => le_trans h hij
  · intro x
    exact ⟨e x, subset_pureHull (s (e x)) (show e x ≤ e x from le_rfl)⟩
  · intro j
    have hle : Cardinal.mk (s j) ≤ Cardinal.mk (Set.Iic j) :=
      Cardinal.mk_le_of_injective (f := fun x : s j => (⟨e x.val, x.property⟩ : Set.Iic j))
        (fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)))
    have eqs : Set.Iic j = insert j (Set.Iio j) := by ext x; simp [le_iff_eq_or_lt]
    have hI : Cardinal.mk (Set.Iic j) < κ := by
      rw [eqs]
      exact Cardinal.mk_insert_le.trans_lt (Cardinal.add_lt_of_lt hk.le
        (Cardinal.mk_Iio_ord_toType j) (one_lt_aleph0.trans hk))
    exact (mk_pureHull_le (R := R) (s j)).trans_lt
      (max_lt hk (max_lt hR (hle.trans_lt hI)))
  · exact fun j => pureHull_isPureMap (s j)

/-- A finitely soluble linear system with fewer than κ rows and variables has
a simultaneous solution in an extension module. No regularity of κ is used. -/
theorem HasExtension.solve_small {F : ModuleCat.{u} R} (hF : HasExtension κ F)
    (hk : ℵ₀ < κ) (hR : Cardinal.mk R < κ) {E V : Type u}
    (s : Germs.System R F E V) (hE : Cardinal.mk E < κ) (hV : Cardinal.mk V < κ)
    (hs : s.FinitelySoluble) : ∃ y : V → F, ∀ i, s.Holds y i := by
  classical
  let l : Filter (Finset E) := atTop
  let N := ModuleCat.of R (Germ l F)
  let d : F →ₗ[R] N := Germs.diagonal l
  have hd : IsPureMap d := Germs.diagonal_pure l
  obtain ⟨x, hx⟩ := Germs.in_germs s hs
  let A := pureHull R (Set.range s.rhs)
  have hA : Cardinal.mk A < κ := (mk_pureHull_le (R := R) _).trans_lt
    (max_lt hk (max_lt hR (Cardinal.mk_range_le.trans_lt hE)))
  let h : A →ₗ[R] N := d.comp A.subtype
  let T : Set N := Set.range h ∪ Set.range x
  let B := pureHull R T
  have hBT : Cardinal.mk T < κ := (Cardinal.mk_union_le _ _).trans_lt
    (Cardinal.add_lt_of_lt hk.le (Cardinal.mk_range_le.trans_lt hA)
       (Cardinal.mk_range_le.trans_lt hV))
  have hB : Cardinal.mk B < κ := (mk_pureHull_le (R := R) _).trans_lt
    (max_lt hk (max_lt hR hBT))
  let i : A →ₗ[R] B := h.codRestrict B (fun a => subset_pureHull T (Or.inl ⟨a, rfl⟩))
  have ha : IsPureMap A.subtype := pureHull_isPureMap _
  have hi : IsPureMap i := IsPureMap.of_comp (A := ModuleCat.of R A) (B := ModuleCat.of R B)
    (C := N) i B.subtype (IsPureMap.comp (A := ModuleCat.of R A) (B := F) (C := N) hd ha)
  obtain ⟨g, _, hg⟩ := hF (ModuleCat.of R A) (ModuleCat.of R B) i A.subtype hB hi ha
  let b (v : V) : B := ⟨x v, subset_pureHull T (Or.inr ⟨v, rfl⟩)⟩
  let a (e : E) : A := ⟨s.rhs e, subset_pureHull _ ⟨e, rfl⟩⟩
  refine ⟨fun v => g (b v), fun e => ?_⟩
  have he : (∑ j, s.coeff e j • b (s.var e j)) = i (a e) := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using hx e
  have hgi : g (i (a e)) = s.rhs e := DFunLike.congr_fun hg (a e)
  exact (by simpa only [map_sum, map_smul] using congrArg g he :
    ∑ j, s.coeff e j • g (b (s.var e j)) = g (i (a e))).trans hgi

end PureEmbeddings
