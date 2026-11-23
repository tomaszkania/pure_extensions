import PureEmbeddings.PureHull
import Mathlib.LinearAlgebra.Quotient.Basic

/-! ## Extending arbitrary maps on small pure submodules

The pushout of a pure inclusion along any linear map is again pure. A small
pure hull of the image keeps this construction within the size bound in `(Eκ)`.
-/
namespace PureEmbeddings
open Cardinal Function
universe u
variable {R : Type u} [Ring R]

namespace Pushout
variable {A B C : ModuleCat.{u} R} (i : A →ₗ[R] B) (f : A →ₗ[R] C)

abbrev relations := LinearMap.range (i.prod (-f))
abbrev Object := (B × C) ⧸ relations i f

abbrev left : B →ₗ[R] Object i f := (relations i f).mkQ.comp (LinearMap.inl R _ _)
abbrev right : C →ₗ[R] Object i f := (relations i f).mkQ.comp (LinearMap.inr R _ _)

theorem commutes : (left i f).comp i = (right i f).comp f := by
  ext a
  apply (Submodule.Quotient.eq (relations i f)).mpr
  exact ⟨a, by ext <;> simp⟩

/-- Purity survives a pushout along an arbitrary map. -/
theorem right_pure (hi : IsPureMap i) : IsPureMap (right i f) := by
  classical
  let J := relations i f
  constructor
  · intro y z h
    obtain ⟨a, ha⟩ := (Submodule.Quotient.eq J).mp h
    have hia : i a = i 0 := by simpa using congrArg Prod.fst ha
    have ha0 : a = 0 := hi.1 hia
    subst a
    have hz : (0 : C) = y - z := by simpa using congrArg Prod.snd ha
    exact sub_eq_zero.mp hz.symm
  · intro m n r c hs
    obtain ⟨x, hx⟩ := hs
    choose t ht using fun j => J.mkQ_surjective (x j)
    have rows (k : Fin m) : ∃ a : A, (i.prod (-f)) a = (∑ j, r k j • t j) - (0, c k) := by
      apply (Submodule.Quotient.eq J).mp
      change J.mkQ (∑ j, r k j • t j) = J.mkQ (0, c k)
      simpa only [map_sum, map_smul, ht] using hx k
    choose a ha using rows
    have hB : Soluble r (i ∘ a) := by
      refine ⟨fun j => (t j).1, fun k => ?_⟩
      have he := congrArg (LinearMap.fst R B C) (ha k)
      simp only [map_sub, map_sum, map_smul] at he
      simpa using he.symm
    obtain ⟨z, hz⟩ := hi.2 r a hB
    refine ⟨fun j => (t j).2 + f (z j), fun k => ?_⟩
    have hC : -(f (a k)) = (∑ j, r k j • (t j).2) - c k := by
      have he := congrArg (LinearMap.snd R B C) (ha k)
      simp only [map_sub, map_sum, map_smul] at he
      simpa using he
    calc
      _ = (∑ j, r k j • (t j).2) + f (∑ j, r k j • z j) := by
        simp only [smul_add, Finset.sum_add_distrib, map_sum, map_smul]
      _ = c k := by rw [hz, ← (eq_sub_iff_add_eq.mp hC)]; abel

end Pushout

/-- A target with `(Eκ)` extends arbitrary linear maps from pure submodules of
any module of size below `κ`. -/
theorem HasExtension.lift_small {κ : Cardinal.{u}} {F : ModuleCat.{u} R} (hF : HasExtension κ F)
    (hk : ℵ₀ < κ) (hR : #R < κ) {U : ModuleCat.{u} R} (A : Submodule R U)
    (hU : #U < κ) (hA : IsPureMap A.subtype) (f : A →ₗ[R] F) :
    ∃ g : U →ₗ[R] F, g.comp A.subtype = f := by
  classical
  let H := pureHull R (Set.range f)
  let C := ModuleCat.of R H
  let A' := ModuleCat.of R A
  let φ : A' →ₗ[R] C := f.codRestrict H (fun a => subset_pureHull _ (Set.mem_range_self a))
  let i : A' →ₗ[R] U := A.subtype
  let P := ModuleCat.of R (Pushout.Object i φ)
  have hsmall : #A < κ := (mk_le_of_injective (f := fun a : A => (a : U)) Subtype.val_injective).trans_lt hU
  have hc : #C < κ := (mk_pureHull_le (R := R) _).trans_lt
    (max_lt hk (max_lt hR (mk_range_le.trans_lt hsmall)))
  have hP : #P < κ := (mk_le_of_surjective (Pushout.relations i φ).mkQ_surjective).trans_lt
    (by simpa only [mk_prod, lift_id] using mul_lt_of_lt hk.le hU hc)
  obtain ⟨g, _, hg⟩ := hF C P (Pushout.right i φ) H.subtype hP
    (Pushout.right_pure i φ hA) (pureHull_isPureMap _)
  refine ⟨g.comp (Pushout.left i φ), ?_⟩
  ext a
  have he := DFunLike.congr_fun (Pushout.commutes i φ) a
  exact (congrArg g he).trans (DFunLike.congr_fun hg (φ a))

end PureEmbeddings
