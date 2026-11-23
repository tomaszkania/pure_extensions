import PureEmbeddings.DedekindMathlib
import PureEmbeddings.PureInjectivity
import PureEmbeddings.BranchingMathlib
import Mathlib.RingTheory.Localization.FractionRing

/-! A family of pairwise incomparable finitely generated prime ideals gives
the same cardinal lower bound as a family of distinct maximal ideals. -/

noncomputable section
namespace PureEmbeddings.PrimeAntichain

open Cardinal Function
open scoped Pointwise BigOperators
universe u
variable {R P : Type u} [CommRing R] (I : P → Ideal R) [∀ p, (I p).IsPrime]

private def Residue (p : P) := FractionRing (R ⧸ I p)
private instance (p : P) : Field (Residue I p) := inferInstanceAs (Field (FractionRing (R ⧸ I p)))

private def reduction (p : P) : R →+* Residue I p :=
  (algebraMap (R ⧸ I p) (FractionRing (R ⧸ I p))).comp (Ideal.Quotient.mk (I p))
private instance (p : P) : Algebra R (Residue I p) := (reduction I p).toAlgebra

private theorem reduction_zero (p : P) (x : R) : reduction I p x = 0 ↔ x ∈ I p := by
  change algebraMap (R ⧸ I p) (FractionRing (R ⧸ I p)) (Ideal.Quotient.mk (I p) x) = 0 ↔ _
  rw [← map_zero (algebraMap (R ⧸ I p) (FractionRing (R ⧸ I p))),
    (IsFractionRing.injective (R ⧸ I p) (FractionRing (R ⧸ I p))).eq_iff, Ideal.Quotient.eq_zero_iff_mem]

private abbrev Ambient (K : Type u) := (t : P × K) → Residue I t.1

private def atom {K : Type u} (p : P) (k : K) : Ambient I K := by
  classical
  exact Pi.single (p,k) 1

private theorem off_mem {K : Type u} {p q : P} (h : ¬I p ≤ I q) (k : K) :
    atom I q k ∈ I p • (⊤ : Submodule R (Ambient I K)) := by
  classical
  obtain ⟨r,hr,hn⟩ := Set.not_subset.mp h
  have hz := mt (reduction_zero I q r).mp hn
  let w : Ambient I K := Pi.single (q,k) (reduction I q r)⁻¹
  have cancel : r • w = atom I q k := by
    funext t
    by_cases he : t = (q,k)
    · subst t
      change r • w (q,k) = atom I q k (q,k)
      simp only [w,atom, Pi.single_eq_same, Algebra.smul_def]
      exact mul_inv_cancel₀ hz
    · change r • w t = atom I q k t
      simp [w,atom, Pi.single_eq_of_ne he]
  exact cancel ▸ Submodule.smul_mem_smul hr (show w ∈ (⊤ : Submodule R (Ambient I K)) from trivial)

private theorem separate {K : Type u} (p : P) (k l : K)
    (mem : atom I p k - atom I p l ∈ I p • (⊤ : Submodule R (Ambient I K))) : k = l := by
  classical
  by_contra ne
  let e : Ambient I K →ₗ[R] Residue I p := LinearMap.proj (p,k)
  have kill : I p • (⊤ : Submodule R (Ambient I K)) ≤ LinearMap.ker e := by
    apply Submodule.smul_le.mpr
    intro r hr x _
    rw [LinearMap.mem_ker,map_smul,Algebra.smul_def]
    change reduction I p r * _ = 0
    rw [(reduction_zero I p r).mpr hr, zero_mul]
  have h := kill mem
  rw [LinearMap.mem_ker,map_sub] at h
  have hn : (p,k) ≠ (p,l) := fun he => ne (congrArg Prod.snd he)
  change atom I p k (p,k) - atom I p l (p,k) = 0 at h
  simp [atom,Pi.single_eq_of_ne hn] at h

/-- The extension property forces at least κ^|P| elements when P indexes a
family of pairwise incomparable finitely generated prime ideals. -/
theorem lower (antichain : ∀ p q, p ≠ q → ¬ I p ≤ I q) (fg : ∀ p, (I p).FG)
    (κ : Cardinal.{u}) (F : ModuleCat.{u} R) (hω : ℵ₀ < κ) (hR : #R < κ)
    (hF : HasExtension κ F) : κ ^ #P ≤ #F := by
  classical
  have dist : Injective I := fun {p q} he => by
    by_contra h
    exact antichain p q h he.le
  have hp := DedekindMathlib.small_index I dist fg κ hω hR
  let K := κ.out
  let ambient := Ambient I K
  let entry (t : P × K) : ambient := atom I t.1 t.2
  let W := pureHull R (Set.range entry)
  have hw : #W ≤ κ := by
    apply (mk_pureHull_le (R := R) (Set.range entry)).trans
    apply max_le hω.le
    apply max_le hR.le
    apply Cardinal.mk_range_le.trans
    simpa only [K, Cardinal.mk_prod,Cardinal.lift_id, Cardinal.mk_out] using
      (mul_le_mul' hp.le (le_refl κ)).trans_eq (Cardinal.mul_eq_self hω.le)
  let w (p : P) (k : K) : W := ⟨atom I p k,subset_pureHull _ (Set.mem_range_self (p,k))⟩
  obtain ⟨f,hf⟩ := hF.universal_le hω hR (ModuleCat.of R W) hw
  let G (p : P) := (I p • (⊤ : Submodule R F)).toAddSubgroup
  rw [← Cardinal.mk_out κ]
  apply Branching.cosetCardinalBound G (fun p k => f (w p k))
  · intro p q k hpq
    have hw' : w q k ∈ I p • (⊤ : Submodule R W) :=
      DedekindMathlib.pure_reflect_ideal (I p) W.subtype (pureHull_isPureMap _) (off_mem I (antichain p q hpq) k)
    have h := Submodule.mem_map_of_mem (f := f) hw'
    rw [Submodule.map_smul''] at h
    exact (Submodule.smul_mono le_rfl le_top) h
  · intro p k l hs
    have hw' := DedekindMathlib.pure_reflect_ideal (I p) f hf (x := w p k - w p l) (by simpa only [map_sub] using hs)
    have h := Submodule.mem_map_of_mem (f := W.subtype) hw'
    rw [Submodule.map_smul''] at h
    exact separate I p k l ((Submodule.smul_mono le_rfl le_top) h)
  · intro c fin
    choose n r hr using fun p => Submodule.fg_iff_exists_fin_generating_family.1 (fg p)
    have h := Germs.coefficient_cosets_of_solver n r c (Germs.algebraically_compact (hF.pureInjective hω hR)) (by
      intro T
      obtain ⟨z,hz⟩ := fin T
      exact ⟨z, fun p hh => (DedekindMathlib.membership_fixed_coefficients (I p) (r p) (hr p) _).1 (hz p hh)⟩)
    obtain ⟨z,hz⟩ := h
    exact ⟨z,fun p => (DedekindMathlib.membership_fixed_coefficients (I p) (r p) (hr p) _).2 (hz p)⟩

end PureEmbeddings.PrimeAntichain
