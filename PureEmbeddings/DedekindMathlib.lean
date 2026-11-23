import PureEmbeddings.BranchingMathlib
import PureEmbeddings.Dedekind
import PureEmbeddings.Universality
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.SetTheory.Cardinal.Finsupp

/-! Concrete residue modules and the branching inequality for maximal ideals.
The ambient hypotheses below are purity of a prescribed direct-sum embedding
and the finite-intersection test for its specified cosets. -/
namespace PureEmbeddings.DedekindMathlib

open scoped DirectSum Pointwise TensorProduct Cardinal

universe u

variable {R P K F : Type u} [CommRing R] [AddCommGroup F] [Module R F]

/-- The base module in the lower-bound argument has finite support on P × K. -/
abbrev ResidueSum (I : P → Ideal R) (K : Type u) :=
  ⨁ t : P × K, R ⧸ I t.1

/-- Tensoring with R/I detects membership in I times a module. -/
theorem reflect_ideal_smul {S : Type u} [AddCommGroup S] [Module R S]
    (I : Ideal R) (f : S →ₗ[R] F)
    (hf : Function.Injective (f.lTensor (R ⧸ I))) {x : S}
    (hx : f x ∈ I • (⊤ : Submodule R F)) :
    x ∈ I • (⊤ : Submodule R S) := by
  have hx' : (1 : R ⧸ I) ⊗ₜ[R] f x = 0 := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk]
    rw [(Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
  have h : (1 : R ⧸ I) ⊗ₜ[R] x = 0 :=
    hf (by simpa using hx')
  have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul S I) h
  apply (Submodule.Quotient.mk_eq_zero _).1
  simpa [← TensorProduct.quotTensorEquivQuotSMul_symm_mk] using hq

/-- Every element of the ideal multiple is a finite linear combination with
coefficients in the ideal, including for ideals which are not finitely generated. -/
theorem coefficients_of_mem {S : Type u} [AddCommGroup S] [Module R S]
    (J : Ideal R) {x : S} (hx : x ∈ J • (⊤ : Submodule R S)) :
    ∃ n : ℕ, ∃ r : Fin n → J, ∃ y : Fin n → S, ∑ i, (r i : R) • y i = x := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha b _
    exact ⟨1, fun _ => ⟨a, ha⟩, fun _ => b, by simp⟩
  · intro x y hx hy
    obtain ⟨m, r, a, ha⟩ := hx
    obtain ⟨n, s, b, hb⟩ := hy
    refine ⟨m+n, Fin.append r s, Fin.append a b, ?_⟩
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, ha, hb]

/-- The finite-system definition of purity suffices for exactly the ideal
membership test used to separate coordinates. -/
theorem pure_reflect_ideal {S : Type u} [AddCommGroup S] [Module R S]
    (J : Ideal R) (f : S →ₗ[R] F) (hf : PureEmbeddings.IsPureMap f) {x : S}
    (h : f x ∈ J • (⊤ : Submodule R F)) : x ∈ J • (⊤ : Submodule R S) := by
  obtain ⟨n, r, y, hy⟩ := coefficients_of_mem J h
  let mat : Fin 1 → Fin n → R := fun _ j => (r j : R)
  let c : Fin 1 → S := fun _ => x
  obtain ⟨v, hv⟩ := hf.2 mat c ⟨y, fun _ => hy⟩
  rw [← show ∑ j, (r j : R) • v j = x from hv 0]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem_smul (r j).property (show v j ∈ (⊤ : Submodule R S) from trivial)

/-- The actual kernel at a residue coordinate contains all ideal multiples. -/
theorem coord_kills (I : P → Ideal R) (p : P) (k : K) :
    I p • (⊤ : Submodule R (ResidueSum I K)) ≤
      LinearMap.ker (DirectSum.component R (P × K) (fun t => R ⧸ I t.1) (p,k)) := by
  apply Submodule.smul_le.2
  intro r hr x _
  rw [LinearMap.mem_ker, map_smul]
  change Ideal.Quotient.mk (I p) r * _ = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]

/-- Distinct maximal ideals supply a scalar in one which acts as the identity
on the other's residue module. -/
theorem separator {J H : Ideal R} [J.IsMaximal] [H.IsMaximal] (hne : J ≠ H) :
    ∃ a ∈ J, Ideal.Quotient.mk H a = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Ideal.isCoprime_iff_exists.mp (Ideal.isCoprime_of_isMaximal hne)
  refine ⟨a, ha, ?_⟩
  have := congrArg (Ideal.Quotient.mk H) hab
  simpa only [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, map_one] using this

variable (I : P → Ideal R) [∀ p, (I p).IsMaximal]

noncomputable def entry (p : P) (k : K) : ResidueSum I K := by
  classical
  exact DirectSum.lof R (P × K) (fun t => R ⧸ I t.1) (p,k) 1

theorem off_mem (dist : Function.Injective I) {p q : P} (hpq : p ≠ q) (k : K) :
    entry I q k ∈ I p • (⊤ : Submodule R (ResidueSum I K)) := by
  classical
  obtain ⟨a, ha, hval⟩ := separator (J := I p) (H := I q) (fun h => hpq (dist h))
  have h1 : a • (1 : R ⧸ I q) = 1 := by
    change Ideal.Quotient.mk (I q) a * 1 = 1
    rw [hval, mul_one]
  have he : a • entry I q k = entry I q k := by
    unfold entry
    rw [← map_smul, h1]
  exact he ▸ Submodule.smul_mem_smul ha (show entry I q k ∈ (⊤ : Submodule R _) from trivial)

theorem entries_separate {p : P} {k l : K}
    (h : entry I p k - entry I p l ∈ I p • (⊤ : Submodule R (ResidueSum I K))) :
    k = l := by
  classical
  by_contra hne
  have hc := coord_kills I p k h
  rw [LinearMap.mem_ker, map_sub] at hc
  have hpair : (p,l) ≠ (p,k) := fun h => hne (congrArg Prod.snd h).symm
  simp only [entry, DirectSum.component.lof_self, DirectSum.component.of,
    dif_neg hpair, sub_zero] at hc
  exact one_ne_zero hc

/-- The Dedekind lower-bound injection for an indexed set of distinct maximal
ideals. This theorem also applies to commutative rings that are not domains. -/
theorem residue_injection (dist : Function.Injective I) (f : ResidueSum I K →ₗ[R] F)
    (pureMap : PureEmbeddings.IsPureMap f)
    (compact : ∀ centres : P → F,
      (∀ js : List P, js.Nodup → ∃ x : F, ∀ i ∈ js,
        x - centres i ∈ I i • (⊤ : Submodule R F)) →
      ∃ x : F, ∀ i, x - centres i ∈ I i • (⊤ : Submodule R F)) :
    Nonempty ((P → K) ↪ F) := by
  classical
  let family : PureEmbeddings.Branching.IndependentFamily P K F :=
    { zero := 0
      add := (· + ·)
      zero_add := zero_add
      add_zero := add_zero
      same := fun p x y => x-y ∈ I p • (⊤ : Submodule R F)
      refl := fun p _ => by simp
      symm := fun p x y h => by simpa only [neg_sub] using (I p • (⊤ : Submodule R F)).neg_mem h
      trans := fun p x y z h₁ h₂ => by
        simpa only [sub_add_sub_cancel] using (I p • (⊤ : Submodule R F)).add_mem h₁ h₂
      add_congr := fun p a b x y h₁ h₂ => by
        rw [add_sub_add_comm]
        exact (I p • (⊤ : Submodule R F)).add_mem h₁ h₂
      entry := fun p k => f (entry I p k)
      off_coordinate := fun p q k h => by
        rw [sub_zero]
        have hm := Submodule.mem_map_of_mem (f := f) (off_mem I dist h k)
        rw [Submodule.map_smul''] at hm
        exact (Submodule.smul_mono le_rfl le_top) hm
      separate := fun p k l h => by
        apply entries_separate I
        apply pure_reflect_ideal (I p) f pureMap
        simpa only [map_sub] using h }
  obtain ⟨point, hinj⟩ := PureEmbeddings.Branching.independentInjection family compact
  exact ⟨⟨point, fun {η ν} h => hinj η ν h⟩⟩

/-- Cardinal form of the injection, with exponent the number of ideals chosen. -/
theorem residue_cardinal_le (dist : Function.Injective I) (f : ResidueSum I K →ₗ[R] F)
    (pureMap : PureEmbeddings.IsPureMap f)
    (compact : ∀ centres : P → F,
      (∀ js : List P, js.Nodup → ∃ x : F, ∀ i ∈ js,
        x - centres i ∈ I i • (⊤ : Submodule R F)) →
      ∃ x : F, ∀ i, x - centres i ∈ I i • (⊤ : Submodule R F)) :
    Cardinal.mk K ^ Cardinal.mk P ≤ Cardinal.mk F := by
  rw [Cardinal.power_def]
  exact (Cardinal.le_def _ _).mpr (residue_injection I dist f pureMap compact)

/-- A fixed generating family for an ideal gives one equation, with the
same coefficients on every module. -/
theorem membership_fixed_coefficients {S : Type u} [AddCommGroup S] [Module R S]
    (J : Ideal R) {n : ℕ} (r : Fin n → R) (hgen : Submodule.span R (Set.range r) = J)
    (x : S) : x ∈ J • (⊤ : Submodule R S) ↔ ∃ y : Fin n → S, x = ∑ i, r i • y i := by
  constructor
  · intro h
    refine Submodule.smul_induction_on h ?_ ?_
    · intro a ha b _
      rw [← hgen] at ha
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
      refine ⟨fun i => c i • b, ?_⟩
      rw [← hc, Finset.sum_smul]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [smul_eq_mul, smul_smul, mul_comm (c i)]
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a+b, by simp [smul_add, Finset.sum_add_distrib]⟩
  · rintro ⟨y, rfl⟩
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem_smul _ (show y j ∈ (⊤ : Submodule R S) from trivial)
    rw [← hgen]
    exact Submodule.subset_span (Set.mem_range_self j)

omit [∀ p, (I p).IsMaximal] in
/-- There are fewer than κ distinct finitely generated ideals when |R| and
ℵ₀ are both strictly below κ. The proof encodes each ideal as a finite list. -/
theorem small_index (dist : Function.Injective I) (finiteGen : ∀ p, (I p).FG)
    (κ : Cardinal.{u}) (hω : Cardinal.aleph0 < κ) (hR : Cardinal.mk R < κ) :
    Cardinal.mk P < κ := by
  classical
  choose s hs using finiteGen
  have hinj : Function.Injective (fun p => (s p).toList) := by
    intro i j h
    have he := congrArg List.toFinset h
    simp only [Finset.toList_toFinset] at he
    exact dist ((hs i).symm.trans ((congrArg (fun a : Finset R => Submodule.span R (a : Set R)) he).trans (hs j)))
  exact (Cardinal.mk_le_of_injective hinj).trans_lt
    ((Cardinal.mk_list_le_max R).trans_lt (max_lt hω hR))

omit [∀ p, (I p).IsMaximal] in
theorem witness_size [Nonempty P] [Infinite K] [Nontrivial R] (κ : Cardinal.{u})
    (hω : Cardinal.aleph0 ≤ κ) (hR : Cardinal.mk R ≤ κ)
    (hK : Cardinal.mk K ≤ κ) (hP : Cardinal.mk P ≤ κ) : Cardinal.mk (ResidueSum I K) ≤ κ := by
  classical
  let q := fun i : P × K => (Ideal.Quotient.mk (I i.1)).toAddMonoidHom
  have hs : Function.Surjective (DirectSum.map q) :=
    (DirectSum.map_surjective q).2 (fun i => Ideal.Quotient.mk_surjective)
  calc
    Cardinal.mk (ResidueSum I K) ≤ Cardinal.mk (⨁ _ : P × K, R) :=
      Cardinal.mk_le_of_surjective hs
    _ = Cardinal.mk ((P × K) →₀ R) := finsuppEquivDFinsupp.symm.cardinal_eq
    _ = max (Cardinal.mk (P × K)) (Cardinal.mk R) := Cardinal.mk_finsupp_of_infinite _ _
    _ ≤ κ := by
      apply max_le _ hR
      rw [Cardinal.mk_prod]
      simp only [Cardinal.lift_id]
      exact (mul_le_mul' hP hK).trans (Cardinal.mul_eq_self hω).le

private theorem small_private_vars (n : P → ℕ) (κ : Cardinal.{u})
    (hω : Cardinal.aleph0 < κ) (hp : Cardinal.mk P < κ) :
    Cardinal.mk (Option ((p : P) × Fin (n p))) < κ := by
  let encode : ((p : P) × Fin (n p)) → P × ULift.{u} ℕ := fun t => (t.1, ⟨t.2.val⟩)
  have e_inj : Function.Injective encode := by
    rintro ⟨p,i⟩ ⟨q,j⟩ h
    have hpq : p=q := congrArg Prod.fst h
    subst q
    have hi : i.val=j.val := congrArg (fun a : P × ULift.{u} ℕ => a.2.down) h
    cases Fin.ext hi
    rfl
  let μ := max (Cardinal.mk P) Cardinal.aleph0
  have hμ : Cardinal.aleph0 ≤ μ := le_max_right _ _
  have hb : Cardinal.mk ((p : P) × Fin (n p)) ≤ μ := by
    apply (Cardinal.mk_le_of_injective e_inj).trans
    rw [Cardinal.mk_prod]
    simp only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_id]
    exact (mul_le_mul' (le_max_left _ _) hμ).trans (Cardinal.mul_eq_self hμ).le
  rw [Cardinal.mk_option]
  apply lt_of_le_of_lt _ (max_lt hp hω)
  exact (add_le_add hb (Cardinal.one_le_aleph0.trans hμ)).trans (Cardinal.add_eq_self hμ).le

/-- It suffices to solve systems with fewer than κ rows and variables.
The deduction applies to a ring of any size satisfying the displayed bounds. -/
theorem lower_of_small_systems (κ : Cardinal.{u}) (F : ModuleCat.{u} R)
    (hω : Cardinal.aleph0 < κ) (hR : Cardinal.mk R < κ) (dist : Function.Injective I)
    (finiteGen : ∀ p, (I p).FG)
    (universal : ∀ M : ModuleCat.{u} R, Cardinal.mk M ≤ κ →
      ∃ f : M →ₗ[R] F, PureEmbeddings.IsPureMap f)
    (solver : ∀ (E V : Type u) (s : PureEmbeddings.Germs.System R F E V),
      Cardinal.mk E < κ → Cardinal.mk V < κ → s.FinitelySoluble → ∃ x, ∀ i, s.Holds x i) :
    κ ^ Cardinal.mk P ≤ Cardinal.mk F := by
  classical
  have hκ : Infinite κ.out := Cardinal.aleph0_le_mk_iff.mp (by simpa using hω.le)
  have hp := small_index I dist finiteGen κ hω hR
  rcases isEmpty_or_nonempty P with hP | hP
  · simpa using (Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero F))
  · letI : Nontrivial R := (Ideal.Quotient.mk_surjective (I := I (Classical.choice hP))).nontrivial
    have hw := witness_size (K := κ.out) I κ hω.le hR.le (by simp) hp.le
    obtain ⟨f, hf⟩ := universal (ModuleCat.of R (ResidueSum I κ.out)) hw
    rw [← Cardinal.mk_out κ]
    apply residue_cardinal_le I dist f hf
    intro c hc
    choose n r hr using fun p => Submodule.fg_iff_exists_fin_generating_family.1 (finiteGen p)
    have hs : ∀ a : Finset P, ∃ z : F, ∀ i ∈ a,
        ∃ y : Fin (n i) → F, z - c i = ∑ j, r i j • y j := by
      intro a
      obtain ⟨z, hz⟩ := hc a.toList a.nodup_toList
      exact ⟨z, fun i hi => (membership_fixed_coefficients (I i) (r i) (hr i) _).1
        (hz i (by simpa using hi))⟩
    obtain ⟨z, hz⟩ := PureEmbeddings.Germs.coefficient_cosets_of_solver n r c
      (fun s => solver _ _ s hp (small_private_vars n κ hω hp)) hs
    exact ⟨z, fun i => (membership_fixed_coefficients (I i) (r i) (hr i) _).2 (hz i)⟩

/-- A direct lower bound from the manuscript's extension property, with
no compactness or universality assumptions. In a Dedekind domain all ideals
are finitely generated. -/
theorem lower_of_extension (κ : Cardinal.{u}) (F : ModuleCat.{u} R)
    (hω : Cardinal.aleph0 < κ) (hR : Cardinal.mk R < κ) (dist : Function.Injective I)
    (finiteGen : ∀ p, (I p).FG) (hF : PureEmbeddings.HasExtension κ F) :
    κ ^ Cardinal.mk P ≤ Cardinal.mk F :=
  lower_of_small_systems I κ F hω hR dist finiteGen
    (hF.universal_le hω hR) (fun _ _ s => hF.solve_small hω hR s)

private def multiples {M : Type u} [AddCommGroup M] [Module R M] (r : R) : AddSubgroup M where
  carrier := {x | ∃ y, r • y = x}
  zero_mem' := ⟨0, smul_zero _⟩
  add_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b, smul_add ..⟩
  neg_mem' := by rintro _ ⟨a,rfl⟩; exact ⟨-a, smul_neg ..⟩

/-- The additional countable lower bound uses one non-zero non-unit. -/
theorem domain_countable_lower [IsDomain R] (nonfield : ¬IsField R) (κ : Cardinal.{u})
    (F : ModuleCat.{u} R) (hω : Cardinal.aleph0 < κ) (hR : Cardinal.mk R < κ)
    (hF : PureEmbeddings.HasExtension κ F) : κ ^ Cardinal.aleph0 ≤ Cardinal.mk F := by
  classical
  obtain ⟨r, hr, hnu⟩ := Ring.exists_not_isUnit_of_not_isField nonfield
  let X := κ.out →₀ R
  have : Infinite κ.out := Cardinal.aleph0_le_mk_iff.mp (by simpa using hω.le)
  have size : Cardinal.mk X ≤ κ := by
    change Cardinal.mk (κ.out →₀ R) ≤ κ
    rw [Cardinal.mk_finsupp_of_infinite, Cardinal.mk_out]
    exact max_le le_rfl hR.le
  obtain ⟨f, hf⟩ := hF.universal_le hω hR (ModuleCat.of R X) size
  let a (n : ℕ) (k : κ.out) : F := f (Finsupp.single k (r^n))
  let H (n : ℕ) : AddSubgroup F := multiples (r^n)
  rw [← Cardinal.mk_out κ]
  apply PureEmbeddings.Branching.countableChainCardinalBound H a
  · rintro n _ ⟨y, rfl⟩
    exact ⟨r • y, by rw [pow_succ, mul_smul]⟩
  · intro n k
    refine ⟨f (Finsupp.single k (1 : R)), ?_⟩
    change r^n • f _ = f _
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  · intro n k l h
    by_contra hkl
    obtain ⟨y, hy⟩ := h
    let z : X := Finsupp.single k (r^n) - Finsupp.single l (r^n)
    have hfy : r^(n+1) • y = f z := by simpa [a,z] using hy
    let mat : Fin 1 → Fin 1 → R := fun _ _ => r^(n+1)
    let c : Fin 1 → X := fun _ => z
    obtain ⟨v,hv⟩ := hf.2 mat c ⟨fun _ => y, fun _ => by simpa [mat,c] using hfy⟩
    have hcoord := congrArg (fun t : X => t k) (hv 0)
    have eqn : r^(n+1) * (v 0 k) = r^n := by
      simp only [Fin.sum_univ_one, mat, c, z] at hcoord
      change (r^(n+1) • (v 0 : κ.out →₀ R)) k =
        (Finsupp.single k (r^n) - Finsupp.single l (r^n)) k at hcoord
      simpa [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_apply,hkl,Ne.symm hkl] using hcoord
    apply hnu
    apply isUnit_of_dvd_one
    refine ⟨v 0 k, mul_left_cancel₀ (pow_ne_zero n hr) ?_⟩
    rw [mul_one, ← mul_assoc, ← pow_succ, eqn]
  · intro levels centres finite
    let n (_ : ULift.{u} ℕ) := 1
    let coeff (j : ULift.{u} ℕ) (_ : Fin (n j)) := r^(levels j.down)
    let c (j : ULift.{u} ℕ) := centres j.down
    have finite' (t : Finset (ULift.{u} ℕ)) :
        ∃ z : F, ∀ i ∈ t, ∃ v : Fin (n i) → F, z-c i = ∑ j, coeff i j • v j := by
      obtain ⟨z,hz⟩ := finite (t.image ULift.down)
      refine ⟨z, fun i hi => ?_⟩
      obtain ⟨y,hy⟩ := hz i.down (Finset.mem_image_of_mem _ hi)
      exact ⟨fun _ => y, by simpa [n,coeff,c] using hy.symm⟩
    have hE : Cardinal.mk (ULift.{u} ℕ) < κ := by simpa using hω
    obtain ⟨z,hz⟩ := PureEmbeddings.Germs.coefficient_cosets_of_solver n coeff c
      (fun s => hF.solve_small hω hR s hE (small_private_vars n κ hω hE)) finite'
    refine ⟨z, fun i => ?_⟩
    obtain ⟨v,hv⟩ := hz ⟨i⟩
    exact ⟨v 0, by simpa [n,coeff,c] using hv.symm⟩

/-- The complete Dedekind-domain lower exponent from the extension property,
including finitely many maximal ideals. -/
theorem dedekind_lower [IsDedekindDomain R] (nonfield : ¬IsField R) (κ : Cardinal.{u})
    (F : ModuleCat.{u} R) (hω : Cardinal.aleph0 < κ) (hR : Cardinal.mk R < κ)
    (hF : PureEmbeddings.HasExtension κ F) :
    κ ^ max Cardinal.aleph0 (Cardinal.mk {p : Ideal R // p.IsMaximal}) ≤ Cardinal.mk F := by
  let P := {p : Ideal R // p.IsMaximal}
  let I : P → Ideal R := Subtype.val
  letI (p : P) : (I p).IsMaximal := p.property
  have prime := lower_of_extension I κ F hω hR Subtype.val_injective
    (fun p => (isNoetherianRing_iff_ideal_fg R).mp inferInstance (I p)) hF
  rcases le_total Cardinal.aleph0 (Cardinal.mk P) with h | h
  · rw [max_eq_right h]
    exact prime
  · rw [max_eq_left h]
    exact domain_countable_lower nonfield κ F hω hR hF

/-- The preceding transport theorems applied to actual modules. -/
def moduleOps (R X : Type u) [CommRing R] [AddCommGroup X] [Module R X] :
    PureEmbeddings.Dedekind.Space R X where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  smul := (· • ·)

def linearMapOps {X Y : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) : PureEmbeddings.Dedekind.LinearMap (moduleOps R X) (moduleOps R Y) where
  fn := f
  mapZero := f.map_zero
  mapAdd := f.map_add
  mapNeg := f.map_neg
  mapSmul := f.map_smul

/-- This is the p-annihilated subspace of the largest divisible submodule,
not the elements of the whole module annihilated by p. -/
def DivisibleSocle (R X : Type u) [CommRing R] [AddCommGroup X] [Module R X] (p : Ideal R) :=
  {x : X // PureEmbeddings.Dedekind.InComponent (moduleOps R X) 0 (· ∈ p) x}

def socleEquiv {X Y : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (p : Ideal R) (e : X ≃ₗ[R] Y) : DivisibleSocle R X p ≃ DivisibleSocle R Y p where
  toFun := fun ⟨x, hx⟩ => ⟨e x, PureEmbeddings.Dedekind.map_component (linearMapOps e.toLinearMap) hx⟩
  invFun := fun ⟨y, hy⟩ => ⟨e.symm y, PureEmbeddings.Dedekind.map_component (linearMapOps e.symm.toLinearMap) hy⟩
  left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
  right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val)

/-- A single prime of different multiplicity distinguishes two models.
The input descriptions of the socles are the structural isomorphisms supplied
by the injective-module decomposition in the manuscript. Their cardinalities
and their invariance are proved here. -/
theorem different_prime_multiplicities {X Y A B : Type u}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Infinite A] [Infinite B]
    (p : Ideal R) [p.IsMaximal]
    (sx : Nonempty (DivisibleSocle R X p ≃ (A →₀ (R ⧸ p))))
    (sy : Nonempty (DivisibleSocle R Y p ≃ (B →₀ (R ⧸ p))))
    (ha : Cardinal.mk (R ⧸ p) ≤ Cardinal.mk A) (hb : Cardinal.mk (R ⧸ p) ≤ Cardinal.mk B)
    (hdiff : Cardinal.mk A ≠ Cardinal.mk B) : IsEmpty (X ≃ₗ[R] Y) := by
  constructor
  intro e
  obtain ⟨s⟩ := sx
  obtain ⟨t⟩ := sy
  have h := ((s.symm.trans (socleEquiv p e)).trans t).cardinal_eq
  rw [Cardinal.mk_finsupp_of_infinite, Cardinal.mk_finsupp_of_infinite,
    max_eq_left ha, max_eq_left hb] at h
  exact hdiff h

end PureEmbeddings.DedekindMathlib
