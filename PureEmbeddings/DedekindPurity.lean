import PureEmbeddings.ValuationPurity
import PureEmbeddings.ResidueUpper
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! Relative divisibility detects purity when the localisations at maximal
ideals are valuation rings. Denominators are retained in the finite row
elimination and then removed using the ideal of all possible multipliers. -/
noncomputable section
namespace PureEmbeddings.DedekindPurity
universe u
open scoped BigOperators Pointwise
variable {R : Type u} [CommRing R]
variable {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

private def row {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (r : Fin n → R) (x : Fin n → M) := ∑ j, r j • x j

private theorem elimRow {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (r q : Fin n → R) (s d : R) (x : Fin n → M) :
    row (fun j => s * r j - d * q j) x = s • row r x - d • row q x := by
  simp [row, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]

private theorem scaleRow {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (r : Fin n → R) (s : R) (x : Fin n → M) :
    row r (fun j => s • x j) = s • row r x := by
  simp only [row, Finset.smul_sum]; exact Finset.sum_congr rfl (fun _ _ => smul_comm ..)

private theorem correctRow {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (r : Fin n → R) (x : Fin n → M) (p : Fin n) (w : M) :
    row r (fun j => x j + if j = p then w else 0) = row r x + r p • w := by
  classical
  simp only [row, smul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- A coefficient of least local valuation divides every coefficient after a
single common denominator outside the prime is cleared. -/
def LocalPivots (P : Ideal R) : Prop :=
  ∀ S : Finset R, S.Nonempty → ∃ a ∈ S, ∃ s ∉ P, ∀ v ∈ S, a ∣ s * v

private theorem partial_system {m n : ℕ} (P : Ideal R) [P.IsPrime] (pivot : LocalPivots P)
    (f : A →ₗ[R] B) (inj : Function.Injective f)
    (reflect : ∀ (v : R) (b : A), (∃ x : B, v • x = f b) → ∃ x : A, v • x = b)
    (T : Finset (Fin m)) (r : Fin m → Fin n → R) (b : Fin m → A) (y : Fin n → B)
    (hy : ∀ i ∈ T, row (r i) y = f (b i)) :
    ∃ t ∉ P, ∃ x : Fin n → A, ∀ i ∈ T, row (r i) x = t • b i := by
  classical
  induction T using Finset.strongInductionOn generalizing r b with
  | _ T ih =>
    by_cases hT : T.Nonempty
    · by_cases hn : Nonempty (Fin n)
      · let S := T ×ˢ (Finset.univ : Finset (Fin n))
        let coeff (p : Fin m × Fin n) := r p.1 p.2
        obtain ⟨a,ha,s,hs,hdiv⟩ := pivot (S.image coeff)
          ((hT.product ⟨hn.some, Finset.mem_univ _⟩).image coeff)
        obtain ⟨⟨i₀,j₀⟩, hp, hcoef⟩ := Finset.mem_image.mp ha
        have hi₀ : i₀ ∈ T := (Finset.mem_product.mp hp).1
        change r i₀ j₀ = a at hcoef
        have dvd (i) (hi : i ∈ T) (j) : a ∣ s * r i j :=
          hdiv _ (Finset.mem_image.mpr ⟨(i,j), Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩,rfl⟩)
        choose c hc using dvd i₀ hi₀
        let d (i : Fin m) := if hi : i ∈ T then (dvd i hi j₀).choose else 0
        have hd (i) (hi : i ∈ T) : s * r i j₀ = a * d i := by
          simpa [d,hi] using (dvd i hi j₀).choose_spec
        let r' (i : Fin m) (j : Fin n) := s * r i j - d i * r i₀ j
        let b' (i : Fin m) := s • b i - d i • b i₀
        obtain ⟨t,ht,x,hx⟩ := ih (T.erase i₀) (Finset.erase_ssubset hi₀) r' b' (by
          intro i hi
          rw [show row (r' i) y = _ from elimRow (r i) (r i₀) s (d i) y,
            hy i (Finset.mem_of_mem_erase hi), hy i₀ hi₀]
          simp [b'])
        have hrow {M : Type u} [AddCommGroup M] [Module R M] (z : Fin n → M) :
            s • row (r i₀) z = a • row c z := by
          simp only [row, Finset.smul_sum, ← mul_smul, hc]
        have hmap : f (row (r i₀) x) = row (r i₀) (f ∘ x) := by
          simp only [row, map_sum, map_smul, Function.comp_apply]
        let e := t • b i₀ - row (r i₀) x
        obtain ⟨w,hw⟩ := reflect a (s • e) (by
          refine ⟨t • row c y - row c (f ∘ x), ?_⟩
          rw [smul_sub, smul_comm a t, ← hrow, ← hrow, hy i₀ hi₀]
          simp only [e,map_smul,map_sub,hmap,smul_sub]; rw [smul_comm t s])
        refine ⟨s * (s * t), P.primeCompl.mul_mem hs (P.primeCompl.mul_mem hs ht),
          fun j => (s * s) • x j + if j = j₀ then s • w else 0, ?_⟩
        intro i hi
        rw [correctRow, scaleRow]
        by_cases eqn : i = i₀
        · subst i
          rw [hcoef,smul_comm a s,hw, mul_smul, mul_smul, mul_smul, ← smul_add, ← smul_add]
          simp [e]
        · have reduced := hx i (Finset.mem_erase.mpr ⟨eqn,hi⟩)
          change row (fun j => s * r i j - d i * r i₀ j) x = t • (s • b i - d i • b i₀) at reduced
          rw [elimRow, smul_sub, smul_comm t s, smul_comm t (d i)] at reduced
          have heq : s • row (r i) x + d i • e = s • t • b i := by
            simp only [e,smul_sub]
            linear_combination (norm := abel) reduced
          rw [smul_comm (r i j₀) s, ← mul_smul, hd i hi, mul_comm a (d i), mul_smul (d i) a, hw,
            smul_comm (d i) s, mul_smul, ← smul_add, heq, mul_smul, mul_smul]
      · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hn
        refine ⟨1,P.primeCompl.one_mem, fun _ => 0, fun i hi => ?_⟩
        apply inj
        simpa [row] using hy i hi
    · exact ⟨1,P.primeCompl.one_mem, fun _ => 0, fun i hi => False.elim (hT ⟨i,hi⟩)⟩

/-- Solubility up to a multiplier defines an ideal; a solution locally at
every maximal ideal forces this ideal to contain 1. -/
theorem pure_of_local_pivots
    (localPivots : ∀ P : Ideal R, P.IsMaximal → LocalPivots P)
    (f : A →ₗ[R] B) (inj : Function.Injective f)
    (reflect : ∀ (v : R) (b : A), (∃ x : B, v • x = f b) → ∃ x : A, v • x = b) :
    IsPureMap f := by
  classical
  refine ⟨inj, ?_⟩
  rintro m n r b ⟨y,hy⟩
  let I : Ideal R := {
    carrier := {t | ∃ x : Fin n → A, ∀ i, row (r i) x = t • b i}
    zero_mem' := ⟨fun _ => 0, by simp [row]⟩
    add_mem' := by
      rintro t s ⟨x,hx⟩ ⟨z,hz⟩
      refine ⟨fun j => x j + z j, fun i => ?_⟩
      simpa [row, smul_add, Finset.sum_add_distrib,add_smul] using congrArg₂ (· + ·) (hx i) (hz i)
    smul_mem' := by
      rintro s t ⟨x,hx⟩
      exact ⟨fun j => s • x j, fun i => by rw [scaleRow,hx]; exact (mul_smul ..).symm⟩ }
  have trivialIdeal : I = ⊤ := by
    by_contra hI
    obtain ⟨P,hP,hIP⟩ := I.exists_le_maximal hI
    letI := hP.isPrime
    obtain ⟨t,ht,x,hx⟩ := partial_system P (localPivots P hP) f inj reflect Finset.univ r b y
      (fun i _ => hy i)
    exact ht (hIP (show t ∈ I from ⟨x, fun i => hx i (Finset.mem_univ _)⟩))
  obtain ⟨x,hx⟩ := (show (1:R) ∈ I by rw [trivialIdeal]; trivial)
  exact ⟨x, fun i => by simpa using hx i⟩

/-- Existence of common denominators follows from the valuation ordering in
the local ring; denominators are multiplied only over the given finite set. -/
theorem local_pivots_of_valuation (P : Ideal R) [P.IsPrime] [IsDomain R]
    [ValuationRing (Localization.AtPrime P)] : LocalPivots P := by
  classical
  intro S hS
  let L := Localization.AtPrime P
  let φ := algebraMap R L
  obtain ⟨w,hw,hd⟩ := ValuationMathlib.finite_common_divisor_mem L (S.image φ) (hS.image φ)
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
  have each (b : S) : ∃ s : P.primeCompl, a ∣ (s : R) * b.val := by
    obtain ⟨z,hz⟩ := hd (φ b.val) (Finset.mem_image_of_mem _ b.property)
    obtain ⟨⟨c,s⟩,hc⟩ := IsLocalization.surj P.primeCompl z
    refine ⟨s,c,IsLocalization.injective L P.primeCompl_le_nonZeroDivisors ?_⟩
    change φ ((s:R) * b.val) = φ (a*c)
    rw [map_mul, map_mul, hz, mul_comm (φ s), mul_assoc, hc]
  choose s hs using each
  let t := ∏ i : S, s i
  refine ⟨a,ha,t.val,t.property,?_⟩
  intro b hb
  let j : S := ⟨b,hb⟩
  obtain ⟨v,hv⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ j)
  obtain ⟨q,hq⟩ := hs j
  refine ⟨v.val*q,?_⟩
  have hval : t.val = (s j).val * v.val := congrArg Subtype.val hv
  rw [hval, mul_assoc, mul_comm (v.val) b, ← mul_assoc]
  change (s j).val * j.val = _ at hq
  rw [hq]; ring

theorem dedekind_detects_purity [IsDomain R] [IsDedekindDomain R] (hnf : ¬ IsField R) :
    ResidueUpper.DetectsPurity (fun J : Ideal R => J) := by
  intro M N f inj tests
  apply pure_of_local_pivots (fun P hP => ?_) f inj
  · rintro a b ⟨z,hz⟩
    exact (ValuationMathlib.mem_principal_multiple a b).mp (tests (Ideal.span {a}) b
      ((ValuationMathlib.mem_principal_multiple a (f b)).mpr ⟨z,hz⟩))
  · letI := hP.isPrime
    letI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R
      (Ring.ne_bot_of_isMaximal_of_not_isField hP hnf) (Localization.AtPrime P)
    exact local_pivots_of_valuation P

end PureEmbeddings.DedekindPurity
