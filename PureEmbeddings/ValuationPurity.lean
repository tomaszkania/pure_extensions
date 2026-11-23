import PureEmbeddings.ValuationMathlib

/-! Over a valuation domain, a linear embedding is pure as soon as it reflects
the solubility of the single equations `t • x = b`. The proof eliminates one
row at a time, using a coefficient that divides all remaining coefficients. -/

namespace PureEmbeddings.ValuationMathlib
universe u
open scoped BigOperators
variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

private def rowValue {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (r : Fin n → R) (x : Fin n → M) := ∑ j, r j • x j

omit [IsDomain R] [ValuationRing R] in
private theorem row_eliminate {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (r q : Fin n → R) (d : R) (x : Fin n → M) :
    rowValue (fun j => r j - d * q j) x = rowValue r x - d • rowValue q x := by
  simp [rowValue, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]

omit [IsDomain R] [ValuationRing R] in
private theorem row_correct {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (r : Fin n → R) (x : Fin n → M) (p : Fin n) (w : M) :
    rowValue r (fun j => x j + if j = p then w else 0) = rowValue r x + r p • w := by
  classical
  simp only [rowValue, smul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private theorem partial_system {m n : ℕ} (f : A →ₗ[R] B) (inj : Function.Injective f)
    (reflect : ∀ (t : R) (b : A), (∃ v : B, t • v = f b) → ∃ u : A, t • u = b)
    (T : Finset (Fin m)) (r : Fin m → Fin n → R) (b : Fin m → A) (y : Fin n → B)
    (hy : ∀ i ∈ T, rowValue (r i) y = f (b i)) :
    ∃ x : Fin n → A, ∀ i ∈ T, rowValue (r i) x = b i := by
  classical
  induction T using Finset.strongInductionOn generalizing r b with
  | _ T ih =>
    by_cases hT : T.Nonempty
    · by_cases hn : Nonempty (Fin n)
      · let S := T ×ˢ (Finset.univ : Finset (Fin n))
        let coeff (p : Fin m × Fin n) := r p.1 p.2
        obtain ⟨a,ha,hdiv⟩ := finite_common_divisor_mem R (S.image coeff)
          ((hT.product ⟨hn.some, Finset.mem_univ _⟩).image coeff)
        obtain ⟨⟨i₀,j₀⟩, hp, hcoef⟩ := Finset.mem_image.mp ha
        have hi₀ : i₀ ∈ T := (Finset.mem_product.mp hp).1
        change r i₀ j₀ = a at hcoef
        have dvd (i) (hi : i ∈ T) (j) : a ∣ r i j :=
          hdiv _ (Finset.mem_image.mpr ⟨(i,j), Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩,rfl⟩)
        choose c hc using dvd i₀ hi₀
        let d (i : Fin m) := if hi : i ∈ T then (dvd i hi j₀).choose else 0
        have hd (i) (hi : i ∈ T) : r i j₀ = a * d i := by
          simpa [d,hi] using (dvd i hi j₀).choose_spec
        let r' (i : Fin m) (j : Fin n) := r i j - d i * r i₀ j
        let b' (i : Fin m) := b i - d i • b i₀
        obtain ⟨x,hx⟩ := ih (T.erase i₀) (Finset.erase_ssubset hi₀) r' b' (by
          intro i hi
          rw [show rowValue (r' i) y = _ from row_eliminate (r i) (r i₀) (d i) y,
            hy i (Finset.mem_of_mem_erase hi), hy i₀ hi₀]
          simp [b'])
        have hrow {M : Type u} [AddCommGroup M] [Module R M] (z : Fin n → M) :
            rowValue (r i₀) z = a • rowValue c z := by
          simp only [rowValue, hc, mul_smul, Finset.smul_sum]
        have hmap : f (rowValue (r i₀) x) = rowValue (r i₀) (f ∘ x) := by
          simp only [rowValue, map_sum, map_smul, Function.comp_apply]
        obtain ⟨w,hw⟩ := reflect a (b i₀ - rowValue (r i₀) x) (by
          refine ⟨rowValue c y - rowValue c (f ∘ x), ?_⟩
          rw [smul_sub, ← hrow, ← hrow, hy i₀ hi₀, map_sub, hmap])
        refine ⟨fun j => x j + if j = j₀ then w else 0, ?_⟩
        intro i hi
        rw [row_correct]
        by_cases eqn : i = i₀
        · subst i
          rw [hcoef, hw]
          abel
        · have reduced := hx i (Finset.mem_erase.mpr ⟨eqn,hi⟩)
          change rowValue (fun j => r i j - d i * r i₀ j) x = b i - d i • b i₀ at reduced
          rw [row_eliminate] at reduced
          rw [hd i hi, mul_comm a, mul_smul, hw, smul_sub]
          rw [sub_eq_iff_eq_add.mp reduced]
          abel
      · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hn
        refine ⟨fun _ => 0, fun i hi => inj ?_⟩
        simpa [rowValue] using hy i hi
    · exact ⟨fun _ => 0, fun i hi => False.elim (hT ⟨i,hi⟩)⟩

/-- Scalar divisibility and injectivity detect all finite systems. -/
theorem pure_of_reflect_scalar (f : A →ₗ[R] B) (inj : Function.Injective f)
    (reflect : ∀ (t : R) (b : A), (∃ v : B, t • v = f b) → ∃ u : A, t • u = b) :
    IsPureMap f := by
  refine ⟨inj, ?_⟩
  rintro m n r b ⟨y,hy⟩
  obtain ⟨x,hx⟩ := partial_system f inj reflect Finset.univ r b y (fun i _ => hy i)
  exact ⟨x, fun i => hx i (Finset.mem_univ i)⟩

omit [IsDomain R] [ValuationRing R] in
theorem mem_principal_multiple {M : Type u} [AddCommGroup M] [Module R M] (a : R) (b : M) :
    b ∈ (Ideal.span {a}) • (⊤ : Submodule R M) ↔ ∃ w : M, a • w = b := by
  rw [Submodule.ideal_span_singleton_smul]
  change (∃ w ∈ (⊤ : Submodule R M), a • w = b) ↔ _
  simp

/-- Only the nonzero proper principal ideals are needed to test purity. -/
theorem pure_of_reflect_principal (f : A →ₗ[R] B) (inj : Function.Injective f)
    (reflect : ∀ (i : PositiveValue R) (b : A),
      f b ∈ i.val • (⊤ : Submodule R B) → b ∈ i.val • (⊤ : Submodule R A)) :
    IsPureMap f := by
  apply pure_of_reflect_scalar f inj
  rintro a b ⟨v,hv⟩
  by_cases ha : a = 0
  · subst a
    exact ⟨0, inj (by simpa using hv)⟩
  by_cases hu : IsUnit a
  · obtain ⟨g,rfl⟩ := hu
    exact ⟨(↑g⁻¹ : R) • b, by simp [smul_smul]⟩
  have hm : a ∈ IsLocalRing.maximalIdeal R := by
    by_contra h
    exact hu (IsLocalRing.notMem_maximalIdeal.mp h)
  let i : PositiveValue R := ⟨Ideal.span {a}, a, hm, ha, rfl⟩
  exact (mem_principal_multiple a b).mp (reflect i b ((mem_principal_multiple a (f b)).mpr ⟨v,hv⟩))

end PureEmbeddings.ValuationMathlib
