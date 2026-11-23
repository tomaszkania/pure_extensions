import PureEmbeddings.ValuationPurity
import PureEmbeddings.ResidueUpper
import PureEmbeddings.Ordinary
import PureEmbeddings.BackAndForth
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Localization.Cardinality

/-! To distinguish models at the minimum, keep the torsion part of an ordinary
universal injective and use a prescribed number of copies of the fraction
field for its torsion-free part. -/

namespace PureEmbeddings.ValuationMathlib

open Cardinal Function
open scoped nonZeroDivisors
universe u
variable {R : Type u} [CommRing R] [IsDomain R]

/-- Any vector space over the fraction field is injective over the domain.
On a nonzero ideal, the image of one nonzero scalar determines the multiplier. -/
theorem fraction_space_injective (X : Type u) [AddCommGroup X] [Module (FractionRing R) X]
    [Module R X] [IsScalarTower R (FractionRing R) X] : Module.Injective R X := by
  apply Module.Baer.injective
  intro I g
  by_cases hI : I = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    have hx0 : x = 0 := by simpa [hI] using hx
    subst x
    exact g.map_zero.symm
  obtain ⟨a,ha,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let k : FractionRing R := algebraMap R (FractionRing R) a
  have hk : k ≠ 0 := by simpa [k] using (IsFractionRing.injective R (FractionRing R)).ne hn
  let v : X := k⁻¹ • g ⟨a,ha⟩
  have cancel (x : X) : a • (k⁻¹ • x) = x := by
    rw [← IsScalarTower.algebraMap_smul (FractionRing R) a]
    simp [← smul_assoc, k,hk]
  refine ⟨LinearMap.toSpanSingleton R X v, fun b hb => ?_⟩
  change b • v = g ⟨b,hb⟩
  have eqn : b • g ⟨a,ha⟩ = a • g ⟨b,hb⟩ := by
    rw [← map_smul, ← map_smul]
    exact congrArg g (Subtype.ext (mul_comm b a))
  change b • (k⁻¹ • g ⟨a,ha⟩) = _
  rw [smul_comm, eqn, smul_comm, cancel]

/-- The torsion part of an injective module over a domain remains injective. -/
theorem torsion_injective (D : ModuleCat.{u} R) (hd : Module.Injective R D) :
    Module.Injective R (Submodule.torsion R D) := by
  apply Module.Baer.injective
  intro I f
  by_cases hI : I = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    have hx0 : x = 0 := by simpa [hI] using hx
    subst x
    exact f.map_zero.symm
  obtain ⟨g,hg⟩ := Module.Baer.of_injective hd I ((Submodule.torsion R D).subtype.comp f)
  obtain ⟨a,ha,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨b,hb⟩ := (f ⟨a,ha⟩).property
  have h1 : g 1 ∈ Submodule.torsion R D := by
    refine ⟨b * (⟨a,mem_nonZeroDivisors_of_ne_zero hn⟩ : R⁰), ?_⟩
    change ((b : R) * a) • g 1 = 0
    rw [mul_smul, ← map_smul, smul_eq_mul, mul_one, hg a ha]
    exact hb
  refine ⟨g.codRestrict _ (fun x => ?_), fun x hx => Subtype.ext (hg x hx)⟩
  have heq : g x = x • g 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  exact heq ▸ (Submodule.torsion R D).smul_mem x h1

omit [IsDomain R] in
private theorem prod_injective {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (hp : Module.Injective R P) (hq : Module.Injective R Q) :
    Module.Injective R (P × Q) := by
  constructor
  intro X Y _ _ _ _ f hf g
  obtain ⟨a,ha⟩ := hp.out f hf ((LinearMap.fst R P Q).comp g)
  obtain ⟨b,hb⟩ := hq.out f hf ((LinearMap.snd R P Q).comp g)
  exact ⟨a.prod b, fun x => Prod.ext (ha x) (hb x)⟩

/-- A module of size at most the index number, with no torsion, embeds in
the corresponding direct sum of copies of the fraction field. -/
theorem torsionFree_embeds (J : Type u) (M : ModuleCat.{u} R) [NoZeroSMulDivisors R M]
    (hm : #M ≤ #J) : ∃ f : M →ₗ[R] (J →₀ FractionRing R), Injective f := by
  classical
  let K := FractionRing R
  let X := ModuleCat.of R (J →₀ K)
  let C := ModuleCat.of R K
  have cyc (y : M) : ∃ j : (R ∙ y) →ₗ[R] C, Function.Injective j := by
    by_cases h : y = 0
    · subst y
      letI : Subsingleton (R ∙ (0:M)) := by rw [Submodule.span_zero_singleton]; infer_instance
      exact ⟨0, fun _ _ _ => Subsingleton.elim _ _⟩
    let e := (LinearEquiv.toSpanNonzeroSingleton R M y h).symm
    exact ⟨(Algebra.linearMap R K).comp e.toLinearMap,
      (IsFractionRing.injective R K).comp e.injective⟩
  exact Ordinary.universal_of_cyclic_copies_for (R := R) (K := J) (C := C) (D := X)
    (fraction_space_injective (R := R) (J →₀ K)) LinearMap.id (fun _ _ h => h) M hm cyc

/-- The ordinary injective used in the residue construction, with explicit
control of the size of its torsion-free part. -/
abbrev Controlled (D : ModuleCat.{u} R) (J : Type u) :=
  Submodule.torsion R D × (J →₀ FractionRing R)

theorem controlled_injective (D : ModuleCat.{u} R) (J : Type u) (hd : Module.Injective R D) :
    Module.Injective R (Controlled D J) :=
  prod_injective (torsion_injective D hd) (fraction_space_injective (R := R) (J →₀ FractionRing R))

theorem controlled_universal (D : ModuleCat.{u} R) (J : Type u) (hd : Module.Injective R D)
    (κ : Cardinal.{u}) (hJ : κ ≤ #J)
    (univ : ∀ M : ModuleCat.{u} R, #M ≤ κ → ∃ f : M →ₗ[R] D, Injective f)
    (M : ModuleCat.{u} R) (hm : #M ≤ κ) :
    ∃ f : M →ₗ[R] Controlled D J, Injective f := by
  let T := Submodule.torsion R M
  obtain ⟨g,hg⟩ := univ M hm
  let t : T →ₗ[R] Submodule.torsion R D := (g.comp T.subtype).codRestrict _ (by
    rintro ⟨x,a,ha⟩
    refine ⟨a,?_⟩
    change (a : R) • g x = 0
    exact (g.map_smul _ _).symm.trans ((congrArg g ha).trans g.map_zero))
  obtain ⟨f,hf⟩ := (torsion_injective D hd).out T.subtype Subtype.val_injective t
  let Q := ModuleCat.of R (M ⧸ T)
  have hQ : #Q ≤ #J := (Cardinal.mk_le_of_surjective T.mkQ_surjective).trans (hm.trans hJ)
  obtain ⟨q,hq⟩ := torsionFree_embeds J Q hQ
  let j := f.prod (q.comp T.mkQ)
  refine ⟨j,(injective_iff_map_eq_zero _).2 ?_⟩
  intro x hx
  have h1 : f x = 0 := congrArg Prod.fst hx
  have h2 : q (T.mkQ x) = 0 := congrArg Prod.snd hx
  have ht := (Submodule.Quotient.mk_eq_zero T).mp (hq (h2.trans q.map_zero.symm))
  have h3 : (t ⟨x,ht⟩ : D) = 0 := congrArg Subtype.val ((hf ⟨x,ht⟩).symm.trans h1)
  exact hg (h3.trans g.map_zero.symm)

/-- The underlying cardinal of the prescribed sum is the index cardinal. -/
theorem fractionSum_cardinal (J : Type u) (hω : ℵ₀ ≤ #J) (hR : #R ≤ #J) :
    #(J →₀ FractionRing R) = #J := by
  letI := Cardinal.aleph0_le_mk_iff.mp hω
  rw [Cardinal.mk_finsupp_of_infinite, Cardinal.mk_fractionRing, max_eq_left hR]

variable [ValuationRing R]

private abbrev Values := PositiveValue R
private abbrev principal (i : Values (R := R)) := i.val
private abbrev Model (D : ModuleCat.{u} R) (J : Type u) :=
  ResidueUpper.Model (principal (R := R)) (ModuleCat.of R (Controlled D J))

/-- A fraction-field vector space embedded in the residue model projects
injectively into the prescribed fraction-field summand. -/
theorem model_fraction_bound (D : ModuleCat.{u} R) (J X : Type u) [AddCommGroup X]
    [Module (FractionRing R) X] [Module R X] [IsScalarTower R (FractionRing R) X]
    (f : X →ₗ[R] Model D J) (hf : Injective f) : #X ≤ #(J →₀ FractionRing R) := by
  let q := (LinearMap.snd R (Submodule.torsion R D) (J →₀ FractionRing R)).comp
    ((LinearMap.fst R (Controlled D J) _).comp f)
  apply Cardinal.mk_le_of_injective (f := q)
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  have erase (i : Values (R := R)) : (f x).2 i = 0 := by
    let a := generator R i
    have ha : a ≠ 0 := (generator_spec R i).2.1
    have hk : algebraMap R (FractionRing R) a ≠ 0 := by
      simpa using (IsFractionRing.injective R (FractionRing R)).ne ha
    let z := (algebraMap R (FractionRing R) a)⁻¹ • x
    have hz : a • z = x := by
      rw [← IsScalarTower.algebraMap_smul (FractionRing R) a]
      simp [z,smul_smul,hk]
    have hm : a ∈ i.val := (generator_spec R i).2.2 ▸ Ideal.subset_span (by simp [a])
    have kill := ((f z).2 i).property a hm
    apply Subtype.ext
    rw [← hz, map_smul]
    exact kill
  obtain ⟨a,ha⟩ := ((f x).1.1).property
  have hz : f ((a : R) • x) = 0 := by
    rw [map_smul]
    apply Prod.ext
    · apply Prod.ext
      · exact Subtype.ext ha
      · change (a : R) • (q x) = 0
        rw [hx,smul_zero]
    · funext i
      change (a : R) • (f x).2 i = 0
      rw [erase i, smul_zero]
  have ax : (a : R) • x = 0 := hf (hz.trans f.map_zero.symm)
  have hne : algebraMap R (FractionRing R) (a : R) ≠ 0 := by
    simp
  exact (smul_eq_zero.mp ((IsScalarTower.algebraMap_smul (FractionRing R) (a:R) x).trans ax)).resolve_left hne

/-- Exact minimum and uniqueness at that minimum, from an ordinary universal
injective of the prescribed size. -/
theorem minimum_and_uniqueness_of_ordinary (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hR : #R < κ)
    (nf : ¬IsField R) (D : ModuleCat.{u} R)
    (size : #D ≤ κ ^ Cardinal.mk (ValuationRing.ValueGroup R (FractionRing R))ˣ)
    (hd : Module.Injective R D)
    (univ : ∀ M : ModuleCat.{u} R, #M ≤ κ → ∃ f : M →ₗ[R] D, Injective f) :
    let μ := κ ^ Cardinal.mk (ValuationRing.ValueGroup R (FractionRing R))ˣ
    HasMinimum (R := R) κ μ ∧ (UniqueAt (R := R) κ μ ↔ μ = κ) := by
  classical
  let P := PositiveValue R
  letI : Infinite P := positiveValues_infinite R nf
  let μ := κ ^ #P
  have hlarge : κ ≤ μ := self_le_power κ (one_lt_aleph0.le.trans (aleph0_le_mk P))
  have hmu : ℵ₀ ≤ μ := hω.le.trans hlarge
  have eqμ : κ ^ Cardinal.mk (ValuationRing.ValueGroup R (FractionRing R))ˣ = μ :=
    congrArg (κ ^ ·) (positiveValues_cardinal_eq_units R nf).symm
  rw [eqμ] at size ⊢
  have low (F : ModuleCat.{u} R) (hf : HasExtension κ F) : μ ≤ #F :=
    eqμ ▸ lower_of_extension R κ F hω hR nf hf
  let F (θ : Cardinal.{u}) := ModuleCat.of R (Model D θ.out)
  have params (θ : Cardinal.{u}) (lo : κ ≤ θ) (hi : θ ≤ μ) : HasExtension κ (F θ) ∧ #(F θ) = μ := by
    have hθ : κ ≤ #θ.out := by simpa using lo
    let E := ModuleCat.of R (Controlled D θ.out)
    have hE := controlled_injective D θ.out hd
    have tests : ResidueUpper.DetectsPurity (principal (R := R)) :=
      fun _ _ f hf h => pure_of_reflect_principal f hf h
    have extF : HasExtension κ (F θ) :=
      EquationCriterion.extension_of_pureInjective_and_universal κ hω hR _
        (ResidueUpper.model_pureInjective _ E hE)
        (ResidueUpper.model_pureUniversal _ κ E (controlled_universal D θ.out hd κ hθ univ) tests)
    have fr : #(θ.out →₀ FractionRing R) = θ :=
      (fractionSum_cardinal θ.out (hω.le.trans hθ) (hR.le.trans hθ)).trans (Cardinal.mk_out θ)
    have eSize : #E ≤ μ := by
      change #(Submodule.torsion R D × (θ.out →₀ FractionRing R)) ≤ μ
      simp only [Cardinal.mk_prod,Cardinal.lift_id, fr]
      exact (mul_le_mul' ((Cardinal.mk_le_of_injective (f := fun z : Submodule.torsion R D => (z : D)) Subtype.val_injective).trans size) hi).trans_eq
        (Cardinal.mul_eq_self hmu)
    have ePower : #E ^ #(Option P) ≤ μ := by
      rw [Cardinal.mk_option,Cardinal.mk_add_one_eq]
      exact (power_le_power_right eSize).trans_eq (by
        change (κ ^ #P) ^ #P = κ ^ #P
        rw [← power_mul, Cardinal.mul_eq_self (aleph0_le_mk P)])
    exact ⟨extF, le_antisymm ((ResidueUpper.model_card (principal (R := R)) E).trans ePower) (low _ extF)⟩
  have hsmall := params κ le_rfl hlarge
  refine ⟨⟨⟨F κ,hsmall⟩,low⟩, ?_, ?_⟩
  · intro uniq
    have hbig := params μ hlarge le_rfl
    obtain ⟨e⟩ := uniq (F μ) (F κ) hbig.1 hsmall.1 hbig.2 hsmall.2
    let X := μ.out →₀ FractionRing R
    let into : X →ₗ[R] F μ := (LinearMap.inl R (Controlled D μ.out) ((i : P) → ResidueUpper.killed i.val (Controlled D μ.out))).comp
      (LinearMap.inr R (Submodule.torsion R D) X)
    have inj : Injective into := fun _ _ h => congrArg Prod.snd (congrArg Prod.fst h)
    have bound := model_fraction_bound D κ.out X (e.toLinearMap.comp into) (e.injective.comp inj)
    have hκ : κ ≤ #κ.out := by simp
    have hμ : κ ≤ #μ.out := by simpa using hlarge
    rw [fractionSum_cardinal μ.out (hω.le.trans hμ) (hR.le.trans hμ),
      fractionSum_cardinal κ.out (hω.le.trans hκ) (hR.le.trans hκ), Cardinal.mk_out, Cardinal.mk_out] at bound
    exact le_antisymm bound hlarge
  · intro eqn
    rw [eqn]
    exact BackAndForth.uniqueAt hω hR

end PureEmbeddings.ValuationMathlib
