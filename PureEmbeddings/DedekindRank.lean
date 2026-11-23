import PureEmbeddings.ValuationRank
import PureEmbeddings.DedekindMinimum
import PureEmbeddings.PureInjectivity

/-! The fraction-field multiplicity in the Dedekind-domain models is
independent of any additional torsion summands. -/

noncomputable section
namespace PureEmbeddings.DedekindRank
open Cardinal Function
open scoped nonZeroDivisors
universe u
variable {R : Type u} [CommRing R] [IsDomain R]

/-- An arbitrary torsion summand, all residue tests, and J copies of the fraction field. -/
abbrev Model (D T : ModuleCat.{u} R) (J : Type u) :=
  (T × ResidueUpper.Model (fun I : Ideal R => I) D) × (J →₀ FractionRing R)

theorem fraction_bound (D T : ModuleCat.{u} R) (hT : Module.IsTorsion R T)
    (J X : Type u) [AddCommGroup X] [Module (FractionRing R) X] [Module R X]
    [IsScalarTower R (FractionRing R) X] (f : X →ₗ[R] Model D T J) (hf : Injective f) :
    #X ≤ #(D × D × (J →₀ FractionRing R)) := by
  let read (x : X) : D × D × (J →₀ FractionRing R) := ((f x).1.2.1,((f x).1.2.2 ⊥).val,(f x).2)
  have zero (x : X) (h : read x = 0) : x = 0 := by
    have d0 : (f x).1.2.1 = 0 := congrArg Prod.fst h
    have d1 : ((f x).1.2.2 ⊥).val = 0 := congrArg (fun z : D × D × (J →₀ FractionRing R) => z.2.1) h
    have d2 : (f x).2 = 0 := congrArg (fun z : D × D × (J →₀ FractionRing R) => z.2.2) h
    have all_zero (I : Ideal R) : (f x).1.2.2 I = 0 := by
      by_cases hI : I = ⊥
      · subst I
        exact Subtype.ext d1
      obtain ⟨a,ha,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      have hk : algebraMap R (FractionRing R) a ≠ 0 := by
        simpa using (IsFractionRing.injective R (FractionRing R)).ne hn
      let z := (algebraMap R (FractionRing R) a)⁻¹ • x
      have hz : a • z = x := by
        rw [← IsScalarTower.algebraMap_smul (FractionRing R) a]
        simp [z,smul_smul,hk]
      have kill := ((f z).1.2.2 I).property a ha
      apply Subtype.ext
      rw [← hz, map_smul]
      exact kill
    obtain ⟨a,ha⟩ := hT (x := (f x).1.1)
    have all : f ((a:R) • x) = 0 := by
      rw [map_smul]
      apply Prod.ext
      · apply Prod.ext
        · exact ha
        · apply Prod.ext
          · change (a:R) • (f x).1.2.1 = 0
            rw [d0, smul_zero]
          · funext i
            change (a:R) • (f x).1.2.2 i = 0
            rw [all_zero i,smul_zero]
      · change (a:R) • (f x).2 = 0
        rw [d2,smul_zero]
    have ax : (a:R) • x = 0 := hf (all.trans f.map_zero.symm)
    exact (smul_eq_zero.mp ((IsScalarTower.algebraMap_smul (FractionRing R) (a:R) x).trans ax)).resolve_left (by simp)
  apply Cardinal.mk_le_of_injective (f := read)
  intro x y h
  apply sub_eq_zero.mp
  apply zero
  change ((f (x-y)).1.2.1, ((f (x-y)).1.2.2 ⊥).val, (f (x-y)).2) = 0
  have diff : read x - read y = 0 := sub_eq_zero.mpr h
  simpa only [read, map_sub] using diff

/-- The index cardinal of a fraction-field summand is invariant under an
isomorphism, even when extra torsion summands change. -/
theorem index_le_of_embedding (D T S : ModuleCat.{u} R)
    (hT : Module.IsTorsion R T) (I J : Type u) (hI : ℵ₀ ≤ #I) (hJ : ℵ₀ ≤ #J)
    (hRI : #R ≤ #I) (hRJ : #R ≤ #J) (hd : #D ≤ #J)
    (f : Model D S I →ₗ[R] Model D T J) (hf : Injective f) : #I ≤ #J := by
  let X := I →₀ FractionRing R
  let start : X →ₗ[R] Model D S I := LinearMap.inr R _ X
  have bound := fraction_bound D T hT J X (f.comp start) (hf.comp (fun _ _ he => congrArg Prod.snd he))
  rw [ValuationMathlib.fractionSum_cardinal I hI hRI] at bound
  apply bound.trans
  simp only [Cardinal.mk_prod,Cardinal.lift_id,ValuationMathlib.fractionSum_cardinal J hJ hRJ]
  exact (mul_le_mul' hd ((mul_le_mul' hd le_rfl).trans_eq (Cardinal.mul_eq_self hJ))).trans_eq
    (Cardinal.mul_eq_self hJ)

omit [IsDomain R] in
/-- The direct product of two pure-injectives is pure-injective. -/
theorem pureInjective_prod (A B : ModuleCat.{u} R) (hA : IsPureInjective A) (hB : IsPureInjective B) :
    IsPureInjective (ModuleCat.of R (A × B)) := by
  intro P Q i t hi
  obtain ⟨f,hf⟩ := hA P Q i ((LinearMap.fst R A B).comp t) hi
  obtain ⟨g,hg⟩ := hB P Q i ((LinearMap.snd R A B).comp t) hi
  exact ⟨f.prod g, LinearMap.ext fun x => Prod.ext (DFunLike.congr_fun hf x) (DFunLike.congr_fun hg x)⟩

omit [IsDomain R] in
/-- Ordinary injectivity implies pure injectivity. -/
theorem pureInjective_of_injective (A : ModuleCat.{u} R) (hA : Module.Injective R A) : IsPureInjective A := by
  intro P Q i t hi
  obtain ⟨g,hg⟩ := hA.out i hi.1 t
  exact ⟨g,LinearMap.ext hg⟩

omit [IsDomain R] in
/-- Adjoining any pure-injective module to a module with (Eκ) preserves (Eκ). -/
theorem extension_prod_right (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hR : #R < κ)
    (A B : ModuleCat.{u} R) (hA : HasExtension κ A) (hB : IsPureInjective B) :
    HasExtension κ (ModuleCat.of R (A × B)) := by
  apply EquationCriterion.extension_of_pureInjective_and_universal κ hω hR
  · exact pureInjective_prod _ _ (hA.pureInjective hω hR) hB
  · intro M hm
    obtain ⟨f,hf⟩ := hA.universal_le hω hR M hm
    let i := LinearMap.inl R A B
    have hi : IsPureMap i := isPureMap_of_retraction (A := A) (B := ModuleCat.of R (A × B))
      i (LinearMap.fst R A B) (fun _ => rfl)
    exact ⟨i.comp f, IsPureMap.comp (A := M) (B := A) (C := ModuleCat.of R (A × B)) hi hf⟩

omit [IsDomain R] in
theorem extension_prod_left (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hR : #R < κ)
    (A B : ModuleCat.{u} R) (hA : IsPureInjective A) (hB : HasExtension κ B) :
    HasExtension κ (ModuleCat.of R (A × B)) :=
  (extension_prod_right κ hω hR B A hB hA).of_equiv (LinearEquiv.prodComm R B A)

abbrev MinimumSize (R : Type u) [CommRing R] (κ : Cardinal.{u}) :=
  κ ^ max ℵ₀ #({p : Ideal R // p.IsMaximal})

variable [IsDedekindDomain R]

/-- Adjoining the requested torsion and fraction-field summands preserves
both the extension property and its minimum cardinal. -/
theorem model_extension_size (hnf : ¬IsField R) (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hR : #R < κ)
    (D : ModuleCat.{u} R) (size : #D ≤ κ) (hd : Module.Injective R D)
    (univ : ∀ M : ModuleCat.{u} R, #M ≤ κ → ∃ f : M →ₗ[R] D, Injective f)
    (T : ModuleCat.{u} R) (hT : IsPureInjective T) (tsize : #T ≤ MinimumSize R κ)
    (J : Type u) (lo : κ ≤ #J) (hi : #J ≤ MinimumSize R κ) :
    HasExtension κ (ModuleCat.of R (Model D T J)) ∧ #(Model D T J) = MinimumSize R κ := by
  let U := ModuleCat.of R (ResidueUpper.Model (fun I : Ideal R => I) D)
  let X := ModuleCat.of R (J →₀ FractionRing R)
  let τ := max ℵ₀ #({p : Ideal R // p.IsMaximal})
  let μ := MinimumSize R κ
  have hτ : ℵ₀ ≤ τ := le_max_left ..
  have hkm : κ ≤ μ := self_le_power κ (one_lt_aleph0.le.trans hτ)
  have hm : ℵ₀ ≤ μ := hω.le.trans hkm
  have hu : HasExtension κ U := EquationCriterion.extension_of_pureInjective_and_universal κ hω hR U
    (ResidueUpper.model_pureInjective _ D hd)
    (ResidueUpper.model_pureUniversal _ κ D univ (DedekindPurity.dedekind_detects_purity hnf))
  have hx := pureInjective_of_injective X (ValuationMathlib.fraction_space_injective (R := R) X)
  have extF := extension_prod_right κ hω hR (ModuleCat.of R (T × U)) X
    (extension_prod_left κ hω hR T U hT hu) hx
  refine ⟨extF,le_antisymm ?_ (DedekindMathlib.dedekind_lower hnf κ _ hω hR extF)⟩
  have co : #(Option (Ideal R)) ≤ τ := by
    rw [Cardinal.mk_option]
    exact (add_le_add (DedekindMathlib.ideal_count R) (one_lt_aleph0.le.trans hτ)).trans_eq
      (Cardinal.add_eq_self hτ)
  have uSize : #U ≤ μ := (ResidueUpper.model_card (fun I : Ideal R => I) D).trans
    ((power_le_power_right size).trans (power_le_power_left (aleph0_pos.trans hω).ne' co))
  change #((T × U) × (J →₀ FractionRing R)) ≤ μ
  simp only [Cardinal.mk_prod,Cardinal.lift_id,
    ValuationMathlib.fractionSum_cardinal J (hω.le.trans lo) (hR.le.trans lo)]
  exact (mul_le_mul' ((mul_le_mul' tsize uSize).trans_eq (Cardinal.mul_eq_self hm)) hi).trans_eq
    (Cardinal.mul_eq_self hm)

/-- Uniqueness at the Dedekind minimum holds exactly when its size is κ.
The distinguishing invariant is the size of an embedded fraction-field space. -/
theorem unique_iff (hnf : ¬IsField R) (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hR : #R < κ) :
    UniqueAt (R := R) κ (MinimumSize R κ) ↔ MinimumSize R κ = κ := by
  obtain ⟨D,size,hd,univ⟩ := Ordinary.exists_universal_noetherian R κ hω.le hR.le
  let μ := MinimumSize R κ
  have hkμ : κ ≤ μ := self_le_power κ (one_lt_aleph0.le.trans (le_max_left ..))
  let T := ModuleCat.of R (⊥ : Submodule R R)
  haveI : Subsingleton T := inferInstanceAs (Subsingleton (⊥ : Submodule R R))
  have hT : IsPureInjective T := by
    intro A B i f hi
    exact ⟨0, LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  have tor : Module.IsTorsion R T := fun {_} => ⟨1,Subsingleton.elim _ _⟩
  have tsize : #T ≤ μ := (show #T ≤ 1 by simp).trans
    (one_lt_aleph0.le.trans (hω.le.trans hkμ))
  constructor
  · intro uniq
    have small := model_extension_size hnf κ hω hR D size hd univ T hT tsize κ.out
      (by simp) (by simpa using hkμ)
    have large := model_extension_size hnf κ hω hR D size hd univ T hT tsize μ.out
      (by simpa using hkμ) (by simp [μ])
    obtain ⟨e⟩ := uniq _ _ large.1 small.1 large.2 small.2
    have bound := index_le_of_embedding D T T tor μ.out κ.out
      (by simpa using hω.le.trans hkμ) (by simpa using hω.le)
      (by simpa using hR.le.trans hkμ) (by simpa using hR.le) (by simpa using size) e.toLinearMap e.injective
    exact (show μ ≤ κ by simpa using bound).antisymm hkμ
  · intro equal
    rw [equal]
    exact BackAndForth.uniqueAt hω hR

end PureEmbeddings.DedekindRank
