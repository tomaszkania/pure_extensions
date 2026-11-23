import PureEmbeddings.Statements
import PureEmbeddings.PureSemisimple
import PureEmbeddings.GeneralUpper
import PureEmbeddings.GeneralLower
import PureEmbeddings.BackAndForth
import PureEmbeddings.OrdinaryBounds
import PureEmbeddings.MatrixCompact
import Mathlib.Algebra.Module.ULift
import Mathlib.RingTheory.Noetherian.Basic

/-! # The arbitrary-ring dichotomy and its countable-ring specialisation -/
namespace PureEmbeddings
open Cardinal Function
universe u

attribute [local instance 10] ULift.module ULift.smulLeft

private abbrev Z := ULift.{u} ℤ

private instance : IsNoetherianRing Z := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm

private theorem sizeIntegers : Cardinal.mk Z ≤ (ℵ₀ : Cardinal.{u}) :=
  Cardinal.mk_le_aleph0_iff.mpr inferInstance

private def liftIntMap {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module Z A] [Module Z B] (f : A →+ B) : A →ₗ[Z] B where
  toFun := f
  map_add' := f.map_add
  map_smul' s x := by
    simp only [RingHom.id_apply]
    have h : (s.down : Z) = s := ULift.ext _ _ (by simp)
    rw [← h,Int.cast_smul_eq_zsmul,Int.cast_smul_eq_zsmul]
    exact f.map_zsmul _ _

private theorem ofLiftedIntegers (κ : Cardinal.{u}) (D : ModuleCat.{u} Z)
    (inj : Module.Injective Z D)
    (univ : ∀ A : ModuleCat.{u} Z, Cardinal.mk A ≤ κ → ∃ f : A →ₗ[Z] D, Injective f) :
    GeneralUpper.InjectiveGroup D ∧ GeneralUpper.UniversalGroup D κ := by
  constructor
  · intro A B i f hi
    let i' : A →ₗ[Z] B := liftIntMap i.toAddMonoidHom
    let f' : A →ₗ[Z] D := liftIntMap f.toAddMonoidHom
    obtain ⟨g,hg⟩ := inj.out i' hi f'
    exact ⟨g.toAddMonoidHom.toIntLinearMap,LinearMap.ext hg⟩
  · intro A ha
    obtain ⟨f,hf⟩ := univ (ModuleCat.of Z A) ha
    exact ⟨f.toAddMonoidHom.toIntLinearMap,hf⟩

private theorem upper_of_ordinary_int {R : Type u} [Ring R]
    (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hr : Cardinal.mk R < κ)
    (hd : ∃ D : ModuleCat.{u} Z, Cardinal.mk D ≤ κ ∧ Module.Injective Z D ∧
      ∀ A : ModuleCat.{u} Z, Cardinal.mk A ≤ κ → ∃ f : A →ₗ[Z] D, Injective f) :
    ∃ F : ModuleCat.{u} R, HasExtension κ F ∧ Cardinal.mk F ≤ κ ^ max (Cardinal.mk R) ℵ₀ := by
  obtain ⟨D,hD,inj,univ⟩ := hd
  obtain ⟨di,du⟩ := ofLiftedIntegers κ D inj univ
  exact GeneralUpper.upper_of_group D κ hω hr hD di du

/-- The general upper estimate, including non-commutative rings. -/
theorem arbitraryRing_upper (R : Type u) [Ring R] (κ : Cardinal.{u})
    (hk : ℵ₀ < κ) (hr : Cardinal.mk R < κ) :
    ∃ F : ModuleCat.{u} R, HasExtension κ F ∧ Cardinal.mk F ≤ κ ^ max (Cardinal.mk R) ℵ₀ :=
  upper_of_ordinary_int κ hk hr (Ordinary.exists_universal_noetherian Z κ hk.le (sizeIntegers.trans hk.le))

/-- Failure of left pure-semisimplicity forces the countable power lower bound. -/
theorem nonSemisimple_lower (R : Type u) [Ring R] (κ : Cardinal.{u})
    (hk : ℵ₀ < κ) (hr : Cardinal.mk R < κ) (hn : ¬ LeftPureSemisimple.{u} R)
    (F : ModuleCat.{u} R) (hF : HasExtension κ F) : κ ^ ℵ₀ ≤ Cardinal.mk F := by
  obtain ⟨M,codes,chain⟩ := MatrixDCC.exists_strict_chain hn
  exact GeneralLower.bound_of_strict_chain κ hk hr F M hF codes chain

/-- Theorem A of the paper, for any non-zero unital ring and any cardinal. -/
theorem theoremA (R : Type u) [Ring R] [Nontrivial R] (κ : Cardinal.{u}) :
    TheoremA R κ := by
  intro hκ
  have hk := lt_of_le_of_lt (le_max_right _ _) hκ
  have hr := lt_of_le_of_lt (le_max_left _ _) hκ
  refine ⟨PureSemisimple.minimum κ hk hr, fun hn => ⟨nonSemisimple_lower R κ hk hr hn,
    arbitraryRing_upper R κ hk hr⟩, BackAndForth.uniqueAt hk hr, ?_⟩
  intro F hsize hF
  exact ⟨fun _ f g hA hf hg => BackAndForth.equiv_over hk hr hF hF hsize hsize hA f g hf hg,
    hF.universal_le hk hr⟩

/-- The exact dichotomy for countable rings, with no unproved input. -/
theorem countable_dichotomy (R : Type u) [Ring R] [Nontrivial R] [Countable R]
    (κ : Cardinal.{u}) (hk : ℵ₀ < κ) :
    (LeftPureSemisimple.{u} R → HasMinimum (R := R) κ κ) ∧
    (¬ LeftPureSemisimple.{u} R → HasMinimum (R := R) κ (κ ^ ℵ₀)) :=
  countable_dichotomy_of_A R κ hk (theoremA R κ)

end PureEmbeddings
