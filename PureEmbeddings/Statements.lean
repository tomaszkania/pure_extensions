import PureEmbeddings.ModuleTheory
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# The paper's statements for arbitrary rings, Dedekind domains and valuation domains

This file defines the propositions so their statements can be read independently
of the proofs. The dedicated theorem files prove the results. Theorem C uses the
concrete supported group defined in `GroupsMathlib`.
-/
namespace PureEmbeddings
open Cardinal
universe u

def UniversalUpTo {R : Type u} [Ring R] (κ : Cardinal.{u}) (F : ModuleCat.{u} R) : Prop :=
  ∀ M : ModuleCat.{u} R, Cardinal.mk M ≤ κ → ∃ f : M →ₗ[R] F, IsPureMap f

/-- The formulation with two maps out of the same module is equivalent to
extending an isomorphism between their pure images. -/
def HomogeneousBelow {R : Type u} [Ring R] (κ : Cardinal.{u}) (F : ModuleCat.{u} R) : Prop :=
  ∀ (A : ModuleCat.{u} R) (f g : A →ₗ[R] F), Cardinal.mk A < κ → IsPureMap f →
    IsPureMap g → ∃ e : F ≃ₗ[R] F, e.toLinearMap.comp f = g

def TheoremA (R : Type u) [Ring R] [Nontrivial R] (κ : Cardinal.{u}) : Prop :=
  max (Cardinal.mk R) ℵ₀ < κ →
    (LeftPureSemisimple.{u} R → HasMinimum (R := R) κ κ) ∧
    (¬ LeftPureSemisimple.{u} R →
      (∀ F : ModuleCat.{u} R, HasExtension κ F → κ ^ ℵ₀ ≤ Cardinal.mk F) ∧
      ∃ F : ModuleCat.{u} R, HasExtension κ F ∧ Cardinal.mk F ≤ κ ^ max (Cardinal.mk R) ℵ₀) ∧
    UniqueAt (R := R) κ κ ∧
    ∀ F : ModuleCat.{u} R, Cardinal.mk F = κ → HasExtension κ F →
      HomogeneousBelow κ F ∧ UniversalUpTo κ F

def TheoremB (S : Type u) [CommRing S] [IsDedekindDomain S] (κ : Cardinal.{u}) : Prop :=
  ¬ IsField S → max (Cardinal.mk S) ℵ₀ < κ →
    let primes := Cardinal.mk {p : Ideal S // p.IsMaximal}
    let μ := κ ^ max ℵ₀ primes
    HasMinimum (R := S) κ μ ∧ (UniqueAt (R := S) κ μ ↔ μ = κ) ∧
      (κ < μ → ∃ I : Type u, Nonempty (I ≃ Set.Icc κ μ) ∧
        ManyAtMinimum (R := S) κ μ (Cardinal.mk I ^ (primes + 1)))

/-- Mathlib calls the value group *with zero* `ValuationRing.ValueGroup`.
Its units are exactly the value group Γ occurring in the paper. -/
def TheoremD (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] (κ : Cardinal.{u}) : Prop :=
  ¬ IsField V → max (Cardinal.mk V) ℵ₀ < κ →
    let μ := κ ^ Cardinal.mk (ValuationRing.ValueGroup V (FractionRing V))ˣ
    HasMinimum (R := V) κ μ ∧ (UniqueAt (R := V) κ μ ↔ μ = κ)

/-- The general bounds specialise to an exact minimum over a countable ring.
The ring-theoretic bounds are hypotheses here, as recorded by `TheoremA`. -/
theorem countable_dichotomy_of_A (R : Type u) [Ring R] [Nontrivial R] [Countable R]
    (κ : Cardinal.{u}) (hκ : ℵ₀ < κ) (hA : TheoremA R κ) :
    (LeftPureSemisimple.{u} R → HasMinimum (R := R) κ κ) ∧
    (¬ LeftPureSemisimple.{u} R → HasMinimum (R := R) κ (κ ^ ℵ₀)) := by
  have hR : Cardinal.mk R ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr inferInstance
  obtain ⟨hs, hn, _⟩ := hA (by simpa [max_eq_right hR] using hκ)
  refine ⟨hs, fun h => ?_⟩
  obtain ⟨low, hi⟩ := hn h
  apply hasMinimum_of_bounds low
  simpa [max_eq_right hR] using hi

/-- Counting non-isomorphic modules by varying integer cardinals in an interval
precludes uniqueness whenever the interval offers at least two choices. -/
theorem ManyAtMinimum.not_unique {R : Type u} [Ring R] {κ μ θ : Cardinal.{u}}
    (h : ManyAtMinimum (R := R) κ μ θ) (hθ : 1 < θ) : ¬ UniqueAt (R := R) κ μ := by
  obtain ⟨I, F, rfl, hF, sep⟩ := h
  haveI : Nontrivial I := Cardinal.one_lt_iff_nontrivial.mp hθ
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  intro hu
  obtain ⟨e⟩ := hu _ _ (hF i).1 (hF j).1 (hF i).2 (hF j).2
  exact (sep i j hij).false e

end PureEmbeddings
