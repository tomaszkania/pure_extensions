import PureEmbeddings.Universality
import PureEmbeddings.CriterionMathlib
import PureEmbeddings.PureInjectivity
import PureEmbeddings.Statements

/-! The extension criterion, with the same inclusive bound on the size of
modules to be embedded as in the paper. -/
namespace PureEmbeddings
open Cardinal
universe u
theorem extension_iff {R : Type u} [Ring R] {κ : Cardinal.{u}}
    (hκ : ℵ₀ < κ) (hR : Cardinal.mk R < κ) (F : ModuleCat.{u} R) :
    HasExtension κ F ↔ IsPureInjective F ∧ UniversalUpTo κ F := by
  constructor
  · exact fun h => ⟨h.pureInjective hκ hR, h.universal_le hκ hR⟩
  · exact fun h => EquationCriterion.extension_of_pureInjective_and_universal κ hκ hR F h.1 h.2
end PureEmbeddings
