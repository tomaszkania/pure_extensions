import PureEmbeddings.DedekindMultiplicity
import PureEmbeddings.Multiplicity

/-! The minimum, uniqueness and independent multiplicities over Dedekind domains. -/
namespace PureEmbeddings
open Cardinal
universe u
theorem theoremB (S : Type u) [CommRing S] [IsDedekindDomain S] (κ : Cardinal.{u}) :
    TheoremB S κ := by
  intro nf bound
  have hκ := (le_max_right _ _).trans_lt bound
  have hS := (le_max_left _ _).trans_lt bound
  exact ⟨DedekindMathlib.dedekind_minimum S nf κ hκ hS,
    DedekindRank.unique_iff nf κ hκ hS, fun hμ =>
    (count_models (R := S) _ κ _ hμ (DedekindMultiplicity.models nf κ hκ hS)).2⟩
end PureEmbeddings
