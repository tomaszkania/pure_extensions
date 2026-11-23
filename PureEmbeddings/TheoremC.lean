import PureEmbeddings.GroupPacking
import PureEmbeddings.CocyclicEmbedding
import PureEmbeddings.IntegerMultiplicity

/-! The extension and coordinate assertions for Kostana's abelian group. -/
namespace PureEmbeddings.Groups
open Cardinal

theorem kostana_extension_iff {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) :
    HasExtension (R := ℤ) κ (ModuleCat.of ℤ (kostanaGroup κ hκ.le)) ↔ ℵ₀ < κ.ord.cof := by
  refine ⟨kostana_extension_cofinality hκ, fun hc => ?_⟩
  apply kostana_extension_of_cocyclic_embeddings hκ hc
  intro M hM
  obtain ⟨T,t,hT,f,hf⟩ := exists_cocyclic_embedding M
  exact ⟨T,t,hT.trans_lt (max_lt hκ hM),f,hf⟩

/-- The full Theorem C in the standard universe of abelian groups. -/
theorem theoremC (κ : Cardinal.{0}) : TheoremC κ := by
  intro hk
  refine ⟨kostana_cardinal κ hk.le, kostana_extension_iff hk, kostana_local_iff_regular κ hk.le,
    fun J hJ => ⟨full_coordinate_product_splits κ hk.le _ J hJ, ?_⟩, IntegerMultiplicity.many κ hk⟩
  exact factors_product_pureInjective (fun j : J => j.val.2)

end PureEmbeddings.Groups
