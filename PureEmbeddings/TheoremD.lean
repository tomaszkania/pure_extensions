import PureEmbeddings.Statements
import PureEmbeddings.ValuationRank
import PureEmbeddings.OrdinaryFixed

/-! # The minimum and its uniqueness over non-field valuation domains -/
namespace PureEmbeddings
open Cardinal ValuationMathlib
universe u

/-- For a non-field valuation domain, the least size is κ^|Γ|. There is
a unique isomorphism type at that size exactly when it equals κ. -/
theorem theoremD (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (κ : Cardinal.{u}) :
    TheoremD R κ := by
  intro nf hκ
  have hω : ℵ₀ < κ := (le_max_right _ _).trans_lt hκ
  have hR : #R < κ := (le_max_left _ _).trans_lt hκ
  let τ := Cardinal.mk (ValuationRing.ValueGroup R (FractionRing R))ˣ
  let μ := κ ^ τ
  letI := positiveValues_infinite R nf
  have v : #(PositiveValue R) = τ := positiveValues_cardinal_eq_units R nf
  have hτ : ℵ₀ ≤ τ := (aleph0_le_mk (PositiveValue R)).trans_eq v
  have htk : τ < κ := v ▸ (positiveValues_cardinal_le R).trans_lt hR
  have hkm : κ ≤ μ := self_le_power κ (one_lt_aleph0.le.trans hτ)
  have hids : #(Ideal R) ≤ μ := (ideals_cardinal_le R nf).trans
    (power_le_power_right ((nat_lt_aleph0 2).le.trans hω.le))
  have hpow : μ ^ τ = μ := by
    change (κ ^ τ) ^ τ = κ ^ τ
    rw [← power_mul, Cardinal.mul_eq_self hτ]
  obtain ⟨D,size,hd,univ⟩ := Ordinary.exists_universal_fixed R κ τ μ hτ htk hkm
    (hR.le.trans hkm) hids hpow (ideal_generators R nf)
  exact minimum_and_uniqueness_of_ordinary κ hω hR nf D size hd univ

end PureEmbeddings
