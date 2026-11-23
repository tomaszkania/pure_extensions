import PureEmbeddings.DedekindPrimeRank
import PureEmbeddings.DedekindEnvelope

/-! Minimal Dedekind modules with independently assigned prime and rational
multiplicities. Essential injective extensions preserve the chosen socles. -/
noncomputable section
namespace PureEmbeddings.DedekindMultiplicity
open Cardinal Function
open scoped Cardinal nonZeroDivisors
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- Each rank assignment produces a module of the exact minimum size.
An isomorphism forces equality of every assigned cardinal. -/
theorem models (hnf : ¬ IsField R) (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hR : #R < κ)
    (T : Type u) (c : T → Cardinal.{u}) (bounds : ∀ t, κ ≤ c t ∧ c t ≤ DedekindRank.MinimumSize R κ) :
    ∃ M : (Option (Maximals R) → T) → ModuleCat.{u} R,
      (∀ f, HasExtension κ (M f) ∧ #(M f) = DedekindRank.MinimumSize R κ) ∧
      ∀ f g, Nonempty (M f ≃ₗ[R] M g) → ∀ i, c (f i) = c (g i) := by
  classical
  let P := Maximals R
  let τ := max ℵ₀ #P
  let μ := DedekindRank.MinimumSize R κ
  have hτ : ℵ₀ ≤ τ := le_max_left ..
  have hκμ : κ ≤ μ := self_le_power _ (one_le_aleph0.trans hτ)
  have fixed : μ ^ τ = μ := by
    change (κ^τ)^τ = κ^τ
    rw [← Cardinal.power_mul, Cardinal.mul_eq_self hτ]
  obtain ⟨D,hD,injD,univ⟩ := Ordinary.exists_universal_noetherian R κ hω.le hR.le
  obtain ⟨D',hD',injD',univ'⟩ := Ordinary.exists_universal_noetherian R μ (hω.le.trans hκμ) (hR.le.trans hκμ)
  let rank (f : Option P → T) (p : P) := c (f (some p))
  let X (f : Option P → T) := ModuleCat.of R (TorsionResidues (rank f))
  let J (f : Option P → T) := (c (f none)).out
  have hJ (f : Option P → T) : #(J f) = c (f none) := Cardinal.mk_out _
  have small (f : Option P → T) : #(X f) ≤ μ := residues_bound fixed
    (le_max_right ..) (hR.le.trans hκμ) (fun p => hω.le.trans (bounds _).1) (fun p => (bounds _).2)
  choose j hj using fun f => univ' (X f) (small f)
  choose E e hinj he hsize ess using fun f => DedekindEnvelope.exists_essential injD' (j f) (hj f)
  let M (f : Option P → T) := ModuleCat.of R (DedekindRank.Model D (E f) (J f))
  have torsion (f : Option P → T) : Module.IsTorsion R (E f) :=
    essential_torsion (e f) (Submodule.torsion_isTorsion (R := R) (M := Residues (rank f))) (ess f)
  refine ⟨M, fun f => DedekindRank.model_extension_size hnf κ hω hR D hD injD univ (E f)
    (DedekindRank.pureInjective_of_injective (E f) (hinj f)) ((hsize f).trans hD')
    (J f) ((hJ f).symm ▸ (bounds _).1) ((hJ f).symm ▸ (bounds _).2), ?_⟩
  have prime (f g : Option P → T) (p : P) (map : M f →ₗ[R] M g) (hm : Injective map) :
      rank f p ≤ rank g p := by
    have upper := killed_card_upper (ranks := rank g) (e g) (he g) (ess g) p
      (hω.le.trans (bounds _).1) (hR.le.trans (bounds _).1)
    exact (killed_card_lower (ranks := rank f) hnf (e f) (he f) p).trans
      (prime_le_of_embedding hnf p D (E f) (E g) (hinj f) (J f) (J g) map hm (rank g p)
        (hω.le.trans (bounds _).1) (hD.trans (bounds _).1) upper)
  have rational (f g : Option P → T) (map : M f →ₗ[R] M g) (hm : Injective map) :
      c (f none) ≤ c (g none) := by
    rw [← hJ f, ← hJ g]
    exact DedekindRank.index_le_of_embedding D (E g) (E f) (torsion g) (J f) (J g)
      (by rw [hJ]; exact hω.le.trans (bounds _).1) (by rw [hJ]; exact hω.le.trans (bounds _).1)
      (by rw [hJ]; exact hR.le.trans (bounds _).1) (by rw [hJ]; exact hR.le.trans (bounds _).1)
      (by rw [hJ]; exact hD.trans (bounds _).1) map hm
  rintro f g ⟨iso⟩ i
  cases i with
  | none =>
    exact le_antisymm (rational f g iso.toLinearMap iso.injective)
      (rational g f iso.symm.toLinearMap iso.symm.injective)
  | some p =>
    exact le_antisymm (prime f g p iso.toLinearMap iso.injective)
      (prime g f p iso.symm.toLinearMap iso.symm.injective)

end PureEmbeddings.DedekindMultiplicity
