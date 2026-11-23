import PureEmbeddings.DedekindPurity
import PureEmbeddings.OrdinaryBounds

/-! The exact minimum cardinal in Theorem B, for every non-field Dedekind
domain, including finite prime spectra and singular size parameters. -/
noncomputable section
namespace PureEmbeddings.DedekindMathlib

open Cardinal
open scoped Cardinal
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsDedekindDomain R]

private theorem option_bound {X : Type u} {τ : Cardinal.{u}} (hω : ℵ₀ ≤ τ) (hX : #X ≤ τ) :
    #(Option X) ≤ τ := by
  rw [Cardinal.mk_option]
  exact (add_le_add hX (Cardinal.one_le_aleph0.trans hω)).trans (Cardinal.add_eq_self hω).le

/-- Every nonzero ideal is a finite product of maximal ideals. We include
a separate code for the zero ideal. -/
theorem ideal_count : #(Ideal R) ≤ max ℵ₀ #({p : Ideal R // p.IsMaximal}) := by
  let P := {p : Ideal R // p.IsMaximal}
  let decode : Option (List P) → Ideal R
    | none => 0
    | some ps => (ps.map Subtype.val).prod
  have surj : Function.Surjective decode := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => exact ⟨none,rfl⟩
    | h₂ x hx => exact ⟨some [],by change (1:Ideal R) = x; rw [Ideal.one_eq_top, Ideal.isUnit_iff.mp hx]⟩
    | h₃ a p ha hp ih =>
      obtain ⟨l,hl⟩ := ih
      cases l with
      | none => exact (ha hl.symm).elim
      | some l =>
        let j : P := ⟨p,(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero⟩
        exact ⟨some (j::l),congrArg (p * ·) hl⟩
  exact (Cardinal.mk_le_of_surjective surj).trans
    (option_bound (le_max_left ..) (Cardinal.mk_list_le_max P))

/-- An actual module realises the minimum, and every module satisfying the
extension property has at least that size. -/
theorem dedekind_minimum (hnf : ¬IsField R) (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hR : #R < κ) :
    (∃ F : ModuleCat.{u} R, HasExtension κ F ∧ #F = κ ^ max ℵ₀ #({p : Ideal R // p.IsMaximal})) ∧
    (∀ F : ModuleCat.{u} R, HasExtension κ F → κ ^ max ℵ₀ #({p : Ideal R // p.IsMaximal}) ≤ #F) := by
  obtain ⟨D,hD,hd,univ⟩ := Ordinary.exists_universal_noetherian R κ hω.le hR.le
  obtain ⟨F,hF,hm⟩ := ResidueUpper.upper (fun J : Ideal R => J) κ hω hR D hd univ
    (DedekindPurity.dedekind_detects_purity hnf)
  have nonzero : κ ≠ 0 := ne_of_gt (Cardinal.aleph0_pos.trans hω)
  have upper := hm.trans ((Cardinal.power_le_power_right hD).trans
    (Cardinal.power_le_power_left nonzero (option_bound (le_max_left ..) (ideal_count R))))
  exact ⟨⟨F,hF,upper.antisymm (dedekind_lower hnf κ F hω hR hF)⟩,
    fun G hG => dedekind_lower hnf κ G hω hR hG⟩

end PureEmbeddings.DedekindMathlib
