import PureEmbeddings.DedekindSocle
import PureEmbeddings.DedekindRank

/-! The size of each prime component can be read through an arbitrary
module embedding between the constructed models. -/
noncomputable section
namespace PureEmbeddings.DedekindMultiplicity
open Cardinal Function
open scoped Cardinal nonZeroDivisors
universe u
variable {R : Type u} [CommRing R] [IsDomain R]

/-- Every nonzero scalar acts surjectively on an ordinary injective over a domain. -/
theorem injective_divisible (E : ModuleCat.{u} R) (he : Module.Injective R E) (a : R) (ha : a ≠ 0)
    (x : E) : ∃ y : E, a • y = x := by
  let j := LinearMap.toSpanSingleton R R a
  have inj : Injective j := fun v w eqn => mul_right_cancel₀ ha eqn
  obtain ⟨g,hg⟩ := he.out j inj (LinearMap.toSpanSingleton R E x)
  refine ⟨g 1,?_⟩
  have h := hg 1
  simpa [j,← map_smul,smul_eq_mul] using h

theorem prime_le_of_embedding (hnf : ¬IsField R) (p : Maximals R)
    (D E G : ModuleCat.{u} R) (hE : Module.Injective R E) (I J : Type u)
    (f : DedekindRank.Model D E I →ₗ[R] DedekindRank.Model D G J) (hf : Injective f)
    (γ : Cardinal.{u}) (hω : ℵ₀ ≤ γ) (hd : #D ≤ γ) (hs : #(ResidueUpper.killed p.val G) ≤ γ) :
    #(ResidueUpper.killed p.val E) ≤ γ := by
  let into : E →ₗ[R] DedekindRank.Model D E I :=
    (LinearMap.inl R (E × ResidueUpper.Model (fun L : Ideal R => L) D) _).comp
      (LinearMap.inl R E _)
  let g := f.comp into
  have gi : Injective g := hf.comp fun _ _ h => congrArg (fun z : DedekindRank.Model D E I => z.1.1) h
  have erase (x : E) (L : Ideal R) (hL : L ≠ ⊥) : (g x).1.2.2 L = 0 := by
    obtain ⟨a,ha,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
    obtain ⟨y,hy⟩ := injective_divisible E hE a hn x
    apply Subtype.ext
    rw [← hy, map_smul]
    exact ((g y).1.2.2 L).property a ha
  let coord (x : ResidueUpper.killed p.val E) : ResidueUpper.killed p.val G :=
    ⟨(g x.val).1.1, fun r hr => by
      have h := congrArg (fun z : DedekindRank.Model D G J => z.1.1)
        ((g.map_smul r x.val).symm.trans ((congrArg g (x.property r hr)).trans g.map_zero))
      exact h⟩
  let read (x : ResidueUpper.killed p.val E) : ResidueUpper.killed p.val G × D × D :=
    (coord x,(g x).1.2.1,((g x).1.2.2 ⊥).val)
  have rational (x : ResidueUpper.killed p.val E) : (g x).2 = 0 := by
    obtain ⟨a,ha,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Ring.ne_bot_of_isMaximal_of_not_isField p.property hnf)
    have h := congrArg (fun z : DedekindRank.Model D G J => z.2)
        ((g.map_smul a x.val).symm.trans ((congrArg g (x.property a ha)).trans g.map_zero))
    change a • (g x).2 = 0 at h
    exact (smul_eq_zero.mp h).resolve_left hn
  have read_inj : Injective read := by
    intro x y eqn
    apply Subtype.ext; apply gi; apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z : ResidueUpper.killed p.val G × D × D => z.1.val) eqn
      · apply Prod.ext
        · exact congrArg (fun z : ResidueUpper.killed p.val G × D × D => z.2.1) eqn
        · funext L
          by_cases e : L = ⊥
          · subst L; exact Subtype.ext (congrArg (fun z : ResidueUpper.killed p.val G × D × D => z.2.2) eqn)
          · exact (erase x L e).trans (erase y L e).symm
    · exact (rational x).trans (rational y).symm
  apply (Cardinal.mk_le_of_injective read_inj).trans
  simp only [Cardinal.mk_prod,Cardinal.lift_id]
  exact (mul_le_mul' hs ((mul_le_mul' hd hd).trans_eq (Cardinal.mul_eq_self hω))).trans_eq
    (Cardinal.mul_eq_self hω)

end PureEmbeddings.DedekindMultiplicity
