import PureEmbeddings.Statements
import PureEmbeddings.OrdinaryBounds
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.Nat.PrimeFin
import PureEmbeddings.TheoremB

/-! Transport between abelian groups and modules over the integers lifted to
the cardinal universe, together with the count of integer maximal ideals. -/
namespace PureEmbeddings.IntegerMultiplicity
open Cardinal Function
universe u
attribute [local instance 10] ULift.module ULift.smulLeft

abbrev Z := ULift.{u} ℤ

instance : IsDomain Z := Function.Injective.isDomain (ULift.ringEquiv : Z ≃+* ℤ) ULift.down_injective

instance : IsPrincipalIdealRing Z := IsPrincipalIdealRing.of_surjective
  (ULift.ringEquiv.symm : ℤ ≃+* Z).toRingHom ULift.up_surjective

private def upMap {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module Z A] [Module Z B] (f : A →+ B) : A →ₗ[Z] B where
  toFun := f
  map_add' := f.map_add
  map_smul' s x := by
    simp only [RingHom.id_apply]
    have h : (s.down : Z) = s := ULift.ext _ _ (by simp)
    rw [← h,Int.cast_smul_eq_zsmul,Int.cast_smul_eq_zsmul]
    exact f.map_zsmul _ _

private theorem scalar_eq {A : Type u} [grp : AddCommGroup A] [modu : Module Z A] (s : Z) (x : A) :
    @SMul.smul Z A modu.toSMul s x = s.down • x := by
  have h : (s.down : Z) = s := ULift.ext _ _ (by simp)
  exact (congrArg (fun v => @SMul.smul Z A modu.toSMul v x) h).symm.trans
    (@Int.cast_smul_eq_zsmul Z A _ grp modu _ _)

private theorem soluble_iff {A : Type u} [AddCommGroup A] [Module Z A] {m n : ℕ}
    (r : Fin m → Fin n → Z) (a : Fin m → A) :
    Soluble r a ↔ Soluble (fun i j => (r i j).down) a := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨x,fun i => Eq.trans ?_ (hx i)⟩
    exact Finset.sum_congr rfl (fun j _ => (scalar_eq (r i j) (x j)).symm)
  · rintro ⟨x,hx⟩
    refine ⟨x,fun i => Eq.trans ?_ (hx i)⟩
    exact Finset.sum_congr rfl (fun j _ => scalar_eq (r i j) (x j))

theorem pure_iff {A B : Type u} [AddCommGroup A] [AddCommGroup B] [Module Z A] [Module Z B]
    (f : A →ₗ[Z] B) : IsPureMap f ↔ IsPureMap f.toAddMonoidHom.toIntLinearMap := by
  constructor
  · rintro ⟨hin,reflect⟩
    refine ⟨hin, ?_⟩
    intro m n r a hs
    let t : Fin m → Fin n → Z := fun i j => ⟨r i j⟩
    exact (soluble_iff t a).1 (reflect t a ((soluble_iff t _).2 hs))
  · rintro ⟨hin,reflect⟩
    refine ⟨hin, ?_⟩
    intro m n r a hs
    exact (soluble_iff r a).2 (reflect _ a ((soluble_iff r _).1 hs))

/-- The extension property is preserved in both directions when the ring of
integers is lifted to the universe of the module's underlying type. -/
theorem extension_iff {κ : Cardinal.{u}} (F : ModuleCat.{u} Z) :
    HasExtension (R := Z) κ F ↔ HasExtension (R := ℤ) κ (ModuleCat.of ℤ F) := by
  constructor
  · intro h A B
    obtain @⟨A,aA,mA⟩ := A
    obtain @⟨B,aB,mB⟩ := B
    have ha : mA = @AddCommGroup.toIntModule A aA := Subsingleton.elim _ _
    have hb : mB = @AddCommGroup.toIntModule B aB := Subsingleton.elim _ _
    subst mA
    subst mB
    intro i f hB hi hf
    let iu : A →ₗ[Z] B := upMap i.toAddMonoidHom
    let fu : A →ₗ[Z] F := upMap f.toAddMonoidHom
    obtain ⟨g,hg,he⟩ := h (ModuleCat.of Z A) (ModuleCat.of Z B) iu fu hB
      ((pure_iff iu).2 hi) ((pure_iff fu).2 hf)
    exact ⟨g.toAddMonoidHom.toIntLinearMap,(pure_iff g).1 hg,LinearMap.ext (fun x => DFunLike.congr_fun he x)⟩
  · intro h A B i f hB hi hf
    obtain ⟨g,hg,he⟩ := h (ModuleCat.of ℤ A) (ModuleCat.of ℤ B)
      i.toAddMonoidHom.toIntLinearMap f.toAddMonoidHom.toIntLinearMap hB ((pure_iff i).1 hi) ((pure_iff f).1 hf)
    let gu : B →ₗ[Z] F := upMap g.toAddMonoidHom
    exact ⟨gu,(pure_iff gu).2 hg,LinearMap.ext (fun x => DFunLike.congr_fun he x)⟩

private theorem many_down {κ μ θ : Cardinal.{u}} (h : ManyAtMinimum (R := Z) κ μ θ) :
    ManyAtMinimum (R := ℤ) κ μ θ := by
  obtain ⟨I,F,hI,hF,sep⟩ := h
  refine ⟨I,fun i => ModuleCat.of ℤ (F i),hI,fun i => ⟨(extension_iff _).1 (hF i).1,(hF i).2⟩,?_⟩
  intro i j hij
  exact ⟨fun e => (sep i j hij).false (LinearEquiv.ofBijective
    (upMap (A := F i) (B := F j) e.toLinearMap.toAddMonoidHom) e.bijective)⟩

private theorem notField : ¬ IsField Z := by
  intro h
  have h' : IsField ℤ := MulEquiv.isField h (ULift.ringEquiv : Z ≃+* ℤ).symm.toMulEquiv
  exact Int.not_even_one ((h'.mul_inv_cancel two_ne_zero).imp fun a => by rw [← two_mul]; exact Eq.symm)

private theorem primes : Cardinal.mk {p : Ideal Z // p.IsMaximal} = (ℵ₀ : Cardinal.{u}) := by
  have upper : Cardinal.mk {p : Ideal Z // p.IsMaximal} ≤ (ℵ₀ : Cardinal.{u}) :=
    (Cardinal.mk_le_of_injective Subtype.val_injective).trans
      (Ordinary.ideals_size_noetherian Z ℵ₀ le_rfl (Cardinal.mk_le_aleph0_iff.mpr inferInstance))
  let J (p : Nat.Primes) : Ideal ℤ := Ideal.span {(p.val : ℤ)}
  have mJ (p : Nat.Primes) : (J p).IsMaximal := by
    have hprime := (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr p.property.ne_zero)).2
      (Nat.prime_iff_prime_int.mp p.property)
    exact hprime.isMaximal (by simpa [J] using (Int.natCast_ne_zero.mpr p.property.ne_zero))
  let f (p : Nat.Primes) : {p : Ideal Z // p.IsMaximal} :=
    ⟨Ideal.comap ULift.ringEquiv (J p),@Ideal.comap_isMaximal_of_equiv _ _ _ _ _ _ _ _ (J p) (mJ p)⟩
  have hf : Injective f := by
    intro p q he
    have eq := Ideal.comap_injective_of_surjective (ULift.ringEquiv : Z ≃+* ℤ).toRingHom
      ULift.down_surjective (congrArg Subtype.val he)
    have hass := Ideal.span_singleton_eq_span_singleton.mp eq
    exact Subtype.ext (dvd_antisymm (Int.natCast_dvd_natCast.mp hass.dvd)
      (Int.natCast_dvd_natCast.mp hass.symm.dvd))
  letI : Infinite {p : Ideal Z // p.IsMaximal} := Infinite.of_injective f hf
  exact upper.antisymm (Cardinal.aleph0_le_mk _)

/-- The multiplicity conclusion of Theorem B gives the stated count for abelian groups. -/
theorem many_of_B (κ : Cardinal.{u}) (hk : ℵ₀ < κ) (hkl : κ < κ ^ ℵ₀) (hb : TheoremB Z κ) :
    ∃ T : Type u, Nonempty (T ≃ Set.Icc κ (κ ^ ℵ₀)) ∧
      ManyAtMinimum (R := ℤ) κ (κ ^ ℵ₀) (Cardinal.mk T ^ ℵ₀) := by
  have hsi : Cardinal.mk Z ≤ (ℵ₀ : Cardinal.{u}) := Cardinal.mk_le_aleph0_iff.mpr inferInstance
  have h := (hb notField (max_lt (hsi.trans_lt hk) hk)).2.2
  simp only [primes,max_self,Cardinal.add_one_eq le_rfl] at h
  obtain ⟨T,e,more⟩ := h hkl
  exact ⟨T,e,many_down more⟩

/-- Distinct multiplicity assignments give the count asserted in Theorem C. -/
theorem many (κ : Cardinal.{u}) (hk : ℵ₀ < κ) (hkl : κ < κ ^ ℵ₀) :
    ∃ T : Type u, Nonempty (T ≃ Set.Icc κ (κ ^ ℵ₀)) ∧
      ManyAtMinimum (R := ℤ) κ (κ ^ ℵ₀) (Cardinal.mk T ^ ℵ₀) :=
  many_of_B κ hk hkl (theoremB Z κ)

end PureEmbeddings.IntegerMultiplicity
