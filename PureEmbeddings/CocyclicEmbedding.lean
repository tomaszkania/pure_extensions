import PureEmbeddings.GroupFactors
import PureEmbeddings.DedekindPurity
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Data.ZMod.QuotientRing

/-! Every abelian group has a small family of maps to cyclic prime-power
groups and Prüfer groups whose diagonal is a pure embedding. -/
namespace PureEmbeddings.Groups

open Cardinal
open scoped BigOperators
noncomputable section

/-- A nonzero element survives in some Prüfer group. Map its cyclic
subgroup onto a group of prime order and extend by divisibility. -/
private theorem separate_primary (A : Type) [AddCommGroup A] {x : A} (hx : x ≠ 0) :
    ∃ (t : FactorIndex) (f : A →ₗ[ℤ] factor t), f x ≠ 0 := by
  have hn : addOrderOf x ≠ 1 := fun h => hx (AddMonoid.addOrderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hn
  letI : Fact p.Prime := ⟨hp⟩
  let D := AddCommGroup.primaryComponent RatModInt p
  let q : RatModInt := QuotientAddGroup.mk ((1 : ℚ) / p)
  have hord : addOrderOf q = p := AddCircle.addOrderOf_period_div hp.pos
  have hkill : p • q = 0 := hord ▸ addOrderOf_nsmul_eq_zero q
  let b : D := ⟨q, exists_addOrderOf_eq_prime_pow_iff.mpr ⟨1, by simpa using hkill⟩⟩
  have hb : b ≠ 0 := fun h => hp.ne_one (hord.symm.trans (by
    rw [show q = 0 from congrArg Subtype.val h, addOrderOf_zero]))
  have kills : (addOrderOf x : ℤ) • b = 0 := by
    obtain ⟨k,hk⟩ := hd
    apply Subtype.ext
    change (addOrderOf x : ℤ) • q = 0
    rw [natCast_zsmul, hk, Nat.mul_comm, mul_smul, hkill, smul_zero]
  let f := Submodule.liftQSpanSingleton (addOrderOf x : ℤ) (LinearMap.toSpanSingleton ℤ D b)
    (by simpa only [LinearMap.toSpanSingleton_apply] using kills)
  let g := f.comp (CharacterModule.intSpanEquivQuotAddOrderOf x).toLinearMap
  letI : DivisibleBy D ℤ := primaryDivisible p
  letI : Module.Injective ℤ D := (Module.Baer.of_divisible D).injective
  obtain ⟨l, hl⟩ := (inferInstanceAs (Module.Injective ℤ D)).out (ℤ ∙ x).subtype
    Subtype.val_injective g
  refine ⟨(⟨p,hp⟩, none), l, ?_⟩
  have h := hl (⟨x, Submodule.mem_span_singleton_self x⟩ : ℤ ∙ x)
  change l x = f ((CharacterModule.intSpanEquivQuotAddOrderOf x) _) at h
  rw [CharacterModule.intSpanEquivQuotAddOrderOf_apply_self] at h
  have h' : l x = b := h.trans (show (1 : ℤ) • b = b from one_smul ℤ b)
  exact h' ▸ hb

/-- A character killed by n takes its values in the cyclic group generated
by 1/n modulo the integers. -/
private theorem bounded_character (A : Type) [AddCommGroup A] (n : ℕ) (hn : 0 < n)
    (kills : ∀ a : A, n • a = 0) {x : A} (hx : x ≠ 0) :
    ∃ f : A →ₗ[ℤ] ZMod n, f x ≠ 0 := by
  obtain ⟨χ,hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx
  let q : AddCircle (1 : ℚ) := QuotientAddGroup.mk ((1 : ℚ) / n)
  have ho : addOrderOf q = n := AddCircle.addOrderOf_period_div hn
  let H : Submodule ℤ (AddCircle (1 : ℚ)) := ℤ ∙ q
  have inside (a : A) : χ a ∈ H := by
    have hz : n • χ a = 0 := by
      change n • (χ : A →+ AddCircle (1 : ℚ)) a = 0
      rw [← map_nsmul, kills, map_zero]
    obtain ⟨m,_, hm⟩ := AddCircle.nsmul_eq_zero_iff hn |>.mp hz
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(m : ℤ), ?_⟩
    rw [natCast_zsmul]
    exact (AddCircle.natCast_div_mul_eq_nsmul (p := (1 : ℚ)) (q := (n : ℚ)) 1 m).symm.trans hm
  let g := (χ : A →+ AddCircle (1 : ℚ)).toIntLinearMap.codRestrict H inside
  let e := CharacterModule.intSpanEquivQuotAddOrderOf q
  let j : H ≃+ ZMod n := by
    rw [← ho]
    exact e.toAddEquiv.trans (Int.quotientSpanNatEquivZMod _).toAddEquiv
  refine ⟨j.toAddMonoidHom.toIntLinearMap.comp g, fun h => hχ ?_⟩
  have : g x = 0 := j.injective (show j (g x) = j 0 from h.trans j.map_zero.symm)
  exact congrArg Subtype.val this

/-- Chinese remaindering leaves a nonzero coordinate in a prime-power
factor. This factor is annihilated by the original modulus. -/
private theorem prime_factor (n : ℕ) (hn : n ≠ 0) {x : ZMod n} (hx : x ≠ 0) :
    ∃ (t : FactorIndex) (h : ZMod n →ₗ[ℤ] factor t),
      h x ≠ 0 ∧ ∀ b : factor t, n • b = 0 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => exact (hn rfl).elim
  | one => exact (hx (Subsingleton.elim ..)).elim
  | prime_pow p k hp hk =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    refine ⟨(⟨p,hp⟩, some j), LinearMap.id, hx, fun b => ?_⟩
    change (p ^ (j+1)) • (b : ZMod (p ^ (j+1))) = 0
    exact ZModModule.char_nsmul_eq_zero (G := ZMod (p^(j+1))) (p^(j+1)) (b : ZMod (p^(j+1)))
  | coprime a b ha hb hab ia ib =>
    let e := (ZMod.chineseRemainder hab).toAddEquiv
    let l := e.toAddMonoidHom.toIntLinearMap
    by_cases h : (e x).1 = 0
    · have hh : (e x).2 ≠ 0 := fun hz => hx (e.injective ((Prod.ext h hz).trans e.map_zero.symm))
      obtain ⟨t,g,hg,kill⟩ := ib (by omega) hh
      refine ⟨t,g.comp ((LinearMap.snd ℤ _ _).comp l), hg, fun z => ?_⟩
      rw [mul_smul, kill, smul_zero]
    · obtain ⟨t,g,hg,kill⟩ := ia (by omega) h
      refine ⟨t,g.comp ((LinearMap.fst ℤ _ _).comp l), hg, fun z => ?_⟩
      rw [Nat.mul_comm, mul_smul, kill, smul_zero]

/-- If a is not divisible by n there is a homomorphism to a co-cyclic
group killed by n on which a survives. The case n=0 separates points. -/
private theorem obstruction (A : Type) [AddCommGroup A] (n : ℕ) (a : A)
    (ha : ¬ ∃ b : A, n • b = a) :
    ∃ (t : FactorIndex) (f : A →ₗ[ℤ] factor t), f a ≠ 0 ∧ ∀ b : factor t, n • b = 0 := by
  by_cases hn : n = 0
  · subst n
    have hne : a ≠ 0 := fun h => ha ⟨0, (zero_smul ℕ (0:A)).trans h.symm⟩
    obtain ⟨t,f,hf⟩ := separate_primary A hne
    exact ⟨t,f,hf,fun _ => zero_smul ..⟩
  let mult : A →ₗ[ℤ] A := (n : ℤ) • LinearMap.id
  let U := LinearMap.range mult
  let Q := A ⧸ U
  let π := U.mkQ
  have kill (q : Q) : n • q = 0 := by
    obtain ⟨b,rfl⟩ := U.mkQ_surjective q
    rw [← map_nsmul]
    exact (Submodule.Quotient.mk_eq_zero U).2 ⟨b, by simp [mult]⟩
  have hq : π a ≠ 0 := fun hz => ha (by
    obtain ⟨b,h⟩ := (Submodule.Quotient.mk_eq_zero U).1 hz
    exact ⟨b, by simpa [mult] using h⟩)
  obtain ⟨g,hg⟩ := bounded_character Q n (Nat.pos_of_ne_zero hn) kill hq
  obtain ⟨t,h,hh,hk⟩ := prime_factor n hn hg
  exact ⟨t, (h.comp g).comp π, hh, hk⟩

/-- Every group admits a pure embedding into a product of at most
max(ℵ₀, |A|) co-cyclic groups. -/
theorem exists_cocyclic_embedding (A : ModuleCat.{0} ℤ) :
    ∃ (I : Type) (t : I → FactorIndex), #I ≤ max ℵ₀ (#A) ∧
      ∃ f : A →ₗ[ℤ] ((i : I) → factor (t i)), IsPureMap f := by
  classical
  let I := {p : ℕ × A // ¬ ∃ y : A, p.1 • y = p.2}
  choose t g hg kill using fun i : I => obstruction A i.val.1 i.val.2 i.property
  let f : A →ₗ[ℤ] ((i : I) → factor (t i)) := LinearMap.pi g
  have reflect (n : ℕ) (a : A) (z : (i : I) → factor (t i)) (hz : n • z = f a) :
      ∃ y : A, n • y = a := by
    by_contra ha
    let i : I := ⟨(n,a),ha⟩
    have h := congrFun hz i
    exact hg i (h.symm.trans (kill i (z i)))
  have inj : Function.Injective f := (injective_iff_map_eq_zero _).2 fun a h => by
    obtain ⟨b,hb⟩ := reflect 0 a 0 (by rw [h, zero_smul])
    simpa using hb.symm
  have intReflect (n : ℤ) (a : A) (h : ∃ z, n • z = f a) :
      ∃ y : A, n • y = a := by
    obtain ⟨z,hz⟩ := h
    cases n with
    | ofNat k =>
      simpa only [Int.ofNat_eq_coe, natCast_zsmul] using reflect k a z (by
        simpa only [Int.ofNat_eq_coe, natCast_zsmul] using hz)
    | negSucc k =>
      obtain ⟨b,hb⟩ := reflect (k+1) a (-z) (by
        simpa only [Int.negSucc_eq, ← Nat.cast_add_one, neg_smul, natCast_zsmul, smul_neg] using hz)
      exact ⟨-b, by simp only [Int.negSucc_eq, ← Nat.cast_add_one, neg_smul, smul_neg, neg_neg, natCast_zsmul]; exact hb⟩
  have hnf : ¬ IsField ℤ := fun h => Int.not_even_one
    ((h.mul_inv_cancel two_ne_zero).imp fun _ => by rw [← two_mul]; exact Eq.symm)
  refine ⟨I, t, ?_, f, ?_⟩
  · calc
      #I ≤ #(ℕ × A) := Cardinal.mk_le_of_injective Subtype.val_injective
      _ = ℵ₀ * #A := by rw [Cardinal.mk_prod, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id]
      _ ≤ (max ℵ₀ (#A)) * (max ℵ₀ (#A)) := mul_le_mul' (le_max_left ..) (le_max_right ..)
      _ = _ := Cardinal.mul_eq_self (le_max_left ..)
  · apply DedekindPurity.pure_of_local_pivots (fun P hP => ?_) f inj intReflect
    letI := hP.isPrime
    letI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
      (Ring.ne_bot_of_isMaximal_of_not_isField hP hnf) (Localization.AtPrime P)
    exact DedekindPurity.local_pivots_of_valuation P

end
end PureEmbeddings.Groups
