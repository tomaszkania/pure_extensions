import PureEmbeddings.DedekindMathlib
import PureEmbeddings.CriterionMathlib
import Mathlib.Algebra.Category.ModuleCat.Injective

/-! Pure-injective upper models built from a universal ordinary injective
and its submodules annihilated by a family of ideals. -/
noncomputable section
namespace PureEmbeddings.ResidueUpper

open Function Cardinal
open scoped Pointwise Cardinal
universe u
variable {R : Type u} [CommRing R]

/-- The submodule killed by every element of J. -/
def killed (J : Ideal R) (D : Type u) [AddCommGroup D] [Module R D] : Submodule R D where
  carrier := {d | ∀ r ∈ J, r • d = 0}
  zero_mem' := fun _ _ => smul_zero _
  add_mem' := fun ha hb r hr => by rw [smul_add, ha r hr, hb r hr, add_zero]
  smul_mem' := fun s d hd r hr => by rw [smul_comm r s, hd r hr, smul_zero]

private abbrev mult (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :=
  J • (⊤ : Submodule R M)

private theorem kills_mult {J : Ideal R} {A B : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (h : ∀ r ∈ J, ∀ x, r • f x = 0) :
    mult J A ≤ LinearMap.ker f := by
  apply Submodule.smul_le.2
  intro r hr a _
  rw [LinearMap.mem_ker, map_smul, h r hr a]

private theorem map_mult {J : Ideal R} {A B : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) : mult J A ≤ (mult J B).comap f := by
  apply Submodule.smul_le.2
  intro r hr x _
  change f (r • x) ∈ mult J B
  rw [map_smul]
  exact Submodule.smul_mem_smul hr (show f x ∈ (⊤ : Submodule R B) from trivial)

private def onQuotient (J : Ideal R) {A B : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (f : A →ₗ[R] B) :=
  (mult J A).mapQ (mult J B) f (map_mult f)

private theorem onQuotient_injective (J : Ideal R) {A B : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (h : IsPureMap f) : Injective (onQuotient J f) := by
  apply (injective_iff_map_eq_zero _).2
  intro z hz
  obtain ⟨a,rfl⟩ := (mult J A).mkQ_surjective z
  apply (Submodule.Quotient.mk_eq_zero _).2
  apply DedekindMathlib.pure_reflect_ideal J f h
  exact (Submodule.Quotient.mk_eq_zero _).1 hz

/-- Any linear map out of A/JA takes its values in the annihilator of J. -/
def intoKilled (J : Ideal R) {A D : Type u} [AddCommGroup A] [Module R A]
    [AddCommGroup D] [Module R D] (f : (A ⧸ mult J A) →ₗ[R] D) : A →ₗ[R] killed J D :=
  (f.comp (mult J A).mkQ).codRestrict _ (by
    intro x r hr
    change r • f ((mult J A).mkQ x) = 0
    rw [← map_smul, ← map_smul]
    have hz : (mult J A).mkQ (r • x) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hr (show x ∈ (⊤ : Submodule R A) from trivial))
    rw [hz,map_zero])

/-- An ordinary injective D has pure-injective submodules D[J]. -/
theorem killed_pureInjective (J : Ideal R) (D : ModuleCat.{u} R) (hd : Module.Injective R D) :
    IsPureInjective (ModuleCat.of R (killed J D)) := by
  intro A B i f hi
  let f' := (killed J D).subtype.comp f
  let bar := (mult J A).liftQ f' (kills_mult f' (fun r hr a => (f a).property r hr))
  obtain ⟨g, hg⟩ := hd.out (onQuotient J i) (onQuotient_injective J i hi) bar
  refine ⟨intoKilled J g, ?_⟩
  apply LinearMap.ext
  intro x
  exact Subtype.ext (hg ((mult J A).mkQ x))

variable {P : Type u} (J : P → Ideal R)
abbrev Model (D : ModuleCat.{u} R) := D × ((p : P) → killed (J p) D)

theorem model_pureInjective (D : ModuleCat.{u} R) (hd : Module.Injective R D) :
    IsPureInjective (ModuleCat.of R (Model J D)) := by
  intro A B i f hi
  obtain ⟨g, hg⟩ := hd.out i hi.1 ((LinearMap.fst R D ((p : P) → killed (J p) D)).comp f)
  let snd := (LinearMap.snd R D ((p : P) → killed (J p) D)).comp f
  have each (p : P) := killed_pureInjective (J p) D hd A B i ((LinearMap.proj p).comp snd) hi
  choose v hv using each
  refine ⟨g.prod (LinearMap.pi v), ?_⟩
  apply LinearMap.ext
  intro x
  exact Prod.ext (hg x) (funext fun p => DFunLike.congr_fun (hv p) x)

theorem model_card (D : ModuleCat.{u} R) : #(Model J D) ≤ #D ^ #(Option P) := by
  rw [Cardinal.power_def]
  let encode (x : Model J D) : Option P → D
    | none => x.1
    | some p => (x.2 p).val
  apply Cardinal.mk_le_of_injective (f := encode)
  intro x y h
  exact Prod.ext (congrFun h none) (funext fun p => Subtype.ext (congrFun h (some p)))

/-- A map is tested by injectivity and by the congruences modulo the chosen
ideals. This is an algebraic property of the family J, independent of κ. -/
def DetectsPurity : Prop :=
  ∀ (M N : ModuleCat.{u} R) (f : M →ₗ[R] N), Injective f →
    (∀ p x, f x ∈ mult (J p) N → x ∈ mult (J p) M) → IsPureMap f

theorem model_pureUniversal (κ : Cardinal.{u}) (D : ModuleCat.{u} R)
    (univ : ∀ M : ModuleCat.{u} R, #M ≤ κ → ∃ f : M →ₗ[R] D, Injective f)
    (tests : DetectsPurity J) (M : ModuleCat.{u} R) (hm : #M ≤ κ) :
    ∃ f : M →ₗ[R] Model J D, IsPureMap f := by
  classical
  obtain ⟨g,hg⟩ := univ M hm
  let quot (p : P) := ModuleCat.of R (M ⧸ mult (J p) M)
  have small (p : P) : #(quot p) ≤ κ :=
    (Cardinal.mk_le_of_surjective (mult (J p) M).mkQ_surjective).trans hm
  choose h hh using fun p => univ (quot p) (small p)
  let f := g.prod (LinearMap.pi (fun p => intoKilled (J p) (h p)))
  refine ⟨f, tests M (ModuleCat.of R (Model J D)) f (fun a b h => hg (congrArg Prod.fst h)) ?_⟩
  intro p x hx
  let read : Model J D →ₗ[R] D :=
    ((killed (J p) D).subtype.comp (LinearMap.proj p)).comp
      (LinearMap.snd R D ((q : P) → killed (J q) D))
  have hr := kills_mult (J := J p) read fun r hr t => (t.2 p).property r hr
  have zero : h p ((mult (J p) M).mkQ x) = 0 := hr hx
  exact (Submodule.Quotient.mk_eq_zero _).1 ((hh p) (zero.trans (h p).map_zero.symm))

/-- Upper model and cardinal estimate for any family detecting purity. -/
theorem upper (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hR : #R < κ)
    (D : ModuleCat.{u} R) (hd : Module.Injective R D)
    (univ : ∀ M : ModuleCat.{u} R, #M ≤ κ → ∃ f : M →ₗ[R] D, Injective f)
    (tests : DetectsPurity J) :
    ∃ F : ModuleCat.{u} R, HasExtension κ F ∧ #F ≤ #D ^ #(Option P) :=
  ⟨ModuleCat.of R (Model J D),
    EquationCriterion.extension_of_pureInjective_and_universal κ hω hR _
      (model_pureInjective J D hd) (model_pureUniversal J κ D univ tests),
    model_card J D⟩

end PureEmbeddings.ResidueUpper
