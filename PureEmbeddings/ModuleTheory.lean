import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Pure embeddings and the extension property

Modules are genuine unital left modules over a possibly non-commutative ring.
Each finite system has `m` equations and `n` unknowns. The size bound applies
to the larger module in the extension problem. Module carriers and cardinal
parameters live in the same universe, and the scalar ring may live in another.
-/
namespace PureEmbeddings
open Cardinal
open scoped BigOperators

universe u v
variable {R : Type v} [Ring R]

/-- Solubility of `r x = a` over a module, with constants `a` in that module. -/
def Soluble {M : Type u} [AddCommGroup M] [Module R M] {m n : ℕ}
    (r : Fin m → Fin n → R) (a : Fin m → M) : Prop :=
  ∃ x : Fin n → M, ∀ i, ∑ j, r i j • x j = a i

/-- Solutions of a finite linear system are preserved by any linear map. -/
theorem Soluble.map {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {m n : ℕ}
    {r : Fin m → Fin n → R} {a : Fin m → M} (h : Soluble r a) (f : M →ₗ[R] N) :
    Soluble r (f ∘ a) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨f ∘ x, fun i => ?_⟩
  simpa [Function.comp_def, map_sum] using congrArg f (hx i)

/-- An embedding is pure when it reflects solubility of every finite system. -/
def IsPureMap {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : Prop :=
  Function.Injective f ∧ ∀ {m n : ℕ} (r : Fin m → Fin n → R) (a : Fin m → M),
    Soluble r (f ∘ a) → Soluble r a

theorem IsPureMap.comp {A B C : ModuleCat.{u} R} {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (hg : IsPureMap g) (hf : IsPureMap f) : IsPureMap (g.comp f) :=
  ⟨hg.1.comp hf.1, fun r a h => hf.2 r a (hg.2 r (f ∘ a) h)⟩

/-- Purity of a composite implies purity of its first map. -/
theorem IsPureMap.of_comp {A B C : ModuleCat.{u} R} (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : IsPureMap (g.comp f)) : IsPureMap f :=
  ⟨fun _ _ he => h.1 (congrArg g he), fun r a hs => h.2 r a (hs.map g)⟩

theorem isPureMap_of_retraction {A B : ModuleCat.{u} R}
    (f : A →ₗ[R] B) (g : B →ₗ[R] A) (h : Function.LeftInverse g f) : IsPureMap f := by
  refine ⟨h.injective, fun r a hs => ?_⟩
  have hfun : g ∘ (f ∘ a) = a := funext fun j => h (a j)
  exact hfun ▸ hs.map g

theorem isPureMap_equiv {A B : ModuleCat.{u} R} (e : A ≃ₗ[R] B) :
    IsPureMap e.toLinearMap :=
  isPureMap_of_retraction e.toLinearMap e.symm.toLinearMap e.symm_apply_apply

/-- Property (Eκ) from the introduction. There is no regularity assumption. -/
def HasExtension (κ : Cardinal.{u}) (F : ModuleCat.{u} R) : Prop :=
  ∀ (A B : ModuleCat.{u} R) (i : A →ₗ[R] B) (f : A →ₗ[R] F),
    Cardinal.mk B < κ → IsPureMap i → IsPureMap f →
      ∃ g : B →ₗ[R] F, IsPureMap g ∧ g.comp i = f

def IsPureInjective (F : ModuleCat.{u} R) : Prop :=
  ∀ (A B : ModuleCat.{u} R) (i : A →ₗ[R] B) (f : A →ₗ[R] F),
    IsPureMap i → ∃ g : B →ₗ[R] F, g.comp i = f

def LeftPureSemisimple (R : Type v) [Ring R] : Prop :=
  ∀ (A B : ModuleCat.{u} R) (i : A →ₗ[R] B), IsPureMap i →
    ∃ r : B →ₗ[R] A, Function.LeftInverse r i

/-- Every module is pure-injective iff all pure inclusions of left modules split. -/
theorem leftPureSemisimple_iff :
    LeftPureSemisimple.{u} R ↔ ∀ F : ModuleCat.{u} R, IsPureInjective F := by
  constructor
  · intro hs F A B i f hi
    obtain ⟨r, hr⟩ := hs A B i hi
    exact ⟨f.comp r, LinearMap.ext fun x => by simp [hr x]⟩
  · intro hs A B i hi
    obtain ⟨r, hr⟩ := hs A A B i LinearMap.id hi
    exact ⟨r, fun x => congrArg (fun f : A →ₗ[R] A => f x) hr⟩

theorem HasExtension.of_equiv {κ : Cardinal.{u}} {F G : ModuleCat.{u} R}
    (hF : HasExtension κ F) (e : F ≃ₗ[R] G) : HasExtension κ G := by
  intro A B i f hB hi hf
  obtain ⟨g, hg, hgi⟩ := hF A B i (e.symm.toLinearMap.comp f) hB hi
    ((isPureMap_equiv e.symm).comp hf)
  refine ⟨e.toLinearMap.comp g, (isPureMap_equiv e).comp hg, ?_⟩
  ext x
  have h := congrArg (fun l : A →ₗ[R] F => l x) hgi
  exact (congrArg e h).trans (e.apply_symm_apply (f x))

theorem isPureMap_from_subsingleton {A B : ModuleCat.{u} R} [Subsingleton A]
    (f : A →ₗ[R] B) : IsPureMap f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ =>
    ⟨fun _ => 0, fun _ => Subsingleton.elim _ _⟩⟩

/-- The zero-domain case of (Eκ) gives pure universality for every smaller module. -/
theorem HasExtension.universal_lt {κ : Cardinal.{u}} {F : ModuleCat.{u} R}
    (hF : HasExtension κ F) (B : ModuleCat.{u} R) (hB : Cardinal.mk B < κ) :
    ∃ f : B →ₗ[R] F, IsPureMap f := by
  let O : ModuleCat.{u} R := ModuleCat.of R (⊥ : Submodule R F)
  letI : Subsingleton O := inferInstanceAs (Subsingleton (⊥ : Submodule R F))
  obtain ⟨f, hf, _⟩ := hF O B 0 0 hB (isPureMap_from_subsingleton _)
    (isPureMap_from_subsingleton _)
  exact ⟨f, hf⟩


/-- If the target itself were smaller than κ, its identity would extend injectively
along its inclusion as the first factor in F × R. The new factor rules this out. -/
theorem HasExtension.lower {R : Type u} [Ring R] [Nontrivial R]
    {κ : Cardinal.{u}} {F : ModuleCat.{u} R} (hF : HasExtension κ F)
    (hκ : ℵ₀ ≤ κ) (hR : Cardinal.mk R < κ) : κ ≤ Cardinal.mk F := by
  by_contra! hsmall
  let B := ModuleCat.of R (F × R)
  let i : F →ₗ[R] B := LinearMap.inl R F R
  let p : B →ₗ[R] F := LinearMap.fst R F R
  have hi : IsPureMap i := isPureMap_of_retraction (A := F) (B := B) i p (fun _ => rfl)
  have hB : Cardinal.mk B < κ := by
    change Cardinal.mk (F × R) < κ
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt hκ hsmall hR
  obtain ⟨g, hg, hgi⟩ := hF F B i LinearMap.id hB hi (isPureMap_equiv (LinearEquiv.refl R F))
  let z : B := (0, 1)
  have he : g (i (g z)) = g z := congrArg (fun f : F →ₗ[R] F => f (g z)) hgi
  have hz : i (g z) = z := hg.1 he
  have : (0 : R) = 1 := congrArg Prod.snd hz
  exact zero_ne_one this

/-- Formulating a minimum includes the existence of a module attaining it. -/
def HasMinimum (κ μ : Cardinal.{u}) : Prop :=
  (∃ F : ModuleCat.{u} R, HasExtension κ F ∧ Cardinal.mk F = μ) ∧
    ∀ F : ModuleCat.{u} R, HasExtension κ F → μ ≤ Cardinal.mk F

theorem hasMinimum_of_bounds {κ μ : Cardinal.{u}}
    (lower : ∀ F : ModuleCat.{u} R, HasExtension κ F → μ ≤ Cardinal.mk F)
    (upper : ∃ F : ModuleCat.{u} R, HasExtension κ F ∧ Cardinal.mk F ≤ μ) :
    HasMinimum (R := R) κ μ := by
  obtain ⟨F, hF, hsize⟩ := upper
  exact ⟨⟨F, hF, le_antisymm hsize (lower F hF)⟩, lower⟩

theorem HasMinimum.unique {κ a b : Cardinal.{u}} (ha : HasMinimum (R := R) κ a)
    (hb : HasMinimum (R := R) κ b) : a = b := by
  obtain ⟨A, hA, rfl⟩ := ha.1
  obtain ⟨B, hB, rfl⟩ := hb.1
  exact le_antisymm (ha.2 B hB) (hb.2 A hA)

def UniqueAt (κ μ : Cardinal.{u}) : Prop :=
  ∀ F G : ModuleCat.{u} R, HasExtension κ F → HasExtension κ G →
    Cardinal.mk F = μ → Cardinal.mk G = μ → Nonempty (F ≃ₗ[R] G)

/-- A lower bound on the number of isomorphism classes of a given size. -/
def ManyAtMinimum (κ μ θ : Cardinal.{u}) : Prop :=
  ∃ (I : Type u) (F : I → ModuleCat.{u} R), Cardinal.mk I = θ ∧
    (∀ i, HasExtension κ (F i) ∧ Cardinal.mk (F i) = μ) ∧
    ∀ i j, i ≠ j → IsEmpty (F i ≃ₗ[R] F j)

end PureEmbeddings
