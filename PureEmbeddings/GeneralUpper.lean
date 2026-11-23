import PureEmbeddings.CriterionMathlib

/-!
# An upper bound from finite matrices

The additive quotient of the tuple group by the image of a finite matrix
detects solubility. Its additive dual on the scalar module carries an action
of the original ring by precomposing with right multiplication.
-/
noncomputable section
namespace PureEmbeddings.GeneralUpper
open Cardinal Function
open scoped BigOperators

universe u
variable {R : Type u} [Ring R] {m n : ℕ}
variable (r : Fin m → Fin n → R)
variable (M : Type u) [AddCommGroup M] [Module R M]
variable {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The action of a finite matrix on tuples is additive over an arbitrary ring. -/
def matrixMap : (Fin n → M) →ₗ[ℤ] (Fin m → M) :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun x i => ∑ j, r i j • x j
    map_zero' := by ext; simp
    map_add' := by intro a b; ext; simp [smul_add, Finset.sum_add_distrib] }

abbrev Test := (Fin m → M) ⧸ LinearMap.range (matrixMap r M)
abbrev proj := (LinearMap.range (matrixMap r M)).mkQ

theorem proj_zero (a : Fin m → M) : proj r M a = 0 ↔ Soluble r a := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨x,h⟩ => ⟨x,congrFun h⟩, fun ⟨x,h⟩ => ⟨x,funext h⟩⟩

variable {M}
private def tupleMap (f : M →ₗ[R] N) : (Fin m → M) →ₗ[ℤ] (Fin m → N) :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun a => f ∘ a
    map_zero' := by ext; simp
    map_add' := by intro x y; ext; simp }

def testMap (f : M →ₗ[R] N) : Test r M →ₗ[ℤ] Test r N :=
  (LinearMap.range (matrixMap r M)).mapQ _ (tupleMap f) (by
    rintro a ⟨x,rfl⟩
    exact ⟨f ∘ x,funext (fun i => by simp [matrixMap, tupleMap, Function.comp_def, map_sum])⟩)

@[simp] theorem testMap_proj (f : M →ₗ[R] N) (a : Fin m → M) :
    testMap r f (proj r M a) = proj r N (f ∘ a) := rfl

theorem testMap_injective (f : M →ₗ[R] N) (hf : IsPureMap f) : Injective (testMap r f) := by
  apply (injective_iff_map_eq_zero _).2
  intro b
  obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r M)).mkQ_surjective b
  simpa only [testMap_proj, proj_zero] using hf.2 r a

variable (D : Type u) [AddCommGroup D]
/-- The additive character group carrying the action induced by right multiplication. -/
def Dual := Test r R →ₗ[ℤ] D
instance : AddCommGroup (Dual r D) := inferInstanceAs (AddCommGroup (Test r R →ₗ[ℤ] D))

private def right (s : R) : R →ₗ[R] R := LinearMap.toSpanSingleton R R s

instance : Module R (Dual r D) where
  smul s h := LinearMap.comp (show Test r R →ₗ[ℤ] D from h) (testMap r (right s))
  one_smul h := by
    apply LinearMap.ext
    intro b
    obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r R)).mkQ_surjective b
    let g : Test r R →ₗ[ℤ] D := h
    change g (proj r R ((right 1) ∘ a)) = g (proj r R a)
    simp [right,Function.comp_def]
  mul_smul s t h := by
    apply LinearMap.ext
    intro b
    obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r R)).mkQ_surjective b
    let g : Test r R →ₗ[ℤ] D := h
    change g (proj r R ((right (s*t)) ∘ a)) = g (proj r R ((right t) ∘ (right s) ∘ a))
    simp [right,Function.comp_def,mul_assoc]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul s t h := by
    apply LinearMap.ext
    intro b
    obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r R)).mkQ_surjective b
    let g : Test r R →ₗ[ℤ] D := h
    change g (proj r R ((right (s+t)) ∘ a)) = g (proj r R ((right s) ∘ a)) + g (proj r R ((right t) ∘ a))
    have he : (right (s+t)) ∘ a = (right s) ∘ a + (right t) ∘ a := by ext; simp [right,mul_add]
    rw [he,map_add,map_add]
  zero_smul h := by
    apply LinearMap.ext
    intro b
    obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r R)).mkQ_surjective b
    let g : Test r R →ₗ[ℤ] D := h
    change g (proj r R ((right 0) ∘ a)) = 0
    have he : (right 0) ∘ a = 0 := by ext; simp [right]
    rw [he,map_zero,map_zero]

private abbrev eval (h : Dual r D) (b : Test r R) : D :=
  (show Test r R →ₗ[ℤ] D from h) b

private def xMap (x : M) : R →ₗ[R] M := LinearMap.toSpanSingleton R M x

/-- Each functional on the matrix quotient assigns a character to each element. -/
def toDual (l : Test r M →ₗ[ℤ] D) : M →ₗ[R] Dual r D where
  toFun x := l.comp (testMap r (xMap x))
  map_add' x y := by
    apply LinearMap.ext
    intro b
    obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r R)).mkQ_surjective b
    change l (proj r M ((xMap (x+y)) ∘ a)) = l (proj r M ((xMap x) ∘ a)) + l (proj r M ((xMap y) ∘ a))
    have he : (xMap (x+y)) ∘ a = (xMap x) ∘ a + (xMap y) ∘ a := by ext; simp [xMap,smul_add]
    rw [he,map_add,map_add]
  map_smul' s x := by
    apply LinearMap.ext
    intro b
    obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r R)).mkQ_surjective b
    change l (proj r M ((xMap (s • x)) ∘ a)) = l (proj r M ((xMap x) ∘ (right s) ∘ a))
    simp [xMap,right,Function.comp_def,mul_smul]

private def basisClass (i : Fin m) : Test r R := proj r R (Pi.single i 1)

private theorem single_scalar (s : R) (i : Fin m) :
    right s ∘ Pi.single i (1 : R) = Pi.single i s := by
  ext k
  by_cases h : i = k <;> simp [h,Pi.single_apply,right]

private theorem single_action (x : M) (i : Fin m) (s : R) :
    xMap x ∘ Pi.single i s = Pi.single i (s • x) := by
  ext k
  by_cases h : i = k <;> simp [h,Pi.single_apply,xMap]

private theorem decompose {X : Type u} [AddCommGroup X] (a : Fin m → X) :
    ∑ i, Pi.single i (a i) = a := by
  ext k
  simp [Finset.sum_apply,Pi.single_apply]

private def trace : (Fin m → Dual r D) →ₗ[ℤ] D :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun a => ∑ i, eval r D (a i) (basisClass r i)
    map_zero' := by change ∑ _i : Fin m, (0 : D) = 0; simp
    map_add' := by intro x y; change ∑ i, (eval r D (x i) (basisClass r i) + eval r D (y i) (basisClass r i)) = _; rw [Finset.sum_add_distrib] }

private theorem trace_column (j : Fin n) (h : Dual r D) :
    ∑ i, eval r D (r i j • h) (basisClass r i) = 0 := by
  let g : Test r R →ₗ[ℤ] D := h
  change ∑ i, g (proj r R (right (r i j) ∘ Pi.single i (1 : R))) = 0
  simp_rw [single_scalar]
  rw [← map_sum, ← map_sum, decompose]
  have he : proj r R (fun i => r i j) = 0 := (proj_zero _ _ _).2 (by
    refine ⟨Pi.single j 1,fun i => ?_⟩
    simp [Pi.single_apply])
  rw [he,map_zero]

/-- The inverse construction evaluates characters on the matrix generators. -/
def fromDual (f : M →ₗ[R] Dual r D) : Test r M →ₗ[ℤ] D :=
  (LinearMap.range (matrixMap r M)).liftQ ((trace r D).comp (tupleMap f)) (by
    rintro _ ⟨x,rfl⟩
    change ∑ i, eval r D (f (∑ j, r i j • x j)) (basisClass r i) = 0
    simp only [map_sum,map_smul]
    have distribute (i : Fin m) :
        eval r D (∑ j, r i j • f (x j)) (basisClass r i) =
          ∑ j, eval r D (r i j • f (x j)) (basisClass r i) := by
      change (∑ j, (show Test r R →ₗ[ℤ] D from r i j • f (x j))) (basisClass r i) = _
      rw [LinearMap.sum_apply]
    simp_rw [distribute]
    rw [Finset.sum_comm]
    simp [trace_column])

@[simp] theorem fromDual_proj (f : M →ₗ[R] Dual r D) (a : Fin m → M) :
    fromDual r D f (proj r M a) = ∑ i, eval r D (f (a i)) (basisClass r i) := rfl

theorem fromDual_toDual (l : Test r M →ₗ[ℤ] D) : fromDual r D (toDual r D l) = l := by
  apply LinearMap.ext
  intro b
  obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r M)).mkQ_surjective b
  rw [fromDual_proj]
  change ∑ i, l (proj r M (xMap (a i) ∘ Pi.single i (1 : R))) = l (proj r M a)
  simp_rw [single_action,one_smul]
  rw [← map_sum, ← map_sum, decompose]

theorem toDual_fromDual (f : M →ₗ[R] Dual r D) : toDual r D (fromDual r D f) = f := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro b
  obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r R)).mkQ_surjective b
  change fromDual r D f (proj r M ((xMap x) ∘ a)) = eval r D (f x) (proj r R a)
  rw [fromDual_proj]
  simp only [Function.comp_apply, xMap, LinearMap.toSpanSingleton_apply, map_smul]
  let g : Test r R →ₗ[ℤ] D := f x
  change ∑ i, g (proj r R (right (a i) ∘ Pi.single i (1 : R))) = g (proj r R a)
  simp_rw [single_scalar]
  rw [← map_sum, ← map_sum, decompose]

theorem fromDual_comp (f : N →ₗ[R] Dual r D) (g : M →ₗ[R] N) :
    fromDual r D (f.comp g) = (fromDual r D f).comp (testMap r g) := by
  apply LinearMap.ext
  intro b
  obtain ⟨a,rfl⟩ := (LinearMap.range (matrixMap r M)).mkQ_surjective b
  rfl

/-- Additive maps into D extend along all additive embeddings. -/
def InjectiveGroup : Prop :=
  ∀ (A B : ModuleCat.{u} ℤ) (i : A →ₗ[ℤ] B) (f : A →ₗ[ℤ] D), Injective i →
    ∃ g : B →ₗ[ℤ] D, g.comp i = f

def UniversalGroup (κ : Cardinal.{u}) : Prop :=
  ∀ A : ModuleCat.{u} ℤ, Cardinal.mk A ≤ κ → ∃ f : A →ₗ[ℤ] D, Injective f

theorem dual_pureInjective (d : InjectiveGroup D) :
    IsPureInjective (ModuleCat.of R (Dual r D)) := by
  intro A B i f hi
  obtain ⟨g,hg⟩ := d (ModuleCat.of ℤ (Test r A)) (ModuleCat.of ℤ (Test r B))
    (testMap r i) (fromDual r D f) (testMap_injective r i hi)
  refine ⟨toDual r D g, ?_⟩
  rw [← toDual_fromDual r D ((toDual r D g).comp i), fromDual_comp, fromDual_toDual, hg,
    toDual_fromDual]

private theorem reflects_test (l : Test r M →ₗ[ℤ] D) (hl : Injective l) (a : Fin m → M)
    (sol : Soluble r ((toDual r D l) ∘ a)) : Soluble r a := by
  apply (proj_zero r M a).mp
  apply hl
  rw [map_zero]
  have fact : (fromDual r D (LinearMap.id : Dual r D →ₗ[R] Dual r D)).comp
      (testMap r (toDual r D l)) = l :=
    (fromDual_comp r D LinearMap.id (toDual r D l)).symm.trans (fromDual_toDual r D l)
  rw [← fact,LinearMap.comp_apply,testMap_proj,(proj_zero r _ _).2 sol,map_zero]

private abbrev Code (R : Type u) := EquationCriterion.EquationCode R R
private abbrev coeff (t : Code R) := t.2.2.1
private abbrev Target (R : Type u) [Ring R] (D : Type u) [AddCommGroup D] :=
  (t : Code R) → Dual (coeff t) D

private theorem product_pureInjective (d : InjectiveGroup D) :
    IsPureInjective (ModuleCat.of R (Target R D)) := by
  intro A B i f hi
  have works (t : Code R) := dual_pureInjective (coeff t) D d A B i ((LinearMap.proj t).comp f) hi
  choose g hg using works
  exact ⟨LinearMap.pi g, LinearMap.ext fun x => funext fun t => LinearMap.congr_fun (hg t) x⟩

theorem test_size (κ : Cardinal.{u}) (hω : ℵ₀ ≤ κ) (hm : Cardinal.mk M ≤ κ) :
    Cardinal.mk (Test r M) ≤ κ := by
  apply (Cardinal.mk_le_of_surjective (LinearMap.range (matrixMap r M)).mkQ_surjective).trans
  rw [Cardinal.mk_arrow, Cardinal.lift_mk_fin, Cardinal.lift_uzero]
  exact (Cardinal.power_le_power_right hm).trans (Cardinal.power_nat_le hω)

private theorem product_universal (κ : Cardinal.{u}) (hω : ℵ₀ ≤ κ) (d : UniversalGroup D κ)
    (M : ModuleCat.{u} R) (hm : Cardinal.mk M ≤ κ) :
    ∃ f : M →ₗ[R] Target R D, IsPureMap f := by
  have embedding (t : Code R) :=
    d (ModuleCat.of ℤ (Test (coeff t) M)) (test_size (coeff t) κ hω hm)
  choose l hl using embedding
  let f : M →ₗ[R] Target R D := LinearMap.pi fun t => toDual (coeff t) D (l t)
  have reflect : ∀ {m n : ℕ} (r : Fin m → Fin n → R) (a : Fin m → M),
      Soluble r (f ∘ a) → Soluble r a := by
    intro m n r a hs
    let t : Code R := ⟨m,n,r,fun _ => 0⟩
    exact reflects_test (coeff t) D (l t) (hl t) a (hs.map (LinearMap.proj t))
  exact ⟨f,EquationCriterion.inj_of_reflect f reflect,reflect⟩

private theorem product_size (κ ρ : Cardinal.{u}) (hω : ℵ₀ ≤ ρ)
    (hr : Cardinal.mk R ≤ ρ) (hd : Cardinal.mk D ≤ κ) (hκ : κ ≠ 0) :
    Cardinal.mk (Target R D) ≤ κ ^ ρ := by
  have codeSize : Cardinal.mk (Code R) ≤ ρ := EquationCriterion.systemCardinal_le ρ hω hr hr
  have factorSize (t : Code R) : Cardinal.mk (Dual (coeff t) D) ≤ κ ^ ρ := by
    calc
      _ ≤ Cardinal.mk (Test (coeff t) R → D) :=
        Cardinal.mk_le_of_injective (DFunLike.coe_injective (F := Test (coeff t) R →ₗ[ℤ] D))
      _ ≤ κ ^ ρ := by
        rw [Cardinal.mk_arrow,Cardinal.lift_id,Cardinal.lift_id]
        exact (Cardinal.power_le_power_right hd).trans
          (Cardinal.power_le_power_left hκ (test_size (coeff t) ρ hω hr))
  calc
    _ = Cardinal.prod (fun t : Code R => Cardinal.mk (Dual (coeff t) D)) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod (fun _ : Code R => κ ^ ρ) := Cardinal.prod_le_prod _ _ factorSize
    _ = (κ ^ ρ) ^ Cardinal.mk (Code R) := by simp [Cardinal.prod_const]
    _ ≤ (κ ^ ρ) ^ ρ := Cardinal.power_le_power_left (Cardinal.power_ne_zero _ hκ) codeSize
    _ = κ ^ ρ := by rw [← Cardinal.power_mul,Cardinal.mul_eq_self hω]

/-- The arbitrary-ring upper bound follows from a small universal injective
abelian group. The target is an explicit product of duals of finite matrix tests. -/
theorem upper_of_group (κ : Cardinal.{u}) (hω : ℵ₀ < κ) (hr : Cardinal.mk R < κ)
    (hd : Cardinal.mk D ≤ κ) (inj : InjectiveGroup D) (univ : UniversalGroup D κ) :
    ∃ F : ModuleCat.{u} R, HasExtension κ F ∧ Cardinal.mk F ≤ κ ^ max (Cardinal.mk R) ℵ₀ := by
  let F := ModuleCat.of R (Target R D)
  refine ⟨F, EquationCriterion.extension_of_pureInjective_and_universal κ hω hr F
    (product_pureInjective D inj) (product_universal D κ hω.le univ), ?_⟩
  exact product_size D κ _ (le_max_right _ _) (le_max_left _ _) hd (ne_of_gt (lt_trans Cardinal.aleph0_pos hω))

end PureEmbeddings.GeneralUpper
