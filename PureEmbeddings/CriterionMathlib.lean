import PureEmbeddings.Criterion
import PureEmbeddings.ModuleTheory
import Mathlib.SetTheory.Cardinal.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Perturbation for actual modules
Over a commutative ring we construct a single linear extension working
for every tensor test in a small family. Right exactness after tensoring,
separation of the coordinate copies, and the counting estimate used to
choose a fresh copy are all proved or instantiated from Mathlib here.
-/
namespace PureEmbeddings.CriterionMathlib

open Function LinearMap TensorProduct
open scoped TensorProduct Cardinal

universe u

variable {R : Type u} [CommRing R]
variable {A B C F : Type u} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup F] [Module R A] [Module R B] [Module R C] [Module R F]

/-- The elementary group used by the core proof, instantiated with the
actual additive group of a module (in particular, a tensor product). -/
private def groupModel (M : Type u) [AddCommGroup M] : Criterion.Abelian where
  Carrier := M
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  assoc := add_assoc
  comm := add_comm
  add_zero := add_zero
  add_neg := add_neg_cancel

private def homModel (f : A →ₗ[R] B) : Criterion.Hom (groupModel A) (groupModel B) where
  map := f
  map_zero := map_zero f
  map_add := map_add f

/-- Right-exact tensor tests certify the actual map `g + j ∘ q` for one
fresh copy. Only the original (untensored) sequence is assumed exact. -/
theorem tensorPerturbation (P : Type u) [AddCommGroup P] [Module R P]
    (i : A →ₗ[R] B) (q : B →ₗ[R] C) (f : A →ₗ[R] F) (g : B →ₗ[R] F) (j : C →ₗ[R] F)
    (seq : Function.Exact i q) (onto : Surjective q) (agrees : g.comp i = f)
    (fPure : Injective (f.lTensor P)) (jPure : Injective (j.lTensor P))
    (fresh : Criterion.DisjointImages 0 (g.lTensor P) (j.lTensor P)) :
    Injective ((g + j.comp q).lTensor P) := by
  have tseq := lTensor_exact P seq onto
  have hgi : (g.lTensor P).comp (i.lTensor P) = f.lTensor P := by
    rw [← LinearMap.lTensor_comp, agrees]
  have result := Criterion.perturbation
    (homModel (i.lTensor P)) (homModel (q.lTensor P))
    (homModel (f.lTensor P)) (homModel (g.lTensor P)) (homModel (j.lTensor P))
    (fun a => (tseq _).2 ⟨a, rfl⟩) (fun b hb => (tseq b).1 hb)
    (fun a => LinearMap.congr_fun hgi a) fPure jPure fresh
  rw [LinearMap.lTensor_add, LinearMap.lTensor_comp]
  exact result.2

/-- A direct-sum inclusion and its matching projection still compose to the
identity after tensoring, while different indices give zero. -/
private theorem tensor_same {I : Type u} (P : Type u) [AddCommGroup P] [Module R P]
    (i : I) (x : P ⊗[R] C) :
    (Finsupp.lapply i : (I →₀ C) →ₗ[R] C).lTensor P
      ((Finsupp.lsingle i : C →ₗ[R] (I →₀ C)).lTensor P x) = x := by
  rw [← LinearMap.lTensor_comp_apply, Finsupp.lapply_comp_lsingle_same, LinearMap.lTensor_id_apply]

private theorem tensor_other {I : Type u} (P : Type u) [AddCommGroup P] [Module R P]
    (i k : I) (different : i ≠ k) (x : P ⊗[R] C) :
    (Finsupp.lapply i : (I →₀ C) →ₗ[R] C).lTensor P
      ((Finsupp.lsingle k : C →ₗ[R] (I →₀ C)).lTensor P x) = 0 := by
  rw [← LinearMap.lTensor_comp_apply, Finsupp.lapply_comp_lsingle_of_ne i k different,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- The tensor product is covered by finite lists of pure tensors. Here
we use that coefficients can already be absorbed by a tensor factor. -/
theorem tensorCardinal_le (P : Type u) [AddCommGroup P] [Module R P]
    (μ : Cardinal.{u}) (hω : ℵ₀ ≤ μ) (hp : Cardinal.mk P ≤ μ) (hb : Cardinal.mk B ≤ μ) :
    Cardinal.mk (P ⊗[R] B) ≤ μ := by
  let eval (xs : List (P × B)) : P ⊗[R] B :=
    (xs.map (fun pair => pair.1 ⊗ₜ[R] pair.2)).sum
  have surj : Surjective eval := by
    intro x
    induction x with
    | zero => exact ⟨[], rfl⟩
    | tmul p b => exact ⟨[(p,b)], by simp [eval]⟩
    | add x y hx hy =>
      obtain ⟨l, hl⟩ := hx
      obtain ⟨m, hm⟩ := hy
      refine ⟨l ++ m, ?_⟩
      simpa only [eval, List.map_append, List.sum_append] using congrArg₂ (· + ·) hl hm
  refine (Cardinal.mk_le_of_surjective surj).trans ((Cardinal.mk_list_le_max _).trans ?_)
  refine max_le hω ?_
  simp only [Cardinal.mk_prod, Cardinal.lift_id]
  exact (mul_le_mul' hp hb).trans_eq (Cardinal.mul_eq_self hω)

/-- Sufficiency argument on a family `P` of tensor tests. All test modules,
their index set, and `B` have cardinality at most `μ`. An embedding of a
larger direct sum of copies of the quotient then yields a single linear
extension passing every test in this family. -/
theorem extendAcrossPureTests {T I : Type u}
    (P : T → Type u) [∀ t, AddCommGroup (P t)] [∀ t, Module R (P t)]
    (μ : Cardinal.{u}) (hω : ℵ₀ ≤ μ) (ht : Cardinal.mk T ≤ μ)
    (hp : ∀ t, Cardinal.mk (P t) ≤ μ) (hb : Cardinal.mk B ≤ μ)
    (big : μ < Cardinal.mk I)
    (i : A →ₗ[R] B) (q : B →ₗ[R] C) (f : A →ₗ[R] F) (g : B →ₗ[R] F)
    (into : (I →₀ C) →ₗ[R] F)
    (seq : Function.Exact i q) (onto : Surjective q) (agrees : g.comp i = f)
    (fPure : ∀ t, Injective (f.lTensor (P t)))
    (intoPure : ∀ t, Injective (into.lTensor (P t))) :
    ∃ h : B →ₗ[R] F, h.comp i = f ∧ ∀ t, Injective (h.lTensor (P t)) := by
  classical
  let j (k : I) : C →ₗ[R] F := into.comp (Finsupp.lsingle k)
  have jPure (t : T) (k : I) : Injective ((j k).lTensor (P t)) := by
    intro x y hxy
    have singles := intoPure t (by simpa only [j, LinearMap.lTensor_comp_apply] using hxy)
    simpa only [tensor_same] using congrArg
      ((Finsupp.lapply k : (I →₀ C) →ₗ[R] C).lTensor (P t)) singles
  have separate (t : T) (k l : I) (different : k ≠ l) :
      Criterion.DisjointImages 0 ((j k).lTensor (P t)) ((j l).lTensor (P t)) := by
    intro x y equal
    have singles := intoPure t (by simpa only [j, LinearMap.lTensor_comp_apply] using equal)
    have xz := congrArg ((Finsupp.lapply k : (I →₀ C) →ₗ[R] C).lTensor (P t)) singles
    have : x = 0 := by simpa only [tensor_same, tensor_other _ _ _ different] using xz
    rw [this, map_zero]
  have domains : Cardinal.mk (Sigma (fun t => P t ⊗[R] B)) ≤ μ := by
    rw [Cardinal.mk_sigma]
    calc
      _ ≤ Cardinal.sum (fun _ : T => μ) :=
        Cardinal.sum_le_sum _ _ (fun t => tensorCardinal_le (P t) μ hω (hp t) hb)
      _ = Cardinal.mk T * μ := Cardinal.sum_const' T μ
      _ ≤ μ := (mul_le_mul' ht le_rfl).trans_eq (Cardinal.mul_eq_self hω)
  have large : ¬ ∃ e : I → Sigma (fun t => P t ⊗[R] B), Criterion.OneToOne e := by
    rintro ⟨e, he⟩
    exact (not_le_of_gt big) ((Cardinal.mk_le_of_injective he).trans domains)
  obtain ⟨k, fresh⟩ := Criterion.freshIndex (fun t => (0 : P t ⊗[R] F))
    (fun t => (g.lTensor (P t)).toFun) (fun t k => ((j k).lTensor (P t)).toFun) separate large
  refine ⟨g + (j k).comp q, ?_, ?_⟩
  · ext a
    have qa : q (i a) = 0 := (seq _).2 ⟨a, rfl⟩
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, qa, map_zero, add_zero]
      using LinearMap.congr_fun agrees a
  · intro t
    exact tensorPerturbation (P t) i q f g (j k) seq onto agrees (fPure t) (jPure t k) (fresh t)

/-- The ordinary submodule inclusion and quotient require no exactness or
surjectivity assumptions. -/
theorem extendFromSubmodule {T I : Type u}
    (P : T → Type u) [∀ t, AddCommGroup (P t)] [∀ t, Module R (P t)]
    (μ : Cardinal.{u}) (hω : ℵ₀ ≤ μ) (ht : Cardinal.mk T ≤ μ)
    (hp : ∀ t, Cardinal.mk (P t) ≤ μ) (hb : Cardinal.mk B ≤ μ)
    (big : μ < Cardinal.mk I) (S : Submodule R B) (f : S →ₗ[R] F) (g : B →ₗ[R] F)
    (into : (I →₀ (B ⧸ S)) →ₗ[R] F) (agrees : g.comp S.subtype = f)
    (fPure : ∀ t, Injective (f.lTensor (P t))) (intoPure : ∀ t, Injective (into.lTensor (P t))) :
    ∃ h : B →ₗ[R] F, h.comp S.subtype = f ∧ ∀ t, Injective (h.lTensor (P t)) :=
  extendAcrossPureTests P μ hω ht hp hb big S.subtype S.mkQ f g into
    (LinearMap.exact_subtype_mkQ S) S.mkQ_surjective agrees fPure intoPure

end PureEmbeddings.CriterionMathlib

namespace PureEmbeddings.EquationCriterion

open Function Cardinal
open scoped BigOperators Cardinal

universe u
variable {R A B C F : Type u} [Ring R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup F] [Module R A] [Module R B] [Module R C] [Module R F]

private def row {m n : ℕ} {M : Type u} [AddCommGroup M] [Module R M]
    (r : Fin m → Fin n → R) (z : Fin n → M) (i : Fin m) : M := ∑ j, r i j • z j

private theorem solubleSub {m n : ℕ} (r : Fin m → Fin n → R) {a b : Fin m → B}
    (ha : Soluble r a) (hb : Soluble r b) : Soluble r (fun i => a i - b i) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  exact ⟨fun j => x j - y j, fun i => by simp [smul_sub, Finset.sum_sub_distrib, hx, hy]⟩

/-- Lifting a solution modulo the prescribed submodule reduces reflection
of the original system to purity of the restriction. -/
private theorem liftSolutions {m n : ℕ} (r : Fin m → Fin n → R) (b : Fin m → B)
    (i : A →ₗ[R] B) (q : B →ₗ[R] C) (f : A →ₗ[R] F) (h : B →ₗ[R] F)
    (exactAt : Exact i q) (onto : Surjective q) (agrees : h.comp i = f)
    (pureF : IsPureMap f) (imageSol : Soluble r (h ∘ b)) (quotSol : Soluble r (q ∘ b)) :
    Soluble r b := by
  classical
  obtain ⟨y, hy⟩ := quotSol
  choose z hz using fun j => onto (y j)
  let w := row r z
  have fromA (l : Fin m) : ∃ a, i a = b l - w l := by
    apply (exactAt _).mp
    simp only [w, row, map_sub, map_sum, map_smul, hz]
    exact sub_eq_zero.mpr (hy l).symm
  choose a ha using fromA
  have wSol : Soluble r w := ⟨z, fun _ => rfl⟩
  have reflected : Soluble r a := by
    apply pureF.2 r a
    have hs := solubleSub r imageSol (wSol.map h)
    have identities : (fun l => (h ∘ b) l - (h ∘ w) l) = f ∘ a := by
      funext l
      calc
        _ = h (b l - w l) := (map_sub h _ _).symm
        _ = h (i (a l)) := congrArg h (ha l).symm
        _ = _ := LinearMap.congr_fun agrees (a l)
    exact identities ▸ hs
  obtain ⟨x, hx⟩ := reflected.map i
  refine ⟨fun j => x j + z j, fun l => ?_⟩
  simp only [smul_add, Finset.sum_add_distrib, hx, Function.comp_apply, ha]
  exact sub_add_cancel _ _

abbrev EquationCode (S X : Type u) :=
  Σ nrows : ℕ, Σ ncols : ℕ, (Fin nrows → Fin ncols → S) × (Fin nrows → X)

omit [Ring R] [AddCommGroup B] [Module R B] in
theorem systemCardinal_le (μ : Cardinal.{u}) (hω : ℵ₀ ≤ μ)
    (hr : Cardinal.mk R ≤ μ) (hb : Cardinal.mk B ≤ μ) :
    Cardinal.mk (EquationCode R B) ≤ μ := by
  have finFun (d : ℕ) (X : Type u) (hx : Cardinal.mk X ≤ μ) : Cardinal.mk (Fin d → X) ≤ μ := by
    rw [Cardinal.mk_arrow, Cardinal.lift_mk_fin, Cardinal.lift_uzero]
    exact (Cardinal.power_le_power_right hx).trans (Cardinal.power_nat_le hω)
  have countSum (s : ℕ → Type u) (hs : ∀ n, Cardinal.mk (s n) ≤ μ) :
      Cardinal.mk (Sigma s) ≤ μ := by
    rw [Cardinal.mk_sigma]
    calc
      _ ≤ Cardinal.sum (fun _ : ℕ => μ) := Cardinal.sum_le_sum _ _ hs
      _ = ℵ₀ * μ := by simp [Cardinal.sum_const]
      _ ≤ μ := (mul_le_mul' hω le_rfl).trans_eq (Cardinal.mul_eq_self hω)
  apply countSum
  intro m
  apply countSum
  intro n
  simp only [Cardinal.mk_prod, Cardinal.lift_id]
  exact (mul_le_mul' (finFun m _ (finFun n _ hr)) (finFun m _ hb)).trans_eq (Cardinal.mul_eq_self hω)

theorem inj_of_reflect (h : B →ₗ[R] F)
    (reflects : ∀ {m n : ℕ} (r : Fin m → Fin n → R) (a : Fin m → B),
      Soluble r (h ∘ a) → Soluble r a) : Injective h := by
  intro x y equal
  apply sub_eq_zero.mp
  let r : Fin 1 → Fin 0 → R := fun _ k => Fin.elim0 k
  let a : Fin 1 → B := fun _ => x - y
  have image : Soluble r (h ∘ a) := ⟨Fin.elim0, fun _ => by simp [a, equal]⟩
  obtain ⟨z, hz⟩ := reflects r a image
  simpa only [a, Finset.univ_eq_empty, Finset.sum_empty] using (hz 0).symm

/-- One coordinate suffices for every finite system over a possibly
noncommutative ring. If two candidate coordinates made the same false
system soluble, subtraction and projection would solve it modulo the
submodule. Lifting that solution gives a contradiction. -/
theorem uniformEquationExtension {I : Type u}
    (μ : Cardinal.{u}) (hω : ℵ₀ ≤ μ) (hr : Cardinal.mk R ≤ μ) (hb : Cardinal.mk B ≤ μ)
    (big : μ < Cardinal.mk I)
    (i : A →ₗ[R] B) (q : B →ₗ[R] C) (f : A →ₗ[R] F) (g : B →ₗ[R] F)
    (into : (I →₀ C) →ₗ[R] F) (exactAt : Exact i q) (onto : Surjective q)
    (agrees : g.comp i = f) (pureF : IsPureMap f) (pureInto : IsPureMap into) :
    ∃ h : B →ₗ[R] F, IsPureMap h ∧ h.comp i = f := by
  classical
  let s (k : I) : C →ₗ[R] (I →₀ C) := Finsupp.lsingle k
  let h (k : I) := g + (into.comp (s k)).comp q
  have extendsOn (k : I) : (h k).comp i = f := by
    ext a
    have qa : q (i a) = 0 := (exactAt _).2 ⟨a, rfl⟩
    simpa only [h, LinearMap.comp_apply, LinearMap.add_apply, qa, map_zero, add_zero]
      using LinearMap.congr_fun agrees a
  let bad (k : I) (p : EquationCode R B) :=
    Soluble p.2.2.1 ((h k) ∘ p.2.2.2) ∧ ¬ Soluble p.2.2.1 p.2.2.2
  have uniqueBad (k l : I) (p : EquationCode R B) (bk : bad k p) (bl : bad l p) : k = l := by
    by_contra different
    let r := p.2.2.1
    let a := p.2.2.2
    let delta (v : Fin p.1) := s k (q (a v)) - s l (q (a v))
    have eqDelta : into ∘ delta = fun v => (h k ∘ a) v - (h l ∘ a) v := by
      funext v
      simp only [delta, h, Function.comp_apply, map_sub, LinearMap.add_apply, LinearMap.comp_apply]
      abel
    have sd : Soluble r delta := by
      apply pureInto.2 r delta
      rw [eqDelta]
      exact solubleSub r bk.1 bl.1
    have proj : (Finsupp.lapply k : (I →₀ C) →ₗ[R] C) ∘ delta = q ∘ a := by
      funext v
      simp [delta, s, Ne.symm different]
    have qs : Soluble r (q ∘ a) := proj ▸ sd.map (Finsupp.lapply k)
    exact bk.2 (liftSolutions r a i q f (h k) exactAt onto (extendsOn k) pureF bk.1 qs)
  have fresh : ∃ k, ∀ p, ¬ bad k p := by
    by_contra! allBad
    choose pick hits using allBad
    have hinj : Injective pick := by
      intro k l eq
      exact uniqueBad k l (pick k) (hits k) (eq.symm ▸ hits l)
    exact (not_le_of_gt big) ((Cardinal.mk_le_of_injective hinj).trans (systemCardinal_le μ hω hr hb))
  obtain ⟨k, hk⟩ := fresh
  have reflEq : ∀ {m n : ℕ} (r : Fin m → Fin n → R) (a : Fin m → B),
      Soluble r (h k ∘ a) → Soluble r a := by
    intro m n r a hs
    by_contra hn
    exact hk ⟨m,n,r,a⟩ ⟨hs,hn⟩
  exact ⟨h k, ⟨inj_of_reflect _ reflEq, reflEq⟩, extendsOn k⟩

/-- The sufficiency direction of the paper's extension criterion, now
in the finite-equation formulation of purity for all left modules over
an arbitrary ring. Both singular and regular cardinals are allowed. -/
theorem extension_of_pureInjective_and_universal (κ : Cardinal.{u})
    (hω : ℵ₀ < κ) (hr : Cardinal.mk R < κ) (F : ModuleCat.{u} R)
    (injectiveF : IsPureInjective F)
    (universal : ∀ M : ModuleCat.{u} R, Cardinal.mk M ≤ κ →
      ∃ u : M →ₗ[R] F, IsPureMap u) : HasExtension κ F := by
  classical
  intro A B i f hB pureI pureF
  obtain ⟨g, agrees⟩ := injectiveF A B i f pureI
  let C := B ⧸ LinearMap.range i
  let q : B →ₗ[R] C := (LinearMap.range i).mkQ
  have onto : Surjective q := (LinearMap.range i).mkQ_surjective
  have exactAt : Exact i q := LinearMap.exact_map_mkQ_range i
  have hC : Cardinal.mk C ≤ κ := (Cardinal.mk_le_of_surjective onto).trans hB.le
  let I := κ.out
  have hI : Cardinal.mk I = κ := Cardinal.mk_out κ
  letI : Infinite I := Cardinal.aleph0_le_mk_iff.mp (hI.symm ▸ hω.le)
  have size : Cardinal.mk (I →₀ C) ≤ κ := by
    calc
      _ ≤ Cardinal.mk (Finset (I × C)) := Cardinal.mk_le_of_injective (Finsupp.graph_injective I C)
      _ = Cardinal.mk (I × C) := Cardinal.mk_finset_of_infinite _
      _ ≤ κ := by
        simp only [Cardinal.mk_prod, Cardinal.lift_id, hI]
        exact (mul_le_mul' le_rfl hC).trans_eq (Cardinal.mul_eq_self hω.le)
  obtain ⟨into, hin⟩ := universal (ModuleCat.of R (I →₀ C)) size
  let μ := max ℵ₀ (max (Cardinal.mk R) (Cardinal.mk B))
  have upper : μ < Cardinal.mk I := by
    rw [hI]
    exact max_lt hω (max_lt hr hB)
  exact uniformEquationExtension μ (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
    upper i q f g into exactAt onto agrees pureF hin

end PureEmbeddings.EquationCriterion
