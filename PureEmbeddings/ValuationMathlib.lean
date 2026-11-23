import PureEmbeddings.Valuation
import PureEmbeddings.ModuleTheory
import PureEmbeddings.Germs
import PureEmbeddings.Universality
import PureEmbeddings.Branching
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.Quotient.Defs

/-! The valuation separation theorem for Mathlib's commutative valuation
domains. The index type consists of all nonzero, proper principal ideals,
equivalently all positive values. The final theorem uses the usual quotient
module and an existential linear equation on its elements. -/

namespace PureEmbeddings.ValuationMathlib

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]

/-- The hypotheses used in the elementary quotient calculation follow
from the valuation-ring instance, including the identification of its
non-units with the unique maximal ideal. -/
def laws : PureEmbeddings.Valuation.DomainLaws R where
  add_assoc := add_assoc
  add_zero := add_zero
  zero_add := zero_add
  add_neg := add_neg_cancel
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  mul_one := mul_one
  mul_zero := mul_zero
  mul_add := mul_add
  cancel := fun h e => mul_left_cancel₀ h e
  inMax := fun x => x ∈ IsLocalRing.maximalIdeal R
  zero_mem := (IsLocalRing.maximalIdeal R).zero_mem
  one_not_mem := IsLocalRing.notMem_maximalIdeal.mpr isUnit_one
  add_mem := (IsLocalRing.maximalIdeal R).add_mem
  neg_mem := (IsLocalRing.maximalIdeal R).neg_mem
  mul_mem := fun x _ h => (IsLocalRing.maximalIdeal R).mul_mem_left x h
  inverse_of_outside := fun h => isUnit_iff_exists_inv.mp (IsLocalRing.notMem_maximalIdeal.mp h)
  divides_total := fun x y => by
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond x y
    · exact Or.inl ⟨c, hc.symm⟩
    · exact Or.inr ⟨c, hc.symm⟩

/-- Index all positive values without choosing an ambient fraction field:
two nonzero elements of the maximal ideal give the same index precisely
when they generate the same principal ideal. -/
def PositiveValue :=
  {p : Ideal R // ∃ a : R, a ∈ IsLocalRing.maximalIdeal R ∧ a ≠ 0 ∧ Ideal.span {a} = p}

noncomputable def generator (i : PositiveValue R) : R := Classical.choose i.property

theorem generator_spec (i : PositiveValue R) :
    generator R i ∈ IsLocalRing.maximalIdeal R ∧ generator R i ≠ 0 ∧
      Ideal.span {generator R i} = i.val := Classical.choose_spec i.property

theorem distinct_values (i j : PositiveValue R) (hij : i ≠ j) :
    ¬ PureEmbeddings.Valuation.DomainLaws.SameValue (generator R i) (generator R j) := by
  rintro ⟨ij, ji⟩
  apply hij
  apply Subtype.ext
  rw [← (generator_spec R i).2.2, ← (generator_spec R j).2.2]
  exact le_antisymm (Ideal.span_singleton_le_span_singleton.mpr ji)
    (Ideal.span_singleton_le_span_singleton.mpr ij)

abbrev MaxIdeal := ↥(IsLocalRing.maximalIdeal R)

/-- The submodule a²m inside m. -/
def layerSubmodule (a : R) : Submodule R (MaxIdeal R) :=
  LinearMap.range ((a * a) • (LinearMap.id : MaxIdeal R →ₗ[R] MaxIdeal R))

/-- The actual Mathlib quotient module. -/
abbrev Layer (a : R) := (MaxIdeal R) ⧸ layerSubmodule R a

/-- The abstract congruence used in the constructive calculation is exactly
equality of representatives in the usual quotient module. -/
theorem class_eq_iff (a : R) (x y : MaxIdeal R) :
    (Submodule.Quotient.mk x : Layer R a) = Submodule.Quotient.mk y ↔
    (laws R).residue a x.val x.property = (laws R).residue a y.val y.property := by
  rw [Submodule.Quotient.eq, (laws R).residue_eq_iff]
  change (∃ d : MaxIdeal R, (a * a) • d = x - y) ↔
    ∃ d : R, d ∈ IsLocalRing.maximalIdeal R ∧ (x : R) = (y : R) + (a * a) * d
  constructor
  · rintro ⟨d, hd⟩
    have eqn : (a * a) * (d : R) = (x : R) - (y : R) := congrArg Subtype.val hd
    exact ⟨d, d.property, by rw [eqn]; exact (add_sub_cancel _ _).symm⟩
  · rintro ⟨d, hd, eqn⟩
    refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
    change (a * a) * d = (x : R) - (y : R)
    rw [eqn, add_sub_cancel_left]

/-- The standard finite linear system, with both witnesses in the ordinary
quotient module. -/
def Mixed {M : Type*} [AddCommGroup M] [Module R M] (t : R) (x : M) : Prop :=
  ∃ y z : M, x = t • y + z ∧ t • z = 0

omit [IsDomain R] [ValuationRing R] in
theorem mixed_iff_equation {M : Type*} [AddCommGroup M] [Module R M] (t : R) (x : M) :
    Mixed R t x ↔ ∃ y : M, t • x = (t * t) • y := by
  constructor
  · rintro ⟨y,z,rfl,hz⟩
    exact ⟨y, by rw [smul_add, hz, add_zero, mul_smul]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, x - t • y, ?_, ?_⟩
    · exact (add_sub_cancel _ _).symm
    · rw [smul_sub, ← mul_smul, hy, sub_self]

theorem mixed_class_iff (a t : R) (x : MaxIdeal R) :
    Mixed R t (Submodule.Quotient.mk x : Layer R a) ↔
    (laws R).Mixed a t ((laws R).residue a x.val x.property) := by
  constructor
  · rintro ⟨y,z,hsum,hann⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (layerSubmodule R a) y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (layerSubmodule R a) z
    exact ⟨y.val, z.val, y.property, z.property,
      (class_eq_iff R a x (t • y + z)).mp hsum,
      (class_eq_iff R a (t • z) 0).mp hann⟩
  · rintro ⟨y,z,hy,hz,hsum,hann⟩
    let y' : MaxIdeal R := ⟨y, hy⟩
    let z' : MaxIdeal R := ⟨z, hz⟩
    exact ⟨Submodule.Quotient.mk y', Submodule.Quotient.mk z',
      (class_eq_iff R a x (t • y' + z')).mpr hsum,
      (class_eq_iff R a (t • z') 0).mpr hann⟩

omit [IsDomain R] [ValuationRing R] in
/-- Purity reflects the one-equation test used for every positive value.
Here purity is the paper's reflection of arbitrary finite systems, with
one row and one unknown in this application. -/
theorem reflect_equation {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : PureEmbeddings.IsPureMap f)
    (t : R) (x : M) (h : ∃ y : N, t • f x = (t * t) • y) :
    ∃ y : M, t • x = (t * t) • y := by
  obtain ⟨y, hy⟩ := h
  let coeff : Fin 1 → Fin 1 → R := fun _ _ => t * t
  let rhs : Fin 1 → M := fun _ => t • x
  have sol : PureEmbeddings.Soluble coeff (f ∘ rhs) := by
    refine ⟨fun _ => y, fun _ => ?_⟩
    simpa [coeff, rhs, Function.comp_def] using hy.symm
  obtain ⟨z, hz⟩ := hf.2 coeff rhs sol
  exact ⟨z 0, by simpa [coeff, rhs] using (hz 0).symm⟩

/-- The module and distinguished class for the positive value i. -/
abbrev ValueLayer (i : PositiveValue R) := Layer R (generator R i)

noncomputable def distinguished (i : PositiveValue R) : ValueLayer R i :=
  Submodule.Quotient.mk (⟨generator R i, (generator_spec R i).1⟩ : MaxIdeal R)

/-- Every positive value contributes a witness satisfying all the other
finite linear conditions and failing its own. All objects in the statement
use ordinary Mathlib rings, ideals, modules, and scalar multiplication. -/
theorem value_separation (i j : PositiveValue R) :
    (∃ y : ValueLayer R i,
      generator R j • distinguished R i = (generator R j * generator R j) • y) ↔ i ≠ j := by
  rw [← mixed_iff_equation]
  change Mixed R (generator R j)
    (Submodule.Quotient.mk (⟨generator R i, (generator_spec R i).1⟩ : MaxIdeal R) :
      Layer R (generator R i)) ↔ i ≠ j
  rw [mixed_class_iff]
  exact (laws R).value_separation (generator R) (fun k => (generator_spec R k).1)
    (fun k => (generator_spec R k).2.1) (distinct_values R) i j


open scoped DirectSum
open Cardinal

/-- A linear equation has a finite list of scalar-variable terms. -/
def evalRow {J F : Type u} [AddCommGroup F] [Module R F]
    (row : List (R × J)) (z : J → F) : F :=
  (row.map (fun p => p.1 • z p.2)).sum

/-- Compactness for prescribed sets of equations and unknowns. -/
def CompactFor (F I J : Type u) [AddCommGroup F] [Module R F] : Prop :=
  ∀ (rows : I → List (R × J)) (b : I → F),
    (∀ s : Finset I, ∃ z : J → F, ∀ i ∈ s, evalRow R (rows i) z = b i) →
    ∃ z : J → F, ∀ i, evalRow R (rows i) z = b i

/-- Every finitely soluble system of linear equations is soluble.
Both the set of equations and the set of unknowns may be infinite. -/
def AlgebraicallyCompact (F : Type u) [AddCommGroup F] [Module R F] : Prop :=
  ∀ I J : Type u, CompactFor R F I J

/-- A direct sum of copies of the separating modules (one family per choice). -/
abbrev TestSpace (K : Type u) :=
  ⨁ p : PositiveValue R × K, ValueLayer R p.1

private noncomputable def entry {K : Type u} (i : PositiveValue R) (k : K) : TestSpace R K := by
  classical
  exact DirectSum.lof R _ (fun p : PositiveValue R × K => ValueLayer R p.1)
    (i,k) (distinguished R i)

omit [IsDomain R] [ValuationRing R] in
private theorem equation_map {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (t : R) (x : M)
    (h : ∃ y : M, t • x = (t*t) • y) :
    ∃ y : N, t • f x = (t*t) • y := by
  obtain ⟨y, hy⟩ := h
  exact ⟨f y, by simpa only [map_smul] using congrArg f hy⟩

private def equationGroup (M : Type u) [AddCommGroup M] [Module R M] (t : R) :
    AddSubgroup M where
  carrier := {x | ∃ y : M, t • x = (t * t) • y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨y,hy⟩ ⟨z,hz⟩
    exact ⟨y+z, by simp only [smul_add, hy, hz]⟩
  neg_mem' := by
    rintro _ ⟨y, hy⟩
    exact ⟨-y, by simp only [smul_neg, hy]⟩

private noncomputable def cosets {K F : Type u} [AddCommGroup F] [Module R F]
    (f : TestSpace R K →ₗ[R] F) (hf : PureEmbeddings.IsPureMap f) :
    PureEmbeddings.Branching.IndependentFamily (PositiveValue R) K F := by
  classical
  let G := fun i => equationGroup R F (generator R i)
  refine {
    zero := 0, add := (· + ·), zero_add := zero_add, add_zero := add_zero,
    same := fun i x y => x-y ∈ G i,
    refl := fun i x => by simp,
    symm := fun i x y h => by simpa using (G i).neg_mem h,
    trans := fun i x y z h h' => by simpa using (G i).add_mem h h',
    add_congr := ?_, entry := fun i k => f (entry R i k),
    off_coordinate := ?_, separate := ?_ }
  · intro i a b x y hab hxy
    have h := (G i).add_mem hab hxy
    convert h using 1; abel
  · intro i j k hij
    rw [sub_zero]
    apply equation_map R f
    exact equation_map R
      (DirectSum.lof R _ (fun p : PositiveValue R × K => ValueLayer R p.1) (j,k))
      (generator R i) (distinguished R j) ((value_separation R j i).2 (Ne.symm hij))
  · intro i k l h
    by_contra hkl
    let p := DirectSum.component R (PositiveValue R × K)
      (fun q : PositiveValue R × K => ValueLayer R q.1) (i,k)
    have hh : ∃ y : TestSpace R K, generator R i • (entry R i k - entry R i l) =
        (generator R i * generator R i) • y :=
      reflect_equation R f hf (generator R i) _ (by simpa only [map_sub] using h)
    have hn : (i,l) ≠ (i,k) := fun eqn => hkl ((congrArg Prod.snd eqn).symm)
    have hzero : p (entry R i l) = 0 := by
      simp only [p, entry, DirectSum.component.of, dif_neg hn]
    have hone : p (entry R i k) = distinguished R i := by
      simp only [p, entry, DirectSum.component.lof_self]
    have hp := equation_map R p _ _ hh
    rw [map_sub, hone, hzero, sub_zero] at hp
    exact (value_separation R i i).mp hp rfl

/-- The cardinal bound from a pure copy of the concrete test space and
the ordinary equation-system formulation of algebraic compactness. -/
theorem lower_of_pure_test_space_small (K F : Type u) [AddCommGroup F] [Module R F]
    (f : TestSpace R K →ₗ[R] F) (hf : PureEmbeddings.IsPureMap f)
    (hc : CompactFor R F (PositiveValue R) (Option (PositiveValue R))) :
    Cardinal.mk K ^ Cardinal.mk (PositiveValue R) ≤ Cardinal.mk F := by
  classical
  let d := cosets R f hf
  obtain ⟨point, hinj⟩ := PureEmbeddings.Branching.independentInjection d (by
    intro b finite
    let row (i : PositiveValue R) : List (R × Option (PositiveValue R)) :=
      [(generator R i, none), (-(generator R i * generator R i), some i)]
    let rhs (i : PositiveValue R) := generator R i • b i
    have row_iff (i : PositiveValue R) (z : Option (PositiveValue R) → F) :
        evalRow R (row i) z = rhs i ↔
          generator R i • (z none - b i) = (generator R i * generator R i) • z (some i) := by
      simp only [evalRow, row, rhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, neg_smul, smul_sub]
      abel_nf
      constructor <;> intro h <;> linear_combination (norm := abel) h
    obtain ⟨z, hz⟩ := hc row rhs (by
      intro s
      obtain ⟨x,hx⟩ := finite s.toList s.nodup_toList
      have ex (i : PositiveValue R) (hi : i ∈ s) :
          ∃ y : F, generator R i • (x - b i) = (generator R i * generator R i) • y :=
        hx i (Finset.mem_toList.mpr hi)
      let z : Option (PositiveValue R) → F
        | none => x
        | some i => if hi : i ∈ s then Classical.choose (ex i hi) else 0
      refine ⟨z, fun i hi => (row_iff i z).mpr ?_⟩
      simpa only [z, dif_pos hi] using Classical.choose_spec (ex i hi))
    exact ⟨z none, fun i => ⟨z (some i), (row_iff i z).mp (hz i)⟩⟩)
  simpa only [Cardinal.mk_arrow, Cardinal.lift_id] using
    (Cardinal.mk_le_of_injective (f := point) (fun _ _ h => hinj _ _ h))


theorem lower_of_pure_test_space (K F : Type u) [AddCommGroup F] [Module R F]
    (f : TestSpace R K →ₗ[R] F) (hf : PureEmbeddings.IsPureMap f)
    (hc : AlgebraicallyCompact R F) :
    Cardinal.mk K ^ Cardinal.mk (PositiveValue R) ≤ Cardinal.mk F :=
  lower_of_pure_test_space_small R K F f hf (hc _ _)

/-- One representative determines a value class. -/
theorem positiveValues_cardinal_le : Cardinal.mk (PositiveValue R) ≤ Cardinal.mk R := by
  apply Cardinal.mk_le_of_injective (f := generator R)
  intro i j h
  apply Subtype.ext
  exact (generator_spec R i).2.2.symm.trans (h ▸ (generator_spec R j).2.2)

/-- The test direct sum has size at most κ whenever R does and κ is infinite.
A finite list of coordinates, with arbitrary maximal-ideal representatives,
already parametrises all of it. -/
theorem testSpace_cardinal_le (K : Type u) (hω : Cardinal.aleph0 ≤ Cardinal.mk K)
    (hR : Cardinal.mk R ≤ Cardinal.mk K) :
    Cardinal.mk (TestSpace R K) ≤ Cardinal.mk K := by
  classical
  let I := PositiveValue R × K
  let atom (p : I × MaxIdeal R) : TestSpace R K :=
    DirectSum.of (fun i : I => ValueLayer R i.1) p.1 (Submodule.Quotient.mk p.2)
  let total (l : List (I × MaxIdeal R)) : TestSpace R K := (l.map atom).sum
  have onto : Function.Surjective total := by
    intro z
    refine DirectSum.induction_on z ?_ ?_ ?_
    · exact ⟨[], rfl⟩
    · intro i x
      obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective (layerSubmodule R (generator R i.1)) x
      exact ⟨[(i,t)], by simp [total, atom]; rfl⟩
    · rintro x y ⟨l,rfl⟩ ⟨l',rfl⟩
      exact ⟨l++l', by simp [total]⟩
  have mulBound {a b : Cardinal.{u}} (ha : a ≤ Cardinal.mk K) (hb : b ≤ Cardinal.mk K) :
      a * b ≤ Cardinal.mk K :=
    (mul_le_mul' ha hb).trans_eq (Cardinal.mul_eq_self hω)
  have hI : Cardinal.mk I ≤ Cardinal.mk K := by
    simpa only [I, Cardinal.mk_prod, Cardinal.lift_id] using
      mulBound ((positiveValues_cardinal_le R).trans hR) (le_refl (Cardinal.mk K))
  have hMax : Cardinal.mk (MaxIdeal R) ≤ Cardinal.mk K :=
    (Cardinal.mk_le_of_injective (f := fun x : MaxIdeal R => (x : R)) Subtype.val_injective).trans hR
  have hProd : Cardinal.mk (I × MaxIdeal R) ≤ Cardinal.mk K := by
    simpa only [Cardinal.mk_prod, Cardinal.lift_id] using mulBound hI hMax
  exact (Cardinal.mk_le_of_surjective onto).trans
    ((Cardinal.mk_list_le_max _).trans (max_le hω hProd))

/-- The lower-bound direction of Theorem D for an algebraically compact
module that contains a pure copy of every module of size at most κ.
PositiveValue R indexes the nonzero proper principal ideals of R. -/
theorem lower_of_universality (κ : Cardinal.{u}) (F : ModuleCat.{u} R)
    (hω : Cardinal.aleph0 ≤ κ) (hR : Cardinal.mk R ≤ κ)
    (universal : ∀ M : ModuleCat.{u} R, Cardinal.mk M ≤ κ →
      ∃ f : M →ₗ[R] F, PureEmbeddings.IsPureMap f)
    (compact : AlgebraicallyCompact R F) :
    κ ^ Cardinal.mk (PositiveValue R) ≤ Cardinal.mk F := by
  have size : Cardinal.mk (TestSpace R κ.out) ≤ κ := by
    have h := testSpace_cardinal_le R κ.out (by simpa using hω) (by simpa using hR)
    simpa using h
  obtain ⟨f, hf⟩ := universal (ModuleCat.of R (TestSpace R κ.out)) size
  simpa using lower_of_pure_test_space R κ.out F f hf compact


omit [IsDomain R] [ValuationRing R] in
/-- The two finite-row presentations of ordinary algebraic compactness
agree; in particular the Germs theorem applies to a pure-injective F. -/
theorem compactFor_of_germs (F : ModuleCat.{u} R) (I J : Type u)
    (solve : ∀ s : PureEmbeddings.Germs.System R F I J, s.FinitelySoluble →
      ∃ z, ∀ i, s.Holds z i) : CompactFor R F I J := by
  intro rows b finitely
  let s : PureEmbeddings.Germs.System R F I J := {
    width := fun i => (rows i).length
    coeff := fun i j => (rows i)[j.1].1
    var := fun i j => (rows i)[j.1].2
    rhs := b }
  have equiv (z : J → F) (i : I) : s.Holds z i ↔ evalRow R (rows i) z = b i := by
    change (∑ j : Fin (rows i).length, (rows i)[j.1].1 • z (rows i)[j.1].2) = b i ↔ _
    unfold evalRow
    rw [← Fin.sum_univ_fun_getElem (rows i) (fun p => p.1 • z p.2)]
  obtain ⟨z,hz⟩ := solve s (by
    intro T
    obtain ⟨z,hz⟩ := finitely T
    exact ⟨z, fun i hi => (equiv z i).mpr (hz i hi)⟩)
  exact ⟨z, fun i => (equiv z i).mp (hz i)⟩

omit [IsDomain R] [ValuationRing R] in
theorem compact_of_pureInjective (F : ModuleCat.{u} R) (hF : PureEmbeddings.IsPureInjective F) :
    AlgebraicallyCompact R F := fun I J =>
  compactFor_of_germs R F I J (PureEmbeddings.Germs.algebraically_compact hF)

theorem lower_of_small_systems_and_universality (κ : Cardinal.{u}) (F : ModuleCat.{u} R)
    (hω : Cardinal.aleph0 < κ) (hR : Cardinal.mk R < κ)
    (universal : ∀ M : ModuleCat.{u} R, Cardinal.mk M ≤ κ →
      ∃ f : M →ₗ[R] F, PureEmbeddings.IsPureMap f)
    (solve : ∀ (E V : Type u), Cardinal.mk E < κ → Cardinal.mk V < κ →
      ∀ s : PureEmbeddings.Germs.System R F E V, s.FinitelySoluble →
        ∃ z, ∀ i, s.Holds z i) :
    κ ^ Cardinal.mk (PositiveValue R) ≤ Cardinal.mk F := by
  have size : Cardinal.mk (TestSpace R κ.out) ≤ κ := by
    have h := testSpace_cardinal_le R κ.out (by simpa using hω.le) (by simpa using hR.le)
    simpa using h
  obtain ⟨f, hf⟩ := universal (ModuleCat.of R (TestSpace R κ.out)) size
  have eSize := (positiveValues_cardinal_le R).trans_lt hR
  have vSize : Cardinal.mk (Option (PositiveValue R)) < κ := by
    rw [Cardinal.mk_option]
    exact Cardinal.add_lt_of_lt hω.le eSize ((by simp : (1 : Cardinal) < Cardinal.aleph0).trans hω)
  have result := lower_of_pure_test_space_small R κ.out F f hf
    (compactFor_of_germs R F _ _ (solve _ _ eSize vSize))
  simpa using result

theorem lower_of_pureInjective_universal (κ : Cardinal.{u}) (F : ModuleCat.{u} R)
    (hω : Cardinal.aleph0 ≤ κ) (hR : Cardinal.mk R ≤ κ)
    (hF : PureEmbeddings.IsPureInjective F)
    (universal : ∀ M : ModuleCat.{u} R, Cardinal.mk M ≤ κ →
      ∃ f : M →ₗ[R] F, PureEmbeddings.IsPureMap f) :
    κ ^ Cardinal.mk (PositiveValue R) ≤ Cardinal.mk F :=
  lower_of_universality R κ F hω hR universal (compact_of_pureInjective R F hF)

private abbrev VG := ValuationRing.ValueGroup R (FractionRing R)

private noncomputable def ringValue (x : R) : VG R :=
  ValuationRing.valuation R (FractionRing R) (algebraMap R (FractionRing R) x)

private theorem value_le_iff {x y : R} : ringValue R x ≤ ringValue R y ↔ y ∣ x := by
  change (∃ c : R, c • algebraMap R (FractionRing R) y = algebraMap R (FractionRing R) x) ↔ _
  constructor
  · rintro ⟨c, h⟩
    refine ⟨c, IsFractionRing.injective R (FractionRing R) ?_⟩
    simpa [Algebra.smul_def, mul_comm] using h.symm
  · rintro ⟨c,rfl⟩
    exact ⟨c, by simp [Algebra.smul_def, mul_comm]⟩

private theorem value_one_of_unit {a : R} (ha : IsUnit a) : ringValue R a = 1 := by
  have : ringValue R (1 : R) = 1 := by simp [ringValue]
  rw [← this]
  exact le_antisymm ((value_le_iff R).mpr (one_dvd _))
    ((value_le_iff R).mpr ha.dvd)

private noncomputable def codeValue : Option (Option (PositiveValue R)) → VG R
  | none => 0
  | some none => 1
  | some (some i) => ringValue R (generator R i)

private theorem ringValue_has_code (x : R) :
    ∃ i, codeValue R i = ringValue R x := by
  classical
  by_cases hx : x = 0
  · subst x
    exact ⟨none, by simp [codeValue,ringValue]⟩
  by_cases hu : IsUnit x
  · exact ⟨some none, (value_one_of_unit R hu).symm⟩
  have hm : x ∈ IsLocalRing.maximalIdeal R := by
    by_contra h
    exact hu (IsLocalRing.notMem_maximalIdeal.mp h)
  let i : PositiveValue R := ⟨Ideal.span {x}, x, hm, hx, rfl⟩
  have heq : Ideal.span {generator R i} = Ideal.span {x} := (generator_spec R i).2.2
  have hd := (Ideal.span_singleton_eq_span_singleton.mp heq)
  exact ⟨some (some i), le_antisymm ((value_le_iff R).mpr hd.dvd') ((value_le_iff R).mpr hd.dvd)⟩

private theorem vg_covered :
    Function.Surjective (fun p : Option (Option (PositiveValue R)) × Option (Option (PositiveValue R)) =>
      codeValue R p.1 / codeValue R p.2) := by
  rintro ⟨x⟩
  obtain ⟨a,b,_,eqn⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨i,hi⟩ := ringValue_has_code R a
  obtain ⟨j,hj⟩ := ringValue_has_code R b
  refine ⟨(i,j),?_⟩
  change codeValue R i / codeValue R j = ValuationRing.valuation R (FractionRing R) x
  rw [hi,hj]
  simpa [ringValue, map_div₀] using congrArg (ValuationRing.valuation R (FractionRing R)) eqn

theorem positiveValues_infinite (nf : ¬IsField R) : Infinite (PositiveValue R) := by
  classical
  obtain ⟨a,ha,hu⟩ := Ring.exists_not_isUnit_of_not_isField nf
  have hma : a ∈ IsLocalRing.maximalIdeal R := by
    by_contra h
    exact hu (IsLocalRing.notMem_maximalIdeal.mp h)
  let v (n : ℕ) : PositiveValue R :=
    ⟨Ideal.span {a^(n+1)}, a^(n+1), (IsLocalRing.maximalIdeal R).pow_mem_of_mem hma _ (by omega),
      pow_ne_zero _ ha,rfl⟩
  have step : ∀ n, (v (n+1)).val < (v n).val := by
    intro n
    apply lt_of_le_of_ne
    · exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (by omega))
    · intro hh
      have wrong := Ideal.span_singleton_le_span_singleton.mp hh.ge
      change a^((n+1)+1) ∣ a^(n+1) at wrong
      obtain ⟨c,hc⟩ := wrong
      apply hu
      apply isUnit_of_dvd_one
      refine ⟨c, mul_left_cancel₀ (pow_ne_zero (n+1) ha) ?_⟩
      rw [mul_one, ← mul_assoc, ← pow_succ, ← hc]
  have inj : Function.Injective v := by
    intro n m eqn
    exact (strictAnti_nat_of_succ_lt (f := fun n => (v n).val) step).injective (congrArg Subtype.val eqn)
  exact Infinite.of_injective v inj

theorem positiveValues_cardinal_eq_units (nf : ¬ IsField R) :
    Cardinal.mk (PositiveValue R) = Cardinal.mk (ValuationRing.ValueGroup R (FractionRing R))ˣ := by
  letI := positiveValues_infinite R nf
  apply le_antisymm
  · let f (i : PositiveValue R) : (VG R)ˣ := Units.mk0 (ringValue R (generator R i)) (by
      have h := (generator_spec R i).2.1
      simpa [ringValue] using (IsFractionRing.injective R (FractionRing R)).ne h)
    apply Cardinal.mk_le_of_injective (f := f)
    intro i j e
    have h : ringValue R (generator R i) = ringValue R (generator R j) := congrArg Units.val e
    apply Subtype.ext
    rw [← (generator_spec R i).2.2, ← (generator_spec R j).2.2]
    exact le_antisymm (Ideal.span_singleton_le_span_singleton.mpr ((value_le_iff R).mp h.le))
      (Ideal.span_singleton_le_span_singleton.mpr ((value_le_iff R).mp h.ge))
  · have q := (Cardinal.mk_le_of_injective (f := Units.val (α := VG R)) Units.val_injective).trans
      (Cardinal.mk_le_of_surjective (vg_covered R))
    simpa only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_option,
      Cardinal.add_one_eq (Cardinal.aleph0_le_mk (PositiveValue R)),
      Cardinal.mul_eq_self (Cardinal.aleph0_le_mk (PositiveValue R))] using q

/-- A nonempty finite set of coefficients contains one which divides them all. -/
theorem finite_common_divisor_mem (s : Finset R) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ x ∈ s, a ∣ x := by
  obtain ⟨a,ha,hm⟩ := s.exists_max_image (ringValue R) hs
  exact ⟨a,ha,fun x hx => (value_le_iff R).mp (hm x hx)⟩

open Classical in
private noncomputable def idealCode (I : Ideal R) : Option (PositiveValue R) → R
  | none => if I = ⊤ then 1 else 0
  | some i => if generator R i ∈ I then generator R i else 0

private theorem span_idealCode (I : Ideal R) :
    Ideal.span (Set.range (idealCode R I)) = I := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | none => by_cases h : I = ⊤ <;> simp [idealCode,h]
    | some i => by_cases h : generator R i ∈ I <;> simp [idealCode,h]
  · intro x hx
    by_cases hI : I = ⊤
    · have : (1 : R) ∈ Ideal.span (Set.range (idealCode R I)) :=
        Ideal.subset_span ⟨none, by simp [idealCode,hI]⟩
      exact (Ideal.eq_top_of_isUnit_mem _ this isUnit_one) ▸ Submodule.mem_top
    by_cases hz : x = 0
    · simp [hz]
    have hu : ¬IsUnit x := fun hu => hI (Ideal.eq_top_of_isUnit_mem I hx hu)
    have hm : x ∈ IsLocalRing.maximalIdeal R := by
      by_contra h
      exact hu (IsLocalRing.notMem_maximalIdeal.mp h)
    let i : PositiveValue R := ⟨Ideal.span {x}, x, hm, hz, rfl⟩
    have eqn : Ideal.span {generator R i} = Ideal.span {x} := (generator_spec R i).2.2
    have rel := Ideal.span_singleton_eq_span_singleton.mp eqn
    have hg : generator R i ∈ I := I.mem_of_dvd rel.dvd' hx
    have memg : generator R i ∈ Ideal.span (Set.range (idealCode R I)) :=
      Ideal.subset_span ⟨some i, by simp [idealCode,hg]⟩
    exact (Ideal.span (Set.range (idealCode R I))).mem_of_dvd rel.dvd memg

/-- Every ideal can be generated by at most as many elements as the value group. -/
theorem ideal_generators (nf : ¬IsField R) (I : Ideal R) :
    ∃ s : Set R, Cardinal.mk s ≤ Cardinal.mk (ValuationRing.ValueGroup R (FractionRing R))ˣ ∧
      Ideal.span s = I := by
  letI := positiveValues_infinite R nf
  refine ⟨Set.range (idealCode R I), ?_, span_idealCode R I⟩
  rw [← positiveValues_cardinal_eq_units R nf]
  exact Cardinal.mk_range_le.trans (by simp [Cardinal.mk_option])

/-- An ideal is determined by the nonzero proper principal ideals it contains
together with the information whether it contains 1. -/
theorem ideals_cardinal_le (nf : ¬IsField R) :
    Cardinal.mk (Ideal R) ≤ 2 ^ Cardinal.mk (ValuationRing.ValueGroup R (FractionRing R))ˣ := by
  classical
  let value : Option (PositiveValue R) → R := Option.elim' 1 (generator R)
  let f (I : Ideal R) : Set (Option (PositiveValue R)) := {i | value i ∈ I}
  have inj : Function.Injective f := by
    intro I J h
    have mem (i) : value i ∈ I ↔ value i ∈ J := Set.ext_iff.mp h i
    have equal : idealCode R I = idealCode R J := by
      funext i
      cases i with
      | none =>
        have h1 : (1:R) ∈ I ↔ 1 ∈ J := mem none
        have he : I = ⊤ ↔ J = ⊤ := by simpa only [Ideal.eq_top_iff_one] using h1
        by_cases hI : I = ⊤
        · simp [idealCode,hI,he.mp hI]
        · simp [idealCode,hI,mt he.mpr hI]
      | some i =>
        have he : generator R i ∈ I ↔ generator R i ∈ J := mem (some i)
        by_cases hI : generator R i ∈ I
        · simp [idealCode,hI,he.mp hI]
        · simp [idealCode,hI,mt he.mpr hI]
    rw [← span_idealCode R I, equal, span_idealCode]
  letI := positiveValues_infinite R nf
  rw [← positiveValues_cardinal_eq_units R nf]
  simpa only [Cardinal.mk_set, Cardinal.mk_option, Cardinal.mk_add_one_eq] using Cardinal.mk_le_of_injective inj

/-- The lower bound in the paper's notation, for every module with (Eκ). -/
theorem lower_of_extension (κ : Cardinal.{u}) (F : ModuleCat.{u} R)
    (hω : ℵ₀ < κ) (hR : Cardinal.mk R < κ) (nf : ¬IsField R)
    (hF : HasExtension κ F) :
    κ ^ Cardinal.mk (ValuationRing.ValueGroup R (FractionRing R))ˣ ≤ Cardinal.mk F := by
  rw [← positiveValues_cardinal_eq_units R nf]
  exact lower_of_small_systems_and_universality R κ F hω hR (hF.universal_le hω hR)
    (fun _ _ hE hV s hs => hF.solve_small hω hR s hE hV hs)

end PureEmbeddings.ValuationMathlib
