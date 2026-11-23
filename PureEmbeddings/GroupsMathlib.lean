import PureEmbeddings.ModuleTheory
import PureEmbeddings.ProductCardinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable

/-!
# Products with support of cardinality less than κ

All cardinalities and cofinalities in this file are Mathlib cardinals and ordinals.
The groups need not have the same coefficient group at every coordinate.
-/

open Set Cardinal Ordinal
open scoped Cardinal

universe u

namespace PureEmbeddings.Groups

variable {I : Type u}

def support {C : I → Type} [∀ i, Zero (C i)] (x : ∀ i, C i) : Set I :=
  {i | x i ≠ 0}

variable (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (C : I → Type) [∀ i, AddCommGroup (C i)]

/-- The additive subgroup of the full product with support of size less than κ. -/
def supportedProduct : AddSubgroup (∀ i, C i) where
  carrier := {x | #(support x) < κ}
  zero_mem' := by simpa [support] using (aleph0_pos.trans_le hκ)
  add_mem' := by
    intro x y hx hy
    have hin : support (x + y) ⊆ support x ∪ support y := by
      intro i hi
      by_contra hn
      have hx0 : x i = 0 := by simpa [support] using (fun h => hn (Or.inl h))
      have hy0 : y i = 0 := by simpa [support] using (fun h => hn (Or.inr h))
      exact hi (by simp [hx0,hy0])
    exact (mk_le_mk_of_subset hin).trans_lt
      ((mk_union_le _ _).trans_lt (add_lt_of_lt hκ hx hy))
  neg_mem' := by
    intro x hx
    simpa [support] using hx

/-- Restriction to a set of coordinates is an additive map. -/
def restrictBlock (J : Set I) :
    supportedProduct κ hκ C →+ ((j : J) → C j.val) where
  toFun x j := x.val j.val
  map_zero' := rfl
  map_add' _ _ := rfl

private noncomputable def putBlock (J : Set I) (y : (j : J) → C j.val)
    (i : I) : C i := by
  classical
  exact if h : i ∈ J then y ⟨i,h⟩ else 0

/-- Extension by zero embeds any full product on fewer than κ coordinates. -/
noncomputable def extendBlock (J : Set I) (hJ : #J < κ) :
    ((j : J) → C j.val) →+ supportedProduct κ hκ C where
  toFun y := ⟨putBlock C J y, (mk_le_mk_of_subset (show support (putBlock C J y) ⊆ J from by
    intro i hi
    by_contra hn
    exact hi (by simp [putBlock, hn]))).trans_lt hJ⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ J <;> simp [putBlock, hi]
  map_add' x y := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ J <;> simp [putBlock, hi]

theorem extendBlock_off (J : Set I) (hJ : #J < κ) (y : (j : J) → C j.val)
    {i : I} (hi : i ∉ J) : (extendBlock κ hκ C J hJ y).val i = 0 := by
  change putBlock C J y i = 0
  simp [putBlock, hi]

theorem full_coordinate_product_splits (J : Set I) (hJ : #J < κ) :
    Function.LeftInverse (restrictBlock κ hκ C J) (extendBlock κ hκ C J hJ) := by
  intro y
  funext j
  simp [restrictBlock, extendBlock, putBlock, j.property]

/-- This is the cardinal step used for countable lists of equations, including at singular κ. -/
theorem common_support_below_cofinality (T : Type u) (hT : #T < κ.ord.cof)
    (x : T → supportedProduct κ hκ C) :
    ∃ J : Set I, #J < κ ∧ ∀ t, support (x t).val ⊆ J := by
  refine ⟨⋃ t, support (x t).val, ?_, fun t => Set.subset_iUnion (fun t => support (x t).val) t⟩
  exact (mk_iUnion_le _).trans_lt (mul_lt_of_lt hκ (hT.trans_le (Ordinal.cof_ord_le κ))
    (Ordinal.iSup_lt hT fun t => (x t).property))

/-- Every small subset is contained in a full product on fewer than κ coordinates. -/
def LocalCoordinateProducts : Prop :=
  ∀ s : Set (supportedProduct κ hκ C), #s < κ →
    ∃ J : Set I, #J < κ ∧ ∀ x ∈ s, support x.val ⊆ J

theorem local_of_regular (hr : κ.IsRegular) : LocalCoordinateProducts κ hκ C := by
  intro s hs
  obtain ⟨J,hJ,hsJ⟩ := common_support_below_cofinality κ hκ C s
    (by simpa [hr.cof_eq] using hs) Subtype.val
  exact ⟨J, hJ, fun x hx => hsJ ⟨x,hx⟩⟩

/-- Singular-cardinal converse. The embedding marks κ coordinates having a nonzero value. -/
theorem regular_of_local (e : κ.ord.toType ↪ I) (v : ∀ i, C i)
    (hv : ∀ a, v (e a) ≠ 0) (hlocal : LocalCoordinateProducts κ hκ C) : κ.IsRegular := by
  classical
  refine ⟨hκ, ?_⟩
  by_contra! hc
  let W := κ.ord.toType
  obtain ⟨s, cofinal, size⟩ := Ordinal.cof_eq' (fun a b : W => a < b)
    (by simpa [W] using Cardinal.isSuccLimit_ord hκ)
  have hs : #s < κ := by simpa [W] using (size.trans_lt (by simpa [W] using hc))
  let D (b : s) : Set I := e '' Set.Iio b.val
  have small (b : s) : #(D b) < κ :=
    Cardinal.mk_image_le.trans_lt (Cardinal.mk_Iio_ord_toType b.val)
  let f (b : s) : supportedProduct κ hκ C :=
    extendBlock κ hκ C (D b) (small b) (fun j => v j.val)
  obtain ⟨J,hJ,hcover⟩ := hlocal (Set.range f) (Cardinal.mk_range_le.trans_lt hs)
  have covers : Set.range e ⊆ J := by
    rintro i ⟨a,rfl⟩
    obtain ⟨b,hb,hab⟩ := cofinal a
    let z : s := ⟨b,hb⟩
    have ha : e a ∈ D z := ⟨a,hab,rfl⟩
    apply hcover (f z) ⟨z,rfl⟩
    change putBlock C (D z) (fun j => v j.val) (e a) ≠ 0
    simpa [putBlock, ha] using hv a
  have bad := (Cardinal.mk_le_mk_of_subset covers).trans_lt hJ
  simp [Cardinal.mk_range_eq e e.injective] at bad

theorem local_iff_regular (e : κ.ord.toType ↪ I) (v : ∀ i, C i)
    (hv : ∀ a, v (e a) ≠ 0) :
    LocalCoordinateProducts κ hκ C ↔ κ.IsRegular :=
  ⟨regular_of_local κ hκ C e v hv, local_of_regular κ hκ C⟩

/-- Factor indexed by a prime p, and by either n (cyclic order p^{n+1}) or infinity (Prüfer). -/
abbrev FactorIndex := {p : ℕ // p.Prime} × Option ℕ

abbrev RatModInt := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- The Prüfer p-group is the p-primary subgroup of the additive quotient ℚ/ℤ. -/
def factor (t : FactorIndex) : Type := by
  letI : Fact t.1.val.Prime := ⟨t.1.property⟩
  exact match t.2 with
    | none => ↥(AddCommGroup.primaryComponent RatModInt t.1.val)
    | some n => ZMod (t.1.val ^ (n+1))

noncomputable instance (t : FactorIndex) : AddCommGroup (factor t) := by
  obtain ⟨⟨p,hp⟩,t⟩ := t
  letI : Fact p.Prime := ⟨hp⟩
  cases t <;> dsimp [factor] <;> infer_instance

/-- Kostana's group on κ copies of each nonzero co-cyclic type. -/
noncomputable abbrev kostanaGroup (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) :=
  supportedProduct κ hκ (fun i : κ.ord.toType × FactorIndex => factor i.2)

private abbrev twoTag : FactorIndex := (⟨2, Nat.prime_two⟩, some 0)

private def twoCoordinates (κ : Cardinal.{u}) : κ.ord.toType ↪ κ.ord.toType × FactorIndex :=
  ⟨fun a => (a, twoTag), fun _ _ h => congrArg Prod.fst h⟩

private noncomputable def marker (t : FactorIndex) : factor t := by
  obtain ⟨⟨p,hp⟩,t⟩ := t
  cases t with
  | none => exact 0
  | some n => exact (1 : ZMod (p^(n+1)))

private theorem marker_two : marker twoTag ≠ 0 := by
  change (1 : ZMod 2) ≠ 0
  exact one_ne_zero

/-- The coordinate-summand assertion of Theorem C for the actual supported product. -/
theorem kostana_local_iff_regular :
    LocalCoordinateProducts κ hκ (fun i : κ.ord.toType × FactorIndex => factor i.2) ↔
      κ.IsRegular :=
  local_iff_regular κ hκ _ (twoCoordinates κ) (fun i => marker i.2) (fun _ => marker_two)

instance factor_countable (t : FactorIndex) : Countable (factor t) := by
  obtain ⟨⟨p,hp⟩,t⟩ := t
  letI : Fact p.Prime := ⟨hp⟩
  cases t with
  | none =>
    letI : Countable RatModInt := Quotient.countable
    change Countable ↥(AddCommGroup.primaryComponent RatModInt p)
    infer_instance
  | some n =>
    change Countable (ZMod (p^(n+1)))
    haveI : NeZero (p^(n+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    infer_instance

include hκ in
private theorem index_size : #(κ.ord.toType × FactorIndex) = κ := by
  refine le_antisymm ?_ ?_
  · rw [Cardinal.mk_prod, Cardinal.mk_ord_toType, Cardinal.lift_uzero]
    apply (mul_le_max_of_aleph0_le_left hκ).trans
    apply max_le le_rfl
    exact ((Cardinal.lift_le.mpr (Cardinal.mk_le_aleph0 (α := FactorIndex))).trans_eq
      Cardinal.lift_aleph0).trans hκ
  · simpa using (Cardinal.mk_le_of_injective (twoCoordinates κ).injective)

/-- Upper bound by the sets that occur as graphs on the non-zero coordinates. -/
theorem supported_cardinal_le [∀ i, Countable (C i)] (hI : #I ≤ κ) :
    #(supportedProduct κ hκ C) ≤ κ ^< κ := by
  let L (i : I) := ULift.{u} (C i)
  let code (x : supportedProduct κ hκ C) : ProductCardinal.SmallProduct L κ :=
    ⟨fun i => ULift.up (x.val i), by
      change #({i : I | (ULift.up (x.val i) : L i) ≠ 0} : Set I) < κ
      have same : {i : I | (ULift.up (x.val i) : L i) ≠ 0} = support x.val := by
        ext i
        change ¬ _ = _ ↔ ¬ _ = _
        exact not_congr ULift.up_inj
      rw [same]; exact x.property⟩
  have hinj : Function.Injective code := by
    intro a b h
    exact Subtype.ext (funext fun i => congrArg (fun z : ProductCardinal.SmallProduct L κ =>
      (z.val i).down) h)
  have hSigma : #(Σ i, L i) ≤ κ := by
    rw [Cardinal.mk_sigma]
    have hL (i : I) : #(L i) ≤ κ := (Cardinal.mk_le_aleph0).trans hκ
    exact (Cardinal.sum_le_sum _ (fun _ : I => κ) hL).trans (by
      rw [Cardinal.sum_const']; exact (mul_le_max_of_aleph0_le_right hκ).trans (max_le hI le_rfl))
  exact (Cardinal.mk_le_of_injective hinj).trans <|
    (ProductCardinal.product_le_smallSubsets L κ).trans <| ProductCardinal.smallSubsets_le _ hκ hSigma

/-- For the lower bound it is enough to have κ non-zero coordinates. -/
theorem cardinal_le_supported (e : κ.ord.toType ↪ I) (v : ∀ i, C i)
    (hv : ∀ a, v (e a) ≠ 0) : κ ^< κ ≤ #(supportedProduct κ hκ C) := by
  classical
  let P := ProductCardinal.SmallSubsets κ.ord.toType κ
  let mark (s : P) := putBlock C (e '' s.val) (fun j => v j.val)
  have hmark (s : P) : support (mark s) = e '' s.val := by
    ext i
    by_cases hi : i ∈ e '' s.val
    · obtain ⟨a,ha,rfl⟩ := hi
      have hm : e a ∈ e '' s.val := ⟨a,ha,rfl⟩
      exact ⟨fun _ => hm, fun _ => by simpa [mark, support, putBlock, hm, ha] using hv a⟩
    · exact ⟨fun hk => False.elim (hk (by simp [mark, putBlock, hi])), fun h => False.elim (hi h)⟩
  let code (s : P) : supportedProduct κ hκ C :=
    ⟨mark s, by change #(support (mark s)) < κ; rw [hmark]; exact mk_image_le.trans_lt s.property⟩
  have hinj : Function.Injective code := by
    intro s t h
    apply Subtype.ext
    apply Set.image_injective.mpr e.injective
    rw [← hmark, ← hmark]
    exact congrArg (fun x : supportedProduct κ hκ C => support x.val) h
  have h := ProductCardinal.powerlt_le_smallSubsets κ.ord.toType (by simpa using hκ)
  exact (by simpa using h : κ ^< κ ≤ #P) |>.trans (Cardinal.mk_le_of_injective hinj)

/-- The size assertion of Theorem C, on the same additive group as its other clauses. -/
theorem kostana_cardinal : #(kostanaGroup κ hκ) = κ ^< κ :=
  le_antisymm (supported_cardinal_le κ hκ _ (index_size κ hκ).le)
    (cardinal_le_supported κ hκ _ (twoCoordinates κ) (fun i => marker i.2) (fun _ => marker_two))

/-- The paper's Theorem C, stated with its group and interval of cardinals.
The proof is assembled in the TheoremC module. -/
def TheoremC (κ : Cardinal.{u}) : Prop :=
  ∀ hκ : ℵ₀ < κ,
    let G := fun i : κ.ord.toType × FactorIndex => factor i.2
    let P := kostanaGroup κ hκ.le
    #P = κ ^< κ ∧
    (HasExtension (R := ℤ) κ (ModuleCat.of ℤ P) ↔ ℵ₀ < κ.ord.cof) ∧
    (LocalCoordinateProducts κ hκ.le G ↔ κ.IsRegular) ∧
    (∀ (J : Set (κ.ord.toType × FactorIndex)) (hJ : #J < κ),
      Function.LeftInverse (restrictBlock κ hκ.le G J) (extendBlock κ hκ.le G J hJ) ∧
      IsPureInjective (ModuleCat.of ℤ ((j : J) → G j.val))) ∧
    (κ < κ ^ ℵ₀ → ∃ T : Type u, Nonempty (T ≃ Set.Icc κ (κ ^ ℵ₀)) ∧
      ManyAtMinimum (R := ℤ) κ (κ ^ ℵ₀) (#T ^ ℵ₀))

private theorem cofinal_sequence (hc : κ.ord.cof = ℵ₀) (hk : ℵ₀ ≤ κ) :
    ∃ b : ℕ → κ.ord.toType, ∀ a, ∃ n, a < b n := by
  classical
  let W := κ.ord.toType
  obtain ⟨S,cofinal,size⟩ := Ordinal.cof_eq' (fun a b : W => a < b)
    (by simpa [W] using Cardinal.isSuccLimit_ord hk)
  have hs : #S = ℵ₀ := by simpa [W, hc] using size
  haveI : Countable S := Cardinal.mk_le_aleph0_iff.mp hs.le
  haveI : Nonempty S := Cardinal.mk_ne_zero_iff.mp (hs ▸ aleph0_ne_zero)
  obtain ⟨enum,onto⟩ := exists_surjective_nat S
  refine ⟨fun n => (enum n).val, fun a => ?_⟩
  obtain ⟨b,hb,hab⟩ := cofinal a
  obtain ⟨n,hn⟩ := onto ⟨b,hb⟩
  exact ⟨n, by simpa [hn] using hab⟩

private abbrev binaryTag (n : ℕ) : FactorIndex := (⟨2,Nat.prime_two⟩, some n)

private noncomputable def entry (n : ℕ) (a : κ.ord.toType) :
    kostanaGroup κ hκ →+ ZMod (2^(n+1)) where
  toFun x := x.val (a, binaryTag n)
  map_zero' := rfl
  map_add' _ _ := rfl

private def binaryBlock (b : κ.ord.toType) (n : ℕ) : Set (κ.ord.toType × FactorIndex) :=
  (fun a => (a, binaryTag n)) '' Set.Iio b

private noncomputable def blockUnit (b : κ.ord.toType) (n : ℕ) : kostanaGroup κ hκ :=
  extendBlock κ hκ _ (binaryBlock κ b n)
    (Cardinal.mk_image_le.trans_lt (Cardinal.mk_Iio_ord_toType b)) (fun j => marker j.val.2)

private theorem entry_unit (a b : κ.ord.toType) (n : ℕ) (hab : a < b) :
    entry κ hκ n a (blockUnit κ hκ b n) = 1 := by
  have h : (a, binaryTag n) ∈ binaryBlock κ b n := ⟨a,hab,rfl⟩
  change putBlock (fun i : κ.ord.toType × FactorIndex => factor i.2) (binaryBlock κ b n)
    (fun j => marker j.val.2) (a,binaryTag n) = _
  simp [putBlock, h, marker, binaryTag]

private theorem entry_other (a b : κ.ord.toType) (m n : ℕ) (hmn : m ≠ n) :
    entry κ hκ n a (blockUnit κ hκ b m) = 0 := by
  have h : (a, binaryTag n) ∉ binaryBlock κ b m := by
    rintro ⟨c,hc,he⟩
    exact hmn (Option.some.inj (congrArg (fun i : κ.ord.toType × FactorIndex => i.2.2) he))
  change putBlock (fun i : κ.ord.toType × FactorIndex => factor i.2) (binaryBlock κ b m)
    (fun j => marker j.val.2) (a,binaryTag n) = _
  simp [putBlock, h]

/-- Partial sums of `2^n u_n` solve every earlier congruence in any additive group. -/
private theorem partial_congruences {H : Type u} [AddCommGroup H] (u : ℕ → H) (m N : ℕ)
    (hm : m ≤ N) :
    ∃ y : H, (∑ k ∈ Finset.range N, (2^k : ℕ) • u k) =
      (∑ k ∈ Finset.range m, (2^k : ℕ) • u k) + (2^m : ℕ) • y := by
  induction N, hm using Nat.le_induction with
  | base => exact ⟨0, by simp⟩
  | succ k hk ih =>
    obtain ⟨y,hy⟩ := ih
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hk
    refine ⟨y + (2^d : ℕ) • u k, ?_⟩
    rw [Finset.sum_range_succ, hy, smul_add, ← mul_smul, ← pow_add, ← hd, add_assoc]

/-- At countable cofinality the actual group Pκ has countably many congruences,
all finitely solvable and without a simultaneous solution. -/
theorem kostana_unsolvable_congruences (hc : κ.ord.cof = ℵ₀) :
    ∃ s : ℕ → kostanaGroup κ hκ,
      (∀ F : Finset ℕ, ∃ x, ∀ m ∈ F, ∃ y, x = s m + (2^m : ℕ) • y) ∧
      ¬ ∃ x, ∀ m, ∃ y, x = s m + (2^m : ℕ) • y := by
  classical
  obtain ⟨b,hb⟩ := cofinal_sequence κ hc hκ
  let u (n : ℕ) := blockUnit κ hκ (b n) n
  let s (m : ℕ) := ∑ k ∈ Finset.range m, (2^k : ℕ) • u k
  refine ⟨s, fun F => ⟨s (F.sup id), fun m hm => partial_congruences u m _ (Finset.le_sup (f := id) hm)⟩, ?_⟩
  rintro ⟨x,hx⟩
  have forced (a : κ.ord.toType) (n : ℕ) (ha : a < b n) : entry κ hκ n a x ≠ 0 := by
    obtain ⟨y,hy⟩ := hx (n+1)
    have he : entry κ hκ n a (s (n+1)) = (2^n : ℕ) • (1 : ZMod (2^(n+1))) := by
      simp only [s, map_sum, map_nsmul]
      rw [Finset.sum_eq_single n]
      · rw [entry_unit κ hκ a (b n) n ha]
      · intro k hk hkn
        rw [entry_other κ hκ a (b k) k n hkn, smul_zero]
      · simp
    rw [hy, map_add, map_nsmul, he, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_self,
      zero_mul, add_zero, mul_one]
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by positivity) (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  choose level chosen using hb
  let inSupport (a : κ.ord.toType) : support x.val :=
    ⟨(a,binaryTag (level a)), forced a (level a) (chosen a)⟩
  have hi : Function.Injective inSupport := fun _ _ h => congrArg (fun z => z.val.1) h
  have mkbound := (Cardinal.mk_le_of_injective hi).trans_lt (show #(support x.val) < κ from x.property)
  simp at mkbound

end PureEmbeddings.Groups
