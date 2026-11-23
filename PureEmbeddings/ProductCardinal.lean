import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# The size of a product with small supports

An infinite index set of size `κ` and non-zero pointed factors of size at most
`κ` give exactly `κ ^< κ` functions whose support has size less than `κ`.
The argument works at singular cardinals as well.
-/

namespace PureEmbeddings.ProductCardinal

open Set Cardinal Function

universe u

/-- Subsets whose cardinality is strictly below a specified bound. -/
abbrev SmallSubsets (X : Type u) (κ : Cardinal.{u}) := {s : Set X // #s < κ}

/-- Count the subsets by grouping them according to the size of the support. -/
theorem smallSubsets_le (X : Type u) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hX : #X ≤ κ) :
    #(SmallSubsets X κ) ≤ κ ^< κ := by
  classical
  let e := Ordinal.enumIsoToType κ.ord
  let bound (i : κ.ord.toType) := (e.symm i).val.card
  let B (i : κ.ord.toType) := {s : Set X // #s ≤ bound i}
  let tag (s : SmallSubsets X κ) : Set.Iio κ.ord := ⟨(#s.val).ord, ord_lt_ord.mpr s.property⟩
  let encode (s : SmallSubsets X κ) : Σ i, B i :=
    ⟨e (tag s), ⟨s.val, by simp [bound, tag]⟩⟩
  have hencode : Injective encode := by
    intro s t h
    exact Subtype.ext (congrArg (fun z : Σ i, B i => z.2.val) h)
  have hbase : κ ≤ κ ^< κ := by
    simpa only [power_one] using le_powerlt κ (one_lt_aleph0.trans_le hκ)
  calc
    #(SmallSubsets X κ) ≤ #(Σ i, B i) := mk_le_of_injective hencode
    _ = sum (fun i => #(B i)) := mk_sigma B
    _ ≤ sum (fun _ : κ.ord.toType => κ ^< κ) := sum_le_sum _ _ fun i =>
      (mk_bounded_set_le X (bound i)).trans <|
        (power_le_power_right (max_le hX hκ)).trans <| le_powerlt κ (lt_ord.mp (e.symm i).property)
    _ = κ * (κ ^< κ) := by rw [sum_const', mk_ord_toType]
    _ ≤ κ ^< κ := (mul_le_max_of_aleph0_le_left hκ).trans (max_le hbase le_rfl)

/-- Encode a function by its graph, using distinct coordinates for ordered pairs. -/
theorem powerlt_le_smallSubsets (I : Type u) (hI : ℵ₀ ≤ #I) :
    #I ^< #I ≤ #(SmallSubsets I (#I)) := by
  classical
  apply powerlt_le.mpr
  intro μ hμ
  induction μ using Cardinal.inductionOn with | _ A =>
    have hprod : #(A × I) ≤ #I := by
      simpa only [mk_prod, lift_id] using
        (mul_le_max_of_aleph0_le_right (a := #A) hI).trans (max_le hμ.le le_rfl)
    obtain ⟨pair⟩ := hprod
    let graph (f : A → I) : SmallSubsets I (#I) :=
      ⟨Set.range (fun a => pair (a, f a)), mk_range_le.trans_lt hμ⟩
    have hg : Injective graph := by
      intro f g h
      funext a
      have he := congrArg Subtype.val h
      have hmem : pair (a, f a) ∈ (graph g).val := by
        rw [← he]
        exact ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem
      have hp : (b, g b) = (a, f a) := pair.injective hb
      have hba : b = a := congrArg Prod.fst hp
      subst b
      exact (congrArg Prod.snd hp).symm
    rw [power_def]
    exact mk_le_of_injective hg

/-- Functions in the dependent product whose non-zero coordinates form a small set. -/
abbrev SmallProduct {I : Type u} (C : I → Type u) [∀ i, Zero (C i)] (κ : Cardinal.{u}) :=
  {f : (i : I) → C i // #({i : I | f i ≠ 0} : Set I) < κ}

/-- Evaluating a chosen non-zero element on a small set embeds the small subsets. -/
theorem smallSubsets_le_product {I : Type u} (C : I → Type u) [∀ i, Zero (C i)]
    [∀ i, Nontrivial (C i)] (κ : Cardinal.{u}) :
    #(SmallSubsets I κ) ≤ #(SmallProduct C κ) := by
  classical
  choose v hv using fun i => exists_ne (0 : C i)
  let mark (s : Set I) (i : I) := if i ∈ s then v i else 0
  have support_mark (s : Set I) : {i : I | mark s i ≠ 0} = s := by
    ext i
    by_cases hi : i ∈ s <;> simp [mark, hi, hv]
  let code (s : SmallSubsets I κ) : SmallProduct C κ :=
    ⟨mark s.val, by rw [support_mark]; exact s.property⟩
  apply mk_le_of_injective (f := code)
  intro s t h
  apply Subtype.ext
  rw [← support_mark s.val, ← support_mark t.val]
  exact congrArg (fun f : (i : I) → C i => {i : I | f i ≠ 0}) (congrArg Subtype.val h)

/-- The graph over the non-zero coordinates encodes each element of the product. -/
theorem product_le_smallSubsets {I : Type u} (C : I → Type u) [∀ i, Zero (C i)]
    (κ : Cardinal.{u}) : #(SmallProduct C κ) ≤ #(SmallSubsets (Σ i, C i) κ) := by
  classical
  let graph (f : (i : I) → C i) : Set (Σ i, C i) :=
    {p | f p.1 ≠ 0 ∧ p.2 = f p.1}
  have hg (f : (i : I) → C i) : #(graph f) ≤ #({i : I | f i ≠ 0} : Set I) := by
    apply mk_le_of_injective (f := fun p : graph f =>
      (⟨p.val.1, p.property.1⟩ : {i : I | f i ≠ 0}))
    rintro ⟨⟨i, x⟩, hi⟩ ⟨⟨j, y⟩, hj⟩ h
    have hIJ : i = j := congrArg Subtype.val h
    subst j
    exact Subtype.ext (congrArg (Sigma.mk i) (hi.2.trans hj.2.symm))
  let code (f : SmallProduct C κ) : SmallSubsets (Σ i, C i) κ :=
    ⟨graph f.val, (hg f.val).trans_lt f.property⟩
  apply mk_le_of_injective (f := code)
  intro f g h
  have he : graph f.val = graph g.val := congrArg Subtype.val h
  have side (x y : (i : I) → C i) (hxy : graph x = graph y) (i : I) (hi : x i ≠ 0) :
      x i = y i := by
    have hm : Sigma.mk i (x i) ∈ graph x := ⟨hi, rfl⟩
    rw [hxy] at hm
    exact hm.2
  apply Subtype.ext
  funext i
  by_cases hf : f.val i = 0
  · by_cases hg : g.val i = 0
    · exact hf.trans hg.symm
    · exact (side _ _ he.symm i hg).symm
  · exact side _ _ he i hf

/-- The size formula for an arbitrary infinite index set and non-trivial factors. -/
theorem mk_smallProduct {I : Type u} (C : I → Type u) [∀ i, Zero (C i)]
    [∀ i, Nontrivial (C i)] (hI : ℵ₀ ≤ #I) (hC : ∀ i, #(C i) ≤ #I) :
    #(SmallProduct C (#I)) = #I ^< #I := by
  have hSigma : #(Σ i, C i) ≤ #I := by
    rw [mk_sigma]
    exact (sum_le_sum _ (fun _ : I => #I) hC).trans_eq (by rw [sum_const', mul_eq_self hI])
  exact le_antisymm ((product_le_smallSubsets C _).trans (smallSubsets_le _ hI hSigma))
    ((powerlt_le_smallSubsets I hI).trans (smallSubsets_le_product C _))

/-- In particular the formula applies to the countable factors in Kostana's group. -/
theorem mk_smallProduct_countable {I : Type u} [Infinite I] (C : I → Type u)
    [∀ i, Zero (C i)] [∀ i, Nontrivial (C i)] [∀ i, Countable (C i)] :
    #(SmallProduct C (#I)) = #I ^< #I :=
  mk_smallProduct C (aleph0_le_mk I) fun _ => mk_le_aleph0.trans (aleph0_le_mk I)

end PureEmbeddings.ProductCardinal
