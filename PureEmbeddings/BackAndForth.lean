import PureEmbeddings.PureHull
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Back-and-forth along an initial ordinal

An increasing chain of partial isomorphisms is represented by their graphs in
the product. The bound at a stage is the maximum of the size of its initial
segment, the size of the ring and `ℵ₀`; this handles singular cardinals.
-/
namespace PureEmbeddings.BackAndForth

open Cardinal Function Set
universe u v

/-- Transfinite recursion with a monotonicity invariant: a move can inspect the
whole earlier chain, and produces an upper bound satisfying the next condition. -/
theorem monotone_recursion {I : Type u} [LinearOrder I] [WellFoundedLT I]
    {P : Type v} [Preorder P] [Nonempty P] (good : I → P → Prop)
    (step : ∀ (i : I) (p : Iio i → P), Monotone p → (∀ j, good j.val (p j)) →
      ∃ q, good i q ∧ ∀ j, p j ≤ q) : ∃ p : I → P, Monotone p ∧ ∀ i, good i (p i) := by
  classical
  let move (i : I) (prev : ∀ j, j < i → P) : P :=
    if h : ∃ q, good i q ∧ ∀ j hj, prev j hj ≤ q then h.choose else Classical.ofNonempty
  let p := wellFounded_lt.fix move
  have inv (i : I) : good i (p i) ∧ ∀ j, j < i → p j ≤ p i := by
    apply wellFounded_lt.induction i
    intro i ih
    have hm : Monotone (fun j : Iio i => p j.val) := by
      intro a b hab
      rcases lt_or_eq_of_le hab with h | h
      · exact (ih b b.property).2 a h
      · exact h ▸ le_rfl
    obtain ⟨q, hq, hprev⟩ := step i _ hm (fun j => (ih j j.property).1)
    have hex : ∃ q, good i q ∧ ∀ j, j < i → p j ≤ q :=
      ⟨q, hq, fun j hj => hprev ⟨j, hj⟩⟩
    have hp : p i = move i (fun j _ => p j) := wellFounded_lt.fix_eq move i
    rw [hp]
    simpa only [move, dif_pos hex] using hex.choose_spec
  refine ⟨p, ?_, fun i => (inv i).1⟩
  intro a b hab
  rcases lt_or_eq_of_le hab with h | rfl
  · exact (inv b).2 a h
  · rfl

variable {R : Type u} [Ring R]

private abbrev fstMap {F G : ModuleCat.{u} R} (S : Submodule R (F × G)) :=
  (LinearMap.fst R F G).comp S.subtype

private abbrev sndMap {F G : ModuleCat.{u} R} (S : Submodule R (F × G)) :=
  (LinearMap.snd R F G).comp S.subtype

/-- Both coordinates of a partial isomorphism are pure maps. -/
structure PureGraph {F G : ModuleCat.{u} R} (S : Submodule R (F × G)) : Prop where
  left : IsPureMap (fstMap S)
  right : IsPureMap (sndMap S)

private theorem pure_factor {A B D : ModuleCat.{u} R} (i : A →ₗ[R] B) (j : B →ₗ[R] D)
    (h : IsPureMap (j.comp i)) : IsPureMap i := by
  refine ⟨fun _ _ he => h.1 (congrArg j he), fun r a hs => ?_⟩
  exact h.2 r a (hs.map j)

/-- The graph of two pure maps is a pure partial isomorphism; it need not be
pure as a submodule of the ambient product. -/
theorem range_prod_pure {A F G : ModuleCat.{u} R} (l : A →ₗ[R] F) (r : A →ₗ[R] G)
    (hl : IsPureMap l) (hr : IsPureMap r) : PureGraph (LinearMap.range (l.prod r)) := by
  let S := LinearMap.range (l.prod r)
  have hi : Injective (l.prod r) := fun _ _ h => hl.1 (congrArg Prod.fst h)
  let e := LinearEquiv.ofInjective (l.prod r) hi
  have ep : IsPureMap e.symm.toLinearMap := isPureMap_equiv (A := ModuleCat.of R S) (B := A) e.symm
  have hl' : fstMap S = l.comp e.symm.toLinearMap := by
    ext x
    exact (congrArg Prod.fst (LinearEquiv.ofInjective_symm_apply (f := l.prod r) x)).symm
  have hr' : sndMap S = r.comp e.symm.toLinearMap := by
    ext x
    exact (congrArg Prod.snd (LinearEquiv.ofInjective_symm_apply (f := l.prod r) x)).symm
  refine ⟨?_, ?_⟩
  · rw [hl']; exact hl.comp (A := ModuleCat.of R S) (B := A) (C := F) ep
  · rw [hr']; exact hr.comp (A := ModuleCat.of R S) (B := A) (C := G) ep

/-- Purity of a map on an increasing union can be checked on the stages. -/
private theorem pure_on_iSup {I : Type u} [LinearOrder I] [Nonempty I]
    {X Y : ModuleCat.{u} R} (l : X →ₗ[R] Y) (S : I → Submodule R X) (hm : Monotone S)
    (h : ∀ j, IsPureMap (l.comp (S j).subtype)) : IsPureMap (l.comp (iSup S).subtype) := by
  classical
  have localise (x : ↥(iSup S : Submodule R X)) : ∃ j, x.val ∈ S j :=
    (Submodule.mem_iSup_of_directed S hm.directed_le).mp x.property
  constructor
  · intro x y hxy
    obtain ⟨a, ha⟩ := localise x
    obtain ⟨b, hb⟩ := localise y
    let m := max a b
    have eq : (⟨x.val, hm (le_max_left a b) ha⟩ : S m) = ⟨y.val, hm (le_max_right a b) hb⟩ :=
      (h m).1 hxy
    exact Subtype.ext (congrArg (fun z : S m => (z : X)) eq)
  · intro m n r a hs
    choose j hj using fun i => localise (a i)
    obtain ⟨t, ht⟩ := (Set.finite_range j).bddAbove
    let d (i : Fin m) : S t := ⟨(a i).val, hm (ht (Set.mem_range_self i)) (hj i)⟩
    have sol : Soluble r ((l.comp (S t).subtype) ∘ d) := hs
    have solved := (h t).2 r d sol
    exact solved.map (Submodule.inclusion (le_iSup S t))

/-- Increasing unions of partial isomorphisms have pure coordinate maps,
including the empty union. -/
theorem pureGraph_iSup {I : Type u} [LinearOrder I] {F G : ModuleCat.{u} R}
    (S : I → Submodule R (F × G)) (hm : Monotone S) (h : ∀ j, PureGraph (S j)) :
    PureGraph (iSup S) := by
  cases isEmpty_or_nonempty I with
  | inl hempty =>
    rw [iSup_of_empty]
    exact ⟨isPureMap_from_subsingleton (A := ModuleCat.of R (⊥ : Submodule R (F × G))) _,
      isPureMap_from_subsingleton (A := ModuleCat.of R (⊥ : Submodule R (F × G))) _⟩
  | inr _ =>
    let X := ModuleCat.of R (F × G)
    exact ⟨pure_on_iSup (X := X) (LinearMap.fst R F G) S hm (fun i => (h i).left),
      pure_on_iSup (X := X) (LinearMap.snd R F G) S hm (fun i => (h i).right)⟩

private theorem size_iSup {I : Type u} [LinearOrder I] {X : Type u} [AddCommGroup X] [Module R X]
    (S : I → Submodule R X) (hm : Monotone S) {δ : Cardinal.{u}} (hd : ℵ₀ ≤ δ)
    (hI : #I ≤ δ) (h : ∀ i, #(S i) ≤ δ) : #↥(iSup S : Submodule R X) ≤ δ := by
  cases isEmpty_or_nonempty I with
  | inl _ =>
    rw [iSup_of_empty, mk_eq_one]
    exact one_le_aleph0.trans hd
  | inr _ =>
    change #((iSup S : Submodule R X) : Set X) ≤ δ
    rw [Submodule.coe_iSup_of_directed S hm.directed_le]
    calc
      _ ≤ Cardinal.sum (fun i => #(S i)) := mk_iUnion_le_sum_mk
      _ ≤ Cardinal.sum (fun _ : I => δ) := sum_le_sum _ _ h
      _ = #I * δ := sum_const' _ _
      _ ≤ δ := (mul_le_max_of_aleph0_le_right hd).trans (max_le hI le_rfl)

/-- Adjoin one specified element on the left, retaining a fixed infinite
cardinality bound. -/
private theorem forth {κ δ : Cardinal.{u}} (hd : ℵ₀ ≤ δ) (hr : #R ≤ δ) (hdk : δ < κ)
    {A F G : ModuleCat.{u} R} (hg : HasExtension κ G) (l : A →ₗ[R] F) (r : A →ₗ[R] G)
    (hl : IsPureMap l) (hp : IsPureMap r) (hA : #A ≤ δ) (x : F) :
    ∃ (B : ModuleCat.{u} R) (j : A →ₗ[R] B) (l' : B →ₗ[R] F) (r' : B →ₗ[R] G),
      #B ≤ δ ∧ IsPureMap l' ∧ IsPureMap r' ∧ l'.comp j = l ∧ r'.comp j = r ∧ x ∈ LinearMap.range l' := by
  classical
  let s : Set F := insert x (Set.range l)
  obtain ⟨H, hsub, hH, hs⟩ := exists_small_pureHull (R := R) s
  let B := ModuleCat.of R H
  let j : A →ₗ[R] B := l.codRestrict H (fun a => hsub (Set.mem_insert_of_mem _ (Set.mem_range_self a)))
  have hj : IsPureMap j := pure_factor (A := A) (B := B) (D := F) j H.subtype hl
  have hB : #B ≤ δ := hs.trans <| max_le hd <| max_le hr <| calc
    #s ≤ #(Set.range l) + 1 := mk_insert_le
    _ ≤ δ + 1 := add_le_add_right (mk_range_le.trans hA) 1
    _ = δ := add_one_eq hd
  obtain ⟨t, ht, htj⟩ := hg A B j r (hB.trans_lt hdk) hj hp
  exact ⟨B, j, H.subtype, t, hB, hH, ht, rfl, htj, ⟨⟨x, hsub (Set.mem_insert _ _)⟩, rfl⟩⟩

/-- One complete back-and-forth step includes a specified element of each
module and contains the previous graph. -/
theorem extend_graph {κ δ : Cardinal.{u}} (hd : ℵ₀ ≤ δ) (hr : #R ≤ δ) (hdk : δ < κ)
    {F G : ModuleCat.{u} R} (hF : HasExtension κ F) (hG : HasExtension κ G)
    (S : Submodule R (F × G)) (hs : PureGraph S) (hsize : #S ≤ δ) (x : F) (y : G) :
    ∃ T : Submodule R (F × G), PureGraph T ∧ #T ≤ δ ∧ S ≤ T ∧
      x ∈ LinearMap.range (fstMap T) ∧ y ∈ LinearMap.range (sndMap T) := by
  classical
  let A := ModuleCat.of R S
  obtain ⟨B, j, l, r, hB, hl, hr', hjl, hjr, b, hb⟩ :=
    forth (A := A) hd hr hdk hG (fstMap S) (sndMap S) hs.left hs.right hsize x
  obtain ⟨D, k, g, f, hD, hg, hf, hkg, hkf, d, hd'⟩ :=
    forth hd hr hdk hF r l hr' hl hB y
  let T := LinearMap.range (f.prod g)
  have ht : #T ≤ δ := (mk_range_le (f := f.prod g)).trans hD
  refine ⟨T, range_prod_pure f g hf hg, ht, ?_, ?_, ?_⟩
  · intro z hz
    let a : A := ⟨z, hz⟩
    refine ⟨k (j a), Prod.ext ?_ ?_⟩
    · exact (congrArg (fun q : B →ₗ[R] F => q (j a)) hkf).trans
        (congrArg (fun q : A →ₗ[R] F => q a) hjl)
    · exact (congrArg (fun q : B →ₗ[R] G => q (j a)) hkg).trans
        (congrArg (fun q : A →ₗ[R] G => q a) hjr)
  · exact ⟨(f.prod g).rangeRestrict (k b), (congrArg (fun q : B →ₗ[R] F => q b) hkf).trans hb⟩
  · exact ⟨(f.prod g).rangeRestrict d, hd'⟩

/-- Two modules of size `κ` with the extension property are isomorphic, and the
isomorphism may be prescribed on any pure partial graph of size below `κ`. -/
theorem equiv_extending_graph {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hr : #R < κ)
    {F G : ModuleCat.{u} R} (hF : HasExtension κ F) (hG : HasExtension κ G)
    (sf : #F = κ) (sg : #G = κ) (S₀ : Submodule R (F × G))
    (h₀ : PureGraph S₀) (hs₀ : #S₀ < κ) :
    ∃ e : F ≃ₗ[R] G, ∀ z : S₀, e z.val.1 = z.val.2 := by
  classical
  let I := κ.ord.toType
  obtain ⟨xf : I ≃ F⟩ := Cardinal.eq.mp ((mk_ord_toType κ).trans sf.symm)
  obtain ⟨xg : I ≃ G⟩ := Cardinal.eq.mp ((mk_ord_toType κ).trans sg.symm)
  let base := max (max ℵ₀ #R) #S₀
  let bound (i : I) := max base #(Iio i)
  have b0 : ℵ₀ ≤ base := (le_max_left _ _).trans (le_max_left _ _)
  have bR : #R ≤ base := (le_max_right _ _).trans (le_max_left _ _)
  have bκ : base < κ := max_lt (max_lt hκ hr) hs₀
  let good (i : I) (S : Submodule R (F × G)) := PureGraph S ∧ #S ≤ bound i ∧ S₀ ≤ S ∧
    xf i ∈ LinearMap.range (fstMap S) ∧ xg i ∈ LinearMap.range (sndMap S)
  have move (i : I) (p : Iio i → Submodule R (F × G)) (hp : Monotone p)
      (hg : ∀ j, good j.val (p j)) : ∃ T, good i T ∧ ∀ j, p j ≤ T := by
    have hd : ℵ₀ ≤ bound i := b0.trans (le_max_left _ _)
    have hR : #R ≤ bound i := bR.trans (le_max_left _ _)
    have hdk : bound i < κ := max_lt bκ (mk_Iio_ord_toType i)
    have prev : ∃ Q : Submodule R (F × G), PureGraph Q ∧ #Q ≤ bound i ∧
        S₀ ≤ Q ∧ ∀ j, p j ≤ Q := by
      cases isEmpty_or_nonempty (Iio i) with
      | inl _ => exact ⟨S₀, h₀, (le_max_right _ _).trans (le_max_left _ _), le_rfl,
          fun j => isEmptyElim j⟩
      | inr hne =>
        obtain ⟨j⟩ := hne
        refine ⟨iSup p, pureGraph_iSup p hp (fun a => (hg a).1),
          size_iSup p hp hd (le_max_right _ _) ?_, ((hg j).2.2.1).trans (le_iSup p j), le_iSup p⟩
        intro a
        exact (hg a).2.1.trans <| max_le_max_left _ <| mk_le_mk_of_subset (Iio_subset_Iio a.property.le)
    obtain ⟨Q, hQ, hsize, hle, hbefore⟩ := prev
    obtain ⟨T, hT, hs, hQT, hx, hy⟩ := extend_graph hd hR hdk hF hG Q hQ hsize (xf i) (xg i)
    exact ⟨T, ⟨hT, hs, hle.trans hQT, hx, hy⟩, fun j => (hbefore j).trans hQT⟩
  obtain ⟨p, hp, hg⟩ := monotone_recursion good move
  let T := iSup p
  have hT : PureGraph T := pureGraph_iSup p hp (fun i => (hg i).1)
  have lf : Surjective (fstMap T) := by
    intro x
    obtain ⟨i, rfl⟩ := xf.surjective x
    obtain ⟨a, ha⟩ := (hg i).2.2.2.1
    exact ⟨Submodule.inclusion (le_iSup p i) a, ha⟩
  have rg : Surjective (sndMap T) := by
    intro x
    obtain ⟨i, rfl⟩ := xg.surjective x
    obtain ⟨a, ha⟩ := (hg i).2.2.2.2
    exact ⟨Submodule.inclusion (le_iSup p i) a, ha⟩
  let f := LinearEquiv.ofBijective (fstMap T) ⟨hT.left.1, lf⟩
  let g := LinearEquiv.ofBijective (sndMap T) ⟨hT.right.1, rg⟩
  refine ⟨f.symm.trans g, fun z => ?_⟩
  let i := xf.symm 0
  let t := Submodule.inclusion (((hg i).2.2.1).trans (le_iSup p i)) z
  change g (f.symm (f t)) = g t
  rw [f.symm_apply_apply]

/-- An isomorphism between the images of two pure embeddings of a small module
extends to an isomorphism of the ambient modules. -/
theorem equiv_over {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hr : #R < κ)
    {A F G : ModuleCat.{u} R} (hF : HasExtension κ F) (hG : HasExtension κ G)
    (sf : #F = κ) (sg : #G = κ) (hA : #A < κ) (l : A →ₗ[R] F) (r : A →ₗ[R] G)
    (hl : IsPureMap l) (hr' : IsPureMap r) : ∃ e : F ≃ₗ[R] G, e.toLinearMap.comp l = r := by
  obtain ⟨e, he⟩ := equiv_extending_graph hκ hr hF hG sf sg _ (range_prod_pure l r hl hr')
    ((mk_range_le (f := l.prod r)).trans_lt hA)
  exact ⟨e, LinearMap.ext fun a => he ((l.prod r).rangeRestrict a)⟩

/-- Uniqueness at `κ` for every ring of size less than `κ`. -/
theorem uniqueAt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hr : #R < κ) : UniqueAt (R := R) κ κ := by
  intro F G hF hG sf sg
  let S : Submodule R (F × G) := ⊥
  have hS : PureGraph S := ⟨isPureMap_from_subsingleton (A := ModuleCat.of R S) _,
                             isPureMap_from_subsingleton (A := ModuleCat.of R S) _⟩
  obtain ⟨e, _⟩ := equiv_extending_graph hκ hr hF hG sf sg S hS
    ((mk_eq_one (α := S)).trans_lt (one_lt_aleph0.trans hκ))
  exact ⟨e⟩

end PureEmbeddings.BackAndForth
