import PureEmbeddings.MatrixFiber
import PureEmbeddings.AlgebraicCompactness
import Mathlib.Data.Finset.Sum

/-! # The descending-chain obstruction to pure-semisimplicity

A maximal finitely consistent assignment solves every row when all finitely
intersecting families of matrix cosets have a point. A family without a point
then supplies a strictly descending sequence of finite intersections.
-/
namespace PureEmbeddings.MatrixDCC
open Set Function Cardinal
open scoped BigOperators
universe u
variable {R M E V : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- The one-variable matrix coset intersection property. -/
def MeetsCosets (R M : Type u) [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ {J : Type u} (codes : J → Code R) (c : J → M),
    (∀ t : Finset J, ∃ x, ∀ j ∈ t, x - c j ∈ group (codes j) M) →
      ∃ x, ∀ j, x - c j ∈ group (codes j) M

private def pinned (s : Germs.System R M E V) : Germs.System R M (E ⊕ (V × M)) V where
  width := Sum.elim s.width (fun _ => 1)
  coeff := fun e => Sum.rec (motive := fun a => Fin (Sum.elim s.width (fun _ : V × M => 1) a) → R)
    s.coeff (fun _ _ => 1) e
  var := fun e => Sum.rec (motive := fun a => Fin (Sum.elim s.width (fun _ : V × M => 1) a) → V)
    s.var (fun p _ => p.1) e
  rhs := Sum.elim s.rhs Prod.snd

private theorem holds_pin (s : Germs.System R M E V) (y : V → M) (p : V × M) :
    (pinned s).Holds y (.inr p) ↔ y p.1 = p.2 := by
  change (∑ _ : Fin 1, (1 : R) • y p.1) = p.2 ↔ _
  simp

private def consistent (s : Germs.System R M E V) (p : Set (V × M)) : Prop :=
  ∀ t : Finset (E ⊕ (V × M)), (t.toRight : Set (V × M)) ⊆ p →
    ∃ y, ∀ e ∈ t, (pinned s).Holds y e

private theorem maximal_consistent (s : Germs.System R M E V) (hs : s.FinitelySoluble) :
    ∃ p, Maximal (consistent s) p := by
  classical
  have h0 : consistent s ∅ := by
    intro t h
    obtain ⟨y, hy⟩ := hs t.toLeft
    refine ⟨y, fun e he => ?_⟩
    cases e with
    | inl e => exact hy e (Finset.mem_toLeft.mpr he)
    | inr e => exact False.elim (h (Finset.mem_toRight.mpr he))
  let S := {p | consistent s p}
  have bound (c : Set (Set (V×M))) (hc : c ⊆ S) (chain : IsChain (· ⊆ ·) c) (hn : c.Nonempty) :
      ∃ q ∈ S, ∀ a ∈ c, a ⊆ q := by
    refine ⟨⋃₀ c, ?_, fun a ha => Set.subset_sUnion_of_mem ha⟩
    intro t ht
    obtain ⟨a, ha, h⟩ := chain.directedOn.exists_mem_subset_of_finite_of_subset_sUnion hn
      t.toRight.finite_toSet ht
    exact hc ha t h
  obtain ⟨p, _, hp⟩ := zorn_subset_nonempty S bound ∅ h0
  exact ⟨p, hp⟩

/-- The one-variable matrix coset intersection property solves arbitrary
row-finite systems, including systems with uncountably many variables. -/
theorem solve_of_cosets (meet : MeetsCosets R M) (s : Germs.System R M E V)
    (hs : s.FinitelySoluble) : ∃ y : V → M, ∀ e, s.Holds y e := by
  classical
  obtain ⟨p, hp⟩ := maximal_consistent s hs
  let T := {t : Finset (E ⊕ (V × M)) // (t.toRight : Set (V × M)) ⊆ p}
  have extend (v : V) : ∃ x, (v,x) ∈ p := by
    have one (t : T) : ∃ z, z ∈ fiber (pinned s) t.val v := by
      obtain ⟨y, hy⟩ := hp.prop t.val t.property
      exact ⟨y v, y, rfl, hy⟩
    choose z hz using one
    choose code hcode using fun t : T => fiber_code (pinned s) t.val v
    have fip (js : Finset T) : ∃ x, ∀ j ∈ js, x-z j ∈ group (code j) M := by
      let all := js.biUnion Subtype.val
      have allowed : (all.toRight : Set (V×M)) ⊆ p := by
        intro a ha
        obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_toRight.mp ha)
        exact j.property (Finset.mem_toRight.mpr hj)
      obtain ⟨y, hy⟩ := hp.prop all allowed
      refine ⟨y v, fun j hj => (hcode j _ (hz j) _).mp ⟨y, rfl, ?_⟩⟩
      exact fun e he => hy e (Finset.mem_biUnion.mpr ⟨j, hj, he⟩)
    obtain ⟨x, hx⟩ := meet code z fip
    have hp' : consistent s (insert (v,x) p) := by
      intro t ht
      let a : E ⊕ (V×M) := .inr (v,x)
      let b := t.erase a
      have allowed : (b.toRight : Set (V×M)) ⊆ p := by
        intro y hy
        obtain ⟨hneq, hmem⟩ := Finset.mem_erase.mp (Finset.mem_toRight.mp hy)
        exact (Set.mem_insert_iff.mp (ht (Finset.mem_toRight.mpr hmem))).resolve_left
          (fun he => hneq (congrArg Sum.inr he))
      let j : T := ⟨b, allowed⟩
      obtain ⟨y, hy, hsol⟩ := (hcode j _ (hz j) _).mpr (hx j)
      refine ⟨y, fun e he => ?_⟩
      by_cases ha : e = a
      · subst e; exact (holds_pin s y (v,x)).mpr hy
      · exact hsol e (Finset.mem_erase.mpr ⟨ha, he⟩)
    exact ⟨x, (hp.le_of_ge hp' (Set.subset_insert _ _)) (Set.mem_insert _ _)⟩
  choose y hy using extend
  refine ⟨y, fun e => ?_⟩
  let pin (j : Fin (s.width e)) : E ⊕ (V×M) := .inr (s.var e j, y (s.var e j))
  let t := insert (Sum.inl e) (Finset.univ.image pin)
  have allowed : (t.toRight : Set (V×M)) ⊆ p := by
    intro a ha
    obtain h | h := Finset.mem_insert.mp (Finset.mem_toRight.mp ha)
    · cases h
    · obtain ⟨j, _, h⟩ := Finset.mem_image.mp h
      obtain rfl := Sum.inr.inj h
      exact hy _
  obtain ⟨w, hw⟩ := hp.prop t allowed
  have agree (j : Fin (s.width e)) : w (s.var e j) = y (s.var e j) :=
    (holds_pin s w _).mp (hw (pin j) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))))
  have he : s.Holds w e := hw (.inl e) (Finset.mem_insert_self _ _)
  simpa only [Germs.System.Holds, agree] using he

/-- From a finitely intersecting family of matrix cosets without a common point,
choose a new constraint at each step that strictly shrinks the homogeneous group. -/
theorem strict_chain_of_cosets {J : Type u} (code : J → Code R) (c : J → M)
    (fip : ∀ t : Finset J, ∃ x, ∀ j ∈ t, x-c j ∈ group (code j) M)
    (fail : ¬ ∃ x, ∀ j, x-c j ∈ group (code j) M) :
    ∃ codes : Nat → Code R, ∀ n,
      groupList ((List.range (n+1)).map codes) M < groupList ((List.range n).map codes) M := by
  classical
  have step (l : List J) : ∃ j, ¬ groupList (l.map code) M ≤ group (code j) M := by
    by_contra! h
    obtain ⟨x, hx⟩ := fip l.toFinset
    apply fail
    refine ⟨x, fun j => ?_⟩
    obtain ⟨y, hy⟩ := fip (insert j l.toFinset)
    have diff : x-y ∈ groupList (l.map code) M := by
      apply (mem_groupList _).mpr
      intro d hd
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
      have hx' := hx a (List.mem_toFinset.mpr ha)
      have hy' := hy a (Finset.mem_insert_of_mem (List.mem_toFinset.mpr ha))
      simpa only [sub_sub_sub_cancel_right] using (group (code a) M).sub_mem hx' hy'
    simpa only [sub_add_sub_cancel] using (group (code j) M).add_mem (h j diff)
      (hy j (Finset.mem_insert_self _ _))
  choose pick hp using step
  let hist : Nat → List J := Nat.rec [] (fun _ l => l ++ [pick l])
  let codes (n : Nat) := code (pick (hist n))
  have eqs (n : Nat) : (hist n).map code = (List.range n).map codes := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change ((hist n ++ [pick (hist n)]).map code) = _
      simp only [List.map_append, List.range_succ, List.map_cons, List.map_nil, ih]
      rfl
  refine ⟨codes, fun n => ?_⟩
  rw [← eqs, ← eqs]
  change groupList ((hist n ++ [pick (hist n)]).map code) M < groupList ((hist n).map code) M
  apply lt_of_le_not_ge
  · intro x hx
    refine (mem_groupList _).mpr fun d hd => (mem_groupList _).mp hx d ?_
    simp only [List.map_append, List.mem_append]
    exact Or.inl hd
  · intro h
    apply hp (hist n)
    intro x hx
    apply (mem_groupList _).mp (h hx) (code (pick (hist n)))
    simp

/-- Failure of left pure-semisimplicity forces a strictly descending chain
of homogeneous finite matrix subgroups in some module. -/
theorem exists_strict_chain (hn : ¬ LeftPureSemisimple.{u} R) :
    ∃ (M : ModuleCat.{u} R) (codes : Nat → Code R), ∀ n,
      groupList ((List.range (n+1)).map codes) M < groupList ((List.range n).map codes) M := by
  classical
  by_contra noChain
  apply hn
  apply leftPureSemisimple_iff.mpr
  intro M
  apply pureInjective_of_solver
  intro E V s hs
  apply solve_of_cosets _ s hs
  intro J code c fip
  by_contra fail
  obtain ⟨codes, hc⟩ := strict_chain_of_cosets code c fip fail
  exact noChain ⟨M, codes, hc⟩

end PureEmbeddings.MatrixDCC
