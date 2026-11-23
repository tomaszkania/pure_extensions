import PureEmbeddings.Branching
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.Abel

namespace PureEmbeddings.Branching

universe u v
variable {I K C F : Type u} [AddCommGroup F]

/-- Finite compatibility of one prescribed coset for every index. The family
of underlying subgroups is fixed: compactness for arbitrary additive
subgroups is not required. -/
def CompactCosets {J : Type v} (H : J → AddSubgroup F) : Prop :=
  ∀ b : J → F, (∀ js : Finset J, ∃ x : F, ∀ i ∈ js, x - b i ∈ H i) →
    ∃ x : F, ∀ i, x - b i ∈ H i

/-- Cardinal lower bound for independent additive cosets. The witnesses
are zero modulo other subgroups and separated modulo their own subgroup. -/
theorem cosetCardinalBound (G : I → AddSubgroup F) (a : I → K → F)
    (off : ∀ i j k, i ≠ j → a j k ∈ G i)
    (sep : ∀ i k l, a i k - a i l ∈ G i → k = l)
    (compact : CompactCosets G) :
    Cardinal.mk K ^ Cardinal.mk I ≤ Cardinal.mk F := by
  classical
  let d : IndependentFamily I K F := {
    zero := 0
    add := (· + ·)
    zero_add := zero_add
    add_zero := add_zero
    same := fun i x y => x - y ∈ G i
    refl := fun i x => by simp
    symm := fun i x y h => by simpa using (G i).neg_mem h
    trans := fun i x y z h₁ h₂ => by
      convert (G i).add_mem h₁ h₂ using 1
      abel
    add_congr := fun i a b x y h₁ h₂ => by
      convert (G i).add_mem h₁ h₂ using 1
      abel
    entry := a
    off_coordinate := fun i j k h => by simpa using off i j k h
    separate := sep }
  obtain ⟨f, hf⟩ := independentInjection d (by
    intro b localSol
    apply compact b
    intro js
    obtain ⟨x, hx⟩ := localSol js.toList js.nodup_toList
    exact ⟨x, fun i hi => hx i (Finset.mem_toList.mpr hi)⟩)
  rw [Cardinal.power_def]
  exact Cardinal.mk_le_of_injective (f := f) (fun {η ν} h => hf η ν h)

/-- Direct-sum version of the independent-family lemma. The algebraic
hypothesis `detects` reflects membership through the pure embedding and
tests it coordinate by coordinate. Each witness is placed into its own
summand of the actual mathlib finitely supported function group. -/
theorem independentCardinalBound [AddCommGroup C]
    (H : I → AddSubgroup C) (G : I → AddSubgroup F) (c : I → C)
    (inc : ((I × K) →₀ C) →+ F)
    (outside : ∀ i, c i ∉ H i)
    (off : ∀ i j, i ≠ j → c j ∈ H i)
    (detects : ∀ i z, inc z ∈ G i ↔ ∀ p, z p ∈ H i)
    (compact : CompactCosets G) :
    Cardinal.mk K ^ Cardinal.mk I ≤ Cardinal.mk F := by
  classical
  apply cosetCardinalBound G (fun i k => inc (Finsupp.single (i,k) (c i))) _ _ compact
  · intro i j k hij
    apply (detects i _).mpr
    intro p
    by_cases h : p = (j,k)
    · subst p
      simpa using off i j hij
    · simp [h]
  · intro i k l h
    by_contra hkl
    have h' : inc (Finsupp.single (i,k) (c i) - Finsupp.single (i,l) (c i)) ∈ G i := by
      simpa using h
    have hm := (detects i _).mp h' (i,k)
    have hcoords : (i,l) ≠ (i,k) := fun heq => hkl (congrArg Prod.snd heq).symm
    exact outside i (by simpa [Finsupp.single_apply, hcoords, Ne.symm hcoords] using hm)

private def branchSum (entry : Nat → K → F) : List K → F
  | [] => 0
  | k :: s => branchSum entry s + entry s.length k

/-- The countable descending-chain bound for genuine additive subgroups.
A node is the coset of the finite sum of its entries. Compactness is
assumed only for cosets of the given subgroups, with arbitrary indexing
by the natural numbers. -/
theorem countableChainCardinalBound (H : Nat → AddSubgroup F) (a : Nat → K → F)
    (down : ∀ n, H (n + 1) ≤ H n)
    (member : ∀ n k, a n k ∈ H n)
    (different : ∀ n k l, a n k - a n l ∈ H (n + 1) → k = l)
    (compact : ∀ levels : Nat → Nat, CompactCosets (fun n => H (levels n))) :
    Cardinal.mk K ^ Cardinal.aleph0 ≤ Cardinal.mk F := by
  classical
  let tree : CosetTree K F := {
    inside := fun s x => x - branchSum a s ∈ H s.length
    inhabitedNode := fun s => ⟨branchSum a s, by simp⟩
    nested := fun s k x hx => by
      change x - (branchSum a s + a s.length k) ∈ H (s.length + 1) at hx
      have h := (H s.length).add_mem (down s.length hx) (member s.length k)
      convert h using 1
      abel
    separatedChildren := fun s k l x hx hy => by
      change x - (branchSum a s + a s.length k) ∈ H (s.length + 1) at hx
      change x - (branchSum a s + a s.length l) ∈ H (s.length + 1) at hy
      apply different s.length
      convert (H (s.length + 1)).sub_mem hy hx using 1
      abel }
  obtain ⟨f, hf⟩ := infiniteBranchInjection tree (by
    intro nodes localSol
    apply compact (fun n => (nodes n).length) (fun n => branchSum a (nodes n))
    intro js
    obtain ⟨x, hx⟩ := localSol js.toList
    exact ⟨x, fun n hn => hx n (Finset.mem_toList.mpr hn)⟩)
  have hmk := Cardinal.mk_le_of_injective (f := f) (fun {η ν} h => hf η ν h)
  simpa only [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.lift_uzero, Cardinal.lift_aleph0] using hmk

end PureEmbeddings.Branching
