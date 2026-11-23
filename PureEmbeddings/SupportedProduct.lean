import Std

/-!
# Support and the congruence obstruction

The coordinates in block `n` are residues modulo `2^(n+1)`, represented by
their `n+1` binary digits, least significant first. Two such residues agree
modulo `2^m` precisely when they agree in the digit positions below `m`.
This representation makes the proof independent of an integer-modulo library.

`CanInject X Y` expresses the cardinal inequality `|X| ≤ |Y|` without any
cardinal arithmetic library. Subsets are represented by subtypes.
-/

namespace PureEmbeddings.SupportedProduct

universe u v

def OneToOne {X : Type u} {Y : Type v} (f : X → Y) : Prop :=
  ∀ ⦃x x'⦄, f x = f x' → x = x'

def CanInject (X : Type u) (Y : Type v) : Prop :=
  ∃ f : X → Y, OneToOne f

/-- A zero-one vector on `A × K` with at most `|A|` nonzero entries. -/
def SparseBits (A : Type u) (K : Type v) :=
  {x : A × K → Bool // CanInject {i : A × K // x i = true} A}

def graphBit {A : Type u} {K : Type v} [DecidableEq K]
    (f : A → K) (i : A × K) : Bool :=
  decide (i.2 = f i.1)

private theorem graph_support_bound {A : Type u} {K : Type v} [DecidableEq K]
    (f : A → K) : CanInject {i : A × K // graphBit f i = true} A := by
  refine ⟨fun i => i.val.1, ?_⟩
  intro i j h
  have hi : i.val.2 = f i.val.1 := by simpa [graphBit] using i.property
  have hj : j.val.2 = f j.val.1 := by simpa [graphBit] using j.property
  exact Subtype.ext (Prod.ext h (hi.trans ((congrArg f h).trans hj.symm)))

/-- The graph construction gives the lower bound for supported products. -/
theorem graphs_inject (A : Type u) (K : Type v) :
    CanInject (A → K) (SparseBits A K) := by
  classical
  refine ⟨fun f => ⟨graphBit f, graph_support_bound f⟩, ?_⟩
  intro f g h
  funext a
  have hb := congrFun (congrArg (fun z : SparseBits A K => z.val) h) (a, f a)
  change graphBit f (a, f a) = graphBit g (a, f a) at hb
  have hg : graphBit g (a, f a) = true := by
    rw [← hb]
    simp [graphBit]
  simpa [graphBit] using hg

/-- The full product of the finite-coordinate blocks in binary representation. -/
abbrev Digits (B : Nat → Type u) :=
  (i : Sigma B) → Fin (i.1 + 1) → Bool

abbrev Prefix (B : Nat → Type u) (m : Nat) :=
  {i : Sigma B // i.1 < m}

def Active {B : Nat → Type u} (x : Digits B) (i : Sigma B) : Prop :=
  ∃ d : Fin (i.1 + 1), x i d = true

/--
A support is small if its cardinality is bounded by that of a finite union of
initial blocks. For block sizes strictly increasing to κ this is exactly the
condition that its cardinality be less than κ. The support itself may meet
every block.
-/
def SmallSupport {B : Nat → Type u} (x : Digits B) : Prop :=
  ∃ m, CanInject {i : Sigma B // Active x i} (Prefix B m)

/-- The truncation with value `2^n` on block `n < m` and zero elsewhere. -/
def truncation (B : Nat → Type u) (m : Nat) : Digits B :=
  fun i d => decide (i.1 < m ∧ d.val = i.1)

/-- At level `m` impose `x ≡ truncation B m (mod 2^m)` in every coordinate. -/
def Congruence {B : Nat → Type u} (x : Digits B) (m : Nat) : Prop :=
  ∀ (i : Sigma B) (d : Fin (i.1 + 1)), d.val < m →
    x i d = truncation B m i d

theorem truncation_small (B : Nat → Type u) (m : Nat) :
    SmallSupport (truncation B m) := by
  refine ⟨m, ?_⟩
  have inside (z : {i : Sigma B // Active (truncation B m) i}) : z.val.1 < m := by
    obtain ⟨d, hd⟩ := z.property
    have ht : z.val.1 < m ∧ d.val = z.val.1 := by
      simpa [truncation] using hd
    exact ht.1
  refine ⟨fun z => ⟨z.val, inside z⟩, ?_⟩
  intro z w he
  exact Subtype.ext (congrArg (fun t : Prefix B m => t.val) he)

theorem truncation_solves {B : Nat → Type u} {m M : Nat} (hm : m ≤ M) :
    Congruence (truncation B M) m := by
  intro i d hd
  by_cases e : d.val = i.1
  · have hi : i.1 < m := e ▸ hd
    have hiM : i.1 < M := Nat.lt_of_lt_of_le hi hm
    simp [truncation, e, hi, hiM]
  · simp [truncation, e]

/-- An upper bound constructed from the indices of any finite subsystem. -/
private def cut : List Nat → Nat
  | [] => 0
  | n :: ns => max n (cut ns)

private theorem le_cut {n : Nat} (ns : List Nat) (hn : n ∈ ns) : n ≤ cut ns := by
  induction ns with
  | nil => simp at hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with he | ht
    · exact he ▸ Nat.le_max_left a (cut ns)
    · exact Nat.le_trans (ih ht) (Nat.le_max_right a (cut ns))

theorem finite_congruences_solvable (B : Nat → Type u) (ns : List Nat) :
    ∃ x : Digits B, SmallSupport x ∧ ∀ m ∈ ns, Congruence x m := by
  refine ⟨truncation B (cut ns), truncation_small B _, ?_⟩
  intro m hm
  exact truncation_solves (le_cut ns hm)

/-- The congruence numbered `n+1` forces a nonzero entry on all of block `n`. -/
theorem all_coordinates_active {B : Nat → Type u} {x : Digits B}
    (solves : ∀ m, Congruence x m) (i : Sigma B) : Active x i := by
  let d : Fin (i.1 + 1) := ⟨i.1, Nat.lt_succ_self _⟩
  refine ⟨d, ?_⟩
  have hbit := solves (i.1 + 1) i d (Nat.lt_succ_self _)
  simpa [truncation, d] using hbit

/--
Each new block has strictly larger cardinality than the preceding finite
union (as for a strictly increasing sequence of infinite cardinals).
Then the full family of congruences has no small-support solution.
-/
theorem no_simultaneous_solution (B : Nat → Type u)
    (grows : ∀ m, ¬ CanInject (B m) (Prefix B m)) :
    ¬ ∃ x : Digits B, SmallSupport x ∧ ∀ m, Congruence x m := by
  rintro ⟨x, ⟨M, f, hf⟩, solves⟩
  apply grows M
  let z (b : B M) : {i : Sigma B // Active x i} :=
    ⟨⟨M, b⟩, all_coordinates_active solves _⟩
  refine ⟨fun b => f (z b), ?_⟩
  intro b c he
  have hbc : (⟨M, b⟩ : Sigma B) = ⟨M, c⟩ :=
    congrArg Subtype.val (hf he)
  cases hbc
  rfl

end PureEmbeddings.SupportedProduct
