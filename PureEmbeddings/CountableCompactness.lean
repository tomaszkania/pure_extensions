import PureEmbeddings.MatrixCompact
import Mathlib.Data.Countable.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Over a countable ring there are only countably many one-variable matrix
subgroups. Finitely intersecting cosets of any one of them coincide. -/
namespace PureEmbeddings.MatrixDCC
open Finset
universe u
variable {R : Type u} [Ring R] [Countable R]

instance : Countable (Code R) := by
  let pack (c : Code R) : Σ m : ℕ, Σ n : ℕ, (Fin m → R) × (Fin m → Fin n → R) :=
    ⟨c.rows,c.cols,c.lead,c.coeff⟩
  let unpack : (Σ m : ℕ, Σ n : ℕ, (Fin m → R) × (Fin m → Fin n → R)) → Code R :=
    fun ⟨m,n,a,b⟩ => ⟨m,n,a,b⟩
  exact (show Function.LeftInverse unpack pack from fun _ => rfl).injective.countable

omit [Countable R] in
/-- One representative of each finite matrix suffices. -/
theorem cosets_of_code_solver {M : Type u} [AddCommGroup M] [Module R M]
    (solve : ∀ (K : Set (Code R))
      (s : Germs.System R M ((k : K) × Fin k.val.rows) (Option ((k : K) × Fin k.val.cols))),
      s.FinitelySoluble → ∃ x, ∀ e, s.Holds x e)
    {J : Type u} (codes : J → Code R) (c : J → M)
    (hf : ∀ t : Finset J, ∃ x, ∀ j ∈ t, x - c j ∈ group (codes j) M) :
    ∃ x, ∀ j, x - c j ∈ group (codes j) M := by
  classical
  let K := Set.range codes
  choose rep hrep using (fun k : K => k.property)
  let Row := (k : K) × Fin k.val.rows
  let Var := Option ((k : K) × Fin k.val.cols)
  let s : Germs.System R M Row Var :=
    { width := fun a => a.1.val.cols + 1
      coeff := fun ⟨k,i⟩ => Fin.cases (k.val.lead i) (k.val.coeff i)
      var := fun ⟨k,_⟩ => Fin.cases none (fun j => some ⟨k,j⟩)
      rhs := fun ⟨k,i⟩ => k.val.lead i • c (rep k) }
  have holds (v : Var → M) (k : K) (i : Fin k.val.rows) :
      s.Holds v ⟨k,i⟩ ↔
        k.val.lead i • (v none - c (rep k)) + ∑ j, k.val.coeff i j • v (some ⟨k,j⟩) = 0 := by
    simp only [s,Germs.System.Holds,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,smul_sub]
    constructor <;> intro h <;> rw [← sub_eq_zero] at * <;> abel_nf at * <;> assumption
  have fip : s.FinitelySoluble := by
    intro a
    let t := a.image (fun (w : Row) => rep w.1)
    obtain ⟨z,hz⟩ := hf t
    have hw (k : K) (hk : rep k ∈ t) : z - c (rep k) ∈ group k.val M := by
      simpa only [hrep] using hz (rep k) hk
    let w (k : K) : Fin k.val.cols → M := if hk : rep k ∈ t then (hw k hk).choose else 0
    let v : Var → M := Option.elim' z (fun ⟨k,j⟩ => w k j)
    refine ⟨v, ?_⟩
    rintro ⟨k,i⟩ hi
    have hk : rep k ∈ t := Finset.mem_image.mpr ⟨⟨k,i⟩,hi,rfl⟩
    apply (holds v k i).mpr
    exact (by simpa only [v, w, Option.elim', dif_pos hk] using (hw k hk).choose_spec i)
  obtain ⟨v,hv⟩ := solve K s fip
  refine ⟨v none, fun j => ?_⟩
  let k : K := ⟨codes j,Set.mem_range_self j⟩
  have mine : v none - c (rep k) ∈ group (codes j) M :=
    ⟨fun d => v (some ⟨k,d⟩), fun i => (holds v k i).mp (hv ⟨k,i⟩)⟩
  obtain ⟨z,hz⟩ := hf {j,rep k}
  have h1 := hz j (by simp)
  have h2 : z - c (rep k) ∈ group (codes j) M := by
    simpa only [hrep] using hz (rep k) (by simp)
  have both := (group (codes j) M).add_mem mine ((group (codes j) M).sub_mem h1 h2)
  convert both using 1
  abel

/-- Countably many equations suffice to intersect any family of finitely
intersecting one-variable matrix cosets over a countable ring. -/
theorem cosets_of_countable_solver {M : Type u} [AddCommGroup M] [Module R M]
    (solve : ∀ {E V : Type u} [Countable E] [Countable V] (s : Germs.System R M E V),
      s.FinitelySoluble → ∃ x, ∀ e, s.Holds x e) : MeetsCosets R M :=
  fun codes c fip => cosets_of_code_solver (fun _ => solve) codes c fip

/-- For modules over any countable ring it suffices to test systems with
countably many rows and countably many variables. -/
theorem pureInjective_iff_countable_solver {M : ModuleCat.{u} R} :
    IsPureInjective M ↔ ∀ {E V : Type u} [Countable E] [Countable V]
      (s : Germs.System R M E V), s.FinitelySoluble → ∃ x, ∀ e, s.Holds x e := by
  constructor
  · intro h E V _ _ s hs
    exact Germs.algebraically_compact h s hs
  · intro solve
    apply pureInjective_of_solver
    intro E V s hs
    apply solve_of_cosets _ s hs
    exact fun codes c fip => cosets_of_countable_solver solve codes c fip

end PureEmbeddings.MatrixDCC
