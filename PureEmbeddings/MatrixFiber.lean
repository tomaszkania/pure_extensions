import PureEmbeddings.MatrixDCC
import Mathlib.Algebra.Module.BigOperators

/-! The possible values of one variable in a finite system form a coset
of a subgroup defined by a finite homogeneous matrix. -/
namespace PureEmbeddings.MatrixDCC

open scoped BigOperators
universe u
variable {R M E V : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- The values of the chosen variable among solutions of a finite set of rows. -/
def fiber (s : Germs.System R M E V) (t : Finset E) (v : V) : Set M :=
  {x | ∃ y : V → M, y v = x ∧ ∀ e ∈ t, s.Holds y e}

/-- Reindex finite arrays by finite ordinals. -/
private theorem encode {I J : Type u} [Fintype I] [Fintype J]
    (l : I → R) (a : I → J → R) :
    ∃ c : Code R, ∀ x : M, x ∈ group c M ↔
      ∃ w : J → M, ∀ i, l i • x + ∑ j, a i j • w j = 0 := by
  classical
  let p := Fintype.equivFin I
  let q := Fintype.equivFin J
  let c : Code R := ⟨_, _, fun i => l (p.symm i), fun i j => a (p.symm i) (q.symm j)⟩
  refine ⟨c, fun x => ?_⟩
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (q j), fun i => ?_⟩
    have h := hw (p i)
    change l (p.symm (p i)) • x + ∑ j, a (p.symm (p i)) (q.symm j) • w j = 0 at h
    simpa only [Equiv.symm_apply_apply, ← q.symm.sum_comp (fun j => a i j • w (q j)),
      Equiv.apply_symm_apply] using h
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (q.symm j), fun i => ?_⟩
    change l (p.symm i) • x + ∑ j, a (p.symm i) (q.symm j) • w (q.symm j) = 0
    rw [q.symm.sum_comp (fun j => a (p.symm i) j • w j)]
    exact hw _

/-- Collect all occurrences of the same variable into a single coefficient. -/
private theorem collect {J : Type u} {K : Type*} [Fintype J] [Fintype K] [DecidableEq J]
    (r : K → R) (atVar : K → J) (w : J → M) :
    ∑ j, (∑ k, if atVar k = j then r k else 0) • w j =
      ∑ k, r k • w (atVar k) := by
  classical
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Subtracting one solution gives the homogeneous system on the same variables. -/
private theorem fiber_sub (s : Germs.System R M E V) (t : Finset E) (v : V)
    {z : M} (hz : z ∈ fiber s t v) (x : M) :
    x ∈ fiber s t v ↔ ∃ d : V → M, d v = x-z ∧ ∀ e ∈ t,
      ∑ k, s.coeff e k • d (s.var e k) = 0 := by
  obtain ⟨y, hy, he⟩ := hz
  constructor
  · rintro ⟨w, hw, hw'⟩
    refine ⟨fun j => w j - y j, by simp only [hw, hy], fun e h => ?_⟩
    simp only [smul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((hw' e h).trans (he e h).symm)
  · rintro ⟨d, hd, hd'⟩
    refine ⟨fun j => d j + y j, by simp only [hd, hy, sub_add_cancel], fun e h => ?_⟩
    change ∑ k, s.coeff e k • (d (s.var e k) + y (s.var e k)) = _
    simp only [smul_add, Finset.sum_add_distrib, hd' e h, zero_add]
    exact he _ h

theorem fiber_code (s : Germs.System R M E V) (t : Finset E) (v : V) :
    ∃ c : Code R, ∀ z ∈ fiber s t v, ∀ x, x ∈ fiber s t v ↔ x-z ∈ group c M := by
  classical
  let J := insert v (t.biUnion (fun e => Finset.univ.image (s.var e)))
  let v₀ : J := ⟨v, Finset.mem_insert_self _ _⟩
  let atVar (e : t) (k : Fin (s.width e)) : J := ⟨s.var e k,
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨e, e.property, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)⟩
  let l : Option t → R := Option.elim' 1 (fun _ => 0)
  let a : Option t → J → R := Option.elim' (fun j => if v₀ = j then -1 else 0)
    (fun e j => ∑ k, if atVar e k = j then s.coeff e k else 0)
  obtain ⟨c, hc⟩ := encode (M := M) l a
  refine ⟨c, fun z hz x => ?_⟩
  rw [fiber_sub s t v hz, hc]
  have head (b : M) (w : J → M) :
      l none • b + ∑ j, a none j • w j = 0 ↔ w v₀ = b := by
    simp [l, a, ite_smul, add_neg_eq_zero]
    exact eq_comm
  have row (b : M) (w : J → M) (e : t) :
      l (some e) • b + ∑ j, a (some e) j • w j = ∑ k, s.coeff e k • w (atVar e k) := by
    simpa [l, a] using collect (s.coeff e) (atVar e) w
  constructor
  · rintro ⟨d, hv, hd⟩
    let w (j : J) := d j
    refine ⟨w, ?_⟩
    rintro (_ | e)
    · exact (head _ _).2 hv
    · rw [row]
      exact hd _ e.property
  · rintro ⟨w, hw⟩
    let d (i : V) : M := if h : i ∈ J then w ⟨i, h⟩ else 0
    have agree (j : J) : d j = w j := dif_pos j.property
    refine ⟨d, (agree v₀).trans ((head _ _).1 (hw none)), fun e he => ?_⟩
    let j : t := ⟨e, he⟩
    have hrow := hw (some j)
    rw [row] at hrow
    convert hrow using 1
    exact Finset.sum_congr rfl (fun k _ => congrArg (s.coeff e k • ·) (agree (atVar j k)))

end PureEmbeddings.MatrixDCC
