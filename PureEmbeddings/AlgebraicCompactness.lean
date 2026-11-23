import PureEmbeddings.Germs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-! A module is pure-injective if and only if all its finitely soluble row-finite
systems have a solution. The converse records the linear equations of an extension map. -/
namespace PureEmbeddings
universe u
variable {R : Type u} [Ring R]

private theorem reflect_finite {A B : ModuleCat.{u} R} (i : A →ₗ[R] B) (hi : IsPureMap i)
    {K T : Type u} [Fintype K] [Fintype T] (r : K → T → R) (c : K → A)
    (x : T → B) (hx : ∀ k, ∑ t, r k t • x t = i (c k)) :
    ∃ y : T → A, ∀ k, ∑ t, r k t • y t = c k := by
  classical
  let e := Fintype.equivFin K
  let d := Fintype.equivFin T
  let m := fun k t => r (e.symm k) (d.symm t)
  let a := fun k => c (e.symm k)
  have hB : Soluble m (i ∘ a) := by
    refine ⟨fun t => x (d.symm t), fun k => ?_⟩
    exact (d.symm.sum_comp (fun t => r (e.symm k) t • x t)).trans (hx _)
  obtain ⟨w,hw⟩ := hi.2 m a hB
  refine ⟨fun t => w (d t), fun k => ?_⟩
  have he := (d.sum_comp (fun j => r k (d.symm j) • w j))
  simpa [e,d,m,a] using he.trans (by simpa [m,a] using hw (e k))

/-- Purity reflects every finite selection of rows of a possibly infinite system.
Repeated occurrences of a variable are collected in the same matrix column. -/
theorem IsPureMap.reflect_rows {A B : ModuleCat.{u} R} (i : A →ₗ[R] B) (hi : IsPureMap i)
    {E V : Type u} (s : Germs.System R A E V) (x : V → B)
    (hx : ∀ e, ∑ j, s.coeff e j • x (s.var e j) = i (s.rhs e)) : s.FinitelySoluble := by
  classical
  intro K
  let T := K.biUnion (fun e => Finset.univ.image (s.var e))
  have inside (e : K) (j : Fin (s.width e.val)) : s.var e.val j ∈ T :=
    Finset.mem_biUnion.mpr ⟨e.val,e.property,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  let col (e : K) (j : Fin (s.width e.val)) : T := ⟨s.var e.val j,inside e j⟩
  let r (e : K) (t : T) := ∑ j, if col e j = t then s.coeff e.val j else 0
  have collect {M : ModuleCat.{u} R} (e : K) (y : T → M) :
      ∑ t, r e t • y t = ∑ j, s.coeff e.val j • y (col e j) := by
    simp only [r, Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single (col e j)]
    · simp
    · intro t ht hne; simp [Ne.symm hne]
    · simp
  obtain ⟨y,hy⟩ := reflect_finite i hi r (fun e => s.rhs e.val) (fun t => x t.val)
    (fun e => (collect (M := B) e (fun t => x t.val)).trans (hx _))
  let v (t : V) : A := if ht : t ∈ T then y ⟨t,ht⟩ else 0
  refine ⟨v, fun k hk => ?_⟩
  let e : K := ⟨k,hk⟩
  have he := (collect (M := A) e y).symm.trans (hy e)
  simpa only [Germs.System.Holds, v, dif_pos (inside e _), col, e] using he

/-- Any target solving all finitely soluble systems extends maps along pure embeddings. -/
theorem pureInjective_of_solver {F : ModuleCat.{u} R}
    (solve : ∀ {E V : Type u} (s : Germs.System R F E V), s.FinitelySoluble →
      ∃ x, ∀ e, s.Holds x e) : IsPureInjective F := by
  classical
  intro A B i f hi
  let E := (B × B) ⊕ ((R × B) ⊕ A)
  let width : E → ℕ := Sum.elim (fun _ => 3) (Sum.elim (fun _ => 2) (fun _ => 1))
  let s : Germs.System R A E B :=
    { width := width
      coeff := fun e => match e with
        | .inl _ => ![1, 1, -1]
        | .inr (.inl (r,_)) => ![r, -1]
        | .inr (.inr _) => ![1]
      var := fun e => match e with
        | .inl (b,c) => ![b,c,b+c]
        | .inr (.inl (r,b)) => ![b,r • b]
        | .inr (.inr a) => ![i a]
      rhs := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) id) }
  have hB (e : E) : ∑ j, s.coeff e j • id (s.var e j) = i (s.rhs e) := by
    rcases e with ⟨b,c⟩ | ⟨r,b⟩ | a <;> simp [s, width, Fin.sum_univ_succ]
  have hs := hi.reflect_rows i s id hB
  let t : Germs.System R F E B := { s with rhs := f ∘ s.rhs }
  have ht : t.FinitelySoluble := by
    intro K
    obtain ⟨x,hx⟩ := hs K
    refine ⟨f ∘ x, fun e he => ?_⟩
    simpa only [t, Germs.System.Holds, Function.comp_def, map_sum, map_smul] using congrArg f (hx e he)
  obtain ⟨v,hv⟩ := solve t ht
  let g : B →ₗ[R] F :=
    { toFun := v
      map_add' := by
        intro b c
        have h := hv (Sum.inl (b,c))
        apply Eq.symm
        apply sub_eq_zero.mp
        simpa [Germs.System.Holds, t, s, width, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h
      map_smul' := by
        intro r b
        have h := hv (Sum.inr (Sum.inl (r,b)))
        apply Eq.symm
        apply sub_eq_zero.mp
        simpa [Germs.System.Holds, t, s, width, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h }
  refine ⟨g, LinearMap.ext fun a => ?_⟩
  simpa [g, Germs.System.Holds, t, s, width] using hv (.inr (.inr a))

theorem pureInjective_iff_solver {F : ModuleCat.{u} R} :
    IsPureInjective F ↔ ∀ {E V : Type u} (s : Germs.System R F E V),
      s.FinitelySoluble → ∃ x, ∀ e, s.Holds x e :=
  ⟨fun h _ _ => Germs.algebraically_compact h, pureInjective_of_solver⟩

end PureEmbeddings
