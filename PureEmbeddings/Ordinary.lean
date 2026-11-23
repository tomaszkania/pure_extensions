import PureEmbeddings.Chains
import PureEmbeddings.PureHull
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.SetTheory.Cardinal.Finsupp
import Mathlib.RingTheory.Noetherian.Defs

/-! Ordinary universal injectives. The cardinality bound is on the module
itself, not just on a family of maps into a larger injective. -/
namespace PureEmbeddings.Ordinary
open Cardinal Submodule LinearMap
universe u
variable {R : Type u} [Ring R]

/-- The module used for one coordinate is required to contain every cyclic module. -/
def CyclicUniversal (C : ModuleCat.{u} R) : Prop :=
  ∀ (M : ModuleCat.{u} R) (y : M), ∃ j : (R ∙ y) →ₗ[R] C, Function.Injective j

private theorem injective_of_zero_only {A B : ModuleCat.{u} R} (f : A →ₗ[R] B)
    (h : ∀ x, f x = 0 → x = 0) : Function.Injective f :=
  LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr h)

/-- An injective module containing κ independent copies of a module containing
all cyclics is ordinarily universal up to κ. We build a partial injection
into the direct sum, reserving a fresh coordinate for each unused generator. -/
theorem universal_of_cyclic_copies_for {K : Type u} {C D : ModuleCat.{u} R}
    (hd : Module.Injective R D)
    (j : (K →₀ C) →ₗ[R] D) (hj : Function.Injective j)
    (M : ModuleCat.{u} R) (hm : Cardinal.mk M ≤ Cardinal.mk K)
    (hc : ∀ y : M, ∃ a : (R ∙ y) →ₗ[R] C, Function.Injective a) :
    ∃ f : M →ₗ[R] D, Function.Injective f := by
  classical
  obtain ⟨e⟩ : Nonempty (M ↪ K) := hm
  let L := ModuleCat.of R (K →₀ C)
  let S : Set (M →ₗ.[R] L) := {p | Function.Injective p.toFun ∧
    ∀ y : M, y ∉ p.domain → ∀ z : p.domain, p z (e y) = 0}
  let b : M →ₗ.[R] L := ⟨⊥, 0⟩
  obtain ⟨p, _, hp⟩ := zorn_le_nonempty₀ S (by
    intro c hc' hchain y hy
    have hd' := hchain.directedOn
    let q := LinearPMap.sSup c hd'
    have hn : c.Nonempty := ⟨y,hy⟩
    refine ⟨q, ⟨?_, ?_⟩, fun z hz => LinearPMap.le_sSup hd' hz⟩
    · apply injective_of_zero_only (A := ModuleCat.of R q.domain) (B := L)
      intro z hz
      obtain ⟨l, hl, hz'⟩ := (LinearPMap.mem_domain_sSup_iff hn hd').mp z.property
      let w : l.domain := ⟨z, hz'⟩
      have hw : l w = 0 := (LinearPMap.sSup_apply hd' hl w).symm.trans hz
      have h0 := (hc' hl).1 (hw.trans l.toFun.map_zero.symm)
      exact Subtype.ext (show (w : M) = 0 from congrArg (fun v : l.domain => (v : M)) h0)
    · intro a ha z
      obtain ⟨l, hl, hz'⟩ := (LinearPMap.mem_domain_sSup_iff hn hd').mp z.property
      let w : l.domain := ⟨z, hz'⟩
      have hw : q z = l w := LinearPMap.sSup_apply hd' hl w
      rw [hw]
      exact (hc' hl).2 a (fun h => ha ((LinearPMap.le_sSup hd' hl).1 h)) w)
    b ⟨(fun _ _ _ => Subsingleton.elim _ _), fun _ _ _ => rfl⟩
  obtain ⟨f, hf⟩ := hd.out p.domain.subtype Subtype.val_injective (j.comp p.toFun)
  refine ⟨f, injective_of_zero_only (A := M) (B := D) f fun y hy => ?_⟩
  by_contra hne
  let Y := R ∙ y
  have hk (z : Y) : f z = 0 := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp z.property
    rw [← ha, map_smul, hy, smul_zero]
  have hinter (z : p.domain) (w : Y) (he : (z : M) = w) : (z : M) = 0 := by
    have h0 : j (p z) = j 0 := (hf z).symm.trans ((congrArg f he).trans ((hk w).trans j.map_zero.symm))
    exact congrArg Subtype.val (hp.1.1 ((hj h0).trans p.toFun.map_zero.symm))
  have hyout : y ∉ p.domain := fun h =>
    hne (hinter ⟨y,h⟩ ⟨y,Submodule.mem_span_singleton_self y⟩ rfl)
  obtain ⟨g, hg⟩ := hc y
  let k : Y →ₗ[R] L := (Finsupp.lsingle (e y)).comp g
  let q : M →ₗ.[R] L := ⟨Y, k⟩
  have compat (z : p.domain) (w : q.domain) (he : (z : M) = w) : p z = q w := by
    have h0 := hinter z w he
    have hz : z = 0 := Subtype.ext h0
    have hw : w = 0 := Subtype.ext (he.symm.trans h0)
    rw [hz, hw, p.map_zero, q.map_zero]
  let t := p.sup q compat
  have hdecomp (z : t.domain) : ∃ (a : p.domain) (b' : q.domain),
      (a : M) + b' = z ∧ t z = p a + q b' := by
    obtain ⟨a, ha, b', hb, he⟩ := Submodule.mem_sup.mp z.property
    exact ⟨⟨a,ha⟩,⟨b',hb⟩,he,LinearPMap.sup_apply compat _ _ _ he⟩
  have ht : t ∈ S := by
    constructor
    · apply injective_of_zero_only (A := ModuleCat.of R t.domain) (B := L)
      intro z hz
      obtain ⟨a, b', hab, ht⟩ := hdecomp z
      have hv := congrArg (fun t' : L => t' (e y)) (ht.symm.trans hz)
      have hqa : p a (e y) = 0 := hp.1.2 y hyout a
      have gb : g b' = 0 := by simpa [L, q, k, hqa, Finsupp.add_apply] using hv
      have hb : b' = 0 := hg (gb.trans g.map_zero.symm)
      have ha0 : p a = 0 := by simpa [hb] using ht.symm.trans hz
      have ha : a = 0 := hp.1.1 (ha0.trans p.toFun.map_zero.symm)
      exact Subtype.ext (by simpa [ha, hb] using hab.symm)
    · intro x hx z
      obtain ⟨a, b', _, ht⟩ := hdecomp z
      have ha := hp.1.2 x (fun h => hx ((p.left_le_sup q compat).1 h)) a
      have hxy : e y ≠ e x := fun h => hx (e.injective h ▸
        (p.right_le_sup q compat).1 (Submodule.mem_span_singleton_self y))
      simp [ht, L, q, k, Finsupp.add_apply, ha, Finsupp.single_eq_of_ne (Ne.symm hxy)]
  exact hyout ((hp.2 ht (p.left_le_sup q compat)).1
    ((p.right_le_sup q compat).1 (Submodule.mem_span_singleton_self y)))

theorem universal_of_cyclic_copies {K : Type u} {C D : ModuleCat.{u} R}
    (hc : CyclicUniversal C) (hd : Module.Injective R D)
    (j : (K →₀ C) →ₗ[R] D) (hj : Function.Injective j)
    (M : ModuleCat.{u} R) (hm : Cardinal.mk M ≤ Cardinal.mk K) :
    ∃ f : M →ₗ[R] D, Function.Injective f :=
  universal_of_cyclic_copies_for hd j hj M hm (hc M)

end PureEmbeddings.Ordinary
