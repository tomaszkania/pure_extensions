import PureEmbeddings.ModuleTheory
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Order.Zorn

/-! # Essential injective extensions with a cardinal bound

An embedding into an injective module contains an essential injective extension
of its domain, of cardinality at most that of the given injective module. This
construction works over every ring.
-/
namespace PureEmbeddings.DedekindEnvelope
open Cardinal Function Set Submodule
universe u
variable {R : Type u} [Ring R] {D : ModuleCat.{u} R}

private def essential (S E : Submodule R D) : Prop :=
  S ≤ E ∧ ∀ x ∈ E, x ≠ 0 → ∃ r : R, r • x ≠ 0 ∧ r • x ∈ S

private theorem maximal_essential (S : Submodule R D) :
    ∃ E, Maximal (essential S) E := by
  classical
  let H := {E : Submodule R D | essential S E}
  have init : S ∈ H := ⟨le_rfl, fun x hx hn => ⟨1, by simpa using hn, by simpa using hx⟩⟩
  have bound (c : Set (Submodule R D)) (hc : c ⊆ H) (chain : IsChain (· ≤ ·) c) (y : Submodule R D)
      (hy : y ∈ c) : ∃ z ∈ H, ∀ a ∈ c, a ≤ z := by
    refine ⟨sSup c, ⟨(hc hy).1.trans (le_sSup hy), ?_⟩, fun _ ha => le_sSup ha⟩
    intro x hx hn
    obtain ⟨a, ha, hx⟩ := (Submodule.mem_sSup_of_directed ⟨y,hy⟩ chain.directedOn).mp hx
    exact (hc ha).2 x hx hn
  obtain ⟨E, _, hE⟩ := zorn_le_nonempty₀ H bound S init
  exact ⟨E, hE⟩

private def separated (E N : Submodule R D) : Prop := ∀ x ∈ N, x ∈ E → x = 0

private theorem maximal_separated (E : Submodule R D) : ∃ N, Maximal (separated E) N := by
  classical
  let H := {N : Submodule R D | separated E N}
  have init : (⊥ : Submodule R D) ∈ H := fun x hx _ => (by simpa using hx)
  have bound (c : Set (Submodule R D)) (hc : c ⊆ H) (chain : IsChain (· ≤ ·) c) (y : Submodule R D)
      (hy : y ∈ c) : ∃ z ∈ H, ∀ a ∈ c, a ≤ z := by
    refine ⟨sSup c, ?_, fun _ ha => le_sSup ha⟩
    intro x hx he
    obtain ⟨a, ha, hx⟩ := (Submodule.mem_sSup_of_directed ⟨y,hy⟩ chain.directedOn).mp hx
    exact hc ha x hx he
  obtain ⟨N, _, hN⟩ := zorn_le_nonempty₀ H bound ⊥ init
  exact ⟨N, hN⟩

private theorem quotient_essential (E N : Submodule R D) (hn : Maximal (separated E) N)
    (x : D ⧸ N) (hx : x ≠ 0) :
    ∃ r : R, r • x ≠ 0 ∧ ∃ y : E, N.mkQ y.val = r • x := by
  classical
  obtain ⟨d, rfl⟩ := N.mkQ_surjective x
  let A := N ⊔ Submodule.span R {d}
  have hbad : ¬ separated E A := by
    intro h
    have hle : A ≤ N := hn.le_of_ge h le_sup_left
    have hd : d ∈ N := hle ((show Submodule.span R {d} ≤ A from le_sup_right) (Submodule.mem_span_singleton_self d))
    exact hx ((Submodule.Quotient.mk_eq_zero N).mpr hd)
  unfold separated at hbad
  push_neg at hbad
  obtain ⟨y, hy, he, hy0⟩ := hbad
  obtain ⟨n, hn', k, hk, heq⟩ := Submodule.mem_sup.mp hy
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hk
  have qn : N.mkQ n = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hn'
  have qy : N.mkQ y = r • N.mkQ d := by rw [← heq, map_add, qn, zero_add, map_smul]
  refine ⟨r, ?_, ⟨y,he⟩, qy⟩
  intro hz
  exact hy0 (hn.prop y ((Submodule.Quotient.mk_eq_zero N).mp (qy.trans hz)) he)

/-- Every module inside an ordinary injective has an essential injective
extension contained, up to an isomorphism, in that same ambient module. -/
theorem exists_essential {X D : ModuleCat.{u} R} (injD : Module.Injective R D)
    (j : X →ₗ[R] D) (hj : Injective j) :
    ∃ (E : ModuleCat.{u} R) (e : X →ₗ[R] E), Module.Injective R E ∧ Injective e ∧ #E ≤ #D ∧
      ∀ x : E, x ≠ 0 → ∃ r : R, r • x ≠ 0 ∧ r • x ∈ LinearMap.range e := by
  classical
  let S := LinearMap.range j
  obtain ⟨E, hE⟩ := maximal_essential S
  obtain ⟨N, hN⟩ := maximal_separated E
  let q : E →ₗ[R] (D ⧸ N) := N.mkQ.comp E.subtype
  have hinj : Injective q := by
    apply (injective_iff_map_eq_zero q).mpr
    intro x hx
    apply Subtype.ext
    exact hN.prop x.val ((Submodule.Quotient.mk_eq_zero N).mp hx) x.property
  obtain ⟨g, hg⟩ := injD.out q hinj E.subtype
  have contains : E ≤ LinearMap.range g := fun y hy => ⟨q ⟨y,hy⟩, hg _⟩
  have good : essential S (LinearMap.range g) := by
    refine ⟨hE.prop.1.trans contains, ?_⟩
    rintro x ⟨t,rfl⟩ hgt
    have ht : t ≠ 0 := fun he => hgt (he ▸ g.map_zero)
    obtain ⟨r, hr, y, he⟩ := quotient_essential E N hN t ht
    have e' : r • g t = y.val := (g.map_smul r t).symm.trans ((congrArg g he.symm).trans (hg y))
    have hy : y.val ≠ 0 := fun h => hr (he.symm.trans (by rw [h, map_zero]))
    obtain ⟨s, hsy, hsS⟩ := hE.prop.2 _ y.property hy
    exact ⟨s*r, by rwa [mul_smul,e'], by rwa [mul_smul,e']⟩
  have landing : LinearMap.range g ≤ E := hE.le_of_ge good contains
  let ret := (g.comp N.mkQ).codRestrict E (fun x => landing (LinearMap.mem_range_self _ _))
  have retract (x : E) : ret x.val = x := Subtype.ext (hg x)
  have injE : Module.Injective R E := by
    constructor
    intro A B _ _ _ _ i hi f
    obtain ⟨t, ht⟩ := injD.out i hi (E.subtype.comp f)
    exact ⟨ret.comp t, fun a => (congrArg ret (ht a)).trans (retract (f a))⟩
  let e := j.codRestrict E (fun a => hE.prop.1 (LinearMap.mem_range_self _ a))
  refine ⟨ModuleCat.of R E, e, injE, fun _ _ h => hj (congrArg Subtype.val h),
    mk_le_of_injective (f := fun x : E => (x : D)) Subtype.val_injective, ?_⟩
  intro x hx
  obtain ⟨r, hr, a, ha⟩ := hE.prop.2 x.val x.property (fun h => hx (Subtype.ext h))
  exact ⟨r, fun h => hr (congrArg (fun z : E => (z : D)) h), ⟨a, Subtype.ext ha⟩⟩

end PureEmbeddings.DedekindEnvelope
