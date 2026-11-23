import PureEmbeddings.ModuleTheory
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Data.Finset.Order

/-! Directed unions of compatible pure linear embeddings, including singular limits. -/
namespace PureEmbeddings
open Cardinal
universe u
variable {R : Type u} [Ring R]

theorem pure_of_finite_lifts {A F : ModuleCat.{u} R} (f : A →ₗ[R] F)
    (loc : ∀ s : Finset A, ∃ (D : ModuleCat.{u} R) (h : D →ₗ[R] A),
      (∀ x ∈ s, x ∈ LinearMap.range h) ∧ IsPureMap (f.comp h)) : IsPureMap f := by
  classical
  constructor
  · intro x y hxy
    obtain ⟨D, h, hs, hf⟩ := loc {x, y}
    obtain ⟨a, rfl⟩ := hs x (by simp)
    obtain ⟨b, rfl⟩ := hs y (by simp)
    exact congrArg h (hf.1 (show f (h a) = f (h b) from hxy))
  · intro m n r a sol
    obtain ⟨D, h, hs, hf⟩ := loc (Finset.univ.image a)
    have hl (i : Fin m) : ∃ d : D, h d = a i := hs (a i) (by simp)
    choose d hd using hl
    have hc : (f.comp h) ∘ d = f ∘ a := funext fun i => congrArg f (hd i)
    have hs' := (hf.2 r d (hc ▸ sol)).map h
    exact (show h ∘ d = a from funext hd) ▸ hs'

theorem pure_of_locally_comp {A F : ModuleCat.{u} R} (f : A →ₗ[R] F)
    (loc : ∀ s : Finset A, ∃ D : Submodule R A, (∀ x ∈ s, x ∈ D) ∧
      IsPureMap (f.comp D.subtype)) : IsPureMap f := by
  apply pure_of_finite_lifts f
  intro s
  obtain ⟨D, hs, hd⟩ := loc s
  exact ⟨ModuleCat.of R D, D.subtype, fun x hx => ⟨⟨x, hs x hx⟩, rfl⟩, hd⟩

/-- In a directed union of partial maps, every finite set in the domain
already lies in the domain of a single member. -/
theorem finite_in_stage {M F : ModuleCat.{u} R} {c : Set (M →ₗ.[R] F)}
    (hc : c.Nonempty) (hd : DirectedOn (· ≤ ·) c)
    (s : Finset (LinearPMap.sSup c hd).domain) :
    ∃ p ∈ c, ∀ x ∈ s, (x : M) ∈ p.domain := by
  classical
  induction s using Finset.induction_on with
  | empty => obtain ⟨p, hp⟩ := hc; exact ⟨p, hp, by simp⟩
  | insert x s _ ih =>
    obtain ⟨p, hp, hs⟩ := ih
    obtain ⟨q, hq, hx⟩ := (LinearPMap.mem_domain_sSup_iff hc hd).1 x.property
    obtain ⟨t, ht, hpt, hqt⟩ := hd p hp q hq
    refine ⟨t, ht, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hqt.1 hx
    · exact hpt.1 (hs y hy)

/-- Purity is preserved when taking the union of a directed family of pure maps. -/
theorem pure_sSup {M F : ModuleCat.{u} R} {c : Set (M →ₗ.[R] F)}
    (hc : c.Nonempty) (hd : DirectedOn (· ≤ ·) c)
    (hp : ∀ p ∈ c, IsPureMap p.toFun) :
    IsPureMap (LinearPMap.sSup c hd).toFun := by
  let t := LinearPMap.sSup c hd
  apply pure_of_finite_lifts (A := ModuleCat.of R t.domain) (F := F) t.toFun
  intro s
  obtain ⟨p, hpc, hs⟩ := finite_in_stage hc hd s
  let h := Submodule.inclusion (LinearPMap.le_sSup hd hpc).1
  have he : t.toFun.comp h = p.toFun := LinearMap.ext fun x =>
    LinearPMap.sSup_apply hd hpc x
  refine ⟨ModuleCat.of R p.domain, h, fun x hx => ⟨⟨x, hs x hx⟩, rfl⟩, he ▸ hp p hpc⟩

theorem pure_domain_sSup {M F : ModuleCat.{u} R} {c : Set (M →ₗ.[R] F)}
    (hc : c.Nonempty) (hd : DirectedOn (· ≤ ·) c)
    (hp : ∀ p ∈ c, IsPureMap p.domain.subtype) :
    IsPureMap (LinearPMap.sSup c hd).domain.subtype := by
  let t := LinearPMap.sSup c hd
  apply pure_of_finite_lifts (A := ModuleCat.of R t.domain) (F := M) t.domain.subtype
  intro s
  obtain ⟨p, hpc, hs⟩ := finite_in_stage hc hd s
  let h := Submodule.inclusion (LinearPMap.le_sSup hd hpc).1
  exact ⟨ModuleCat.of R p.domain, h, fun x hx => ⟨⟨x, hs x hx⟩, rfl⟩, hp p hpc⟩

/-- If both maps into an ambient module are pure, the smaller submodule is
pure in every intermediate submodule. Only the purity of the smaller is needed. -/
theorem pure_inclusion_of_subtype {M : ModuleCat.{u} R} {A B : Submodule R M}
    (h : A ≤ B) (hp : IsPureMap A.subtype) : IsPureMap (Submodule.inclusion h) := by
  refine ⟨Submodule.inclusion_injective h, fun r a hs => ?_⟩
  exact hp.2 r a (hs.map B.subtype)


/-- Universality across a linearly ordered cover by small pure submodules.
The cover need not be continuous, and κ need not be regular. -/
theorem HasExtension.universal_of_chain {κ : Cardinal.{u}} {M F : ModuleCat.{u} R}
    (hF : HasExtension κ F) {I : Type u} [LinearOrder I]
    (H : I → Submodule R M) (monoH : Monotone H)
    (cover : ∀ x : M, ∃ j, x ∈ H j) (small : ∀ j, Cardinal.mk (H j) < κ)
    (pureH : ∀ j, IsPureMap (H j).subtype) :
    ∃ f : M →ₗ[R] F, IsPureMap f := by
  classical
  let S : Set (M →ₗ.[R] F) := {p | IsPureMap p.toFun ∧ IsPureMap p.domain.subtype ∧
    ∀ j, p.domain ≤ H j ∨ H j ≤ p.domain}
  let b : M →ₗ.[R] F := ⟨⊥, 0⟩
  have hb : b ∈ S := by
    refine ⟨isPureMap_from_subsingleton (A := ModuleCat.of R (⊥ : Submodule R M)) (B := F) _,
      isPureMap_from_subsingleton (A := ModuleCat.of R (⊥ : Submodule R M)) (B := M) _,
      fun _ => Or.inl bot_le⟩
  obtain ⟨p, _, hp⟩ := zorn_le_nonempty₀ S (by
    intro c hc hchain y hy
    have hd := hchain.directedOn
    have hne : c.Nonempty := ⟨y, hy⟩
    let t := LinearPMap.sSup c hd
    refine ⟨t, ⟨pure_sSup hne hd (fun q hq => (hc hq).1),
      pure_domain_sSup hne hd (fun q hq => (hc hq).2.1), ?_⟩,
      fun q hq => LinearPMap.le_sSup hd hq⟩
    intro j
    by_cases hall : ∀ q ∈ c, q.domain ≤ H j
    · exact Or.inl (sSup_le (by rintro _ ⟨q, hq, rfl⟩; exact hall q hq))
    · push_neg at hall
      obtain ⟨q, hq, hqj⟩ := hall
      exact Or.inr (((hc hq).2.2 j).resolve_left hqj |>.trans (LinearPMap.le_sSup hd hq).1)) b hb
  have hdom : ∀ x : M, x ∈ p.domain := by
    intro x
    obtain ⟨j, hx⟩ := cover x
    rcases hp.1.2.2 j with hpj | hjp
    · let i := Submodule.inclusion hpj
      obtain ⟨g, hg, he⟩ := hF (ModuleCat.of R p.domain) (ModuleCat.of R (H j))
        i p.toFun (small j) (pure_inclusion_of_subtype (M := M) hpj hp.1.2.1) hp.1.1
      let q : M →ₗ.[R] F := ⟨H j, g⟩
      have hq : q ∈ S := ⟨hg, pureH j, fun k =>
        (le_total j k).imp (fun h => monoH h) (fun h => monoH h)⟩
      have hpq : p ≤ q := by
        refine ⟨hpj, ?_⟩
        intro a b hab
        have hd : i a = b := Subtype.ext hab
        exact (congrArg (fun l : p.domain →ₗ[R] F => l a) he).symm.trans (congrArg g hd)
      exact (hp.2 hq hpq).1 hx
    · exact hjp hx
  let fromM : M →ₗ[R] p.domain := LinearMap.codRestrict _ LinearMap.id hdom
  have he : IsPureMap fromM := isPureMap_of_retraction (A := M) (B := ModuleCat.of R p.domain)
    fromM p.domain.subtype (fun _ => rfl)
  exact ⟨p.toFun.comp fromM, IsPureMap.comp (A := M) (B := ModuleCat.of R p.domain)
    (C := F) hp.1.1 he⟩

end PureEmbeddings
