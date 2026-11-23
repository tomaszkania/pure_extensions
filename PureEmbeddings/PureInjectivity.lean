import PureEmbeddings.RelativeHull
import PureEmbeddings.SmallLifting
import PureEmbeddings.Chains

/-! The extension property forces ordinary algebraic pure-injectivity. -/
namespace PureEmbeddings
open Cardinal

universe u
variable {R : Type u} [Ring R]

/-- It suffices to extend homomorphisms over pure inclusions with target of
size at most the larger of the ring cardinal and the countably infinite
cardinal. We enlarge a partial homomorphism over a pure domain by gluing it
to a homomorphism defined on a small submodule. -/
theorem isPureInjective_of_smallLifts {F : ModuleCat.{u} R}
    (liftSmall : ∀ (U : ModuleCat.{u} R) (A : Submodule R U),
      Cardinal.mk U ≤ max ℵ₀ (Cardinal.mk R) → IsPureMap A.subtype →
      ∀ f : A →ₗ[R] F, ∃ g : U →ₗ[R] F, g.comp A.subtype = f) :
    IsPureInjective F := by
  classical
  intro A B i f hi
  let e : A ≃ₗ[R] LinearMap.range i := LinearEquiv.ofInjective i hi.1
  let start : B →ₗ.[R] F := ⟨LinearMap.range i, f.comp e.symm.toLinearMap⟩
  have hrange : i.comp e.symm.toLinearMap = (LinearMap.range i).subtype :=
    LinearMap.ext fun x => congrArg Subtype.val (e.apply_symm_apply x)
  have hpure : IsPureMap start.domain.subtype := by
    change IsPureMap (LinearMap.range i).subtype
    rw [← hrange]
    exact IsPureMap.comp (A := ModuleCat.of R (LinearMap.range i)) (B := A) (C := B)
      hi (isPureMap_equiv (A := ModuleCat.of R (LinearMap.range i)) (B := A) e.symm)
  let S : Set (B →ₗ.[R] F) := {p | IsPureMap p.domain.subtype}
  obtain ⟨p, hstart, hp⟩ := zorn_le_nonempty₀ S (by
    intro c hc hchain x hx
    have hd := hchain.directedOn
    exact ⟨LinearPMap.sSup c hd, pure_domain_sSup (M := B) (F := F) ⟨x,hx⟩ hd hc,
      fun q hq => LinearPMap.le_sSup hd hq⟩) start hpure
  have total (b : B) : b ∈ p.domain := by
    obtain ⟨U, hb, hU, hInter, hSum⟩ := exists_small_relativeHull p.domain hp.1 b
    let T := p.domain.comap U.subtype
    let incl : T →ₗ[R] p.domain :=
      (U.subtype.comp T.subtype).codRestrict p.domain (fun x => x.property)
    obtain ⟨g, hg⟩ := liftSmall (ModuleCat.of R U) T hU hInter (p.toFun.comp incl)
    let q : B →ₗ.[R] F := ⟨U,g⟩
    have agree (x : p.domain) (y : q.domain) (hxy : (x : B) = y) : p x = q y := by
      let z : T := ⟨y, by
        change (y : B) ∈ p.domain
        rw [← hxy]
        exact x.property⟩
      have hz : incl z = x := Subtype.ext hxy.symm
      exact (congrArg p.toFun hz).symm.trans (DFunLike.congr_fun hg z).symm
    have hsup : p.sup q agree ∈ S := hSum
    exact (hp.2 hsup (p.left_le_sup q agree)).1 ((p.right_le_sup q agree).1 hb)
  let toDom : B →ₗ[R] p.domain := LinearMap.id.codRestrict p.domain total
  refine ⟨p.toFun.comp toDom, LinearMap.ext fun a => ?_⟩
  have hpA : p.toFun (toDom (i a)) = start.toFun (e a) :=
    (@hstart.2 (e a) (toDom (i a)) rfl).symm
  exact hpA.trans (congrArg f (e.symm_apply_apply a))

/-- Algebraic pure-injectivity follows from the embedding extension
property at every cardinal strictly larger than the ring and ℵ₀. -/
theorem HasExtension.pureInjective {κ : Cardinal.{u}} {F : ModuleCat.{u} R}
    (hF : HasExtension κ F) (hk : ℵ₀ < κ) (hR : Cardinal.mk R < κ) :
    IsPureInjective F := by
  apply isPureInjective_of_smallLifts
  intro U A hU hA f
  exact hF.lift_small hk hR A (hU.trans_lt (max_lt hk hR)) hA f

end PureEmbeddings
