import PureEmbeddings.ModuleTheory
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# The extension property over a division ring

For `κ` uncountable and larger than the scalar ring, a vector space has the
extension property exactly when its dimension is at least `κ`. This gives
the minimum, uniqueness at the minimum, and universality through size `κ`.
-/

namespace PureEmbeddings.Fields

open Cardinal Function Module.Free
universe u
variable {K : Type u} [DivisionRing K]

/-- An injective map of vector spaces has a linear retraction. -/
theorem pure_of_injective {A B : ModuleCat.{u} K} (f : A →ₗ[K] B) (hf : Injective f) :
    IsPureMap f := by
  obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  exact isPureMap_of_retraction f r (fun a => congrArg (fun g : A →ₗ[K] A => g a) hr)

/-- An injection of the basis indices induces an injective linear map. -/
theorem embed_of_rank_le {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (h : Module.rank K V ≤ Module.rank K W) :
    ∃ j : V →ₗ[K] W, Injective j := by
  let v := chooseBasis K V
  let w := chooseBasis K W
  have hι : #(ChooseBasisIndex K V) ≤ #(ChooseBasisIndex K W) := by
    rwa [v.mk_eq_rank'', w.mk_eq_rank'']
  obtain ⟨e⟩ := hι
  let g := Finsupp.lmapDomain K K e
  exact ⟨w.repr.symm.toLinearMap.comp (g.comp v.repr.toLinearMap),
    w.repr.symm.injective.comp ((Finsupp.mapDomain_injective e.injective).comp v.repr.injective)⟩

/-- Extend the map across a complement of `range i`, sending that complement
into a complement of `range f`. -/
theorem extension_of_rank {κ : Cardinal.{u}} {F : ModuleCat.{u} K} (hκ : ℵ₀ ≤ κ)
    (hF : κ ≤ Module.rank K F) : HasExtension κ F := by
  intro A B i f hB hi hf
  obtain ⟨V, hV⟩ := (LinearMap.range i).exists_isCompl
  obtain ⟨W, hW⟩ := (LinearMap.range f).exists_isCompl
  let b := Submodule.prodEquivOfIsCompl _ _ hV
  let c := Submodule.prodEquivOfIsCompl _ _ hW
  have hA : Module.rank K A < κ := (rank_le_card K A).trans_lt ((mk_le_of_injective hi.1).trans_lt hB)
  have hlarge : κ ≤ Module.rank K W := by
    by_contra! hw
    have hrs := c.rank_eq
    rw [rank_prod', rank_range_of_injective f hf.1] at hrs
    exact (not_lt_of_ge hF) (hrs ▸ add_lt_of_lt hκ hA hw)
  have hsmall : Module.rank K V < κ := (rank_le_card K V).trans_lt
    ((mk_le_of_injective (f := fun x : V => (x : B)) Subtype.val_injective).trans_lt hB)
  obtain ⟨j, hj⟩ := embed_of_rank_le (hsmall.le.trans hlarge)
  let a := (LinearEquiv.ofInjective i hi.1).symm.trans (LinearEquiv.ofInjective f hf.1)
  let g := c.toLinearMap.comp ((a.toLinearMap.prodMap j).comp b.symm.toLinearMap)
  have hprod : Injective (a.toLinearMap.prodMap j) := a.injective.prodMap hj
  refine ⟨g, pure_of_injective g (c.injective.comp (hprod.comp b.symm.injective)), ?_⟩
  ext x
  have hb : b.symm (i x) = ((LinearEquiv.ofInjective i hi.1) x, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left (LinearMap.range i) V hV
      ((LinearEquiv.ofInjective i hi.1) x)
  change c ((a.toLinearMap.prodMap j) (b.symm (i x))) = f x
  rw [hb]
  simp [a, c, LinearMap.prodMap_apply]

/-- A vector space of small dimension over a small division ring has small cardinality. -/
theorem mk_lt_of_rank_lt {V : Type u} [AddCommGroup V] [Module K V]
    {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hK : #K < κ) (hv : Module.rank K V < κ) : #V < κ := by
  classical
  let b := chooseBasis K V
  let T := ChooseBasisIndex K V × K
  have ht : #T < κ := by
    simpa only [T, mk_prod, lift_id, b.mk_eq_rank''] using mul_lt_of_lt hκ.le hv hK
  calc
    #V = #(ChooseBasisIndex K V →₀ K) := b.repr.toEquiv.cardinal_eq
    _ ≤ #(Finset T) := mk_le_of_injective (Finsupp.graph_injective _ _)
    _ ≤ #(List T) := mk_le_of_surjective List.toFinset_surjective
    _ ≤ max ℵ₀ #T := mk_list_le_max T
    _ < κ := max_lt hκ ht

/-- Full characterisation; regularity of `κ` is immaterial. -/
theorem extension_iff_rank {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hK : #K < κ)
    (F : ModuleCat.{u} K) : HasExtension κ F ↔ κ ≤ Module.rank K F := by
  constructor
  · intro hF
    by_contra! h
    exact (not_lt_of_ge (hF.lower hκ.le hK)) (mk_lt_of_rank_lt hκ hK h)
  · exact extension_of_rank hκ.le

/-- A free vector space on `κ` basis vectors attains the minimum size. -/
theorem hasMinimum {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hK : #K < κ) :
    HasMinimum (R := K) κ κ := by
  let F := ModuleCat.of K (κ.out →₀ K)
  have hI : Infinite κ.out := aleph0_le_mk_iff.mp (by simpa using hκ.le)
  have hr : Module.rank K F = κ := by change Module.rank K (κ.out →₀ K) = κ; simp
  have hs : #F = κ := by
    change #(κ.out →₀ K) = κ
    rw [mk_finsupp_of_infinite, mk_out, max_eq_left hK.le]
  exact ⟨⟨F, extension_of_rank hκ.le hr.ge, hs⟩, fun _ h => h.lower hκ.le hK⟩

/-- Any two spaces of minimum size with the extension property are isomorphic. -/
theorem uniqueAt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hK : #K < κ) : UniqueAt (R := K) κ κ := by
  intro F G hF hG sF sG
  have dim (V : ModuleCat.{u} K) (h : HasExtension κ V) (s : #V = κ) :
      Module.rank K V = κ := le_antisymm ((rank_le_card K V).trans s.le)
        ((extension_iff_rank hκ hK V).mp h)
  exact nonempty_linearEquiv_of_rank_eq ((dim F hF sF).trans (dim G hG sG).symm)

/-- The copy of any space of size at most `κ` can be chosen pure. -/
theorem universal_le {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hK : #K < κ)
    {F : ModuleCat.{u} K} (hF : HasExtension κ F) (V : ModuleCat.{u} K) (hV : #V ≤ κ) :
    ∃ j : V →ₗ[K] F, IsPureMap j := by
  obtain ⟨j, hj⟩ := embed_of_rank_le (K := K)
    ((rank_le_card K V).trans (hV.trans ((extension_iff_rank hκ hK F).mp hF)))
  exact ⟨j, pure_of_injective j hj⟩

end PureEmbeddings.Fields
