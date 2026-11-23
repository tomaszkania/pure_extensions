import PureEmbeddings.MatrixDCC
import PureEmbeddings.PureInjectivity
import PureEmbeddings.Universality
import PureEmbeddings.BranchingMathlib
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# The countable branching lower bound over an arbitrary ring

A strict chain on any module is witnessed in a small pure submodule. Copies
of its witnesses in a direct sum provide κ disjoint children at each level.
The reduced-power retraction fills each branch in the extension module.
-/
namespace PureEmbeddings.GeneralLower
open Cardinal Function Filter MatrixDCC
open scoped BigOperators

universe u
variable {R : Type u} [Ring R]
variable {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

theorem map_group (c : Code R) (f : A →ₗ[R] B) {x : A} (hx : x ∈ group c A) :
    f x ∈ group c B := by
  obtain ⟨y,hy⟩ := hx
  exact ⟨f ∘ y, fun i => by simpa [map_sum,Function.comp_def] using congrArg f (hy i)⟩

theorem reflect_group (c : Code R) (f : A →ₗ[R] B) (hp : IsPureMap f)
    {x : A} (hx : f x ∈ group c B) : x ∈ group c A := by
  obtain ⟨y,hy⟩ := hx
  let a : Fin c.rows → A := fun i => -(c.lead i • x)
  have hs : Soluble c.coeff (f ∘ a) :=
    ⟨y, fun i => by simpa [Function.comp_def,a] using eq_neg_of_add_eq_zero_right (hy i)⟩
  obtain ⟨z,hz⟩ := hp.2 _ _ hs
  exact ⟨z, fun i => by rw [hz]; simp [a]⟩

theorem map_groupList (L : List (Code R)) (f : A →ₗ[R] B) {x : A} (hx : x ∈ groupList L A) :
    f x ∈ groupList L B := (mem_groupList _).2 fun c hc => map_group c f ((mem_groupList _).1 hx c hc)

theorem reflect_groupList (L : List (Code R)) (f : A →ₗ[R] B) (hp : IsPureMap f)
    {x : A} (hx : f x ∈ groupList L B) : x ∈ groupList L A :=
  (mem_groupList _).2 fun c hc => reflect_group c f hp ((mem_groupList _).1 hx c hc)

/-- Compactness for cosets cut out by arbitrary finite lists of finite matrix
systems. The finite choices are turned into a single element of a reduced
power, then a retraction brings it back to the original module. -/
theorem countable_compact {F : ModuleCat.{u} R} (hinj : IsPureInjective F)
    (L : ℕ → List (Code R)) : Branching.CompactCosets (fun n => groupList (L n) F) := by
  classical
  intro b localSol
  let Q := Finset (ULift.{u} ℕ)
  let l := (atTop : Filter Q)
  let d : F →ₗ[R] Germ l F := Germs.diagonal l
  obtain ⟨ret,hr⟩ := hinj F (ModuleCat.of R (Germ l F)) d LinearMap.id (Germs.diagonal_pure l)
  choose s hs using fun q : Q => localSol (q.image ULift.down)
  let X : Germ l F := Germ.ofFun s
  refine ⟨ret X, fun i => ?_⟩
  have mem : X - d (b i) ∈ groupList (L i) (Germ l F) := by
    apply (mem_groupList _).2
    intro c hc
    let y : Q → F := fun q => if ULift.up i ∈ q then s q - b i else 0
    have good (q : Q) : y q ∈ group c F := by
      by_cases h : ULift.up i ∈ q
      · rw [show y q = s q - b i from if_pos h]
        exact (mem_groupList _).1 (hs q i
          (Finset.mem_image.mpr ⟨ULift.up i,h,rfl⟩)) c hc
      · simp [y,h]
    have solutions (q : Q) : ∃ v : Fin c.cols → F,
        ∀ k, c.lead k • y q + ∑ j, c.coeff k j • v j = 0 := good q
    choose v hv using solutions
    have hy : y ∈ group c (Q → F) :=
      ⟨fun j q => v q j, fun k => funext (fun q => by
        simpa only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,Pi.zero_apply] using hv q k)⟩
    have he : Germs.ofFunLinear (R := R) l y = X - d (b i) := by
      change Germ.ofFun y = Germ.ofFun (fun q => s q - b i)
      apply Germ.coe_eq.mpr
      apply (eventually_ge_atTop ({ULift.up i} : Q)).mono
      intro q h
      exact if_pos (h (Finset.mem_singleton_self _))
    exact he ▸ map_group c (Germs.ofFunLinear l) hy
  have hret : ret (d (b i)) = b i := LinearMap.congr_fun hr (b i)
  simpa only [map_sub,hret] using map_groupList (L i) ret mem

/-- Each strict descent in the list of matrix conditions gives κ choices. -/
theorem bound_of_strict_chain (κ : Cardinal.{u}) (hk : ℵ₀ < κ) (hR : Cardinal.mk R < κ)
    (F M : ModuleCat.{u} R) (hF : HasExtension κ F) (codes : ℕ → Code R)
    (chain : ∀ n, groupList ((List.range (n+1)).map codes) M < groupList ((List.range n).map codes) M) :
    κ ^ ℵ₀ ≤ Cardinal.mk F := by
  classical
  let L (n : ℕ) := (List.range n).map codes
  have witness (n : ℕ) : ∃ a : M, a ∈ groupList (L n) M ∧ a ∉ groupList (L (n+1)) M := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using (not_le_of_gt (chain n))
  choose a ha ht using witness
  obtain ⟨W,contains,pureW,sizeW⟩ := exists_small_pureHull (R := R) (Set.range a)
  let w (n : ℕ) : W := ⟨a n,contains ⟨n,rfl⟩⟩
  have hw (n : ℕ) : w n ∈ groupList (L n) W := reflect_groupList _ W.subtype pureW (ha n)
  have ho (n : ℕ) : w n ∉ groupList (L (n+1)) W := fun h => ht n (map_groupList _ W.subtype h)
  let K := κ.out
  letI : Infinite K := Cardinal.aleph0_le_mk_iff.mp ((Cardinal.mk_out κ).symm ▸ hk.le)
  letI : Countable (Set.range a) := (Set.countable_range a).to_subtype
  have hW : Cardinal.mk W ≤ κ := sizeW.trans (max_le hk.le (max_le hR.le
    ((Cardinal.mk_le_aleph0_iff.mpr (inferInstanceAs (Countable (Set.range a)))).trans hk.le)))
  have hsum : Cardinal.mk (K →₀ W) ≤ κ := by
    calc
      _ ≤ Cardinal.mk (Finset (K × W)) := Cardinal.mk_le_of_injective (Finsupp.graph_injective _ _)
      _ = Cardinal.mk (K × W) := Cardinal.mk_finset_of_infinite _
      _ ≤ κ := by
        rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id,Cardinal.mk_out]
        exact (mul_le_mul' le_rfl hW).trans_eq (Cardinal.mul_eq_self hk.le)
  obtain ⟨f,hf⟩ := hF.universal_le hk hR (ModuleCat.of R (K →₀ W)) hsum
  let entry (n : ℕ) (k : K) : F := f (Finsupp.single k (w n))
  rw [← Cardinal.mk_out κ]
  apply Branching.countableChainCardinalBound (fun n => groupList (L n) F) entry
  · intro n x hx
    apply (mem_groupList _).2
    intro c hc
    apply (mem_groupList _).1 hx c
    simpa [L,List.range_succ] using Or.inl hc
  · intro n k
    exact map_groupList (L n) (f.comp (Finsupp.lsingle k)) (hw n)
  · intro n k t h
    by_contra hne
    have image : f (Finsupp.single k (w n) - Finsupp.single t (w n)) ∈ groupList (L (n+1)) F := by
      simpa only [map_sub,entry] using h
    have hmem := reflect_groupList (L (n+1)) f hf image
    have hproj := map_groupList (L (n+1)) (Finsupp.lapply k : (K →₀ W) →ₗ[R] W) hmem
    exact ho n (by simpa [Finsupp.single_apply,hne,Ne.symm hne] using hproj)
  · exact fun levels => countable_compact (hF.pureInjective hk hR) (fun n => L (levels n))

end PureEmbeddings.GeneralLower
