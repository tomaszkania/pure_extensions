import PureEmbeddings.DedekindMinimum
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Localization.Cardinality

/-! Independent cardinal invariants for the divisible socles. -/
noncomputable section
namespace PureEmbeddings.DedekindMultiplicity
open Cardinal Function
open scoped Cardinal nonZeroDivisors
universe u
variable {R : Type u} [CommRing R] [IsDomain R]

abbrev Maximals (R : Type u) [CommRing R] := {p : Ideal R // p.IsMaximal}
instance (p : Maximals R) : p.val.IsMaximal := p.property
abbrev Residues (ranks : Maximals R → Cardinal.{u}) :=
  (p : Maximals R) → (ranks p).out →₀ R ⧸ p.val
abbrev TorsionResidues (ranks : Maximals R → Cardinal.{u}) :=
  Submodule.torsion R (Residues ranks)

variable {ranks : Maximals R → Cardinal.{u}}

theorem residues_bound {μ τ : Cardinal.{u}} (hμ : μ ^ τ = μ) (hP : #(Maximals R) ≤ τ)
    (hR : #R ≤ μ) (hω : ∀ p, ℵ₀ ≤ ranks p) (h : ∀ p, ranks p ≤ μ) :
    #(TorsionResidues ranks) ≤ μ := by
  classical
  have each (p : Maximals R) : #((ranks p).out →₀ R ⧸ p.val) ≤ μ := by
    letI : Infinite (ranks p).out := aleph0_le_mk_iff.mp (by simpa using hω p)
    rw [mk_finsupp_of_infinite, mk_out]
    exact max_le (h p) ((mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := p.val))).trans hR)
  let code (p : Maximals R) : ((ranks p).out →₀ R ⧸ p.val) ↪ μ.out :=
    Classical.choice (Cardinal.lift_mk_le'.mp (by simpa using each p))
  have injection : Injective (fun v : TorsionResidues ranks => fun p => code p (v.val p)) := by
    intro a b e
    exact Subtype.ext (funext fun p => (code p).injective (congrFun e p))
  apply (Cardinal.mk_le_of_injective injection).trans
  simp only [Cardinal.mk_arrow,Cardinal.lift_id,Cardinal.mk_out]
  exact (Cardinal.power_le_power_left (lt_of_lt_of_le (pos_iff_ne_zero.mpr (mk_ne_zero R)) hR).ne' hP).trans hμ.le

/-- Essential extensions of torsion modules over a domain are torsion. -/
theorem essential_torsion {X E : ModuleCat.{u} R} (i : X →ₗ[R] E) (ht : Module.IsTorsion R X)
    (ess : ∀ y : E, y ≠ 0 → ∃ r : R, r • y ≠ 0 ∧ r • y ∈ LinearMap.range i) :
    Module.IsTorsion R E := by
  intro x
  by_cases hx : x = 0
  · exact ⟨1,by simp [hx]⟩
  obtain ⟨r,hr,y,hy⟩ := ess x hx
  obtain ⟨s,hs⟩ := @ht y
  have hr' : r ≠ 0 := fun e => hr (by simp [e])
  refine ⟨s * (⟨r,mem_nonZeroDivisors_of_ne_zero hr'⟩ : R⁰), ?_⟩
  change ((s:R)*r) • x = 0
  rw [mul_smul, ← hy, ← map_smul]
  change (s:R) • y = 0 at hs
  rw [hs,map_zero]

omit [IsDomain R] in
/-- A cyclic p-annihilated submodule is simple; in an essential extension
it lies entirely in the original submodule. -/
theorem essential_killed {X E : ModuleCat.{u} R} (i : X →ₗ[R] E) (p : Maximals R)
    (ess : ∀ y : E, y ≠ 0 → ∃ r : R, r • y ≠ 0 ∧ r • y ∈ LinearMap.range i)
    (y : ResidueUpper.killed p.val E) : y.val ∈ LinearMap.range i := by
  classical
  letI := Ideal.Quotient.field p.val
  by_cases hy : y.val = 0
  · rw [hy]; exact Submodule.zero_mem _
  obtain ⟨r,hr,hmem⟩ := ess y.val hy
  have hq : Ideal.Quotient.mk p.val r ≠ 0 := fun e => hr (y.property _ (Ideal.Quotient.eq_zero_iff_mem.mp e))
  obtain ⟨s,hs⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk p.val r)⁻¹)
  have ann : s*r-1 ∈ p.val := Ideal.Quotient.eq_zero_iff_mem.mp (by simp [hs,hq])
  have h1 : s • r • y.val = y.val := by
    have hh := y.property (s*r-1) ann
    rw [sub_smul,one_smul,mul_smul,sub_eq_zero] at hh
    exact hh
  exact h1 ▸ (LinearMap.range i).smul_mem s hmem

omit [IsDomain R] in
private theorem annihilated_at {p q : Maximals R} (hne : p ≠ q) (x : TorsionResidues ranks)
    (hx : ∀ r ∈ p.val, r • x = 0) : x.val q = 0 := by
  obtain ⟨a,ha,hv⟩ := DedekindMathlib.separator (J := p.val) (H := q.val) (fun he => hne (Subtype.ext he))
  ext j
  have eqn := congrArg (fun w : TorsionResidues ranks => w.val q j) (hx a ha)
  change (Ideal.Quotient.mk q.val a) * (x.val q j) = 0 at eqn
  simpa [hv] using eqn

omit [IsDomain R] in
/-- The p-annihilated part can be read in the p-coordinate of the original
residue product. -/
theorem killed_card_upper {E : ModuleCat.{u} R}
    (i : TorsionResidues ranks →ₗ[R] E) (hi : Injective i)
    (ess : ∀ y : E, y ≠ 0 → ∃ r : R, r • y ≠ 0 ∧ r • y ∈ LinearMap.range i)
    (p : Maximals R) (hω : ℵ₀ ≤ ranks p) (hR : #R ≤ ranks p) :
    #(ResidueUpper.killed p.val E) ≤ ranks p := by
  classical
  let X := ModuleCat.of R (TorsionResidues ranks)
  choose pre hpre using essential_killed (X := X) i p ess
  have hpreKill (v : ResidueUpper.killed p.val E) (r : R) (hr : r ∈ p.val) :
      r • pre v = 0 := hi (by rw [map_smul,hpre,v.property r hr,map_zero])
  let read (v : ResidueUpper.killed p.val E) := (pre v).val p
  have inj : Injective read := by
    intro v w he
    have eqp : pre v = pre w := by
      apply Subtype.ext; funext q
      by_cases eqn : q = p
      · subst q; exact he
      · rw [annihilated_at (Ne.symm eqn) _ (hpreKill v),annihilated_at (Ne.symm eqn) _ (hpreKill w)]
    exact Subtype.ext ((hpre v).symm.trans ((congrArg i eqp).trans (hpre w)))
  apply (Cardinal.mk_le_of_injective inj).trans
  haveI : Infinite (ranks p).out := aleph0_le_mk_iff.mp (by simpa using hω)
  rw [mk_finsupp_of_infinite,mk_out]
  exact max_le le_rfl ((mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := p.val))).trans hR)

/-- The original p-coordinate supplies the matching independent residue
vectors, even before the essential extension is taken. -/
theorem killed_card_lower {E : ModuleCat.{u} R} (hnf : ¬ IsField R)
    (i : TorsionResidues ranks →ₗ[R] E) (hi : Injective i) (p : Maximals R) :
    ranks p ≤ #(ResidueUpper.killed p.val E) := by
  classical
  let H (t : (ranks p).out) : Residues ranks := Pi.single p (Finsupp.single t (1 : R ⧸ p.val))
  have killed (r : R) (hr : r ∈ p.val) (t : (ranks p).out) : r • H t = 0 := by
    funext q
    by_cases eqn : q = p
    · subst q
      ext j
      change Ideal.Quotient.mk p.val r * ((H t) p j) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
    · change r • (H t q) = (0 : (ranks q).out →₀ R ⧸ q.val)
      simp [H,Pi.single_eq_of_ne eqn]
  obtain ⟨a,ha,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ring.ne_bot_of_isMaximal_of_not_isField p.property hnf)
  let v (t : (ranks p).out) : TorsionResidues ranks :=
    ⟨H t, ⟨⟨a,mem_nonZeroDivisors_of_ne_zero hn⟩,killed a ha t⟩⟩
  let f (t : (ranks p).out) : ResidueUpper.killed p.val E :=
    ⟨i (v t), fun r hr => by rw [← map_smul, show r • v t = 0 from Subtype.ext (killed r hr t),map_zero]⟩
  have inj : Injective f := by
    intro t s eqn
    have hv : v t = v s := hi (congrArg Subtype.val eqn)
    have eq1 := congrArg (fun w : TorsionResidues ranks => w.val p) hv
    have e : Finsupp.single t (1 : R ⧸ p.val) = Finsupp.single s 1 := by simpa [v,H] using eq1
    by_contra h
    simpa [Finsupp.single_apply,h,Ne.symm h] using (congrArg (fun z : (ranks p).out →₀ R ⧸ p.val => z t) e)
  simpa using Cardinal.mk_le_of_injective inj

end PureEmbeddings.DedekindMultiplicity
