import PureEmbeddings.Statements
import PureEmbeddings.BackAndForth

/-! Counting a family distinguished by cardinal-valued invariants. All model
indices stay in the universe of the underlying modules. -/
noncomputable section
namespace PureEmbeddings
open Cardinal Function
universe u

/-- One parameter ranges over the cardinals in the interval [κ, μ] for each
index in P, and one further parameter is free. -/
theorem count_models {R : Type u} [Ring R] (P : Type u) (κ μ : Cardinal.{u})
    (hμ : κ < μ)
    (models : ∀ (T : Type u) (c : T → Cardinal.{u}), (∀ t, κ ≤ c t ∧ c t ≤ μ) →
      ∃ M : (Option P → T) → ModuleCat.{u} R,
        (∀ f, HasExtension κ (M f) ∧ Cardinal.mk (M f) = μ) ∧
        ∀ f g, Nonempty (M f ≃ₗ[R] M g) → ∀ i, c (f i) = c (g i)) :
    ¬ UniqueAt (R := R) κ μ ∧ ∃ I : Type u, Nonempty (I ≃ Set.Icc κ μ) ∧
      ManyAtMinimum (R := R) κ μ (Cardinal.mk I ^ (Cardinal.mk P + 1)) := by
  classical
  let I := Shrink.{u} (Set.Icc κ μ)
  let e : I ≃ Set.Icc κ μ := (equivShrink _).symm
  let c (i : I) : Cardinal.{u} := (e i).val
  obtain ⟨M,hM,sep⟩ := models I c (fun i => (e i).property)
  have hc : Injective c := fun _ _ he => e.injective (Subtype.ext he)
  have separate (f g : Option P → I) (hne : f ≠ g) : IsEmpty (M f ≃ₗ[R] M g) :=
    ⟨fun iso => hne (funext (fun i => hc (sep f g ⟨iso⟩ i)))⟩
  have many : ManyAtMinimum (R := R) κ μ (Cardinal.mk I ^ (Cardinal.mk P + 1)) := by
    refine ⟨Option P → I, M, ?_, hM, separate⟩
    simp only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_option]
  refine ⟨?_, I, ⟨e⟩, many⟩
  intro h
  let f (_ : Option P) := e.symm ⟨κ,le_rfl,hμ.le⟩
  let g (_ : Option P) := e.symm ⟨μ,hμ.le,le_rfl⟩
  obtain ⟨t⟩ := h _ _ (hM f).1 (hM g).1 (hM f).2 (hM g).2
  have he := sep f g ⟨t⟩ none
  exact hμ.ne (by simpa [c,f,g] using he)

end PureEmbeddings
