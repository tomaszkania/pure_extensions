import PureEmbeddings.Germs
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Zorn

/-! # Failure of pure-semisimplicity supplies a descending chain of matrix subgroups -/
namespace PureEmbeddings.MatrixDCC
open Function Finset Set
open scoped BigOperators
universe u
variable {R : Type u} [Ring R]

structure Code (R : Type u) where
  rows : Nat
  cols : Nat
  lead : Fin rows → R
  coeff : Fin rows → Fin cols → R

/-- One distinguished variable in a finite homogeneous matrix system. -/
def group (c : Code R) (M : Type u) [AddCommGroup M] [Module R M] : AddSubgroup M where
  carrier := {x | ∃ y : Fin c.cols → M, ∀ k, c.lead k • x + ∑ j, c.coeff k j • y j = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨v,hv⟩ ⟨w,hw⟩
    refine ⟨fun j => v j + w j, fun k => ?_⟩
    simp only [smul_add, Finset.sum_add_distrib]
    rw [add_add_add_comm, hv, hw, add_zero]
  neg_mem' := by
    rintro x ⟨v,hv⟩
    exact ⟨fun j => -v j, fun k => by simp [← neg_add, hv]⟩

/-- The subgroup defined by all the systems in a finite list. -/
def groupList (L : List (Code R)) (M : Type u) [AddCommGroup M] [Module R M] : AddSubgroup M :=
  ⨅ c ∈ L, group c M

theorem mem_groupList {L : List (Code R)} {M : Type u} [AddCommGroup M] [Module R M] (x : M) :
    x ∈ groupList L M ↔ ∀ c ∈ L, x ∈ group c M := by simp only [groupList, AddSubgroup.mem_iInf]

end PureEmbeddings.MatrixDCC
