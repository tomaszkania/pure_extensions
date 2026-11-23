import Std

/-! The separating family for a valuation domain, proved on the quotient
of its maximal ideal by the submodule a²m.  We state the ring laws used
in the proof explicitly so that the file needs no external algebra library.
The local ring and divisibility hypotheses are used only in the final two
theorems; the three membership calculations apply more generally. -/

namespace PureEmbeddings.Valuation

universe u v

/-- Ring operations are supplied by Lean's standard notation classes.
The predicate `inMax` denotes a proper ideal.  The last two fields express
that elements outside it are units and that divisibility is total. -/
structure DomainLaws (R : Type u) [Add R] [Mul R] [Neg R] [OfNat R 0] [OfNat R 1] where
  add_assoc : ∀ x y z : R, (x + y) + z = x + (y + z)
  add_zero : ∀ x : R, x + 0 = x
  zero_add : ∀ x : R, 0 + x = x
  add_neg : ∀ x : R, x + (-x) = 0
  mul_comm : ∀ x y : R, x * y = y * x
  mul_assoc : ∀ x y z : R, (x * y) * z = x * (y * z)
  mul_one : ∀ x : R, x * 1 = x
  mul_zero : ∀ x : R, x * 0 = 0
  mul_add : ∀ x y z : R, x * (y + z) = x * y + x * z
  cancel : ∀ {x y z : R}, x ≠ 0 → x * y = x * z → y = z
  inMax : R → Prop
  zero_mem : inMax 0
  one_not_mem : ¬ inMax 1
  add_mem : ∀ {x y : R}, inMax x → inMax y → inMax (x + y)
  neg_mem : ∀ {x : R}, inMax x → inMax (-x)
  mul_mem : ∀ (x : R) {y : R}, inMax y → inMax (x * y)
  inverse_of_outside : ∀ {x : R}, ¬ inMax x → ∃ y : R, x * y = 1
  divides_total : ∀ x y : R, (∃ d : R, y = x * d) ∨ (∃ d : R, x = y * d)

namespace DomainLaws

variable {R : Type u} [Add R] [Mul R] [Neg R] [OfNat R 0] [OfNat R 1]
variable (V : DomainLaws R)

/-- Congruence of representatives modulo a²m. -/
def Congruent (a x y : R) : Prop :=
  ∃ d : R, V.inMax d ∧ x = y + (a * a) * d

theorem congruent_refl (a x : R) : V.Congruent a x x := by
  exact ⟨0, V.zero_mem, by rw [V.mul_zero, V.add_zero]⟩

theorem congruent_symm {a x y : R} (h : V.Congruent a x y) :
    V.Congruent a y x := by
  obtain ⟨d, hd, eqn⟩ := h
  refine ⟨-d, V.neg_mem hd, ?_⟩
  symm
  calc
    x + (a * a) * (-d) = (y + (a * a) * d) + (a * a) * (-d) := by rw [eqn]
    _ = y + (a * a) * (d + (-d)) := by rw [V.add_assoc, V.mul_add]
    _ = y := by rw [V.add_neg, V.mul_zero, V.add_zero]

theorem congruent_trans {a x y z : R} (h : V.Congruent a x y)
    (k : V.Congruent a y z) : V.Congruent a x z := by
  obtain ⟨b, hb, eqn⟩ := h
  obtain ⟨c, hc, eqn'⟩ := k
  refine ⟨c + b, V.add_mem hc hb, ?_⟩
  calc
    x = y + (a * a) * b := eqn
    _ = (z + (a * a) * c) + (a * a) * b := by rw [eqn']
    _ = z + (a * a) * (c + b) := by rw [V.add_assoc, V.mul_add]

/-- The congruence restricted to the maximal ideal. -/
def layerSetoid (a : R) : Setoid {x : R // V.inMax x} where
  r x y := V.Congruent a x.val y.val
  iseqv := ⟨fun x => V.congruent_refl a x.val,
    fun h => V.congruent_symm h, fun h k => V.congruent_trans h k⟩

/-- The quotient C_a = m / a²m. -/
def Layer (a : R) := Quotient (V.layerSetoid a)

def residue (a x : R) (hx : V.inMax x) : V.Layer a :=
  Quotient.mk (V.layerSetoid a) ⟨x, hx⟩

theorem residue_eq_iff (a x y : R) (hx : V.inMax x) (hy : V.inMax y) :
    V.residue a x hx = V.residue a y hy ↔ V.Congruent a x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem residue_eq_of_eq (a x y : R) (hx : V.inMax x) (hy : V.inMax y)
    (h : x = y) : V.residue a x hx = V.residue a y hy := by
  cases h
  rfl

/-- On C_a, a class lies in t C_a + Ann(t) if it has a representative
of the form t y + z, modulo a²m, with t z zero modulo a²m. -/
def Mixed (a t : R) (x : V.Layer a) : Prop :=
  ∃ (y z : R) (hy : V.inMax y) (hz : V.inMax z),
    x = V.residue a (t * y + z) (V.add_mem (V.mul_mem t hy) hz) ∧
    V.residue a (t * z) (V.mul_mem t hz) = V.residue a 0 V.zero_mem

/-- At its own value, the distinguished class a is outside the sum. -/
theorem misses_own (a : R) (ha : V.inMax a) (hne : a ≠ 0) :
    ¬ V.Mixed a a (V.residue a a ha) := by
  intro h
  obtain ⟨y, z, hy, hz, hsum, hann⟩ := h
  obtain ⟨d, hd, hrep⟩ := (V.residue_eq_iff _ _ _ _ _).mp hsum
  obtain ⟨w, hw, hzero⟩ := (V.residue_eq_iff _ _ _ _ _).mp hann
  have hz' : z = a * w := V.cancel hne (by
    calc
      a * z = 0 + (a * a) * w := hzero
      _ = a * (a * w) := by rw [V.zero_add, V.mul_assoc])
  have hone : (1 : R) = (y + w) + a * d := V.cancel hne (by
    calc
      a * 1 = a := V.mul_one _
      _ = (a * y + z) + (a * a) * d := hrep
      _ = (a * y + a * w) + a * (a * d) := by rw [hz', V.mul_assoc a a d]
      _ = a * ((y + w) + a * d) := by rw [V.mul_add a (y + w), V.mul_add a y w])
  apply V.one_not_mem
  rw [hone]
  exact V.add_mem (V.add_mem hy hw) (V.mul_mem _ hd)

/-- If a/t belongs to m, the distinguished class is itself a multiple of t. -/
theorem hits_divisor (a t d : R) (ha : V.inMax a) (hd : V.inMax d)
    (h : a = t * d) : V.Mixed a t (V.residue a a ha) := by
  refine ⟨d, 0, hd, V.zero_mem, ?_, ?_⟩
  · apply V.residue_eq_of_eq
    rw [V.add_zero]
    exact h
  · apply V.residue_eq_of_eq
    exact V.mul_zero t

/-- If t/a belongs to m, the distinguished class is annihilated by t. -/
theorem hits_multiple (a t d : R) (ha : V.inMax a) (hd : V.inMax d)
    (h : t = a * d) : V.Mixed a t (V.residue a a ha) := by
  refine ⟨0, a, V.zero_mem, ha, ?_, ?_⟩
  · apply V.residue_eq_of_eq
    rw [V.mul_zero, V.zero_add]
  · apply (V.residue_eq_iff _ _ _ _ _).mpr
    refine ⟨d, hd, ?_⟩
    calc
      t * a = (a * d) * a := by rw [h]
      _ = (a * a) * d := by rw [V.mul_assoc a d a, V.mul_comm d a, ← V.mul_assoc]
      _ = 0 + (a * a) * d := (V.zero_add _).symm

/-- An invertible quotient also gives divisibility in the reverse direction. -/
private theorem reverse_divides {a b d : R} (h : b = a * d) (hd : ¬ V.inMax d) :
    ∃ u : R, a = b * u := by
  obtain ⟨u, hu⟩ := V.inverse_of_outside hd
  refine ⟨u, ?_⟩
  calc
    a = a * 1 := (V.mul_one a).symm
    _ = a * (d * u) := by rw [hu]
    _ = b * u := by rw [h, V.mul_assoc]

/-- Mutual divisibility is equality of values for two nonzero elements. -/
def SameValue (a b : R) : Prop :=
  (∃ d : R, b = a * d) ∧ (∃ d : R, a = b * d)

/-- Distinct principal ideals yield the required alternative automatically. -/
theorem hits_other (a t : R) (ha : V.inMax a) (h : ¬ SameValue a t) :
    V.Mixed a t (V.residue a a ha) := by
  classical
  rcases V.divides_total a t with ⟨d, hd⟩ | ⟨d, hd⟩
  · by_cases hm : V.inMax d
    · exact V.hits_multiple a t d ha hm hd
    · exact False.elim (h ⟨⟨d, hd⟩, V.reverse_divides hd hm⟩)
  · by_cases hm : V.inMax d
    · exact V.hits_divisor a t d ha hm hd
    · exact False.elim (h ⟨V.reverse_divides hd hm, ⟨d, hd⟩⟩)

/-- A family of representatives of distinct positive values gives a class
in each C_a failing exactly the associated one-variable condition. -/
theorem value_separation {I : Type v} (a : I → R)
    (positive : ∀ i, V.inMax (a i)) (nonzero : ∀ i, a i ≠ 0)
    (distinct : ∀ i j, i ≠ j → ¬ SameValue (a i) (a j)) (i j : I) :
    V.Mixed (a i) (a j) (V.residue (a i) (a i) (positive i)) ↔ i ≠ j := by
  constructor
  · intro hm hij
    cases hij
    exact V.misses_own _ (positive i) (nonzero i) hm
  · intro hij
    exact V.hits_other _ _ (positive i) (distinct i j hij)

end DomainLaws
end PureEmbeddings.Valuation
