import Std

/-!
# Residues and multiplicities over a Dedekind domain

The first result proves a finite Chinese remainder theorem from pairwise
separators, as supplied by distinct maximal ideals. The second part proves
invariance of the divisible part and of its annihilator subspaces, and the
multiplicity separation argument. The classification and dimension
computations over a Dedekind domain are inputs to the latter argument.
-/

namespace PureEmbeddings.Dedekind

universe u v w z t

/-- The operations and identities used by the elementary Chinese remainder
proof. The residue maps can, for example, be quotient maps to residue fields.
For distinct maximal ideals p,q, comaximality supplies an element congruent
to one modulo p and zero modulo q. -/
structure ResidueOps (P : Type u) (R : Type v) (K : P → Type w) where
  one : R
  add : R → R → R
  mul : R → R → R
  sub : R → R → R
  val : (p : P) → R → K p
  zeroAt : (p : P) → K p
  oneAt : (p : P) → K p
  addAt : (p : P) → K p → K p → K p
  mulAt : (p : P) → K p → K p → K p
  subAt : (p : P) → K p → K p → K p
  mapOne : ∀ p, val p one = oneAt p
  mapAdd : ∀ p x y, val p (add x y) = addAt p (val p x) (val p y)
  mapMul : ∀ p x y, val p (mul x y) = mulAt p (val p x) (val p y)
  mapSub : ∀ p x y, val p (sub x y) = subAt p (val p x) (val p y)
  oneMul : ∀ p x, mulAt p (oneAt p) x = x
  zeroMul : ∀ p x, mulAt p (zeroAt p) x = zeroAt p
  mulZero : ∀ p x, mulAt p x (zeroAt p) = zeroAt p
  zeroAdd : ∀ p x, addAt p (zeroAt p) x = x
  addZero : ∀ p x, addAt p x (zeroAt p) = x
  addSub : ∀ p x y, addAt p x (subAt p y x) = y
/-- Each separator has residues one and zero at its two specified indices. -/
structure Residues (P : Type u) (R : Type v) (K : P → Type w)
    extends ResidueOps P R K where
  separate : P → P → R
  separateLeft : ∀ {p q}, p ≠ q → val p (separate p q) = oneAt p
  separateRight : ∀ {p q}, p ≠ q → val q (separate p q) = zeroAt q

/-- Distinct residue kernels are comaximal if one splits as the sum of
an element of each kernel. -/
def PairwiseComaximal {P R K} (d : ResidueOps P R K) : Prop :=
  ∀ p q, p ≠ q → ∃ a b, d.add a b = d.one ∧
    d.val p a = d.zeroAt p ∧ d.val q b = d.zeroAt q

theorem separator_of_comaximal {P R K} (d : ResidueOps P R K)
    (h : PairwiseComaximal d) {p q : P} (hpq : p ≠ q) :
    ∃ s, d.val p s = d.oneAt p ∧ d.val q s = d.zeroAt q := by
  obtain ⟨a, b, hab, ha, hb⟩ := h p q hpq
  refine ⟨b, ?_, hb⟩
  have he := congrArg (d.val p) hab
  simpa only [d.mapAdd, ha, d.zeroAdd, d.mapOne] using he

noncomputable def ResidueOps.withSeparators {P R K} (d : ResidueOps P R K)
    (h : PairwiseComaximal d) : Residues P R K := by
  classical
  let sep (p q : P) := if hpq : p ≠ q then
    Classical.choose (separator_of_comaximal d h hpq) else d.one
  refine ⟨d, sep, ?_, ?_⟩
  · intro p q hpq
    simpa only [sep, dif_pos hpq] using
      (Classical.choose_spec (separator_of_comaximal d h hpq)).1
  · intro p q hpq
    simpa only [sep, dif_pos hpq] using
      (Classical.choose_spec (separator_of_comaximal d h hpq)).2

namespace Residues

variable {P : Type u} {R : Type v} {K : P → Type w}
variable (d : Residues P R K)

/-- A finite product of pairwise separators. Repeating an index is harmless. -/
def selector [DecidableEq P] (p : P) : List P → R
  | [] => d.one
  | q :: qs =>
      if p = q then selector p qs
      else d.mul (d.separate p q) (selector p qs)

theorem selector_here [DecidableEq P] (p : P) (ps : List P) :
    d.val p (d.selector p ps) = d.oneAt p := by
  induction ps with
  | nil => exact d.mapOne p
  | cons q qs ih =>
    by_cases heq : p = q
    · simpa [selector, heq] using ih
    · simp only [selector, if_neg heq, d.mapMul, d.separateLeft heq, d.oneMul, ih]

theorem selector_elsewhere [DecidableEq P] {p q : P} (hpq : p ≠ q)
    (ps : List P) (hm : q ∈ ps) : d.val q (d.selector p ps) = d.zeroAt q := by
  induction ps with
  | nil => simp at hm
  | cons k ks ih =>
    rcases List.mem_cons.mp hm with hq | hq
    · subst k
      simp only [selector, if_neg hpq, d.mapMul, d.separateRight hpq, d.zeroMul]
    · by_cases hpk : p = k
      · simpa [selector, hpk] using ih hq
      · simp only [selector, if_neg hpk, d.mapMul, ih hq, d.mulZero]

/-- Simultaneous finite residue prescription, with no assumption that the
indices in the list are distinct. Targets are given by representatives. -/
theorem finite_prescription [DecidableEq P] (targets : P → R) (ps : List P) :
    ∃ x : R, ∀ p ∈ ps, d.val p x = d.val p (targets p) := by
  induction ps with
  | nil => exact ⟨d.one, by simp⟩
  | cons p ps ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨d.add x (d.mul (d.selector p ps) (d.sub (targets p) x)), ?_⟩
    intro q hq
    by_cases h : p = q
    · subst q
      rw [d.mapAdd, d.mapMul, d.selector_here, d.oneMul, d.mapSub, d.addSub]
    · have hmem : q ∈ ps := (List.mem_cons.mp hq).resolve_left (Ne.symm h)
      rw [d.mapAdd, d.mapMul, d.selector_elsewhere h ps hmem, d.zeroMul, d.addZero]
      exact hx q hmem

end Residues

/-- Finite CRT for arbitrary residue targets that individually have lifts. -/
theorem crt_of_comaximal {P R K} (d : ResidueOps P R K)
    (h : PairwiseComaximal d) (ps : List P) (v : (p : P) → K p)
    (surj : ∀ p, ∃ a, d.val p a = v p) :
    ∃ x : R, ∀ p ∈ ps, d.val p x = v p := by
  classical
  let target (p : P) := Classical.choose (surj p)
  obtain ⟨x, hx⟩ := (d.withSeparators h).finite_prescription target ps
  refine ⟨x, ?_⟩
  intro p hp
  exact (hx p hp).trans (Classical.choose_spec (surj p))

/-- Operations used to specify submodules and linear maps. The following
transport results also hold before one imposes the module equations. -/
structure Space (R : Type u) (X : Type v) where
  zero : X
  add : X → X → X
  neg : X → X
  smul : R → X → X

structure LinearMap {R : Type u} {X : Type v} {Y : Type w}
    (M : Space R X) (N : Space R Y) where
  fn : X → Y
  mapZero : fn M.zero = N.zero
  mapAdd : ∀ x y, fn (M.add x y) = N.add (fn x) (fn y)
  mapNeg : ∀ x, fn (M.neg x) = N.neg (fn x)
  mapSmul : ∀ r x, fn (M.smul r x) = N.smul r (fn x)

namespace LinearMap

def id {R X} (M : Space R X) : LinearMap M M where
  fn x := x
  mapZero := rfl
  mapAdd _ _ := rfl
  mapNeg _ := rfl
  mapSmul _ _ := rfl

def comp {R X Y Z} {M : Space R X} {N : Space R Y} {O : Space R Z}
    (f : LinearMap N O) (g : LinearMap M N) : LinearMap M O where
  fn x := f.fn (g.fn x)
  mapZero := by rw [g.mapZero, f.mapZero]
  mapAdd _ _ := by rw [g.mapAdd, f.mapAdd]
  mapNeg _ := by rw [g.mapNeg, f.mapNeg]
  mapSmul _ _ := by rw [g.mapSmul, f.mapSmul]

end LinearMap

structure LinearIso {R : Type u} {X : Type v} {Y : Type w}
    (M : Space R X) (N : Space R Y) where
  toMap : LinearMap M N
  invMap : LinearMap N M
  leftInv : ∀ x, invMap.fn (toMap.fn x) = x
  rightInv : ∀ y, toMap.fn (invMap.fn y) = y

namespace LinearIso

def refl {R X} (M : Space R X) : LinearIso M M where
  toMap := LinearMap.id M
  invMap := LinearMap.id M
  leftInv _ := rfl
  rightInv _ := rfl

def symm {R X Y} {M : Space R X} {N : Space R Y} (e : LinearIso M N) :
    LinearIso N M := ⟨e.invMap, e.toMap, e.rightInv, e.leftInv⟩

def trans {R X Y Z} {M : Space R X} {N : Space R Y} {O : Space R Z}
    (e : LinearIso M N) (f : LinearIso N O) : LinearIso M O where
  toMap := f.toMap.comp e.toMap
  invMap := e.invMap.comp f.invMap
  leftInv x := by simp [LinearMap.comp, f.leftInv, e.leftInv]
  rightInv z := by simp [LinearMap.comp, e.rightInv, f.rightInv]

end LinearIso

/-- Membership in the sum of all divisible submodules, expressed by existence
of a divisible submodule containing the element. -/
def InDivisiblePart {R X} (M : Space R X) (zeroR : R) (x : X) : Prop :=
  ∃ S : X → Prop, S x ∧ S M.zero ∧
    (∀ a b, S a → S b → S (M.add a b)) ∧
    (∀ a, S a → S (M.neg a)) ∧
    (∀ r a, S a → S (M.smul r a)) ∧
    ∀ r, r ≠ zeroR → ∀ a, S a → ∃ b, S b ∧ M.smul r b = a

/-- The image of a divisible submodule is divisible. -/
theorem map_divisible {R X Y} {M : Space R X} {N : Space R Y}
    (f : LinearMap M N) {zeroR : R} {x : X} (hx : InDivisiblePart M zeroR x) :
    InDivisiblePart N zeroR (f.fn x) := by
  obtain ⟨S, hsx, hs0, hadd, hneg, hsmul, hdiv⟩ := hx
  refine ⟨fun y => ∃ a, S a ∧ f.fn a = y, ⟨x, hsx, rfl⟩,
    ⟨M.zero, hs0, f.mapZero⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨M.add a b, hadd a b ha hb, f.mapAdd a b⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨M.neg a, hneg a ha, f.mapNeg a⟩
  · rintro r _ ⟨a, ha, rfl⟩
    exact ⟨M.smul r a, hsmul r a ha, f.mapSmul r a⟩
  · rintro r hr _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := hdiv r hr a ha
    exact ⟨f.fn b, ⟨b, hb, rfl⟩, by rw [← f.mapSmul, hab]⟩

/-- The divisible part killed by the chosen set of scalars. With the empty
set this is the entire divisible part. -/
def InComponent {R X} (M : Space R X) (zeroR : R) (ann : R → Prop) (x : X) :
    Prop := InDivisiblePart M zeroR x ∧ ∀ r, ann r → M.smul r x = M.zero

theorem map_component {R X Y} {M : Space R X} {N : Space R Y}
    (f : LinearMap M N) {z : R} {ann : R → Prop} {x : X}
    (h : InComponent M z ann x) : InComponent N z ann (f.fn x) := by
  refine ⟨map_divisible f h.1, ?_⟩
  intro r hr
  rw [← f.mapSmul, h.2 r hr, f.mapZero]

/-- A probe embeds linearly into the indicated component. In the intended
application probes are direct sums of residue fields or of the fraction field. -/
def Fits {R T X} (probe : Space R T) (M : Space R X) (z : R) (ann : R → Prop) :
    Prop := ∃ f : LinearMap probe M,
      (∀ a b, f.fn a = f.fn b → a = b) ∧ ∀ a, InComponent M z ann (f.fn a)

theorem fits_iso {R T X Y} {probe : Space R T} {M : Space R X} {N : Space R Y}
    (e : LinearIso M N) {z : R} {ann : R → Prop} :
    Fits probe M z ann → Fits probe N z ann := by
  rintro ⟨f, hf, hmem⟩
  refine ⟨e.toMap.comp f, ?_, ?_⟩
  · intro a b hab
    have h := congrArg e.invMap.fn hab
    change e.invMap.fn (e.toMap.fn (f.fn a)) = e.invMap.fn (e.toMap.fn (f.fn b)) at h
    rw [e.leftInv, e.leftInv] at h
    exact hf a b h
  · exact fun a => map_component e.toMap (hmem a)

/-- Isomorphism on a given family of modules. -/
def isoSetoid {R : Type u} {J : Type v} {X : J → Type w}
    (models : (i : J) → Space R (X i)) : Setoid J where
  r i j := Nonempty (LinearIso (models i) (models j))
  iseqv := ⟨fun i => ⟨LinearIso.refl (models i)⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Distinct multiplicity profiles give distinct isomorphism classes. The
hypothesis `readout` is precisely the dimension computation for the models
under consideration. No classification of injectives is assumed by the
transport lemmas above. -/
theorem profiles_injective {R : Type u} {P : Type v} {I : Type w}
    {X : (P → I) → Type z} {T : P → I → Type t}
    (models : (f : P → I) → Space R (X f))
    (probes : (p : P) → (i : I) → Space R (T p i))
    (zR : R) (ann : P → R → Prop) (le : I → I → Prop)
    (refl_le : ∀ i, le i i) (antisymm_le : ∀ i j, le i j → le j i → i = j)
    (readout : ∀ f p i, Fits (probes p i) (models f) zR (ann p) ↔ le i (f p))
    (f g : P → I)
    (h : Quotient.mk (isoSetoid models) f = Quotient.mk (isoSetoid models) g) :
    f = g := by
  have hiso : Nonempty (LinearIso (models f) (models g)) := Quotient.exact h
  obtain ⟨e⟩ := hiso
  funext p
  apply antisymm_le
  · exact (readout g p (f p)).1
      (fits_iso e ((readout f p (f p)).2 (refl_le (f p))))
  · exact (readout f p (g p)).1
      (fits_iso e.symm ((readout g p (g p)).2 (refl_le (g p))))

end PureEmbeddings.Dedekind
