import Std

/-!
The elementary part of the pure-embedding criterion. The inputs of
`simultaneousPerturbation` model the maps obtained after tensoring with
each finitely presented right module. The proof chooses one copy for
all tests and proves injectivity of the corrected maps.
-/
namespace PureEmbeddings.Criterion

universe u

/-- The additive group underlying each tensor product in a test. -/
structure Abelian where
  Carrier : Type u
  zero : Carrier
  add : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  assoc : ∀ x y z, add (add x y) z = add x (add y z)
  comm : ∀ x y, add x y = add y x
  add_zero : ∀ x, add x zero = x
  add_neg : ∀ x, add x (neg x) = zero

namespace Abelian

theorem zero_add (G : Abelian) (x : G.Carrier) : G.add G.zero x = x :=
  (G.comm _ _).trans (G.add_zero x)

theorem neg_add (G : Abelian) (x : G.Carrier) : G.add (G.neg x) x = G.zero :=
  (G.comm _ _).trans (G.add_neg x)

theorem eq_neg_of_add_zero (G : Abelian) {x y : G.Carrier}
    (h : G.add x y = G.zero) : x = G.neg y := by
  calc
    x = G.add x G.zero := (G.add_zero x).symm
    _ = G.add x (G.add y (G.neg y)) := by rw [G.add_neg]
    _ = G.add (G.add x y) (G.neg y) := (G.assoc _ _ _).symm
    _ = G.neg y := by rw [h, G.zero_add]

theorem eq_of_sub_zero (G : Abelian) {x y : G.Carrier}
    (h : G.add x (G.neg y) = G.zero) : x = y := by
  calc
    x = G.add x G.zero := (G.add_zero x).symm
    _ = G.add x (G.add (G.neg y) y) := by rw [G.neg_add]
    _ = G.add (G.add x (G.neg y)) y := (G.assoc _ _ _).symm
    _ = y := by rw [h, G.zero_add]

theorem interchange (G : Abelian) (a b c d : G.Carrier) :
    G.add (G.add a b) (G.add c d) = G.add (G.add a c) (G.add b d) := by
  calc
    _ = G.add a (G.add (G.add b c) d) := by rw [G.assoc a b, G.assoc b c d]
    _ = G.add a (G.add (G.add c b) d) := by rw [G.comm b c]
    _ = _ := by rw [G.assoc a c, G.assoc c b d]

end Abelian

/-- An additive homomorphism. Preservation of negatives is proved below. -/
structure Hom (A B : Abelian) where
  map : A.Carrier → B.Carrier
  map_zero : map A.zero = B.zero
  map_add : ∀ x y, map (A.add x y) = B.add (map x) (map y)

def OneToOne {X Y : Type u} (f : X → Y) : Prop :=
  ∀ ⦃x y⦄, f x = f y → x = y

namespace Hom

theorem map_neg {A B : Abelian} (f : Hom A B) (x : A.Carrier) :
    f.map (A.neg x) = B.neg (f.map x) := by
  apply B.eq_neg_of_add_zero
  rw [← f.map_add, A.neg_add, f.map_zero]

def comp {A B C : Abelian} (g : Hom B C) (f : Hom A B) : Hom A C where
  map x := g.map (f.map x)
  map_zero := by rw [f.map_zero, g.map_zero]
  map_add x y := by rw [f.map_add, g.map_add]

def add {A B : Abelian} (f g : Hom A B) : Hom A B where
  map x := B.add (f.map x) (g.map x)
  map_zero := by rw [f.map_zero, g.map_zero, B.add_zero]
  map_add x y := by rw [f.map_add, g.map_add, B.interchange]

theorem injective_of_kernel {A B : Abelian} (f : Hom A B)
    (kernel : ∀ x, f.map x = B.zero → x = A.zero) : OneToOne f.map := by
  intro x y equal
  apply A.eq_of_sub_zero
  apply kernel
  rw [f.map_add, f.map_neg, equal, B.add_neg]

end Hom

/-- The two images meet only in zero. -/
def DisjointImages {X Y Z : Type u} (zero : Z) (f : X → Z) (g : Y → Z) : Prop :=
  ∀ x y, f x = g y → f x = zero

/-- Right exactness at the middle term and injectivity on the prescribed
submodule give injectivity of the corrected map for a single tensor test. -/
theorem perturbation {A B C F : Abelian.{u}}
    (i : Hom A B) (q : Hom B C) (f : Hom A F) (g : Hom B F) (j : Hom C F)
    (quotient : ∀ a, q.map (i.map a) = C.zero)
    (exactAt : ∀ b, q.map b = C.zero → ∃ a, i.map a = b)
    (agreesOnA : ∀ a, g.map (i.map a) = f.map a)
    (fInj : OneToOne f.map) (jInj : OneToOne j.map)
    (fresh : DisjointImages F.zero g.map j.map) :
    (∀ a, (g.add (j.comp q)).map (i.map a) = f.map a) ∧
      OneToOne (g.add (j.comp q)).map := by
  constructor
  · intro a
    change F.add (g.map (i.map a)) (j.map (q.map (i.map a))) = f.map a
    rw [quotient, j.map_zero, F.add_zero, agreesOnA]
  · apply Hom.injective_of_kernel
    intro b inKernel
    change F.add (g.map b) (j.map (q.map b)) = F.zero at inKernel
    have agree : g.map b = j.map (C.neg (q.map b)) :=
      (F.eq_neg_of_add_zero inKernel).trans (j.map_neg _).symm
    have gz : g.map b = F.zero := fresh _ _ agree
    have jz : j.map (q.map b) = F.zero := by
      simpa only [gz, F.zero_add] using inKernel
    have qz : q.map b = C.zero := jInj (jz.trans j.map_zero.symm)
    obtain ⟨a, ha⟩ := exactAt b qz
    have fz : f.map a = F.zero := (agreesOnA a).symm.trans ((congrArg g.map ha).trans gz)
    have az : a = A.zero := fInj (fz.trans f.map_zero.symm)
    calc
      b = i.map a := ha.symm
      _ = i.map A.zero := congrArg i.map az
      _ = B.zero := i.map_zero

/-- Choosing a single fresh copy in a family of tests. If all indices
were bad, choosing a non-zero intersection would inject the indices into
the disjoint union of the test domains. -/
theorem freshIndex {I T : Type u} {B C F : T → Type u}
    (zero : (t : T) → F t) (g : (t : T) → B t → F t)
    (j : (t : T) → I → C t → F t)
    (separate : ∀ t i k, i ≠ k → DisjointImages (zero t) (j t i) (j t k))
    (large : ¬ ∃ e : I → Sigma B, OneToOne e) :
    ∃ i, ∀ t, DisjointImages (zero t) (g t) (j t i) := by
  classical
  apply Classical.byContradiction
  intro noFresh
  let hit (i : I) (w : Sigma B) : Prop :=
    ∃ c, g w.1 w.2 = j w.1 i c ∧ g w.1 w.2 ≠ zero w.1
  have bad : ∀ i, ∃ w, hit i w := by
    intro i
    apply Classical.byContradiction
    intro noHit
    apply noFresh
    refine ⟨i, ?_⟩
    intro t b c equal
    apply Classical.byContradiction
    intro nonzero
    exact noHit ⟨⟨t, b⟩, c, equal, nonzero⟩
  let e (i : I) : Sigma B := Classical.choose (bad i)
  have chosen : ∀ i, hit i (e i) := fun i => Classical.choose_spec (bad i)
  apply large
  refine ⟨e, ?_⟩
  intro i k equal
  apply Classical.byContradiction
  intro different
  obtain ⟨ci, left, nonzero⟩ := chosen i
  have same : hit k (e i) := by rw [equal]; exact chosen k
  obtain ⟨ck, right, _⟩ := same
  exact nonzero (left.trans (separate _ i k different ci ck (left.symm.trans right)))

/-- Uniform version of the perturbation argument. Under the testwise
hypotheses one index works for every test, and the resulting maps both
extend the prescribed restrictions and are injective. -/
theorem simultaneousPerturbation {I T : Type u}
    {A B C F : T → Abelian.{u}}
    (i : (t : T) → Hom (A t) (B t)) (q : (t : T) → Hom (B t) (C t))
    (f : (t : T) → Hom (A t) (F t)) (g : (t : T) → Hom (B t) (F t))
    (j : (t : T) → I → Hom (C t) (F t))
    (quotient : ∀ t a, (q t).map ((i t).map a) = (C t).zero)
    (exactAt : ∀ t b, (q t).map b = (C t).zero → ∃ a, (i t).map a = b)
    (agreesOnA : ∀ t a, (g t).map ((i t).map a) = (f t).map a)
    (fInj : ∀ t, OneToOne (f t).map) (jInj : ∀ t k, OneToOne (j t k).map)
    (separate : ∀ t k l, k ≠ l → DisjointImages (F t).zero (j t k).map (j t l).map)
    (large : ¬ ∃ e : I → Sigma (fun t => (B t).Carrier), OneToOne e) :
    ∃ k, ∀ t, (∀ a, ((g t).add ((j t k).comp (q t))).map ((i t).map a) = (f t).map a) ∧
      OneToOne ((g t).add ((j t k).comp (q t))).map := by
  obtain ⟨k, fresh⟩ := freshIndex (fun t => (F t).zero) (fun t => (g t).map)
    (fun t k => (j t k).map) separate large
  exact ⟨k, fun t => perturbation (i t) (q t) (f t) (g t) (j t k)
    (quotient t) (exactAt t) (agreesOnA t) (fInj t) (jInj t k) (fresh t)⟩

/-- Compatible embeddings on a directed cover glue to an embedding.
This supplies the injectivity step at a limit stage of back-and-forth. -/
theorem glueEmbeddings {T X Y : Type u}
    (stage : T → X → Prop) (f : (t : T) → (x : X) → stage t x → Y)
    (cover : ∀ x, ∃ t, stage t x)
    (directed : ∀ s t, ∃ r, (∀ x, stage s x → stage r x) ∧ (∀ x, stage t x → stage r x))
    (compatible : ∀ s t x (hs : stage s x) (ht : stage t x), f s x hs = f t x ht)
    (locallyInj : ∀ t x y (hx : stage t x) (hy : stage t y), f t x hx = f t y hy → x = y) :
    ∃ h : X → Y, OneToOne h ∧ ∀ t x (hx : stage t x), h x = f t x hx := by
  classical
  let owner (x : X) := Classical.choose (cover x)
  have member (x : X) : stage (owner x) x := Classical.choose_spec (cover x)
  let h (x : X) := f (owner x) x (member x)
  have agrees (t : T) (x : X) (hx : stage t x) : h x = f t x hx :=
    compatible (owner x) t x (member x) hx
  refine ⟨h, ?_, agrees⟩
  intro x y equal
  obtain ⟨r, left, right⟩ := directed (owner x) (owner y)
  have rx := left x (member x)
  have ry := right y (member y)
  exact locallyInj r x y rx ry ((agrees r x rx).symm.trans (equal.trans (agrees r y ry)))

end PureEmbeddings.Criterion
