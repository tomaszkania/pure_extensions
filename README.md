# Extending pure embeddings of modules

A Lean 4 formalisation of the main results in Tomasz Kania’s upcoming paper. The entry point is `import PureEmbeddings`. The hypotheses, including strict cardinal bounds, appear in the Lean statements.

## Results

| Paper | Main declaration | Content |
| --- | --- | --- |
| Theorem A | `PureEmbeddings.theoremA` | For arbitrary non-zero rings, the minimum is κ in the left pure-semisimple case. In the other case it lies between κ^ℵ₀ and κ^max(ℵ₀,\|R\|). A model of size κ is unique, homogeneous below κ and universal up to κ. |
| Theorem B | `PureEmbeddings.theoremB` | The exact minimum over a non-field Dedekind domain S is κ^max(ℵ₀,\|Max S\|). The theorem gives the uniqueness criterion and a lower bound on the number of isomorphism types at the minimum. |
| Theorem C | `PureEmbeddings.Groups.theoremC` | Kostana’s supported product has size κ^{<κ} and has the extension property precisely at uncountable cofinality. The theorem includes the regularity criterion for full coordinate products, their splitting and pure-injectivity, and the lower bound on the number of optimal abelian groups. |
| Theorem D | `PureEmbeddings.theoremD` | For a non-field valuation domain with value group Γ, the minimum is κ^\|Γ\|. It is attained by a unique isomorphism type exactly when it equals κ. |

[Statements of A, B and D](PureEmbeddings/Statements.lean) · [Statement of C and definition of the group](PureEmbeddings/GroupsMathlib.lean) · [Definitions of purity, extension and minimum](PureEmbeddings/ModuleTheory.lean)

`IsPureMap` requires injectivity and reflection of solutions of finite linear systems. `HasExtension κ F` says that a pure embedding into F extends along a pure inclusion A → B whenever |B| < κ. `HasMinimum κ μ` includes a module attaining μ and a lower bound applying to every module with the extension property. The count of isomorphism types is witnessed by an indexed family of modules together with a proof that distinct indices give non-isomorphic modules.

Theorems A, B and D are polymorphic in the Lean universe containing the ring, modules and cardinals. Theorem C uses `Cardinal.{0}`, the cardinals of types in Lean’s usual base universe. Within that universe κ is arbitrary, subject only to uncountability, and may be singular.

## Building and checking

The project pins Lean 4.24.0 and the corresponding mathlib release commit in [lean-toolchain](lean-toolchain) and [lakefile.toml](lakefile.toml). From the extracted project directory, with Elan installed, run

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lake resolves the dependencies from the supplied lockfile and fetches their compiled cache. The final command displays the signatures of the main theorems and the axioms on which their proofs depend.

## Further entry points

- [The extension criterion](PureEmbeddings/ExtensionCriterion.lean) proves that the extension property is equivalent to pure-injectivity together with universality for modules of size at most κ.
- [The countable-ring dichotomy](PureEmbeddings/TheoremA.lean) specialises the general bounds to an exact minimum.
- [Transfinite branching](PureEmbeddings/TransfiniteBranching.lean) derives a lower bound from a well-ordered family of finite matrix tests.
- [The supported product](PureEmbeddings/GroupExtension.lean) and [co-cyclic embeddings](PureEmbeddings/CocyclicEmbedding.lean) exhibit the two ingredients in the positive direction of Theorem C.
- [Prime antichains](PureEmbeddings/PrimeAntichain.lean) gives the lower bound κ^|P| for a set P of pairwise incomparable, finitely generated prime ideals in a commutative ring.
- [Supported products of modules](PureEmbeddings/SupportedModules.lean) extends the pure-injectivity argument to any ring R when cf(κ) > max(ℵ₀, |R|). In particular, uncountable cofinality suffices over every countable ring.
