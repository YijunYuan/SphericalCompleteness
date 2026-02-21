# SphericalCompleteness

[![CI](https://github.com/YijunYuan/SphericalCompleteness/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/YijunYuan/SphericalCompleteness/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.28.0-5C2D91)](https://github.com/leanprover/lean4)
[![mathlib](https://img.shields.io/badge/mathlib-v4.28.0-5C2D91)](https://github.com/leanprover-community/mathlib4)

This repository is a Lean 4 / mathlib formalization of **spherical completeness** in ultrametric spaces and its consequences in **non-Archimedean normed vector spaces**.

## What the project does

At a high level, the library provides:

- The core typeclass `SphericallyCompleteSpace` and foundational consequences (including completeness).
- Multiple equivalent formulations of spherical completeness in ultrametric settings.
- Structural results for normed spaces: orthogonality, orthogonal complements, quotient stability.
- A non-Archimedean Hahn-Banach theorem with norm-preserving extension.
- A construction and characterization of `SphericalCompletion` via maximal immediate extensions.

The main umbrella import is:

- `SphericalCompleteness.lean`

## Main mathematical results

The central conclusions formalized in this project include:

1. Equivalent characterizations of spherical completeness (`SphericalCompleteness/Basic.lean`):
   - Nested closed balls with nonempty intersection (definition form).
   - Equivalent formulations with antitone or strictly antitone radii.
   - Equivalence with the pairwise-intersection criterion for closed balls (TFAE in ultrametric spaces).
2. Spherical completeness implies completeness (`SphericalCompleteness/Defs.lean`).
3. A non-spherical-completeness mechanism (`SphericalCompleteness/Dense.lean`):
   - Separable + ultrametric + spherically dense implies not spherically complete.
   - Applied to show that `ℂ_[p]` is not spherically complete.
4. Non-Archimedean Hahn-Banach (`SphericalCompleteness/NormedVectorSpace/ContinuousLinearMap/HahnBanach.lean`):
   - Continuous linear maps extend from subspaces while preserving operator norm.
5. Orthogonal complements and projections (`SphericalCompleteness/NormedVectorSpace/Orthogonal/OrthComp.lean`):
   - Construction of orthogonal projection and complement with `IsCompl` decomposition.
6. Closure properties:
   - Finite-dimensional spaces over a spherically complete base are spherically complete (`.../NormedVectorSpace/Basic.lean`).
   - Quotients preserve spherical completeness (`.../NormedVectorSpace/Quotient.lean`).
7. Spherical completion theory (`.../NormedVectorSpace/SphericalCompletion/*`):
   - Construction of `SphericalCompletion` and its embedding.
   - Minimality, uniqueness, and universal property.
   - Characterizations:
     - `SphericallyCompleteSpace E ↔ MaximallyComplete 𝕜 E`
     - `SphericallyCompleteSpace E ↔` surjectivity of `SphericalCompletionEmbedding`.

## Why the project is useful

Spherical completeness is a key notion in non-Archimedean analysis (for example, in $p$-adic and ultrametric geometry). This library is designed to make it easier to:

- Reuse a coherent `SphericallyCompleteSpace` API across downstream developments.
- Access standard nested-ball and pairwise-intersection formulations in one place.
- Use typeclass-friendly closure results and functional-analytic consequences.
- Build and reason about spherical completions with universal properties.

## Repository structure

The library is organized in layers.

### Entry points and utilities

- `SphericalCompleteness.lean`
  - Umbrella import of the main library modules.
- `DependencyExtractor.lean`
  - Utility script to extract dependency graphs of declarations to JSON.

### Core spherical-completeness theory

- `SphericalCompleteness/Defs.lean`
  - Definition of `SphericallyCompleteSpace` and fundamental transfer/instance lemmas.
- `SphericalCompleteness/Basic.lean`
  - Equivalent formulations (TFAE) and basic constructions (products, finite `Pi`, standard instances).
- `SphericalCompleteness/Dense.lean`
  - Definition of spherical density and non-spherical-completeness criteria.

### External support layer (`SphericalCompleteness/External/*`)

- `Complete.lean`: completeness vs nested balls with radii tending to zero.
- `ContinuityOfRoots.lean`: continuity-of-roots estimates in non-Archimedean settings.
- `DenselyNormedField.lean`: persistence of densely normed field structure under completion.
- `NNReal.lean`: helper lemmas on `NNReal`.
- `PadicAlgCl.lean`: separability and density results for `PadicAlgCl`.
- `PadicComplex.lean`: transfer of these structures to `ℂ_[p]`.
- `Sequence.lean`: sequence/subsequence selection lemmas used in core arguments.
- `Submodule.lean`: algebraic submodule lemmas used in decomposition arguments.
- `Ultrametric.lean`: ultrametric lemmas and lifted ultrametric instances.

### Normed vector space layer (`SphericalCompleteness/NormedVectorSpace/*`)

- `Basic.lean`
  - Spherical completeness for finite-dimensional spaces over spherically complete fields.
- `Immediate.lean`
  - `IsImmediate`, `MaximallyComplete`, and immediate-extension machinery.
- `Quotient.lean`
  - Spherical completeness for quotient spaces.

### Continuous linear maps and Hahn-Banach

- `ContinuousLinearMap/Basic.lean`
  - Spherical completeness of `E →L[𝕜] F` when codomain hypotheses hold.
- `ContinuousLinearMap/SupportingResults.lean`
  - Technical extension machinery (van Rooij-style supporting lemmas).
- `ContinuousLinearMap/HahnBanach.lean`
  - Main non-Archimedean Hahn-Banach theorems.

### Orthogonality theory

- `Orthogonal/Defs.lean`
  - Definitions of `MOrth`, `Orth`, `SOrth`.
- `Orthogonal/Basic.lean`
  - Fundamental properties and equivalent formulations of orthogonality.
- `Orthogonal/MOrth.lean`
  - Existence and decomposition statements involving `MOrth`.
- `Orthogonal/OrthComp.lean`
  - Construction of `OrthComp` and `OrthProj`; complement decomposition results.

### Spherical completion construction

- `SphericalCompletion/SphericallyCompleteExtension.lean`
  - Construction of a large spherically complete ambient extension (via an `lp/c₀` quotient).
- `SphericalCompletion/Defs.lean`
  - Definition of `SphericalCompletion` via maximal immediate subspaces (Zorn-style existence).
- `SphericalCompletion/Basic.lean`
  - Minimality, uniqueness, universal property, and completion criteria.

## How users can get started

### Prerequisites

- Lean toolchain: `leanprover/lean4:v4.28.0` (see `lean-toolchain`).
- mathlib revision: `v4.28.0` (see `lakefile.toml`).
- Recommended editor: VS Code + the Lean 4 extension.

### Build

```bash
lake update
# Optional but recommended: download precompiled `.olean` caches (mathlib + deps)
lake exe cache get
lake build
```

If `lake exe cache get` fails in your environment (e.g. network restrictions), you can still build from source using just `lake build`.

### Using the library in Lean

To import everything:

```lean
import SphericalCompleteness
```

To import only the core definition of spherical completeness:

```lean
import SphericalCompleteness.Defs
```

Example (sketch): once you have `[SphericallyCompleteSpace α]`, you can use the defining intersection principle.

```lean
import SphericalCompleteness.Defs

open Metric

variable {α : Type} [PseudoMetricSpace α] [SphericallyCompleteSpace α]

-- Given a nested sequence of closed balls, the intersection is nonempty.
example (ci : ℕ → α) (ri : ℕ → NNReal)
    (hanti : Antitone (fun i => closedBall (ci i) (ri i))) :
    (⋂ i, closedBall (ci i) (ri i)).Nonempty :=
  SphericallyCompleteSpace.isSphericallyComplete (ci := ci) (ri := ri) hanti
```

## Where users can get help

- If something in this repo fails to compile: open a GitHub issue in this repository.
- For Lean / mathlib questions:
  - Lean community Zulip: <https://leanprover.zulipchat.com/>
  - mathlib documentation: <https://leanprover-community.github.io/mathlib4_docs/>
  - Lean 4 manual: <https://lean-lang.org/lean4/doc/>

## Who maintains and contributes

Maintainers: Yijun Yuan

