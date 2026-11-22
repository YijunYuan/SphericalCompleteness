# SphericalCompleteness

[![CI](https://github.com/YijunYuan/SphericalCompleteness/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/YijunYuan/SphericalCompleteness/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.36.0-5C2D91)](https://github.com/leanprover/lean4)
[![mathlib](https://img.shields.io/badge/mathlib-4.36.0-5C2D91)](https://github.com/leanprover-community/mathlib4/releases/tag/v4.36.0)
[![License](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

[![Graph](https://img.shields.io/badge/Dependency_graph-100000?style=for-the-badge&logo=GitHub&logoColor=white&labelColor=black&color=black)](https://yijunyuan.github.io/lean-graph/?url=https://raw.githubusercontent.com/YijunYuan/SphericalCompleteness/refs/heads/master/SphericallyCompleteSpace.json#dark)

This Lean 4 library formalizes **spherical completeness** for bundled pseudometrics and valuations of arbitrary rank, with applications to non-Archimedean normed vector spaces.

## What the project does

At a high level, the library provides:

- For a bundled distance `d : PseudoMetric X Γ`, `d.IsSphericallyComplete` says that every nonempty nest of nonempty closed balls has a common point.
- For real-valued pseudometric spaces, `Metric.sphericallyCompleteSpace_iff` identifies this property with the sequence class `SphericallyCompleteSpace X` used throughout the normed vector space library.
- For a valuation `v`, `v.IsSphericallyComplete` is invariant under equivalent valuations. With a compatible valuative uniformity it implies `CompleteSpace`.
- Multiple equivalent formulations of spherical completeness in ultrametric settings.
- Structural results for normed spaces: orthogonality, orthogonal complements, quotient stability.
- A non-Archimedean Hahn-Banach theorem with norm-preserving extension.
- A construction and characterization of `SphericalCompletion` via maximal immediate extensions.

The main umbrella import is:

- `SphericalCompleteness.lean`

## Main mathematical results

The central conclusions formalized in this project include:

1. Equivalent characterizations of spherical completeness (`SphericalCompleteness/Metric/Basic.lean`):
   - Nested closed balls with nonempty intersection (definition form).
   - Equivalent formulations with antitone or strictly antitone radii.
   - Equivalence with the pairwise-intersection criterion for closed balls (TFAE in ultrametric spaces).
2. Spherical completeness implies completeness (`SphericalCompleteness/Metric/Basic.lean`).
3. A non-spherical-completeness mechanism (`SphericalCompleteness/Metric/Dense.lean`):
   - Separable + ultrametric + spherically dense implies not spherically complete.
   - The application to `ℂ_[p]` is in `SphericalCompleteness/Examples/Padic.lean`.
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

The table lists paths under `SphericalCompleteness/`. Each module can be imported independently.

| Module | Contents |
| --- | --- |
| `PseudoMetric.lean` and `PseudoMetric/` | Bundled distances, arbitrary nests, pairwise intersection, realized radii, best approximation, products and transport. |
| `Metric/Defs.lean` | The real-valued sequence class and its equivalence with the bundled definition. |
| `Metric/Basic.lean` | Completeness, proper spaces, equivalent tests, isometries and finite products. |
| `Metric/Dense.lean` | Spherical density and the obstruction to spherical completeness for separable pseudo-ultrametric spaces. |
| `Valuation/Basic.lean` | Multiplicative and additive valuations, equivalent representatives and `ValuativeRel`. |
| `Valuation/Complete.lean` | Completeness of a spherically complete valued ring in a compatible uniformity. |
| `Valuation/Normed.lean` | The bridges between valuations and ultrametric norms. |
| `Examples/Padic.lean` | The metric and valuation formulations for both `ℚ_[p]` and `ℂ_[p]`. |

For the metric instance on `ℚ_[p]` alone, import `SphericalCompleteness.Examples.Padic.ProperSpace`.
The earlier `Metric`, `Defs`, `Basic`, `Dense`, `Valuation` and `Valuation.Padic` imports remain available.

### External support layer (`SphericalCompleteness/External/*`)

- `Complete.lean`: completeness vs nested balls with radii tending to zero.
- `DenselyNormedField.lean`: persistence of densely normed field structure under completion.
- `PadicAlgCl.lean`: separability and density results for `PadicAlgCl`.
- `PadicComplex.lean`: transfer of these structures to `ℂ_[p]`.
- `Sequence.lean`: sequence/subsequence selection lemmas used in core arguments.
- `Submodule.lean`: algebraic submodule lemmas used in decomposition arguments.
- `Ultrametric/Basic.lean` contains ultrametric ball, norm and completion lemmas.
- `Ultrametric/NormedSpace.lean` adds the quotient and operator-space instances.
- `Ultrametric.lean` re-exports both modules and adds the `lp` instance.

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
- `ContinuousLinearMap/Extension.lean`
  - Technical extension machinery (van Rooij-style supporting lemmas).
- `ContinuousLinearMap/HahnBanach.lean`
  - Main non-Archimedean Hahn-Banach theorems.

### Orthogonality theory

- `Orthogonal/Defs.lean`
  - Definitions of `IsMOrtho`, `IsVOrtho`, `IsOrtho`.
- `Orthogonal/Basic.lean`
  - Fundamental properties and equivalent formulations of orthogonality.
- `Orthogonal/IsMOrtho.lean`
  - Existence and decomposition statements involving `IsMOrtho`.
- `Orthogonal/OrthComp.lean`
  - Construction of `OrthComp` and `OrthProj`; complement decomposition results.

### Spherical completion construction

- `SphericalCompletion/LpQuotient.lean`
  - Construction of a large spherically complete ambient extension (via an `lp/c₀` quotient).
- `SphericalCompletion/Defs.lean`
  - Definition of `SphericalCompletion` via maximal immediate subspaces (Zorn-style existence).
- `SphericalCompletion/Basic.lean`
  - Minimality, uniqueness, universal property, and completion criteria.

## How users can get started

### Prerequisites

- Lean toolchain: `leanprover/lean4:v4.36.0` (see `lean-toolchain`).
- mathlib version: `v4.36.0` (see `lakefile.toml`), pinned to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` in `lake-manifest.json`.
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

Use `import SphericalCompleteness` for the whole library. The metric interface gives existing
normed-space results access to arbitrary nests through the bundled distance.

```lean
import SphericalCompleteness.Metric.Defs

example (X : Type*) [PseudoMetricSpace X] [SphericallyCompleteSpace X] :
    (Metric.nnMetric X).IsSphericallyComplete := inferInstance

example (X : Type*) [PseudoMetricSpace X] (h : (Metric.nnMetric X).IsSphericallyComplete) :
    SphericallyCompleteSpace X := (Metric.sphericallyCompleteSpace_iff X).mpr h
```

Use `SphericalCompleteness.Valuation.Basic` for a specified valuation. A multiplicative valuation's
closed balls are given by `v (x - c) ≤ r`. An additive valuation uses `r ≤ v (x - c)`.

```lean
import SphericalCompleteness.Valuation.Basic

example {R Γ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ]
    (v : Valuation R Γ) (c : R) (r : Γ) :
    v.toPseudoMetric.closedBall c (MaxTropical.trop r) = {x | v (x - c) ≤ r} := rfl
```

## Where users can get help

- If something in this repo fails to compile: open a GitHub issue in this repository.
- For Lean / mathlib questions:
  - Lean community Zulip: <https://leanprover.zulipchat.com/>
  - mathlib documentation: <https://leanprover-community.github.io/mathlib4_docs/>
  - Lean 4 manual: <https://lean-lang.org/lean4/doc/>

## Who maintains and contributes

Maintainers: Yijun Yuan

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE).
