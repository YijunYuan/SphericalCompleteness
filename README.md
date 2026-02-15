# SphericalCompleteness

[![CI](https://github.com/YijunYuan/SphericalCompleteness/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/YijunYuan/SphericalCompleteness/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.27.0-5C2D91)](https://github.com/leanprover/lean4)
[![mathlib](https://img.shields.io/badge/mathlib-v4.27.0-5C2D91)](https://github.com/leanprover-community/mathlib4)


## What the project does

This repository is a Lean 4 / mathlib development about **spherical completeness** in ultrametric (pseudo)metric spaces and related constructions for **non-Archimedean normed vector spaces**.

At a high level it provides:

- A definition of `SphericallyCompleteSpace` and basic consequences (e.g. deriving `CompleteSpace`).
- Equivalent characterizations of spherical completeness in the ultrametric setting.
- A construction of a (non-canonical) **spherical completion** of an ultrametric normed space via maximal immediate extensions.

The main umbrella import is:

- `SphericalCompleteness.lean`

## Why the project is useful

Spherical completeness is a key completeness notion in non-Archimedean analysis (e.g. $p$-adic and ultrametric geometry). This library aims to make it easy to:

- Reuse a single, well-documented `SphericallyCompleteSpace` API in downstream formalizations.
- Access standard “nested closed balls have nonempty intersection” formulations.
- Work with stability properties (e.g. products, finite dependent products) in a typeclass-friendly way.
- Build spherical completions of normed spaces inside a fixed spherically complete ambient space.

## How users can get started

### Prerequisites

- Lean toolchain: `leanprover/lean4:v4.26.0` (see `lean-toolchain`).
- mathlib revision: `v4.26.0` (see `lakefile.toml`).
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

open Metric Filter

variable {α : Type} [PseudoMetricSpace α] [SphericallyCompleteSpace α]

-- Given a nested sequence of closed balls, the intersection is nonempty.
example (ci : ℕ → α) (ri : ℕ → NNReal)
    (hanti : Antitone (fun i => closedBall (ci i) (ri i))) :
    (⋂ i, closedBall (ci i) (ri i)).Nonempty :=
  SphericallyCompleteSpace.isSphericallyComplete (ci := ci) (ri := ri) hanti
```

### Repository layout

- `SphericalCompleteness.lean`: umbrella import for the project.
- `SphericalCompleteness/Defs.lean`: definition of `SphericallyCompleteSpace` and basic instances.
- `SphericalCompleteness/Basic.lean`: characterizations and basic closure properties.
- `SphericalCompleteness/NormedVectorSpace/SphericalCompletion/Defs.lean`: construction of `SphericalCompletion` and its embedding.

## Where users can get help

- If something in this repo fails to compile: open a GitHub issue in this repository.
- For Lean / mathlib questions:
  - Lean community Zulip: https://leanprover.zulipchat.com/
  - mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/
  - Lean 4 manual: https://lean-lang.org/lean4/doc/

## Who maintains and contributes

Maintainers: Yijun Yuan

