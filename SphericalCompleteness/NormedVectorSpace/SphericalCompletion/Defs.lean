/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.NormedVectorSpace.Immediate
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp
public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.SphericallyCompleteExtension

/-!
# Spherical completion: definition

This file defines the class `IsSphericalCompletion 𝕜 E F`, which characterises when a spherically
complete ultrametric normed space `F` is a *spherical completion* of an ultrametric normed
`𝕜`-vector space `E`.

A spherical completion of `E` is a spherically complete space `F` into which `E` embeds
isometrically and which is *minimal* with this property: among the `𝕜`-submodules of `F`, the only
spherically complete one containing the image of `E` is `F` itself. Concretely,
`IsSphericalCompletion 𝕜 E F` — with `F` already carrying a `SphericallyCompleteSpace` instance —
asserts that there is a linear isometry `ι : E →ₗᵢ[𝕜] F` such that every spherically complete
submodule `D ≤ F` with `ι.range ≤ D` equals `⊤`.

Existence of such an `F` for every `E`, its uniqueness up to linear isometry, the universal
property, and the equivalence with maximal completeness are established in the companion file
`Basic`. There `F` is produced as a maximal immediate extension (via
`SphericallyCompleteSpace.IsImmediate.exists_maximal_immediateExtensionSubmodule`) of the
constant-sequence embedding of `E` into a spherically complete `ℓ∞`-quotient
(`canonicalSphericallyCompleteExtension`).

## Main definitions

* `SphericallyCompleteSpace.IsSphericalCompletion 𝕜 E F` — the class asserting that the spherically
  complete space `F` is a spherical completion of `E`, i.e. `E` embeds isometrically into `F` as a
  minimal spherically complete extension.
-/

@[expose] public section

namespace SphericallyCompleteSpace

/--
`IsSphericalCompletion 𝕜 E F` states that the spherically complete ultrametric normed `𝕜`-vector
space `F` is a *spherical completion* of `E`.

It holds when there is a linear isometric embedding `ι : E →ₗᵢ[𝕜] F` that is *minimal* among
spherically complete spaces: the only spherically complete submodule `D ≤ F` containing the image
`ι.range` of `E` is `F` itself, i.e. `D = ⊤`.

Intuitively, $F$ is the smallest spherically complete space containing an isometric copy of $E$:
no proper spherically complete subspace of $F$ still contains $E$. The ambient
`[SphericallyCompleteSpace F]` instance records that `F` is itself spherically complete, so the
class pins down *which* spherically complete extension counts as a completion. That such an `F` is
in addition an immediate extension of `E`, and is unique up to linear isometry, is proved in
`Basic`.
-/
class IsSphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    [SphericallyCompleteSpace F] : Prop where
  /-- There is a linear isometry `ι : E →ₗᵢ[𝕜] F` that is minimal among spherically complete
  extensions: every spherically complete submodule `D ≤ F` containing `ι.range` is all of `F`. -/
  is_sph_comp : ∃ ι : E →ₗᵢ[𝕜] F,
    ∀ D : Submodule 𝕜 F, SphericallyCompleteSpace D → ι.range ≤ D → D = ⊤

end SphericallyCompleteSpace
