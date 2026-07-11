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

This file defines the class `IsSphericalCompletion ι`, indexed by a linear isometry
`ι : E →ₗᵢ[𝕜] F`, which characterises when a spherically complete ultrametric normed space `F` is a
*spherical completion* of an ultrametric normed `𝕜`-vector space `E` via the embedding `ι`.

A spherical completion of `E` is a spherically complete space `F` into which `E` embeds
isometrically (through `ι`) and which is *minimal* with this property: among the `𝕜`-submodules of
`F`, the only spherically complete one containing the image of `E` is `F` itself. The class
`IsSphericalCompletion ι` bundles the spherical completeness of `F` (it `extends
SphericallyCompleteSpace F`) with the assertion that every spherically complete submodule `D ≤ F`
with `ι.range ≤ D` equals `⊤`.

Existence of such an `F` for every `E`, its uniqueness up to linear isometry, the universal
property, and the equivalence with maximal completeness are established in the companion file
`Basic`. There `F` is produced as a maximal immediate extension (via
`SphericallyCompleteSpace.IsImmediate.exists_maximal_immediateExtensionSubmodule`) of the
constant-sequence embedding of `E` into a spherically complete `ℓ∞`-quotient
(`canonicalSphericallyCompleteExtension`).

## Main definitions

* `SphericallyCompleteSpace.IsSphericalCompletion ι` — the class asserting that the spherically
  complete space `F` is a spherical completion of `E` via the linear isometry `ι : E →ₗᵢ[𝕜] F`,
  i.e. `E` embeds isometrically into `F` through `ι` as a minimal spherically complete extension.
-/

@[expose] public section

namespace SphericallyCompleteSpace

/--
`IsSphericalCompletion ι`, for a linear isometry `ι : E →ₗᵢ[𝕜] F`, states that the ultrametric
normed `𝕜`-vector space `F` is a *spherical completion* of `E` via the embedding `ι`.

The class `extends SphericallyCompleteSpace F`, so it bundles the fact that `F` is itself
spherically complete together with a *minimality* condition on the given isometric embedding
`ι : E →ₗᵢ[𝕜] F`: the only spherically complete submodule `D ≤ F` containing the image `ι.range`
of `E` is `F` itself, i.e. `D = ⊤`.

Intuitively, $F$ is the smallest spherically complete space containing the isometric copy $ι(E)$
of $E$: no proper spherically complete subspace of $F$ still contains $ι(E)$. Because spherical
completeness is carried by the class, any `[IsSphericalCompletion ι]` instance automatically yields
`SphericallyCompleteSpace F` (through the parent projection `toSphericallyCompleteSpace`), so call
sites need not assume it separately. That such an `ι` is in addition an immediate extension of `E`,
and that `F` is unique up to linear isometry, is proved in `Basic`.
-/
class IsSphericalCompletion {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    (ι : E →ₗᵢ[𝕜] F)
    : Prop extends SphericallyCompleteSpace F where
  /-- The linear isometry `ι : E →ₗᵢ[𝕜] F` is minimal among spherically complete extensions: every
  spherically complete submodule `D ≤ F` containing `ι.range` is all of `F`. -/
  minimal_of_sphericallyComplete :
    ∀ D : Submodule 𝕜 F, SphericallyCompleteSpace D → ι.range ≤ D → D = ⊤

end SphericallyCompleteSpace
