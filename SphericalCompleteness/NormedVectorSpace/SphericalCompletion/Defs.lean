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
spherically complete one containing the image of `E` is `F` itself. The class
`IsSphericalCompletion 𝕜 E F` bundles the spherical completeness of `F` (it `extends
SphericallyCompleteSpace F`) with the assertion that there is a linear isometry `ι : E →ₗᵢ[𝕜] F`
such that every spherically complete submodule `D ≤ F` with `ι.range ≤ D` equals `⊤`.

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
`IsSphericalCompletion 𝕜 E F` states that the ultrametric normed `𝕜`-vector space `F` is a
*spherical completion* of `E`.

The class `extends SphericallyCompleteSpace F`, so it bundles the fact that `F` is itself
spherically complete together with a *minimality* condition: there is a linear isometric embedding
`ι : E →ₗᵢ[𝕜] F` for which the only spherically complete submodule `D ≤ F` containing the image
`ι.range` of `E` is `F` itself, i.e. `D = ⊤`.

Intuitively, $F$ is the smallest spherically complete space containing an isometric copy of $E$:
no proper spherically complete subspace of $F$ still contains $E$. Because spherical completeness
is carried by the class, any `[IsSphericalCompletion 𝕜 E F]` instance automatically yields
`SphericallyCompleteSpace F` (through the parent projection `toSphericallyCompleteSpace`), so call
sites need not assume it separately. That such an `F` is in addition an immediate extension of `E`,
and is unique up to linear isometry, is proved in `Basic`.
-/
class IsSphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    extends SphericallyCompleteSpace F where
  /-- There is a linear isometry `ι : E →ₗᵢ[𝕜] F` that is minimal among spherically complete
  extensions: every spherically complete submodule `D ≤ F` containing `ι.range` is all of `F`. -/
  is_sph_comp : ∃ ι : E →ₗᵢ[𝕜] F,
    ∀ D : Submodule 𝕜 F, SphericallyCompleteSpace D → ι.range ≤ D → D = ⊤

end SphericallyCompleteSpace
