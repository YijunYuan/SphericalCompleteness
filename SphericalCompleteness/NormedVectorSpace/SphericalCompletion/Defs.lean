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
# Spherical completion: definitions

This file constructs the *spherical completion* `SphericalCompletion 𝕜 E` of an ultrametric
normed vector space `E` over a nontrivially normed field `𝕜`, together with its canonical
isometric embedding `SphericalCompletion.embedding 𝕜 E : E →ₗᵢ[𝕜] SphericalCompletion 𝕜 E`.

The construction proceeds in two steps. First, `sphericallyCompleteExtension 𝕜 E` embeds `E`
isometrically into a fixed spherically complete ambient space (a quotient of an `ℓ∞`-type space).
Second, among the submodules of that ambient space which contain the image of `E` and form an
*immediate* extension of it, `SphericalCompletion.exists_maximal_immediateExtensionSubmodule`
selects a maximal one via
Zorn's lemma; the underlying type of that submodule is `SphericalCompletion 𝕜 E`. The auxiliary
predicate `SphericalCompletion.immediateExtensionSubmodules` and the transport lemmas around
`inclusionᵢ` set up this
Zorn argument.

## Main definitions

* `SphericalCompletion.immediateExtensionSubmodules` — the collection of candidate immediate
  intermediate submodules.
* `SphericalCompletion 𝕜 E` — the underlying type of a chosen maximal immediate extension of `E`.
* `SphericalCompletion.embedding 𝕜 E` — the canonical isometric embedding of `E` into it.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

class IsSphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    [SphericallyCompleteSpace F] : Prop where
  is_sph_comp : ∃ ι : E →ₗᵢ[𝕜] F,
    ∀ D : Submodule 𝕜 F, SphericallyCompleteSpace D → ι.range ≤ D → D = ⊤

end SphericallyCompleteSpace
