/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.Basic
public import SphericalCompleteness.External.Submodule

/-!
# Orthogonality: definitions

Definitions for (norm) orthogonality in ultrametric normed spaces.
-/

@[expose] public section

namespace SphericallyCompleteSpace

/-!
### Orthogonality in ultrametric normed spaces

Orthogonality in a non-Archimedean space is not defined through an inner product but through
best approximation: a vector is orthogonal to a subspace when the subspace offers no better
approximation of it than the origin does. All three notions below are phrased with
`Metric.infDist` and the norm `‖·‖`, which behave well under the strong triangle inequality
(`[IsUltrametricDist E]`).

Notation:

* `x ⟂ₘ F` for `MOrth _ x F`
* `F ⟂ₛ G` for `SOrth _ F G`
* `x ⟂[𝕜] y` for `Orth 𝕜 x y`
-/

/-- `MOrth 𝕜 x F` is *metric orthogonality* of a vector to a subspace: the distance from `x`
to `F` equals `‖x‖`, i.e. no point of `F` approximates `x` better than `0` does. This is the
non-Archimedean substitute for "`x` has no component along `F`". -/
def MOrth (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (x : E) (F : Subspace 𝕜 E) := Metric.infDist x F = ‖x‖

/-- `Orth 𝕜 x y` is orthogonality of two vectors: `x` is metrically orthogonal to the line
`𝕜 ∙ y` spanned by `y`. Despite the asymmetric definition this relation is symmetric
(see `Orth.symm`). -/
def Orth (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (x y : E) := Metric.infDist x (𝕜 ∙ y) = ‖x‖

/-- `SOrth 𝕜 F₁ F₂` is orthogonality of two subspaces: every vector of `F₁` is metrically
orthogonal to `F₂`. Like `Orth`, this relation is in fact symmetric (see `SOrth.symm`). -/
def SOrth (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (F1 : Subspace 𝕜 E) (F2 : Subspace 𝕜 E) := ∀ x ∈ F1, MOrth 𝕜 x F2

notation:50 x " ⟂ₘ " F => MOrth _ x F
notation:50 F " ⟂ₛ " G => SOrth _ F G
notation:50 x " ⟂[" 𝕜 "] " y => Orth 𝕜 x y

end SphericallyCompleteSpace
