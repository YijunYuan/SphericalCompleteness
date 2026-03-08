import SphericalCompleteness.Basic
import SphericalCompleteness.External.Submodule

namespace SphericallyCompleteSpace

/--
Definitions of orthogonality in an ultrametric normed vector space over a nontrivially normed field.

These notions are phrased using `Metric.infDist` (infimum distance) and the norm `‖·‖`,
which is well-suited to the ultrametric setting (`[IsUltrametricDist E]`).

* `MOrth 𝕜 x F` (“metric orthogonality” of a vector to a subspace): `x` is *metrically*
  orthogonal to the subspace `F` if the distance from `x` to `F` equals `‖x‖`.
  Intuitively, `F` does not provide any approximation of `x` better than the origin.

* `Orth 𝕜 x y` (orthogonality of two vectors): `x` is orthogonal to `y` if `x` is
  metrically orthogonal to the one-dimensional subspace `𝕜 ∙ y` spanned by `y`.

* `SOrth 𝕜 F₁ F₂` (subspace orthogonality): `F₁` is orthogonal to `F₂` if every
  vector `x ∈ F₁` is metrically orthogonal to `F₂`.

Notation:

* `x ⟂ₘ F` for `MOrth _ x F`
* `F ⟂ₛ G` for `SOrth _ F G`
* `x ⟂[𝕜] y` for `Orth 𝕜 x y`
-/
def MOrth (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(x : E) (F : Subspace 𝕜 E) := Metric.infDist x F = ‖x‖

def Orth (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(x y : E) := Metric.infDist x (𝕜 ∙ y) = ‖x‖

def SOrth (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(F1 : Subspace 𝕜 E) (F2 : Subspace 𝕜 E) := ∀ x ∈ F1, MOrth 𝕜 x F2

notation:50 x " ⟂ₘ " F => MOrth _ x F
notation:50 F " ⟂ₛ " G => SOrth _ F G
notation:50 x " ⟂[" 𝕜 "] " y => Orth 𝕜 x y

end SphericallyCompleteSpace
