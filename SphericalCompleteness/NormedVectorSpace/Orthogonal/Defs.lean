import SphericalCompleteness.Basic
import SphericalCompleteness.External.Submodule

namespace SphericallyCompleteSpace

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
