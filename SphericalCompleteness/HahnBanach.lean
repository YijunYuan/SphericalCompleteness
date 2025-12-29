import SphericalCompleteness.VectorSpace

namespace SphericalCompleteness

lemma lemma_4_4_codim_1
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
(a : E) (ha1 : a ∉ D) (ha2 : D + Submodule.span 𝕜 {a} = ⊤)
(F : Type*) [NormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
(S : D →L[𝕜] F) (𝒰 : Set (E →L[𝕜] F)) (h𝒰 : 𝒰.Nonempty)
(ε : ↑𝒰 → ℝ)
(hε1 : ∀ T : ↑𝒰, 0 < ε T)
(hε2 : ∀ U V : ↑𝒰, ‖U.val - V.val‖ ≤ max (ε U) (ε V))
(hε3 : ∀ U : ↑𝒰, ∀ x : D, ‖S x - U.val x‖ ≤ ε U * ‖x‖)
:
∃ (T : E →L[𝕜] F), (∀ x : D, T x = S x) ∧ (∀ U : ↑𝒰, ‖T - U.val‖ ≤ ε U)
 := sorry

lemma lemma_4_4
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
{F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
{S : D →L[𝕜] F} {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
(ε : ↑𝒰 → ℝ)
(hε1 : ∀ T : ↑𝒰, 0 < ε T)
(hε2 : ∀ U V : ↑𝒰, ‖U.val - V.val‖ ≤ max (ε U) (ε V))
(hε3 : ∀ U : ↑𝒰, ∀ x : D, ‖S x - U.val x‖ ≤ ε U * ‖x‖)
:
∃ (T : E →L[𝕜] F), (∀ x : D, T x = S x) ∧ (∀ U : ↑𝒰, ‖T - U.val‖ ≤ ε U)
 := sorry


end SphericalCompleteness

#check StrongDual
