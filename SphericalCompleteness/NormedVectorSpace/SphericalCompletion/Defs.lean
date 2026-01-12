import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.SphericallyCompleteExtension
import SphericalCompleteness.NormedVectorSpace.Immediate
import SphericalCompleteness.NormedVectorSpace.Existance

namespace SphericallyCompleteSpace

def IsSphericalComletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
(F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] : Prop :=
SphericallyCompleteSpace F ∧
∃ (f : E →ₗᵢ[𝕜] F), ∀ M : Submodule 𝕜 F, LinearMap.range f ≤ M → SphericallyCompleteSpace M → M = ⊤

--noncomputable def SphericalCompletion {𝕜 : Type*} [NontriviallyNormedField 𝕜]
--(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def LinearIsometry.submodule_subset_submodule (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
{F₁ F₂ : Submodule 𝕜 E} (h : F₁ ≤ F₂) :
↥F₁ →ₗᵢ[𝕜] ↥F₂ where
  toFun x := ⟨x.1, h x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl


def ayaka {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀)
: Set (Submodule 𝕜 E₀) := {M : Submodule 𝕜 E₀ |
    ∃ hc : LinearMap.range f ≤ M,
    IsImmediate ({toFun x := ⟨x.1, hc x.2⟩
                  map_add' _ _ := rfl
                  map_smul' _ _ := rfl
                  norm_map' _ := rfl} : LinearMap.range f →ₗᵢ[𝕜] M)
  }

theorem zorn_ayaka (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) : ∃ m, Maximal (fun x ↦ x ∈ ayaka E E₀ f) m := by
  apply zorn_le₀

  sorry

def SphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: Type u := ↥(zorn_ayaka 𝕜 E (↥(lp (fun x ↦ E) ⊤) ⧸ c₀ 𝕜 fun x ↦ E) (sphericallyCompleteExtension 𝕜 E)).choose

noncomputable instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: NormedAddCommGroup (SphericalCompletion 𝕜 E) := by
  unfold SphericalCompletion
  infer_instance

noncomputable instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: NormedSpace 𝕜 (SphericalCompletion 𝕜 E) := by
  unfold SphericalCompletion
  infer_instance

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: IsUltrametricDist (SphericalCompletion 𝕜 E) := by
  unfold SphericalCompletion
  infer_instance

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: SphericallyCompleteSpace (SphericalCompletion 𝕜 E) := by
  unfold SphericalCompletion
  sorry

end SphericallyCompleteSpace
