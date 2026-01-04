import SphericalCompleteness.Basic

open Metric
open Filter

namespace SphericallyCompleteSpace

def IsOrthogonal' (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(x : E) (F : Subspace 𝕜 E) := Metric.infDist x F = ‖x‖

def IsOrthogonal (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(x y : E) := Metric.infDist x (𝕜 ∙ y) = ‖x‖

def IsOrthogonal'' (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(F1 : Subspace 𝕜 E) (F2 : Subspace 𝕜 E) := ∀ x ∈ F1, IsOrthogonal' 𝕜 x F2

notation:50 x " ⟂ " F => IsOrthogonal' _ x F
notation:50 F " ⟂'' " G => IsOrthogonal'' _ F G
notation:50 x " ⟂[" 𝕜 "] " y => IsOrthogonal 𝕜 x y

theorem smul_span_singleton_eq_self {𝕜 : Type*} [Field 𝕜]
  {E : Type*} [AddCommMonoid E] [Module 𝕜 E] {y : E}
   {a : 𝕜} (ha : a ≠ 0) :
  (@HSMul.hSMul 𝕜 (Set E) (Set E) (@instHSMul 𝕜 (Set E) Set.smulSet) a ↑(Submodule.span 𝕜 {y}))
    = ↑(Submodule.span 𝕜 {y}) := by
  ext z
  constructor
  · intro h
    rw [Set.mem_smul_set] at h
    rcases h with ⟨c, hc, hz⟩
    rw [← hz]
    exact Submodule.smul_mem (Submodule.span 𝕜 {y}) a hc
  · intro h
    refine Set.mem_smul_set.mpr ?_
    rcases Submodule.mem_span_singleton.1 h with ⟨c, hc⟩
    use a⁻¹ • c • y
    constructor
    · rw [smul_smul]
      simp
      refine Submodule.mem_span_singleton.mpr ?_
      use a⁻¹ • c
      rfl
    · rw [hc, smul_smul]
      subst hc
      simp_all only [ne_eq, SetLike.mem_coe, not_false_eq_true, mul_inv_cancel₀, one_smul]

lemma orth_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [iud : IsUltrametricDist E] {x y : E} :
(x ⟂[𝕜] y) ↔ (∀ α β : 𝕜, ‖α • x + β • y‖ = max ‖α • x‖ ‖β • y‖) := by
  unfold IsOrthogonal
  constructor
  · intro h a b
    if hab : a = 0 ∨ b = 0 then
      rcases hab with ha | hb
      · simp only [ha, zero_smul, zero_add, norm_zero, norm_nonneg, sup_of_le_right]
      · simp only [hb, zero_smul, add_zero, norm_zero, norm_nonneg, sup_of_le_left]
    else
    push_neg at hab
    refine eq_of_le_of_ge (iud.norm_add_le_max _ _) ?_
    apply max_le
    · rw [← sub_neg_eq_add, ← dist_eq_norm]
      refine le_trans ?_ <| infDist_le_dist_of_mem (by
        simp
        refine Submodule.mem_span_singleton.mpr ?_
        use b : - (b • y) ∈ 𝕜 ∙ y)
      have := infDist_smul₀ hab.1 (Submodule.span 𝕜 {y} : Set E) x
      rw [smul_span_singleton_eq_self hab.1] at this
      rw [this, h, norm_smul]
    · have : a • x + b • y = b • y - - (a • x) := by abel
      rw [this, ← dist_eq_norm]
      refine le_trans ?_ <| infDist_le_dist_of_mem (by
        simp
        refine Submodule.mem_span_singleton.mpr ?_
        use a : - (a • x) ∈ 𝕜 ∙ x)
      have := infDist_smul₀ hab.2 (Submodule.span 𝕜 {x} : Set E) y
      rw [smul_span_singleton_eq_self hab.2] at this
      rw [this, norm_smul]
      sorry
  sorry

lemma orth_comm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] {x y : E} :
(x ⟂[𝕜] y) ↔ (y ⟂[𝕜] x) := by
  sorry

lemma orth_comm'' {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] {F1 F2 : Subspace 𝕜 E} :
(F1 ⟂'' F2) ↔ (F2 ⟂'' F1) := by
  sorry

end SphericallyCompleteSpace
