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

theorem orth_of_orth {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [iud : IsUltrametricDist E] {x y : E}
  (h : x ⟂[𝕜] y) : y ⟂[𝕜] x := by
  unfold IsOrthogonal at *
  refine eq_of_le_of_not_lt ?_ ?_
  · have := @infDist_le_dist_of_mem E _ ↑(Submodule.span 𝕜 {x}) y 0 (by simp)
    simpa only [ge_iff_le, dist_zero_right] using this
  · by_contra hc
    rcases (infDist_lt_iff (by use 0; simp)).1 hc with ⟨z, hz1, hz2⟩
    simp at hz1
    rcases Submodule.mem_span_singleton.1 hz1 with ⟨a, ha⟩
    rw [← ha] at hz2
    if ha' : a = 0 then
      subst ha'
      simp only [zero_smul, dist_zero_right, lt_self_iff_false] at *
    else
    rw [dist_eq_norm] at hz2
    have hax : ‖a • x‖ = ‖y‖ := by
      rw [← norm_neg, neg_sub] at hz2
      rw [(by abel : a • x = a • x - y + y), iud.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hz2),
        max_eq_right hz2.le]
    have : y = a • a⁻¹ • y := (inv_smul_eq_iff₀ ha').mp rfl
    rw [← hax, this, ← smul_sub, norm_smul, norm_smul, norm_sub_rev,
      ← dist_eq_norm, mul_lt_mul_iff_right₀ <| norm_pos_iff.mpr ha'] at hz2
    have := lt_of_le_of_lt (infDist_le_dist_of_mem
      (Submodule.mem_span_singleton.mpr ⟨a⁻¹,rfl⟩)) hz2
    linarith

lemma orth_symm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [iud : IsUltrametricDist E] {x y : E} :
(x ⟂[𝕜] y) ↔ (y ⟂[𝕜] x) :=
  ⟨fun h => orth_of_orth h, fun h => orth_of_orth h⟩

lemma orth_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [iud : IsUltrametricDist E] {x y : E} :
(x ⟂[𝕜] y) ↔ (∀ α β : 𝕜, ‖α • x + β • y‖ = max ‖α • x‖ ‖β • y‖) := by
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
      rw [this, norm_smul, mul_le_mul_iff_right₀ (norm_pos_iff.mpr hab.2)]
      rw [orth_symm] at h
      simpa only using le_of_eq h.symm
  · intro h
    unfold IsOrthogonal
    suffices hh : ∀ y' ∈ ↑(Submodule.span 𝕜 {y}), dist x y' ≥ ‖x‖ by
      refine eq_of_le_of_ge ?_ ?_
      · rw [← dist_zero, dist_comm]
        apply infDist_le_dist_of_mem
        simp only [SetLike.mem_coe, zero_mem]
      · rw [infDist_eq_iInf]
        refine (le_ciInf_set_iff ?_ ?_).mpr hh
        · use 0
          simp only [SetLike.mem_coe, zero_mem]
        · use ‖x‖
          simpa only [lowerBounds, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, ge_iff_le] using hh
    intro y' hy'
    rcases Submodule.mem_span_singleton.1 hy' with ⟨s, hs⟩
    rw [← hs, dist_eq_norm, sub_eq_add_neg, ← one_nsmul x,← neg_one_zsmul]
    have : -1 • s • y = (-1 * s) • y := by simp only [Int.reduceNeg, neg_smul, one_smul,
      neg_mul, one_mul]
    rw [this]
    specialize h 1 (-1 * s)
    simp only [Int.reduceNeg, neg_smul, one_smul, neg_mul, one_mul, norm_neg] at *
    simp only [h, le_sup_left]



lemma orth_comm'' {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] {F1 F2 : Subspace 𝕜 E} :
(F1 ⟂'' F2) ↔ (F2 ⟂'' F1) := by
  sorry

end SphericallyCompleteSpace
