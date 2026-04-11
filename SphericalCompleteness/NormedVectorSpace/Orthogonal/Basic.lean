import SphericalCompleteness.NormedVectorSpace.Orthogonal.Defs

open Metric

namespace SphericallyCompleteSpace

private lemma orth_of_orth {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [iud : IsUltrametricDist E] {x y : E}
  (h : x ⟂[𝕜] y) : y ⟂[𝕜] x := by
  unfold Orth at *
  refine eq_of_le_of_not_lt ?_ ?_
  · have := @infDist_le_dist_of_mem E _ ↑(Submodule.span 𝕜 {x}) y 0 (by simp)
    simpa only [ge_iff_le, dist_zero_right] using this
  · by_contra hc
    rcases (infDist_lt_iff (by use 0; simp)).1 hc with ⟨z, hz1, hz2⟩
    simp only [SetLike.mem_coe] at hz1
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
  ⟨orth_of_orth, orth_of_orth⟩

lemma orth_iff_birkhoff_james_orth {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [iud : IsUltrametricDist E]
(x y : E) :
(x ⟂[𝕜] y) ↔ ∀ c : 𝕜, ‖x‖ ≤ ‖x + c • y‖ := by
  constructor
  · intro h c
    have : x + c • y = x - (-c) • y := by
      simp only [neg_smul, sub_neg_eq_add]
    rw [← h, this, ← dist_eq_norm]
    refine infDist_le_dist_of_mem ?_
    simp only [neg_smul, SetLike.mem_coe, neg_mem_iff]
    exact Submodule.mem_span_singleton.mpr ⟨c, by simp⟩
  · intro h
    by_contra hc
    replace hc := lt_of_le_of_ne ?_ hc
    · replace hc := (infDist_lt_iff ?_).1 hc
      · rcases hc with ⟨y', hy', hy''⟩
        rcases Submodule.mem_span_singleton.1 hy' with ⟨c, hc⟩
        rw [← hc, dist_eq_norm, sub_eq_add_neg, ← neg_smul] at hy''
        specialize h (-c); linarith
      · use 0; simp only [SetLike.mem_coe, zero_mem]
    · nth_rw 2 [← sub_zero x]
      rw [← dist_eq_norm]
      refine infDist_le_dist_of_mem ?_
      simp only [SetLike.mem_coe, zero_mem]

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
        simp only [neg_mem_iff]
        refine Submodule.mem_span_singleton.mpr ?_
        use b : - (b • y) ∈ 𝕜 ∙ y)
      have := infDist_smul₀ hab.1 (Submodule.span 𝕜 {y} : Set E) x
      rw [smul_submodule_eq_self hab.1] at this
      rw [this, h, norm_smul]
    · have : a • x + b • y = b • y - - (a • x) := by abel
      rw [this, ← dist_eq_norm]
      refine le_trans ?_ <| infDist_le_dist_of_mem (by
        simp only [neg_mem_iff]
        refine Submodule.mem_span_singleton.mpr ?_
        use a : - (a • x) ∈ 𝕜 ∙ x)
      have := infDist_smul₀ hab.2 (Submodule.span 𝕜 {x} : Set E) y
      rw [smul_submodule_eq_self hab.2] at this
      rw [this, norm_smul, mul_le_mul_iff_right₀ (norm_pos_iff.mpr hab.2)]
      rw [orth_symm] at h
      simpa only using le_of_eq h.symm
  · intro h
    unfold Orth
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

theorem smul_orth_of_orth {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] {x y : E}
(a : 𝕜) : (x ⟂[𝕜] y) → ((a • x) ⟂[𝕜] y) := by
  intro h
  unfold Orth at *
  if ha : a = 0 then
    subst ha
    simp only [zero_smul, norm_zero]
    refine infDist_zero_of_mem ?_
    simp only [SetLike.mem_coe, zero_mem]
  else
  rw [norm_smul, ← h, ← infDist_smul₀ ha]
  congr
  rw [smul_submodule_eq_self ha]

theorem smul_orth_iff_orth_of_nonzero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] {x y : E}
{a : 𝕜} (ha : a ≠ 0) : (x ⟂[𝕜] y) ↔ ((a • x) ⟂[𝕜] y) := by
  refine ⟨smul_orth_of_orth a, fun h => ?_⟩
  apply smul_orth_of_orth a⁻¹ at h
  rwa [inv_smul_smul₀ ha x] at h

theorem orth_smul_of_orth {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] {x y : E}
(a : 𝕜) : (x ⟂[𝕜] y) → (x ⟂[𝕜] (a • y)) := by
  intro h
  rw [orth_symm] at *
  exact smul_orth_of_orth a h

theorem orth_smul_iff_orth_of_nonzero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] {x y : E}
{a : 𝕜} (ha : a ≠ 0) : (x ⟂[𝕜] y) ↔ (x ⟂[𝕜] (a • y)) := by
  nth_rw 1 [orth_symm]
  nth_rw 2 [orth_symm]
  exact smul_orth_iff_orth_of_nonzero ha

lemma morth_iff_forall_orth {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(x : E) (F : Subspace 𝕜 E) :
  (x ⟂ₘ F) ↔ ∀ y ∈ F, (x ⟂[𝕜] y) := by
  constructor
  · intro h y hy
    refine eq_of_le_of_not_lt ?_ ?_
    · simpa only [dist_zero_right] using
        @infDist_le_dist_of_mem E _ _ x 0 (Submodule.zero_mem (Submodule.span 𝕜 {y}))
    · by_contra hc
      rcases (infDist_lt_iff (Submodule.nonempty (Submodule.span 𝕜 {y}))).1 hc with ⟨y', hy'⟩
      exact lt_iff_not_ge.1 hy'.2 <| (le_infDist (Submodule.nonempty F)).1
        (by rw [h]) (by aesop : y' ∈ F)
  · intro h
    refine eq_of_le_of_not_lt ?_ ?_
    · simpa only [dist_zero_right] using infDist_le_dist_of_mem (Submodule.zero_mem F)
    · by_contra hc
      rcases (infDist_lt_iff (Submodule.nonempty F)).1 hc with ⟨y, hy⟩
      exact lt_iff_not_ge.1 hy.2 <|
        (h y hy.1) ▸ (le_infDist (Submodule.nonempty (Submodule.span 𝕜 {y}))).1
          le_rfl (Submodule.mem_span_singleton_self y)

-- This is important, but it requires `NormedAddCommGroup` instead of `SeminormedAddCommGroup`
theorem eq_zero_of_morth_of_mem {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [NormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
{x : E} {F : Subspace 𝕜 E} : x ∈ F → (x ⟂ₘ F) → x = 0 := by
  intro h1 h2
  unfold MOrth at h2
  rw [infDist_zero_of_mem h1] at h2
  exact norm_eq_zero.mp h2.symm

theorem smul_morth_of_morth {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
{x : E} {F : Subspace 𝕜 E} (a : 𝕜) :
  (x ⟂ₘ F) → ((a • x) ⟂ₘ F) := by
  intro h
  rw [morth_iff_forall_orth] at *
  intro y hy
  exact smul_orth_of_orth a (h y hy)

theorem smul_morth_iff_morth_of_nonzero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
{x : E} {F : Subspace 𝕜 E} {a : 𝕜} (ha : a ≠ 0) :
  (x ⟂ₘ F) ↔ ((a • x) ⟂ₘ F) := by
  refine ⟨smul_morth_of_morth a, fun h => ?_⟩
  apply smul_morth_of_morth a⁻¹ at h
  rwa [inv_smul_smul₀ ha x] at h

theorem not_morth_iff_exists_dist_lt_norm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
{x : E} {F : Subspace 𝕜 E} :
  ¬ (x ⟂ₘ F) ↔ ∃ y ∈ F, dist x y < ‖x‖ := by
  unfold MOrth
  constructor
  · intro h
    contrapose h
    push_neg at h
    exact eq_of_le_of_ge
      (by simpa only [dist_zero_right] using infDist_le_dist_of_mem (by simp : (0 : E) ∈ ↑F))
      ((le_infDist <| Submodule.nonempty F).2 h)
  · intro h
    contrapose h
    push_neg
    rw [← h]
    exact fun z hz => infDist_le_dist_of_mem hz

theorem sorth_iff_forall_orth {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(F1 F2 : Subspace 𝕜 E) : (F1 ⟂ₛ F2) ↔ ∀ x ∈ F1, ∀ y ∈ F2, (x ⟂[𝕜] y) := by
  simp only [SOrth, morth_iff_forall_orth]

private lemma sorth_of_sorth {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] {F1 F2 : Subspace 𝕜 E} :
(F1 ⟂ₛ F2) → (F2 ⟂ₛ F1) := by
  intro h
  simp only [SOrth, morth_iff_forall_orth] at *
  exact fun x hx y hy => orth_of_orth (h y hy x hx)

theorem sorth_symm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] {F1 F2 : Subspace 𝕜 E} :
(F1 ⟂ₛ F2) ↔ (F2 ⟂ₛ F1) :=
  ⟨sorth_of_sorth, sorth_of_sorth⟩

end SphericallyCompleteSpace
