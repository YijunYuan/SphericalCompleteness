import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Operator.LinearIsometry
open Metric
open Filter


noncomputable def ndist (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] (x y : {z : E // z ≠ 0}) :=
(Metric.infDist x.val (𝕜 ∙ y.val)) / ‖x.val‖

def orth (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] (x y : E) := Metric.infDist x (𝕜 ∙ y) = ‖x‖

noncomputable def orth' (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] (x : E) (F : Subspace 𝕜 E) := Metric.infDist x F = ‖x‖

lemma orth'_iff (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] (x : E) (F : Subspace 𝕜 E) :
  orth' 𝕜 x F ↔ ∀ y ∈ F, orth 𝕜 x y := by
  unfold orth orth'
  constructor
  · intro h y hy
    refine eq_of_le_of_not_lt ?_ ?_
    · have := (@Metric.le_infDist E _
        (↑(Submodule.span 𝕜 {y}) : Set E) x (infDist x ↑(Submodule.span 𝕜 {y}))
        (Submodule.nonempty (Submodule.span 𝕜 {y}))).1 (le_refl _) (zero_mem _)
      simpa only [ge_iff_le, dist_zero_right] using this
    · by_contra hc
      rcases (@Metric.infDist_lt_iff E _
        (↑(Submodule.span 𝕜 {y}) : Set E) x ‖x‖
        (Submodule.nonempty (Submodule.span 𝕜 {y}))).1 hc with ⟨y',hy'⟩
      have := (@Metric.le_infDist E _ ↑F x ‖x‖ (Submodule.nonempty F)).1 (by simp only [h,
        le_refl]) (by aesop : y' ∈ F)
      replace hy' := hy'.2
      linarith
  · intro h
    refine eq_of_le_of_not_lt ?_ ?_
    · have := @Metric.infDist_le_dist_of_mem E _ ↑F x 0 (zero_mem _)
      simpa only [ge_iff_le, dist_zero_right] using this
    · by_contra hc
      rcases (@Metric.infDist_lt_iff E _
        ↑F x ‖x‖ (Submodule.nonempty F)).1 hc with ⟨y,hy⟩
      specialize h y hy.1
      have := h ▸ (@Metric.le_infDist E _ ↑(Submodule.span 𝕜 {y})
        x (infDist x ↑(Submodule.span 𝕜 {y}))
        (Submodule.nonempty (Submodule.span 𝕜 {y}))).1
        (le_refl _) (Submodule.mem_span_singleton_self y)
      replace hy := hy.2
      linarith

noncomputable def test (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [NormedAddCommGroup E]
[NormedSpace 𝕜 E] (x : E) (F : Subspace 𝕜 E) (hxF : orth' 𝕜 x F) :
(Submodule.span 𝕜 {x}) × F≃ₛₗᵢ[RingHom.id 𝕜] (Submodule.span 𝕜 {x}) + F where
  toFun z := ⟨z.1.val + z.2.val, by
    simp only [Submodule.add_eq_sup]
    refine Submodule.add_mem_sup z.1.prop z.2.prop
    ⟩
  map_add' := by
    simp only [Submodule.add_eq_sup, Prod.fst_add, Submodule.coe_add, Prod.snd_add,
      AddMemClass.mk_add_mk, Subtype.mk.injEq, Prod.forall, Subtype.forall]
    intros
    exact add_add_add_comm _ _ _ _
  map_smul' := by
    intro m a
    simp only [Submodule.add_eq_sup, Prod.smul_fst, SetLike.val_smul, Prod.smul_snd,
      RingHom.id_apply, SetLike.mk_smul_mk, smul_add]
  norm_map' := by
    simp only [Submodule.add_eq_sup, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      AddSubgroupClass.coe_norm, Prod.forall, Prod.norm_mk, Subtype.forall]
    intro a ha b hab
    if hh : a = 0 ∨ b = 0 then
      cases' hh with hh hh
      · simp only [hh, zero_add, norm_zero, norm_nonneg, sup_of_le_right]
      · simp only [hh, add_zero, norm_zero, norm_nonneg, sup_of_le_left]
    else
      replace hh : a ≠ b := by
        by_contra h
        unfold orth' at hxF
        subst h
        simp only [or_self] at hh
        rcases (Submodule.mem_span_singleton.1 ha) with ⟨c,hc⟩
        rw [← hc] at hab
        have : c ≠ 0 := by
          by_contra hcc
          simp only [hcc, zero_smul] at hc
          exact hh hc.symm
        replace hab : x ∈ F := by
          have : c⁻¹ • c • x ∈ F := Submodule.smul_mem F c⁻¹ hab
          simp only [smul_smul] at this
          simp_all only [ne_eq, not_false_eq_true,
            inv_mul_cancel₀, one_smul]
        have := hxF ▸ @Metric.infDist_le_dist_of_mem E _ F x x hab
        simp only [dist_self] at this
        replace : ‖x‖ = 0 := eq_of_le_of_ge this (norm_nonneg x)
        simp only [norm_eq_zero] at this
        simp only [this, Submodule.span_zero_singleton, Submodule.mem_bot] at ha
        exact hh ha

      sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
