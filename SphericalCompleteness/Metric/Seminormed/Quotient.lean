/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import SphericalCompleteness.Metric.Seminormed.Basic
public import SphericalCompleteness.PseudoMetric.AddGroup.Quotient

/-!
# Spherical completeness of quotients of seminormed groups

The quotient seminorm lifts strict inequalities on distances, including when a coset has
no element of least norm. This suffices for spherical completeness.
-/

@[expose] public section

open Metric

/-- A quotient of a spherically complete ultrametric seminormed group is spherically complete. -/
@[to_additive /-- A quotient of a spherically complete ultrametric seminormed additive group
is spherically complete. -/]
theorem QuotientGroup.sphericallyCompleteSpace {G : Type*} [SeminormedCommGroup G]
    [IsUltrametricDist G] [SphericallyCompleteSpace G] (H : Subgroup G) :
    SphericallyCompleteSpace (G ⧸ H) := by
  apply (sphericallyCompleteSpace_iff _).mpr
  apply PseudoMetric.IsSphericallyComplete.of_lift_dist_lt (nnMetric G) (nnMetric (G ⧸ H))
    (QuotientGroup.mk'_surjective H) _ _ exists_seq_le_of_nonempty_radii
  · intro x z
    change nndist (QuotientGroup.mk' H x) (QuotientGroup.mk' H z) ≤ nndist x z
    apply NNReal.coe_le_coe.mp
    simp only [coe_nndist, dist_eq_norm_div, ← map_div]
    exact QuotientGroup.norm_mk_le_norm
  · intro x y r hy
    have hy' : ‖y / (QuotientGroup.mk' H) x‖ < r := by
      rw [← dist_eq_norm_div]; exact NNReal.coe_lt_coe.mpr hy
    obtain ⟨a, ha, har⟩ := QuotientGroup.norm_lt_iff.mp hy'
    refine ⟨a * x, ?_, ?_⟩
    · rw [map_mul, QuotientGroup.mk'_apply, ha, div_mul_cancel]
    · apply NNReal.coe_lt_coe.mp
      simpa only [nnMetric_apply, coe_nndist, dist_eq_norm_div, mul_div_cancel_right] using har

/-- For a spherically complete subgroup the minimum defining the valued quotient agrees
with the infimum defining the usual quotient seminorm. -/
theorem Metric.addQuotient_nnMetric {G : Type*} [SeminormedAddCommGroup G] [IsUltrametricDist G]
    (H : AddSubgroup G) [((nnMetric G).comap (Subtype.val : H → G)).IsSphericallyComplete] :
    (nnMetric G).addQuotient H = nnMetric (G ⧸ H) := by
  apply DFunLike.ext
  intro q
  funext q'
  rw [PseudoMetric.addQuotient_apply, nnMetric_apply, nnDist_eq_nnNorm]
  have hmin := (nnMetric G).isLeast_addQuotientNorm H (q - q')
  obtain ⟨a, ha, hnorm⟩ := hmin.1
  rw [← hnorm, nnMetric_apply, nndist_zero_right]
  apply le_antisymm
  · by_contra! h
    obtain ⟨b, hb, hb'⟩ := QuotientAddGroup.norm_lt_iff.mp (NNReal.coe_lt_coe.mpr h)
    have hle := hmin.2 (show (nnMetric G) b 0 ∈ _ from ⟨b, hb, rfl⟩)
    rw [← hnorm, nnMetric_apply, nnMetric_apply, nndist_zero_right, nndist_zero_right] at hle
    exact hb'.not_ge (NNReal.coe_le_coe.mpr hle)
  · rw [← ha]
    exact NNReal.coe_le_coe.mp QuotientAddGroup.norm_mk_le_norm
