/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import SphericalCompleteness.Metric.Defs
public import SphericalCompleteness.PseudoMetric.Module.Basic

/-!
# The bundled pseudometric of a seminormed space

The usual seminorm gives a translation-invariant distance, and scalar multiplication
preserves comparisons. On a scalar line the distance is the scalar distance multiplied by
the seminorm of the generator, which may be zero.
-/

@[expose] public section

namespace Metric

variable {K E : Type*} [SeminormedAddCommGroup E]

instance : (nnMetric E).IsAddInvariant where
  add_right x y a := by simp only [nnMetric_apply, nnDist_eq_nnNorm, add_sub_add_right_eq_sub]

variable [NormedField K] [NormedSpace K E]

instance : (nnMetric E).IsSMulMono K where
  smul_le a x y h := by
    simpa only [nnMetric_apply, nndist_zero_right, nnNorm_smul] using
      (mul_le_mul_right (show ‖x‖₊ ≤ ‖y‖₊ by simpa only [nnMetric_apply, nndist_zero_right] using h)
        ‖a‖₊)

end Metric
