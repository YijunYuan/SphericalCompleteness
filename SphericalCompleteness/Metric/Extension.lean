/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import SphericalCompleteness.Metric.Defs
public import SphericalCompleteness.PseudoMetric.Extension

/-!
# Lipschitz extensions of maps between pseudoultrametric spaces

A Lipschitz map into a nonempty spherically complete pseudoultrametric space extends
from any subset of its domain with the same Lipschitz constant.
-/

@[expose] public section

namespace Metric

open scoped NNReal

/-- Extend a Lipschitz map from a subset into a nonempty spherically complete
pseudoultrametric space, preserving its Lipschitz constant. -/
theorem exists_lipschitzWith_extension {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [IsUltrametricDist X] [IsUltrametricDist Y] [Nonempty Y] [SphericallyCompleteSpace Y]
    (D : Set X) {K : ℝ≥0} (f : D → Y) (hf : LipschitzWith K f) :
    ∃ g : X → Y, (∀ x : D, g x = f x) ∧ LipschitzWith K g := by
  obtain ⟨g, hg, h⟩ := (nnMetric X).exists_extension_of_le_modulus (nnMetric Y) (K * ·)
    (fun _ _ h ↦ mul_le_mul_of_nonneg_left h K.2) (by simp) D f hf.nndist_le
  exact ⟨g, hg, LipschitzWith.of_dist_le_mul (fun x y ↦ NNReal.coe_le_coe.mpr (h x y))⟩

end Metric
