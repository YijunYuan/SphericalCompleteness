/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Tactic.Common
public import SphericalCompleteness.External.Ultrametric.Basic
public import SphericalCompleteness.External.Ultrametric.NormedSpace

/-!
# Ultrametric instances

This module collects the results on ultrametric balls, groups, and normed spaces and provides the
ultrametric distance on bounded families.
-/

@[expose] public section

namespace IsUltrametricDist

/--
`lp E ⊤` (the `ℓ∞`-product) inherits an ultrametric distance from its coordinate spaces.

Assuming each component `E i` is an ultrametric space (via `IsUltrametricDist (E i)`), and that
the index type `ι` is nonempty, the induced distance on `lp E ⊤` is also ultrametric, i.e.
for all `x y z : lp E ⊤` we have
`dist x z ≤ max (dist x y) (dist y z)`.

This instance is the standard fact that the supremum metric on a product of ultrametric spaces
remains ultrametric.
-/
instance instIsUltrametricDistLp
    {ι : Type*} {E : ι → Type*} [Nonempty ι] [∀ i, NormedAddCommGroup (E i)]
    [iiud : ∀ i, IsUltrametricDist (E i)] :
    IsUltrametricDist (lp E ⊤) where
  dist_triangle_max a b c := by
    simp only [dist_eq_norm, lp.norm_eq_ciSup]
    refine ciSup_le fun j ↦ ?_
    rw [show ‖(↑(a - c) : (i : ι) → E i) j‖ = ‖a j - c j‖ from rfl, ← dist_eq_norm]
    refine ((iiud j).dist_triangle_max (a j) (b j) (c j)).trans (max_le_max ?_ ?_)
    · exact (dist_eq_norm _ _).trans_le (lp.norm_apply_le_norm ENNReal.top_ne_zero (a - b) j)
    · exact (dist_eq_norm _ _).trans_le (lp.norm_apply_le_norm ENNReal.top_ne_zero (b - c) j)

end IsUltrametricDist
