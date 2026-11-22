/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.Module.Quotient
public import SphericalCompleteness.Valuation.Module.Basic

/-! # The valuative seminorm on a quotient by a spherically complete subspace -/

@[expose] public section

namespace Valuation

variable {K E Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [LinearOrderedCommMonoidWithZero Γ] {v : Valuation K Γ}
    {d : PseudoMetric E (MaxTropical Γ)} [d.IsAddInvariant]

/-- Quotienting by a spherically complete subspace preserves homogeneity for the same
valuation and value monoid. Each coset has a representative of least valuative seminorm. -/
theorem IsHomogeneous.moduleQuotient (hd : v.IsHomogeneous d) (D : Submodule K E)
    [(d.comap ((↑) : D → E)).IsSphericallyComplete] : v.IsHomogeneous (d.moduleQuotient D) := by
  let := hd.isSMulMono
  intro a q
  obtain ⟨x, hx, hdist⟩ := d.exists_addQuotient_dist_eq D.toAddSubgroup 0 q
  change D.mkQ x = q at hx
  subst q
  rw [map_zero] at hdist
  change d x 0 = d.moduleQuotient D (D.mkQ x) 0 at hdist
  have horth := (d.addQuotient_mk_zero_eq_iff_isOrthogonalTo D x).mp hdist.symm
  rw [← D.mkQ.map_smul, (d.addQuotient_mk_zero_eq_iff_isOrthogonalTo D _).mpr (horth.smul a),
    ← hdist, hd]

end Valuation
