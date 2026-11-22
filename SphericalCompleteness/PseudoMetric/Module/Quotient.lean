/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import SphericalCompleteness.PseudoMetric.AddGroup.Quotient
public import SphericalCompleteness.PseudoMetric.Module.Basic

/-!
# The quotient of a module with a valued pseudoultrametric

A representative realizes its quotient distance to zero exactly when it is orthogonal to
the submodule. This identifies scalar multiplication on the quotient with scalar
multiplication on orthogonal representatives.
-/

@[expose] public section

namespace PseudoMetric

variable {K E Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [Zero Γ] [Add Γ] [LinearOrder Γ] (d : PseudoMetric E Γ) [d.IsAddInvariant] [d.IsUltra]
  (F : Submodule K E) [(d.comap (Subtype.val : F → E)).IsSphericallyComplete]

/-- The quotient pseudoultrametric on the quotient module, with its scalar action. -/
noncomputable abbrev moduleQuotient : PseudoMetric (E ⧸ F) Γ := d.addQuotient F.toAddSubgroup

instance : (d.moduleQuotient F).IsUltra :=
  inferInstanceAs (d.addQuotient F.toAddSubgroup).IsUltra

instance : (d.moduleQuotient F).IsAddInvariant :=
  inferInstanceAs (d.addQuotient F.toAddSubgroup).IsAddInvariant

instance [d.IsSphericallyComplete] : (d.moduleQuotient F).IsSphericallyComplete :=
  inferInstanceAs (d.addQuotient F.toAddSubgroup).IsSphericallyComplete

/-- A representative realizes the distance to zero in the quotient exactly when it is
orthogonal to the submodule. -/
theorem addQuotient_mk_zero_eq_iff_isOrthogonalTo (x : E) :
    d.moduleQuotient F (F.mkQ x) 0 = d x 0 ↔ d.IsOrthogonalTo x F := by
  constructor
  · intro h y hy
    have hy' : F.mkQ y = 0 := Submodule.Quotient.mk_eq_zero F |>.mpr hy
    rw [← h, ← hy']
    exact d.addQuotient_mk_le F.toAddSubgroup x y
  · intro h
    obtain ⟨z, hz, hd⟩ := d.exists_addQuotient_dist_eq F.toAddSubgroup 0 (F.mkQ x)
    change F.mkQ z = F.mkQ x at hz
    rw [map_zero] at hd
    refine le_antisymm ?_ (hd ▸ ?_)
    · have hle := d.addQuotient_mk_le F.toAddSubgroup x 0
      change d.moduleQuotient F (F.mkQ x) (F.mkQ 0) ≤ d x 0 at hle
      simpa only [map_zero] using hle
    · have hxz : x - z ∈ F := QuotientAddGroup.eq_iff_sub_mem.mp hz.symm
      simpa only [← d.sub_zero_eq x (x - z), sub_sub_cancel] using h (x - z) hxz

instance [d.IsSMulMono K] : (d.moduleQuotient F).IsSMulMono K where
  smul_le c {x y} h := by
    obtain ⟨u, hu, hu'⟩ := d.exists_addQuotient_dist_eq F.toAddSubgroup 0 x
    obtain ⟨v, hv, hv'⟩ := d.exists_addQuotient_dist_eq F.toAddSubgroup 0 y
    change F.mkQ u = x at hu
    change F.mkQ v = y at hv
    subst x y
    rw [map_zero] at hu' hv'
    have hou := ((d.addQuotient_mk_zero_eq_iff_isOrthogonalTo F u).mp hu'.symm).smul c
    have hov := ((d.addQuotient_mk_zero_eq_iff_isOrthogonalTo F v).mp hv'.symm).smul c
    rw [← F.mkQ.map_smul, ← F.mkQ.map_smul,
      (d.addQuotient_mk_zero_eq_iff_isOrthogonalTo F _).mpr hou,
      (d.addQuotient_mk_zero_eq_iff_isOrthogonalTo F _).mpr hov]
    exact IsSMulMono.smul_le (d := d) c (hu'.trans_le (h.trans_eq hv'.symm))

end PseudoMetric
