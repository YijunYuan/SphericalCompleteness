/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.Valuation.Basic
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Completeness of a spherically complete valued ring

The closed valuation balls belonging to a Cauchy filter meet pairwise. Their intersection contains
a limit of the filter, including when the value group is trivial or the support is nonzero.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Valuation

variable {R Γ₀ : Type*} [Ring R] [ValuativeRel R] [UniformSpace R] [IsUniformAddGroup R]
    [IsValuativeTopology R] [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} [v.Compatible]

/-- Every open valuation radius admits a strictly smaller closed radius whose ball around some
point belongs to the Cauchy filter. The closed radius may be zero. -/
private theorem exists_closedBall_mem_of_cauchy {F : Filter R} (hF : Cauchy F)
    (γ : v.ValueGroup₀ˣ) :
    ∃ (c : R) (r : v.ValueGroup₀), r < γ.val ∧ {x | v.restrict (x - c) ≤ r} ∈ F := by
  obtain ⟨hne, hc⟩ := v.cauchy_iff.mp hF
  have chooseCenter (δ : v.ValueGroup₀ˣ) : ∃ c : R, {x | v.restrict (x - c) < δ.val} ∈ F := by
    obtain ⟨M, hM, hdiam⟩ := hc δ
    obtain ⟨c, hc⟩ := Filter.nonempty_of_mem hM
    exact ⟨c, mem_of_superset hM fun x hx ↦ hdiam c hc x hx⟩
  by_cases hδ : ∃ δ : v.ValueGroup₀ˣ, δ.val < γ.val
  · obtain ⟨δ, hδ⟩ := hδ
    obtain ⟨c, hc⟩ := chooseCenter δ
    refine ⟨c, δ.val, hδ, mem_of_superset hc fun x hx ↦ ?_⟩
    exact show v.restrict (x - c) ≤ δ.val from le_of_lt hx
  · obtain ⟨c, hc⟩ := chooseCenter γ
    refine ⟨c, 0, Units.zero_lt γ, mem_of_superset hc fun x hx ↦ ?_⟩
    change v.restrict (x - c) ≤ 0
    by_contra! h
    exact hδ ⟨Units.mk0 _ h.ne', hx⟩

/-- A spherically complete valuation makes every Cauchy filter converge in a compatible
valuative uniformity. -/
theorem IsSphericallyComplete.completeSpace (h : v.IsSphericallyComplete) : CompleteSpace R := by
  constructor
  intro F hF
  have : F.NeBot := hF.1
  let d := v.restrict.toPseudoMetric
  let S := {B ∈ d.closedBalls | B ∈ F}
  have hsmall (γ : v.ValueGroup₀ˣ) :
      ∃ (c : R) (r : v.ValueGroup₀), r < γ.val ∧ d.closedBall c (MaxTropical.trop r) ∈ S := by
    obtain ⟨c, r, hr, hmem⟩ := exists_closedBall_mem_of_cauchy hF γ
    exact ⟨c, r, hr, ⟨c, MaxTropical.trop r, rfl⟩, hmem⟩
  obtain ⟨c, r, _, hmem⟩ := hsmall 1
  have hs := v.isEquiv_restrict.isSphericallyComplete_iff.mp h
  obtain ⟨z, hz⟩ := (PseudoMetric.isSphericallyComplete_iff_pairwise d).mp hs S
    (fun _ hB ↦ hB.1) ⟨_, hmem⟩
    (fun _ hB _ hC ↦ Filter.nonempty_of_mem (inter_mem hB.2 hC.2))
  refine ⟨z, fun U hU ↦ ?_⟩
  obtain ⟨γ, hγ⟩ := v.mem_nhds_iff.mp hU
  obtain ⟨c, r, hr, hb⟩ := hsmall γ
  have hz' : v.restrict (z - c) ≤ r := mem_sInter.mp hz _ hb
  refine mem_of_superset hb.2 fun x hx ↦ hγ ?_
  have hx' : v.restrict (x - c) ≤ r := hx
  have hxz : v.restrict (x - z) ≤ r := by
    simpa only [sub_sub_sub_cancel_right] using v.restrict.map_sub_le hx' hz'
  exact hxz.trans_lt hr

end Valuation

/-- Spherical completeness of the canonical valuation implies completeness of the valuative
uniform space. -/
instance (priority := low) ValuativeRel.completeSpace_of_isSphericallyComplete
    {R : Type*} [Ring R] [ValuativeRel R] [UniformSpace R] [IsUniformAddGroup R]
    [IsValuativeTopology R] [h : ValuativeRel.IsSphericallyComplete R] : CompleteSpace R :=
  Valuation.IsSphericallyComplete.completeSpace (v := ValuativeRel.valuation R) h
