/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import SphericalCompleteness.Metric.Seminormed.Basic
public import SphericalCompleteness.PseudoMetric.Module.SphericalCompletion

/-!
# Immediate spherical completions of seminormed and normed spaces

The arbitrary-value linear construction for the nonnegative-real distance also preserves
scalar homogeneity. Its distance to zero gives a seminorm on the extension. When the source
is separated, immediacy ensures that the extension is separated as well.
-/

@[expose] public section

open Function
open scoped NNReal

namespace Metric

variable {K E : Type*} [NormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]

private theorem seminormed_of_immediate {F : Type*} [AddCommGroup F] [Module K F]
    (e : PseudoMetric F ℝ≥0) [e.IsUltra] [e.IsAddInvariant] [e.IsSMulMono K]
    [e.IsSphericallyComplete] (i : E →ₗ[K] F) (hinj : Injective i)
    (hd : ∀ x y, e (i x) (i y) = nnMetric E x y) (hi : e.IsImmediate i) :
    ∃ (_ : SeminormedAddCommGroup F) (_ : NormedSpace K F) (_ : IsUltrametricDist F)
      (f : E →ₗᵢ[K] F), SphericallyCompleteSpace F ∧ Injective f ∧ (nnMetric F).IsImmediate f := by
  let n : Norm F := ⟨fun y ↦ (e y 0 : ℝ)⟩
  have base (x : E) : e (i x) 0 = ‖x‖₊ := by
    simpa only [map_zero, nnMetric_apply, nndist_zero_right] using hd x 0
  let core : SeminormedSpace.Core K F := {
    norm_nonneg := fun x ↦ (e x 0).property
    norm_smul := fun c y ↦ by
      obtain ⟨x, hx⟩ := hi.exists_forall_smul_dist_eq e K y
      have h₁ := hx 1
      simp only [one_smul] at h₁
      change (e (c • y) 0 : ℝ) = ‖c‖ * (e y 0 : ℝ)
      rw [hx c, h₁, base, base, nnNorm_smul, NNReal.coe_mul, coe_nnNorm]
    norm_triangle := fun x y ↦ by
      have ht : e (x + y) y = e x 0 := by
        simpa only [zero_add] using PseudoMetric.IsAddInvariant.add_right (d := e) x 0 y
      exact NNReal.coe_le_coe.mpr ((e.triangle (x + y) y 0).trans_eq (by rw [ht])) }
  let sf : SeminormedAddCommGroup F := .ofCore core
  let ns : NormedSpace K F := { norm_smul_le c y := (core.norm_smul c y).le }
  have he : nnMetric F = e := by
    ext x y
    change (nndist x y : ℝ) = (e x y : ℝ)
    rw [coe_nndist, dist_eq_norm]
    exact congrArg NNReal.toReal (e.sub_zero_eq x y)
  let uf : IsUltrametricDist F := ⟨fun x y z ↦ by
    rw [← coe_nndist, ← coe_nndist, ← coe_nndist, ← NNReal.coe_max, NNReal.coe_le_coe]
    change nnMetric F x z ≤ max (nnMetric F x y) (nnMetric F y z)
    rw [he]
    exact PseudoMetric.IsUltra.le_sup' (d := e) x y z⟩
  let f : E →ₗᵢ[K] F := ⟨i, fun x ↦ congrArg NNReal.toReal (base x)⟩
  exact ⟨sf, ns, uf, f, (sphericallyCompleteSpace_iff _).mpr (he ▸ inferInstanceAs
    e.IsSphericallyComplete), hinj, he ▸ hi⟩

private theorem normed_of_seminormed_immediate {K E F : Type*} [NormedField K]
    [NormedAddCommGroup E] [NormedSpace K E] [SeminormedAddCommGroup F] [NormedSpace K F]
    [IsUltrametricDist F] (i : E →ₗᵢ[K] F) (hsc : SphericallyCompleteSpace F)
    (hi : (nnMetric F).IsImmediate i) :
    ∃ nf : NormedAddCommGroup F,
      let _ := nf.toSeminormedAddCommGroup
      ∃ (_ : NormedSpace K F) (_ : IsUltrametricDist F) (f : E →ₗᵢ[K] F),
        SphericallyCompleteSpace F ∧ (nnMetric F).IsImmediate f := by
  have sep (x : F) (hx : ‖x‖ = 0) : x = 0 := by
    by_cases him : x ∈ Set.range i
    · obtain ⟨y, rfl⟩ := him
      rw [i.norm_map] at hx
      rw [norm_eq_zero.mp hx, map_zero]
    obtain ⟨y, hy⟩ := (hi x him).2 0
    simp only [nnMetric_apply, ← NNReal.coe_lt_coe, coe_nndist, map_zero, dist_zero_right, hx] at hy
    exact (hy.not_ge dist_nonneg).elim
  let nf : NormedAddCommGroup F := { ‹SeminormedAddCommGroup F› with
    eq_of_dist_eq_zero := fun {x y} h ↦ sub_eq_zero.mp <| sep (x - y) (dist_eq_norm x y ▸ h) }
  exact ⟨nf, inferInstance, inferInstance, i, hsc, hi⟩

/-- Every ultrametric seminormed space has a spherically complete, immediate linear
extension in the universe of the source. Its inclusion is injective on points, including
distinct vectors whose difference has seminorm zero. -/
theorem exists_seminormed_linearSphericalCompletion (K : Type*) [NormedField K] (E : Type u)
    [SeminormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E] :
    ∃ (F : Type u) (_ : SeminormedAddCommGroup F) (_ : NormedSpace K F) (_ : IsUltrametricDist F)
      (i : E →ₗᵢ[K] F), SphericallyCompleteSpace F ∧ Injective i ∧ (nnMetric F).IsImmediate i := by
  obtain ⟨F, _, _, e, i, _, _, _, _, hinj, hd, hi⟩ :=
    (nnMetric E).exists_linearSphericalCompletion K
  exact ⟨F, seminormed_of_immediate e i hinj hd hi⟩

/-- A normed space over any normed field has a spherically complete immediate normed
linear extension. -/
theorem exists_normed_linearSphericalCompletion (K : Type*) [NormedField K] (E : Type u)
    [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E] :
    ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace K F) (_ : IsUltrametricDist F)
      (i : E →ₗᵢ[K] F), SphericallyCompleteSpace F ∧ (nnMetric F).IsImmediate i := by
  obtain ⟨F, _, _, _, i, hsc, _, hi⟩ := exists_seminormed_linearSphericalCompletion K E
  exact ⟨F, normed_of_seminormed_immediate i hsc hi⟩

end Metric
