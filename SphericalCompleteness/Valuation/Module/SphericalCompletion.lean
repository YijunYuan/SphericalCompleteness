/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.Module.SphericalCompletion
public import SphericalCompleteness.Valuation.Module.Basic

/-!
# Linear spherical completions of valued vector spaces

The valuation of a scalar acts on the completed space by the original homogeneity law.
The value monoid and its order are the same throughout the extension.
-/

@[expose] public section

namespace Valuation

universe u v w

variable {K : Type v} {E : Type u} {Γ : Type w} [DivisionRing K] [AddCommGroup E] [Module K E]
    [LinearOrderedCommMonoidWithZero Γ] {vK : Valuation K Γ} {d : PseudoMetric E (MaxTropical Γ)}

/-- Homogeneity over the valued division ring passes to an immediate linear extension:
an element and all of its scalar multiples realize their values already in the base. -/
theorem IsHomogeneous.of_isImmediate (hd : vK.IsHomogeneous d) {F : Type*} [AddCommGroup F]
    [Module K F] {e : PseudoMetric F (MaxTropical Γ)} [e.IsAddInvariant] [e.IsSMulMono K]
    {i : E →ₗ[K] F} (hi : e.IsImmediate i) (hbase : ∀ x, e (i x) 0 = d x 0) :
    vK.IsHomogeneous e := by
  intro c y
  obtain ⟨x, hx⟩ := hi.exists_forall_smul_dist_eq e K y
  have hy : e y 0 = d x 0 := by simpa only [one_smul, hbase] using hx 1
  rw [hx c, hbase, hd, hy]

/-- Every valued vector space admits an immediate linear spherical completion for the same
scalar valuation. The embedding is injective even when the seminorm has a kernel. -/
theorem IsHomogeneous.exists_linearSphericalCompletion [d.IsAddInvariant]
    (hd : vK.IsHomogeneous d) :
    ∃ (F : Type (max u w)) (_ : AddCommGroup F) (_ : Module K F)
      (e : PseudoMetric F (MaxTropical Γ)) (i : E →ₗ[K] F),
      e.IsAddInvariant ∧ vK.IsHomogeneous e ∧ d.IsLinearSphericalCompletion e i := by
  let := hd.isSMulMono
  obtain ⟨F, hF, hKF, e, i, _, hadd, hsmul, hi⟩ := d.exists_linearSphericalCompletion K
  exact ⟨F, hF, hKF, e, i, hadd, hd.of_isImmediate hi.immediate
    (fun x ↦ by simpa only [map_zero] using hi.map_dist x 0), hi⟩

/-- Spherical completeness is equivalent to having no proper immediate linear extension
homogeneous for the given valuation. -/
theorem IsHomogeneous.isSphericallyComplete_iff_maximallyComplete [d.IsAddInvariant]
    (hd : vK.IsHomogeneous d) :
    d.IsSphericallyComplete ↔ ∀ {F : Type (max u w)} [AddCommGroup F] [Module K F]
      (e : PseudoMetric F (MaxTropical Γ)) [e.IsAddInvariant], vK.IsHomogeneous e →
      ∀ i : E →ₗ[K] F, Function.Injective i → (∀ x y, e (i x) (i y) = d x y) →
      e.IsImmediate i → Function.Surjective i := by
  constructor
  · exact fun _ _ _ _ e _ _ _ _ hdist hi ↦ hi.surjective d e hdist
  · intro h
    obtain ⟨F, _, _, e, i, _, he, hi⟩ := hd.exists_linearSphericalCompletion
    have hsurj := h e he i hi.injective hi.map_dist hi.immediate
    exact (d.isSphericallyComplete_iff_of_surjective e hsurj hi.map_dist).mpr hi.complete

end Valuation
