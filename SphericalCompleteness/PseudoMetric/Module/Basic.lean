/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import SphericalCompleteness.PseudoMetric.AddGroup.Basic

/-!
# Orthogonality for translation-invariant pseudoultrametrics

A vector is orthogonal to a subspace when zero is one of its best approximations in the
subspace. This only compares distances. It applies to arbitrary ordered values, including
distances that vanish on distinct points.
-/

@[expose] public section

namespace PseudoMetric

variable {E Γ : Type*} [Zero Γ] [Add Γ]

section Pointed

variable [LE Γ] [Zero E] (d : PseudoMetric E Γ)

/-- Scalar multiplication preserves weak comparisons of distances from the origin.
For a nonzero scalar the inverse scalar gives the reverse implication. -/
class IsSMulMono (K : Type*) [SMul K E] : Prop where
  smul_le : ∀ (a : K) {x y : E}, d x 0 ≤ d y 0 → d (a • x) 0 ≤ d (a • y) 0

/-- Zero is a best approximation to `x` in `S` when `S` contains zero and this inequality holds. -/
def IsOrthogonalTo (x : E) (S : Set E) : Prop := ∀ y ∈ S, d x 0 ≤ d x y

end Pointed

variable [AddCommGroup E] [LinearOrder Γ] (d : PseudoMetric E Γ)

/-- Nonzero scalar multiplication preserves strict inequalities of distances from zero. -/
theorem IsSMulMono.smul_lt {K : Type*} [DivisionRing K] [Module K E] [d.IsSMulMono K]
    {c : K} (hc : c ≠ 0) {x y : E} (h : d x 0 < d y 0) : d (c • x) 0 < d (c • y) 0 := by
  apply lt_of_not_ge
  intro hle
  have hback := IsSMulMono.smul_le (d := d) c⁻¹ hle
  exact h.not_ge (by simpa only [inv_smul_smul₀ hc] using hback)

/-- Nonzero scalar multiplication preserves strict distance comparisons in a
translation-invariant pseudometric. -/
theorem IsSMulMono.smul_dist_lt {K : Type*} [DivisionRing K] [Module K E] [d.IsSMulMono K]
    [d.IsAddInvariant] {c : K} (hc : c ≠ 0) {w x y z : E} (h : d w x < d y z) :
    d (c • w) (c • x) < d (c • y) (c • z) := by
  simpa only [smul_sub, d.sub_zero_eq] using
    IsSMulMono.smul_lt d hc (x := w - x) (y := y - z) (by simpa only [d.sub_zero_eq] using h)

section Restrict

variable {K : Type*} [Ring K] [Module K E] (F : Submodule K E)

instance [d.IsAddInvariant] : (d.comap ((↑) : F → E)).IsAddInvariant where
  add_right x y a := IsAddInvariant.add_right (d := d) (x : E) y a

instance [d.IsSMulMono K] : (d.comap ((↑) : F → E)).IsSMulMono K where
  smul_le a _ _ h := IsSMulMono.smul_le (d := d) a h

end Restrict

variable {K : Type*} [DivisionRing K] [Module K E] {d}
variable {F G : Submodule K E} {x : E}

theorem IsOrthogonalTo.smul [d.IsAddInvariant] [d.IsSMulMono K] [d.IsUltra]
    (h : d.IsOrthogonalTo x F) (a : K) : d.IsOrthogonalTo (a • x) F := by
  intro y hy
  by_cases ha : a = 0
  · simpa only [ha, zero_smul, d.refl] using d.nonneg_of_ultra 0 y
  have hle := h (a⁻¹ • y) (F.smul_mem _ hy)
  rw [← d.sub_zero_eq x (a⁻¹ • y)] at hle
  have hmul := IsSMulMono.smul_le (d := d) a hle
  rwa [smul_sub, smul_inv_smul₀ ha, d.sub_zero_eq] at hmul

/-- On the sum of orthogonal vectors the distance to zero is the larger of the two values. -/
theorem IsOrthogonalTo.add_eq_max [d.IsAddInvariant] [d.IsUltra]
    (h : d.IsOrthogonalTo x F) {y : E} (hy : y ∈ F) :
    d (x + y) 0 = max (d x 0) (d y 0) := by
  have htrans : d (x + y) y = d x 0 := by
    simpa only [zero_add] using IsAddInvariant.add_right (d := d) x 0 y
  have hle : d x 0 ≤ d (x + y) 0 := by
    simpa only [← d.sub_zero_eq x (-y), sub_neg_eq_add] using h (-y) (F.neg_mem hy)
  refine le_antisymm ((IsUltra.le_sup' (d := d) (x + y) y 0).trans_eq (by rw [htrans]))
    (max_le hle ?_)
  exact (IsUltra.le_sup' (d := d) y (x + y) 0).trans
    (sup_le (by rwa [d.symm y (x + y), htrans]) le_rfl)

/-- Two subspaces are orthogonal exactly when addition has the product distance on them. -/
theorem forall_isOrthogonalTo_iff_add_eq_max [d.IsAddInvariant] [d.IsUltra] :
    (∀ x ∈ F, d.IsOrthogonalTo x G) ↔
      ∀ x ∈ F, ∀ y ∈ G, d (x + y) 0 = max (d x 0) (d y 0) := by
  refine ⟨fun h x hx _ hy ↦ (h x hx).add_eq_max hy, ?_⟩
  intro h x hx y hy
  rw [← d.sub_zero_eq x y, sub_eq_add_neg, h x hx (-y) (G.neg_mem hy)]
  exact le_max_left _ _

theorem forall_isOrthogonalTo_comm [d.IsAddInvariant] [d.IsUltra] :
    (∀ x ∈ F, d.IsOrthogonalTo x G) ↔ (∀ y ∈ G, d.IsOrthogonalTo y F) := by
  rw [forall_isOrthogonalTo_iff_add_eq_max, forall_isOrthogonalTo_iff_add_eq_max]
  constructor <;> intro h x hx y hy <;> rw [add_comm, h y hy x hx, max_comm]

/-- Testing against each scalar line is equivalent to testing against the subspace. -/
theorem isOrthogonalTo_iff_forall_span_singleton :
    d.IsOrthogonalTo x F ↔ ∀ y ∈ F, d.IsOrthogonalTo x (K ∙ y) := by
  refine ⟨fun h y hy z hz ↦ h z ((Submodule.span_singleton_le_iff_mem y F).mpr hy hz), ?_⟩
  exact fun h y hy ↦ h y hy y (Submodule.mem_span_singleton_self y)

theorem forall_isOrthogonalTo_span_singleton_left [d.IsAddInvariant] [d.IsSMulMono K] [d.IsUltra] :
    (∀ y ∈ K ∙ x, d.IsOrthogonalTo y F) ↔ d.IsOrthogonalTo x F := by
  refine ⟨fun h ↦ h x (Submodule.mem_span_singleton_self x), ?_⟩
  rintro h y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  exact h.smul a

/-- Orthogonality of two vectors is symmetric, including on the kernel of the pseudometric. -/
theorem isOrthogonalTo_span_singleton_comm [d.IsAddInvariant] [d.IsSMulMono K] [d.IsUltra]
    {y : E} : d.IsOrthogonalTo x (K ∙ y) ↔ d.IsOrthogonalTo y (K ∙ x) := by
  rw [← forall_isOrthogonalTo_span_singleton_left (x := x),
    forall_isOrthogonalTo_comm, forall_isOrthogonalTo_span_singleton_left]

/-- The two scalar axes are orthogonal iff linear combinations have the supremum distance. -/
theorem isOrthogonalTo_span_singleton_iff_max [d.IsAddInvariant] [d.IsSMulMono K] [d.IsUltra]
    {y : E} : d.IsOrthogonalTo x (K ∙ y) ↔
      ∀ a b : K, d (a • x + b • y) 0 = max (d (a • x) 0) (d (b • y) 0) := by
  rw [← forall_isOrthogonalTo_span_singleton_left, forall_isOrthogonalTo_iff_add_eq_max]
  constructor
  · exact fun h a b ↦ h _ (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩)
      _ (Submodule.mem_span_singleton.mpr ⟨b, rfl⟩)
  · intro h u hu v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact h a b

/-- Subtracting a nearest point in a spherically complete subspace produces an orthogonal
representative of the same coset. No dimension or separation assumption is needed. -/
theorem exists_sub_isOrthogonalTo [d.IsAddInvariant] [d.IsUltra] (F : Submodule K E)
    [(d.comap ((↑) : F → E)).IsSphericallyComplete] (a : E) :
    ∃ z : F, d.IsOrthogonalTo (a - z) F := by
  obtain ⟨z, hz⟩ := d.exists_bestApprox (F : Set E) F.nonempty a
  refine ⟨z, fun y hy ↦ ?_⟩
  rw [d.sub_zero_eq]
  simpa only [← d.sub_right_eq a (y + (z : E)) z, add_sub_cancel_right] using
    hz ⟨y + z, F.add_mem hy z.property⟩

end PseudoMetric
