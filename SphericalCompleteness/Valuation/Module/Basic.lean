/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.Module.Basic
public import SphericalCompleteness.Valuation.Basic

/-!
# Pseudometrics on vector spaces over a valued field

Homogeneity expresses the scalar law for a valuative seminorm. The seminorm is the
distance to zero, with values in the ordered monoid of the scalar valuation.
-/

@[expose] public section

namespace Valuation

variable {K E Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [LinearOrderedCommMonoidWithZero Γ]

/-- A bundled distance is homogeneous for `v` if scalar multiplication scales its
distance to zero by the valuation of the scalar. -/
def IsHomogeneous (v : Valuation K Γ) (d : PseudoMetric E (MaxTropical Γ)) : Prop :=
  ∀ (a : K) (x : E), MaxTropical.untrop (d (a • x) 0) = v a * MaxTropical.untrop (d x 0)

section Seminorm

variable (v : Valuation K Γ) (p : E → Γ)
    (hadd : ∀ x y, p (x + y) ≤ max (p x) (p y))
    (hsmul : ∀ (a : K) x, p (a • x) = v a * p x)

/-- The bundled pseudometric defined by a valuative seminorm. Homogeneity at zero and at
minus one supplies the diagonal and symmetry axioms. -/
def pseudoMetricOfSeminorm : PseudoMetric E (MaxTropical Γ) where
  toFun x y := MaxTropical.trop (p (x - y))
  refl' x := by
    change MaxTropical.trop (p (x - x)) = MaxTropical.trop (⊥ : Γ)
    rw [sub_self, bot_eq_zero]
    exact congrArg _ (by simpa only [zero_smul, map_zero, zero_mul] using hsmul 0 (0 : E))
  symm' x y := by
    apply congrArg MaxTropical.trop
    simpa only [neg_one_smul, neg_sub, map_neg, map_one, one_mul] using hsmul (-1) (y - x)
  triangle' x y z := by
    change p (x - z) ≤ max (p (x - y)) (p (y - z))
    simpa only [sub_add_sub_cancel] using hadd (x - y) (y - z)

@[simp] theorem pseudoMetricOfSeminorm_apply (x y : E) :
    v.pseudoMetricOfSeminorm p hadd hsmul x y = MaxTropical.trop (p (x - y)) := rfl

instance : (v.pseudoMetricOfSeminorm p hadd hsmul).IsAddInvariant where
  add_right x y a := by simp only [pseudoMetricOfSeminorm_apply, add_sub_add_right_eq_sub]

theorem isHomogeneous_pseudoMetricOfSeminorm :
    v.IsHomogeneous (v.pseudoMetricOfSeminorm p hadd hsmul) := by
  intro a x
  simpa only [pseudoMetricOfSeminorm_apply, MaxTropical.untrop_trop, sub_zero] using hsmul a x

end Seminorm

variable {v : Valuation K Γ} {d : PseudoMetric E (MaxTropical Γ)}

theorem IsHomogeneous.isSMulMono (h : v.IsHomogeneous d) : d.IsSMulMono K where
  smul_le a x y hxy := by
    change MaxTropical.untrop _ ≤ MaxTropical.untrop _
    rw [h, h]
    exact mul_le_mul_right
      (show MaxTropical.untrop (d x 0) ≤ MaxTropical.untrop (d y 0) from hxy) _

/-- Distances on a parametrized scalar line are the scalar distances multiplied by a
fixed value, which may be zero. -/
theorem IsHomogeneous.dist_smul [d.IsAddInvariant] (h : v.IsHomogeneous d) (a b : K) (x : E) :
    MaxTropical.untrop (d (a • x) (b • x)) = v (a - b) * MaxTropical.untrop (d x 0) := by
  rw [← d.sub_zero_eq, ← sub_smul, h]

/-- Restriction to a submodule preserves homogeneity. -/
theorem IsHomogeneous.submodule (h : v.IsHomogeneous d) (D : Submodule K E) :
    v.IsHomogeneous (d.comap ((↑) : D → E)) := fun a x ↦ h a x

/-- A valuation on a division ring is homogeneous for its own scalar action. -/
theorem isHomogeneous_self (v : Valuation K Γ) : v.IsHomogeneous v.toPseudoMetric := by
  intro a x
  change v (a * x - 0) = v a * v (x - 0)
  rw [sub_zero, sub_zero, map_mul]

instance (v : Valuation K Γ) : v.toPseudoMetric.IsSMulMono K :=
  v.isHomogeneous_self.isSMulMono

variable {A : Type*} [Ring A] (w : Valuation A Γ)

instance : w.toPseudoMetric.IsAddInvariant where
  add_right x y a := by simp only [toPseudoMetric_apply, add_sub_add_right_eq_sub]

variable {k : Type*} [Field k] [Algebra k A]

/-- An algebra valuation scales by its restriction to the scalar field. -/
theorem isHomogeneous_comap : (w.comap (algebraMap k A)).IsHomogeneous w.toPseudoMetric := by
  intro a x
  change w (a • x - 0) = w (algebraMap k A a) * w (x - 0)
  rw [sub_zero, sub_zero, Algebra.smul_def, map_mul]

instance : w.toPseudoMetric.IsSMulMono k := w.isHomogeneous_comap.isSMulMono

end Valuation
