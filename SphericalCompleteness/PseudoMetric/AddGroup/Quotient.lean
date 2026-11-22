/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import SphericalCompleteness.PseudoMetric.AddGroup.Basic
public import SphericalCompleteness.PseudoMetric.Quotient

/-!
# Quotients by spherically complete additive subgroups

For a translation-invariant pseudoultrametric, every coset of a spherically complete
subgroup contains a representative nearest to zero. Its distance to zero defines the
quotient distance at arbitrary rank, even when the value order has no infima.
-/

@[expose] public section

open Set

namespace PseudoMetric

variable {G Γ : Type*} [AddCommGroup G] [Zero Γ] [Add Γ] [LinearOrder Γ]
  (d : PseudoMetric G Γ) [d.IsAddInvariant] [d.IsUltra] (H : AddSubgroup G)
  [(d.comap (Subtype.val : H → G)).IsSphericallyComplete]

/-- Each coset has a representative at minimum distance from zero. -/
theorem exists_minimalRepresentative (q : G ⧸ H) :
    ∃ a : G, (QuotientAddGroup.mk' H) a = q ∧
      ∀ b : G, (QuotientAddGroup.mk' H) b = q → d a 0 ≤ d b 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H q
  obtain ⟨h, hh⟩ := d.exists_bestApprox (H : Set G) ⟨0, H.zero_mem⟩ x
  refine ⟨x - h, ?_, fun b hb ↦ ?_⟩
  · rw [map_sub, QuotientAddGroup.mk'_apply H (h : G), (QuotientAddGroup.eq_zero_iff _).mpr h.prop,
      sub_zero]
  · have hx : x - b ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp hb.symm
    simpa only [d.sub_zero_eq, ← d.sub_zero_eq x (x - b), sub_sub_cancel] using
      hh ⟨x - b, hx⟩

/-- The minimum distance to zero among all representatives of a coset. -/
noncomputable def addQuotientNorm (q : G ⧸ H) : Γ :=
  d (d.exists_minimalRepresentative H q).choose 0

private theorem addQuotientNorm_le (a : G) :
    d.addQuotientNorm H (QuotientAddGroup.mk' H a) ≤ d a 0 :=
  (d.exists_minimalRepresentative H _).choose_spec.2 a rfl

private theorem exists_addQuotientNorm_eq (q : G ⧸ H) :
    ∃ a : G, QuotientAddGroup.mk' H a = q ∧ d a 0 = d.addQuotientNorm H q :=
  ⟨(d.exists_minimalRepresentative H q).choose, (d.exists_minimalRepresentative H q).choose_spec.1,
    rfl⟩

private theorem addQuotientNorm_le_of_mk {q : G ⧸ H} {a : G} (ha : QuotientAddGroup.mk' H a = q) :
    d.addQuotientNorm H q ≤ d a 0 := ha ▸ d.addQuotientNorm_le H a

/-- The quotient value is the least distance to zero of a representative of the coset. -/
theorem isLeast_addQuotientNorm (q : G ⧸ H) :
    IsLeast {r | ∃ a : G, QuotientAddGroup.mk' H a = q ∧ d a 0 = r} (d.addQuotientNorm H q) :=
  ⟨d.exists_addQuotientNorm_eq H q, by
    rintro _ ⟨a, ha, rfl⟩
    exact d.addQuotientNorm_le_of_mk H ha⟩

private theorem addQuotientNorm_sub_le_swap (a b : G ⧸ H) :
    d.addQuotientNorm H (a - b) ≤ d.addQuotientNorm H (b - a) := by
  obtain ⟨z, hz, hz'⟩ := d.exists_addQuotientNorm_eq H (b - a)
  have hneg : QuotientAddGroup.mk' H (-z) = a - b := by rw [map_neg, hz, neg_sub]
  refine (d.addQuotientNorm_le_of_mk H hneg).trans_eq (?_ : d (-z) 0 = _)
  simpa only [← hz', ← zero_sub z, d.sub_zero_eq] using d.symm 0 z

private theorem exists_quotient_triangle_representatives (a b c : G ⧸ H) :
    ∃ x y : G, d (x + y) y = d.addQuotientNorm H (a - b) ∧ d y 0 = d.addQuotientNorm H (b - c) ∧
      d.addQuotientNorm H (a - c) ≤ d (x + y) 0 := by
  obtain ⟨x, hx, hx'⟩ := d.exists_addQuotientNorm_eq H (a - b)
  obtain ⟨y, hy, hy'⟩ := d.exists_addQuotientNorm_eq H (b - c)
  refine ⟨x, y, ?_, hy', d.addQuotientNorm_le_of_mk H (a := x + y) ?_⟩
  · simpa only [zero_add, hx'] using IsAddInvariant.add_right (d := d) x 0 y
  · rw [map_add, hx, hy, sub_add_sub_cancel]

/-- The distance between two cosets is the minimum distance between their representatives. -/
noncomputable def addQuotient : PseudoMetric (G ⧸ H) Γ where
  toFun a b := d.addQuotientNorm H (a - b)
  refl' a := by
    rw [sub_self]
    apply le_antisymm
    · simpa only [map_zero, d.refl] using d.addQuotientNorm_le H 0
    · exact d.nonneg_of_ultra _ _
  symm' a b := by
    exact le_antisymm (d.addQuotientNorm_sub_le_swap H a b) (d.addQuotientNorm_sub_le_swap H b a)
  triangle' a b c := by
    obtain ⟨x, y, hx, hy, hxy⟩ := d.exists_quotient_triangle_representatives H a b c
    rw [← hx, ← hy]
    exact hxy.trans (d.triangle (x + y) y 0)

theorem addQuotient_apply (a b : G ⧸ H) :
    d.addQuotient H a b = d.addQuotientNorm H (a - b) := rfl

instance : (d.addQuotient H).IsAddInvariant where
  add_right x y a := by simp only [addQuotient_apply, add_sub_add_right_eq_sub]

instance : (d.addQuotient H).IsUltra where
  le_sup' a b c := by
    obtain ⟨x, y, hx, hy, hxy⟩ := d.exists_quotient_triangle_representatives H a b c
    exact hxy.trans <| (IsUltra.le_sup' (d := d) (x + y) y 0).trans_eq (congrArg₂ (· ⊔ ·) hx hy)

/-- The quotient map is nonexpansive. -/
theorem addQuotient_mk_le (x y : G) :
    d.addQuotient H (QuotientAddGroup.mk' H x) (QuotientAddGroup.mk' H y) ≤ d x y := by
  change d.addQuotientNorm H _ ≤ _
  rw [← map_sub, ← d.sub_zero_eq]
  exact d.addQuotientNorm_le H (x - y)

/-- From any prescribed representative of one endpoint, the quotient distance to the other
endpoint is attained by a representative of that coset. -/
theorem exists_addQuotient_dist_eq (x : G) (q : G ⧸ H) :
    ∃ z : G, QuotientAddGroup.mk' H z = q ∧
      d z x = d.addQuotient H q (QuotientAddGroup.mk' H x) := by
  obtain ⟨u, hu, hd⟩ := d.exists_addQuotientNorm_eq H (q - QuotientAddGroup.mk' H x)
  refine ⟨u + x, by rw [map_add, hu, sub_add_cancel], ?_⟩
  simpa only [zero_add, hd, addQuotient_apply] using IsAddInvariant.add_right (d := d) u 0 x

/-- The quotient map takes every closed ball onto its corresponding quotient ball. -/
theorem image_closedBall_addQuotient (x : G) (r : Γ) :
    QuotientAddGroup.mk' H '' d.closedBall x r =
      (d.addQuotient H).closedBall (QuotientAddGroup.mk' H x) r := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (d.addQuotient_mk_le H z x).trans hz
  · intro hq
    obtain ⟨z, hz, hd⟩ := d.exists_addQuotient_dist_eq H x q
    exact ⟨z, hd.trans_le hq, hz⟩

instance [d.IsSphericallyComplete] : (d.addQuotient H).IsSphericallyComplete :=
  .of_image_closedBall d (d.addQuotient H) (QuotientAddGroup.mk'_surjective H)
    (d.image_closedBall_addQuotient H)

end PseudoMetric
