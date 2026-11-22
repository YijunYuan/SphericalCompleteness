/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.Module.ImmediateSubmodule
public import SphericalCompleteness.PseudoMetric.Module.SphericalCompletion.OneDimensional
public import SphericalCompleteness.PseudoMetric.Module.Extension

/-!
# Immediate extensions of modules with valued pseudoultrametrics

An immediate linear extension embeds over its base into any compatible spherically complete
target containing that base. Two spherically complete immediate linear extensions are linearly
isometric over their base. These assertions also hold if the distances fail to separate points.
-/

@[expose] public section

open Set Function

namespace PseudoMetric

variable {K E F H Γ : Type*} [DivisionRing K] [AddCommGroup E] [AddCommGroup F] [AddCommGroup H]
variable [Module K E] [Module K F] [Module K H] [Zero Γ] [Add Γ] [LinearOrder Γ]
variable (d : PseudoMetric F Γ) (e : PseudoMetric H Γ) [d.IsUltra] [e.IsUltra]

variable [d.IsAddInvariant] [e.IsAddInvariant]

/-- A nonexpansive linear map preserving distances from zero on an immediate subspace preserves
all distances. -/
theorem IsImmediate.linearMap_dist_eq {i : E →ₗ[K] F} (hi : d.IsImmediate i) (g : F →ₗ[K] H)
    (hg : ∀ x, e (g x) 0 ≤ d x 0) (hbase : ∀ x, e (g (i x)) 0 = d (i x) 0) :
    ∀ x y, e (g x) (g y) = d x y := by
  have hle (x y : F) : e (g x) (g y) ≤ d x y := by
    simpa only [map_sub, e.sub_zero_eq, d.sub_zero_eq] using hg (x - y)
  have hzero (x : F) : e (g x) 0 = d x 0 := by
    by_cases hx : x ∈ range i
    · obtain ⟨u, rfl⟩ := hx
      exact hbase u
    obtain ⟨u, hu⟩ := (hi x hx).2 0
    rw [map_zero] at hu
    have hd := d.eq_of_lt hu
    have hstrict : e (g (i u)) (g x) < e (g (i u)) 0 := by
      rw [e.symm, hbase, hd]
      exact (hle x (i u)).trans_lt hu
    exact (e.eq_of_lt hstrict).trans ((hbase u).trans hd)
  intro x y
  simpa only [map_sub, d.sub_zero_eq, e.sub_zero_eq] using hzero (x - y)

/-- A spherically complete submodule containing the base of an immediate extension is the
whole ambient module. Subtracting a nearest point would otherwise give an outside vector
for which zero is a best approximation in the base. -/
theorem IsImmediate.eq_top_of_isSphericallyComplete {i : E →ₗ[K] F} (hi : d.IsImmediate i)
    (G : Submodule K F) (hG : i.range ≤ G) [(d.comap ((↑) : G → F)).IsSphericallyComplete] :
    G = ⊤ := by
  apply top_unique
  intro x _
  by_contra hx
  obtain ⟨z, hz⟩ := d.exists_sub_isOrthogonalTo G x
  have hout : x - (z : F) ∉ range i := by
    rintro ⟨u, hu⟩
    exact hx ((G.sub_mem_iff_left z.prop).mp (hu ▸ hG (LinearMap.mem_range_self i u)))
  obtain ⟨u, hu⟩ := (hi _ hout).2 0
  rw [map_zero] at hu
  exact hu.not_ge (hz _ (hG (LinearMap.mem_range_self i u)))

variable (hsmul : ∀ (c : K) {u : H} {x : F}, e u 0 ≤ d x 0 → e (c • u) 0 ≤ d (c • x) 0)

include hsmul in
/-- **Weak universal property of an immediate linear extension.** Extend a distance-preserving
linear map on the base to the whole immediate extension. The scalar actions must preserve
distance comparisons between the source and target. -/
theorem IsImmediate.exists_linearMap_comp_eq [e.IsSphericallyComplete] (i : E →ₗ[K] F)
    (hinj : Injective i) (hi : d.IsImmediate i) (j : E →ₗ[K] H)
    (hbase : ∀ x, e (j x) 0 = d (i x) 0) :
    ∃ g : F →ₗ[K] H, g.comp i = j ∧ ∀ x y, e (g x) (g y) = d x y := by
  let inv := (LinearEquiv.ofInjective i hinj).symm
  obtain ⟨g, hagree, hg⟩ := d.exists_linearExtension_of_le_modulus e id monotone_id hsmul
    i.range (j.comp inv.toLinearMap) (fun x ↦ by
      change e (j (inv x)) 0 ≤ d (x : F) 0
      rw [hbase]
      exact le_of_eq (congrArg (fun v : i.range ↦ d (v : F) 0)
        ((LinearEquiv.ofInjective i hinj).apply_symm_apply x)))
  have hcomp : g.comp i = j := by
    ext x
    exact (hagree ⟨i x, LinearMap.mem_range_self i x⟩).trans (congrArg j <|
      (LinearEquiv.ofInjective i hinj).symm_apply_apply x)
  refine ⟨g, hcomp, hi.linearMap_dist_eq d e g hg ?_⟩
  intro x
  simpa only [← LinearMap.comp_apply g i, hcomp] using hbase x

include hsmul in
/-- Two spherically complete immediate linear extensions of a common base with compatible
scalar actions are linearly isometric over the base. -/
theorem IsImmediate.exists_linearEquiv_comp_eq [d.IsSphericallyComplete] [e.IsSphericallyComplete]
    (i : E →ₗ[K] F) (hinj : Injective i) (hi : d.IsImmediate i) (j : E →ₗ[K] H)
    (hjinj : Injective j) (hj : e.IsImmediate j) (hbase : ∀ x, e (j x) 0 = d (i x) 0) :
    ∃ g : F ≃ₗ[K] H, g.toLinearMap.comp i = j ∧ ∀ x y, e (g x) (g y) = d x y := by
  obtain ⟨g, hcomp, heq⟩ := hi.exists_linearMap_comp_eq d e hsmul i hinj j hbase
  have hg_inj : Injective g := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hzero : d x 0 = 0 := by rw [← heq, hx, g.map_zero, e.refl]
    by_cases hr : x ∈ range i
    · obtain ⟨u, rfl⟩ := hr
      have hu : j u = 0 := by simpa only [← LinearMap.comp_apply g i, hcomp] using hx
      rw [hjinj (hu.trans j.map_zero.symm), map_zero]
    · obtain ⟨u, hu⟩ := (hi x hr).2 0
      rw [map_zero, hzero] at hu
      exact (hu.not_ge (d.nonneg_of_ultra x _)).elim
  have : (e.comap ((↑) : g.range → H)).IsSphericallyComplete :=
    (d.isSphericallyComplete_iff_of_surjective _ g.surjective_rangeRestrict heq).mp inferInstance
  have htop := hj.eq_top_of_isSphericallyComplete e g.range
    (hcomp ▸ LinearMap.range_comp_le_range i g)
  exact ⟨LinearEquiv.ofBijective g ⟨hg_inj, LinearMap.range_eq_top.mp htop⟩, hcomp, heq⟩

/-- A linear spherical completion is a spherically complete immediate extension by an
injective distance-preserving linear map. Injectivity is explicit for nonseparated distances. -/
structure IsLinearSphericalCompletion (d₀ : PseudoMetric E Γ) (d : PseudoMetric F Γ)
    (i : E →ₗ[K] F) : Prop where
  complete : d.IsSphericallyComplete
  injective : Injective i
  map_dist : ∀ x y, d (i x) (i y) = d₀ x y
  immediate : d.IsImmediate i

/-- Inside a spherically complete ambient module, minimality among spherically complete
submodules containing the base is equivalent to immediacy. -/
theorem isLinearSphericalCompletion_iff_minimal [d.IsSMulMono K] [d.IsSphericallyComplete]
    (d₀ : PseudoMetric E Γ) (i : E →ₗ[K] F) (hinj : Injective i)
    (hdist : ∀ x y, d (i x) (i y) = d₀ x y) :
    d₀.IsLinearSphericalCompletion d i ↔ ∀ D : Submodule K F, i.range ≤ D →
      (d.comap ((↑) : D → F)).IsSphericallyComplete → D = ⊤ := by
  constructor
  · exact fun h D hD _ ↦ h.immediate.eq_top_of_isSphericallyComplete d D hD
  · intro hmin
    obtain ⟨M, hm⟩ := d.exists_maximal_isImmediateSubmodule i.range
    have htop := hmin M hm.prop.1 (d.isSphericallyComplete_of_maximal_isImmediateSubmodule hm)
    exact ⟨inferInstance, hinj, hdist, (d.isImmediate_iff_range i).mpr (htop ▸ hm.prop)⟩

/-- Two linear spherical completions are linearly isometric over the original module.
Immediacy realizes each value, together with all of its scalar multiples, in the base.
Thus the two scalar actions automatically agree on comparisons between the completions. -/
theorem IsLinearSphericalCompletion.unique [d.IsSMulMono K] [e.IsSMulMono K]
    {d₀ : PseudoMetric E Γ} {i : E →ₗ[K] F} {j : E →ₗ[K] H}
    (hi : d₀.IsLinearSphericalCompletion d i) (hj : d₀.IsLinearSphericalCompletion e j) :
    ∃ g : F ≃ₗ[K] H, g.toLinearMap.comp i = j ∧ ∀ x y, e (g x) (g y) = d x y := by
  let := hi.complete
  let := hj.complete
  have hbase (x : E) : e (j x) 0 = d (i x) 0 := by
    simpa only [map_zero] using (hj.map_dist x 0).trans (hi.map_dist x 0).symm
  apply hi.immediate.exists_linearEquiv_comp_eq d e _ i hi.injective j hj.injective
    hj.immediate hbase
  intro c u x h
  obtain ⟨a, ha⟩ := hj.immediate.exists_forall_smul_dist_eq e K u
  obtain ⟨b, hb⟩ := hi.immediate.exists_forall_smul_dist_eq d K x
  have hle : d (i a) 0 ≤ d (i b) 0 := by
    have ha₁ := ha 1
    have hb₁ := hb 1
    simp only [one_smul, hbase] at ha₁ hb₁
    exact ha₁.symm.trans_le (h.trans_eq hb₁)
  rw [ha c, hb c, hbase, i.map_smul, i.map_smul]
  exact IsSMulMono.smul_le (d := d) c hle

end PseudoMetric
