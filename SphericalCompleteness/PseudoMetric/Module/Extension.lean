/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Abel
public import SphericalCompleteness.PseudoMetric.Extension
public import SphericalCompleteness.PseudoMetric.Module.Basic

/-!
# Hahn–Banach for modules with valued pseudoultrametrics

A linear map into a spherically complete module extends with its original bound whenever
scalar multiplication preserves that bound on the source and target. A monotone map between
the two value types expresses the bound. This includes nonexpansive linear maps over a valued
field and bounded linear maps between ultrametric normed spaces.
-/

@[expose] public section

open Set Submodule

namespace PseudoMetric

variable {K E F Γ Δ : Type*} [DivisionRing K] [AddCommGroup E] [AddCommGroup F]
variable [Module K E] [Module K F] [Zero Γ] [Add Γ] [LinearOrder Γ] [Zero Δ] [Add Δ] [LinearOrder Δ]
variable (d : PseudoMetric E Γ) (e : PseudoMetric F Δ)
variable [d.IsUltra] [e.IsUltra] [d.IsAddInvariant] [e.IsAddInvariant] [e.IsSphericallyComplete]
section Family

variable {ι : Type*} (T : ι → E →ₗ[K] F) (φ : ι → Γ → Δ)
  (hmono : ∀ i, Monotone (φ i)) (hcmp : ∀ i j, φ i ≤ φ j ∨ φ j ≤ φ i)
  (hsmul : ∀ i (c : K) {u : F} {x : E}, e u 0 ≤ φ i (d x 0) →
    e (c • u) 0 ≤ φ i (d (c • x) 0))
  (hT : ∀ i j x, e (T i x) (T j x) ≤ max (φ i (d x 0)) (φ j (d x 0)))

include hmono hcmp hT in
/-- Choose the value of a simultaneous linear extension at a single vector. The bounds
only use distances at this step, so compatibility with scalar multiplication enters later. -/
theorem exists_linearExtensionValue (D : Submodule K E) (p : D →ₗ[K] F)
    (hp : ∀ i (u : D), e (p u) (T i u) ≤ φ i (d u 0)) (a : E) :
    ∃ b : F, ∀ i (u : D), e b (T i (a - u) + p u) ≤ φ i (d a u) := by
  let center (i : ι × D) := T i.1 (a - i.2) + p i.2
  let radius (i : ι × D) := φ i.1 (d a i.2)
  have bound (i j : ι) (u v : D) (hij : φ i ≤ φ j) :
      e (center (i, u)) (center (j, v)) ≤ max (radius (i, u)) (radius (j, v)) := by
    have huv : e (center (i, u)) (center (i, v)) = e (p (u - v)) (T i (u - v)) := by
      rw [← e.sub_zero_eq, ← e.sub_zero_eq (p (u - v))]
      apply congrArg (fun z ↦ e z 0)
      simp only [center, map_sub]
      abel
    have hdist := (IsUltra.le_sup' (d := d) (u : E) a v).trans_eq (by rw [d.symm (u : E) a])
    have h₁ := (hp i (u - v)).trans <| (hmono i) <|
      (d.sub_zero_eq (u : E) v).le.trans hdist
    rw [(hmono i).map_sup] at h₁
    have h₂ := (hT i j (a - v)).trans_eq (max_eq_right (hij _))
    rw [d.sub_zero_eq] at h₂
    apply (IsUltra.le_sup' (d := e) (center (i, u)) (center (i, v)) (center (j, v))).trans
    refine max_le ((huv.trans_le h₁).trans (max_le_max_left _ (hij _))) ?_
    exact ((IsAddInvariant.add_right (d := e) _ _ (p v)).trans_le h₂).trans (le_max_right _ _)
  obtain ⟨b, hb⟩ := IsSphericallyComplete.exists_dist_le e center radius (fun i j ↦ by
    rcases hcmp i.1 j.1 with h | h
    · exact bound _ _ _ _ h
    · rw [e.symm, max_comm]; exact bound _ _ _ _ h)
  exact ⟨b, fun i u ↦ hb (i, u)⟩

include hmono hcmp hsmul hT in
private theorem exists_bounded_supSpanSingleton (p : E →ₗ.[K] F)
    (hp : ∀ i (u : p.domain), e (p u) (T i u) ≤ φ i (d u 0)) (a : E) (ha : a ∉ p.domain) :
    ∃ b : F, ∀ i (u : (p.supSpanSingleton a b ha).domain),
      e (p.supSpanSingleton a b ha u) (T i u) ≤ φ i (d u 0) := by
  obtain ⟨b, hb⟩ := exists_linearExtensionValue d e T φ hmono hcmp hT p.domain p.toFun hp a
  refine ⟨b, ?_⟩
  rintro i ⟨w, hw⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup.mp hw
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hv
  rw [LinearPMap.supSpanSingleton_apply_mk p a b ha u hu c]
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using hp i ⟨u, hu⟩
  · let t : p.domain := ⟨u, hu⟩
    have h := hb i (-(c⁻¹ • t))
    change e b (T i (a - ↑(-(c⁻¹ • t))) + p (-(c⁻¹ • t))) ≤ φ i (d a ↑(-(c⁻¹ • t))) at h
    rw [← e.sub_zero_eq, ← d.sub_zero_eq] at h
    have h' := hsmul i c h
    simp only [NegMemClass.coe_neg, SetLike.val_smul, sub_neg_eq_add, p.map_neg, p.map_smul,
      smul_sub, smul_add, smul_neg, smul_inv_smul₀ hc, ← LinearMap.map_smul,
      t] at h'
    rw [add_comm (c • a) u] at h'
    rw [← e.sub_zero_eq, RingHom.id_apply]
    convert h' using 2
    abel

include hmono hcmp hsmul hT in
/-- Extend a partial linear map subject to a family of bounds around prescribed linear
operators. The moduli must be totally ordered pointwise and respect scalar multiplication. -/
theorem exists_linearExtension_of_le_moduli (D : Submodule K E) (f : D →ₗ[K] F)
    (hf : ∀ i (x : D), e (f x) (T i x) ≤ φ i (d x 0)) :
    ∃ g : E →ₗ[K] F, (∀ x : D, g x = f x) ∧ ∀ i x, e (g x) (T i x) ≤ φ i (d x 0) := by
  let P := {p : E →ₗ.[K] F | ∀ i (x : p.domain), e (p x) (T i x) ≤ φ i (d x 0)}
  have chainBound (C : Set (E →ₗ.[K] F)) (hC : C ⊆ P) (chain : IsChain (· ≤ ·) C)
      (p : E →ₗ.[K] F) (hp : p ∈ C) : ∃ q ∈ P, ∀ t ∈ C, t ≤ q := by
    have directed := chain.directedOn
    refine ⟨LinearPMap.sSup C directed, ?_, fun _ ↦ LinearPMap.le_sSup directed⟩
    rintro i ⟨x, hx⟩
    obtain ⟨q, hq, hxq⟩ := (LinearPMap.mem_domain_sSup_iff ⟨p, hp⟩ directed).mp hx
    have hle := LinearPMap.le_sSup directed hq
    exact (hle.2 (x := ⟨x, hxq⟩) (y := ⟨x, hx⟩) rfl) ▸ hC hq i ⟨x, hxq⟩
  obtain ⟨p, hfp, hp⟩ := zorn_le_nonempty₀ P chainBound (⟨D, f⟩ : E →ₗ.[K] F) hf
  have htop : p.domain = ⊤ := by
    by_contra h
    obtain ⟨a, ha⟩ := SetLike.exists_notMem_of_ne_top p.domain h rfl
    obtain ⟨b, hb⟩ := exists_bounded_supSpanSingleton d e T φ hmono hcmp hsmul hT p hp.prop a ha
    have hle : p ≤ p.supSpanSingleton a b ha := p.left_le_sup _ _
    have hrev := hp.le_of_ge hb hle
    exact ha (hrev.1 (mem_sup_right (mem_span_singleton_self a)))
  obtain ⟨dom, g⟩ := p
  change dom = ⊤ at htop
  subst dom
  exact ⟨g.comp (LinearMap.id.codRestrict ⊤ fun _ ↦ trivial),
    fun x ↦ (hfp.2 (x := x) (y := ⟨x, trivial⟩) rfl).symm,
    fun i x ↦ hp.prop i ⟨x, trivial⟩⟩

end Family

variable (φ : Γ → Δ) (hφ : Monotone φ)
variable (hsmul : ∀ (c : K) {u : F} {x : E}, e u 0 ≤ φ (d x 0) → e (c • u) 0 ≤ φ (d (c • x) 0))

include hφ hsmul in
/-- **Non-Archimedean Hahn–Banach theorem.** Extend a linear map from a submodule,
preserving its bound. Scalar multiplication must jointly preserve this bound on the two
modules. Neither distance needs to separate points. -/
theorem exists_linearExtension_of_le_modulus (D : Submodule K E) (f : D →ₗ[K] F)
    (hf : ∀ x : D, e (f x) 0 ≤ φ (d x 0)) :
    ∃ g : E →ₗ[K] F, (∀ x : D, g x = f x) ∧ ∀ x, e (g x) 0 ≤ φ (d x 0) := by
  have hnonneg (x : E) : 0 ≤ φ (d x 0) := by
    have h := hf 0
    simp only [map_zero, ZeroMemClass.coe_zero, e.refl, d.refl] at h
    exact h.trans (hφ (d.nonneg_of_ultra _ _))
  obtain ⟨g, hg, hb⟩ := exists_linearExtension_of_le_moduli d e (fun _ : Unit ↦ 0)
    (fun _ ↦ φ) (fun _ ↦ hφ) (fun _ _ ↦ Or.inl le_rfl) (fun _ ↦ hsmul)
    (fun _ _ x ↦ by simpa only [LinearMap.zero_apply, e.refl, max_self] using hnonneg x)
    D f (fun _ x ↦ hf x)
  exact ⟨g, hg, hb ()⟩

/-- A spherically complete submodule has a nonexpansive linear projection, for any
translation-invariant pseudoultrametric on which scalars preserve comparisons. -/
theorem exists_nonexpansive_linear_retraction [d.IsSMulMono K] (D : Submodule K E)
    [(d.comap ((↑) : D → E)).IsSphericallyComplete] :
    ∃ p : E →ₗ[K] D, (∀ x : D, p x = x) ∧ ∀ x y, d (p x) (p y) ≤ d x y := by
  let g := d.comap ((↑) : D → E)
  obtain ⟨p, hp, hbound⟩ := exists_linearExtension_of_le_modulus d g id monotone_id
    (fun c {u x} h ↦ by
      simpa only [g, comap_apply, SetLike.val_smul, ZeroMemClass.coe_zero, id_eq] using
        IsSMulMono.smul_le (d := d) c (show d (u : E) 0 ≤ d x 0 from h))
    D LinearMap.id (fun _ ↦ le_rfl)
  refine ⟨p, hp, fun x y ↦ ?_⟩
  simpa only [map_sub, AddSubgroupClass.coe_sub, g, comap_apply, ZeroMemClass.coe_zero,
    id_eq, d.sub_zero_eq] using hbound (x - y)

/-- A spherically complete submodule is an orthogonal direct summand. -/
theorem exists_isCompl_forall_isOrthogonalTo [d.IsSMulMono K] (D : Submodule K E)
    [(d.comap ((↑) : D → E)).IsSphericallyComplete] :
    ∃ G : Submodule K E, IsCompl D G ∧ ∀ x ∈ G, d.IsOrthogonalTo x D := by
  obtain ⟨p, hp, hle⟩ := d.exists_nonexpansive_linear_retraction D
  refine ⟨p.ker, LinearMap.isCompl_of_proj hp, fun x hx y hy ↦ ?_⟩
  have h := d.dist_retraction_le (D := (D : Set E)) p hp hle x ⟨y, hy⟩
  simpa only [show p x = 0 from hx, ZeroMemClass.coe_zero] using h

omit [e.IsUltra] [e.IsAddInvariant] [e.IsSphericallyComplete] in
include hφ in
/-- When the source submodule is spherically complete, precomposition with a linear projection
extends maps with any monotone distance bound. The target may be any module with a distance. -/
theorem exists_linearExtension_of_domain [d.IsSMulMono K] (D : Submodule K E)
    [(d.comap ((↑) : D → E)).IsSphericallyComplete] (f : D →ₗ[K] F)
    (hf : ∀ x : D, e (f x) 0 ≤ φ (d x 0)) :
    ∃ g : E →ₗ[K] F, (∀ x : D, g x = f x) ∧ ∀ x, e (g x) 0 ≤ φ (d x 0) := by
  obtain ⟨p, hp, hle⟩ := d.exists_nonexpansive_linear_retraction D
  exact ⟨f.comp p, fun x ↦ congrArg f (hp x),
    fun x ↦ (hf (p x)).trans (hφ (by simpa only [map_zero, ZeroMemClass.coe_zero] using hle x 0))⟩

end PseudoMetric
