/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
public import Mathlib.Order.Filter.Bases.Basic
public import SphericalCompleteness.PseudoMetric.Immediate
public import SphericalCompleteness.PseudoMetric.Module.Basic

/-!
# A one-dimensional immediate extension of a valued module

A failed nest defines a filter along which the distance to each old point is eventually
constant. Evaluate an affine expression `x + a • z` along this filter. The eventual values of
its distances define a pseudometric on `E × K`, adjoining one vector to the original module.
This detects spherical completeness using immediate linear extensions of arbitrary rank.
-/

@[expose] public section

open Set Filter Function

namespace PseudoMetric

variable {E Γ : Type*} [Zero Γ] [Add Γ] [LinearOrder Γ] (d : PseudoMetric E Γ) [d.IsUltra]

/-- A failed nest gives a nontrivial filter whose eventual distances to old points have
no minimum. This form of a pseudolimit does not use sequences. -/
theorem exists_filter_of_not_isSphericallyComplete (h : ¬ d.IsSphericallyComplete) :
    ∃ (L : Filter E) (r : E → Γ), L.NeBot ∧ (∀ x, ∀ᶠ z in L, d z x = r x) ∧
      ∀ x, ∃ w, r w < r x := by
  obtain ⟨e, he, hiso, hi⟩ := d.exists_isImmediate_option_of_not_isSphericallyComplete h
  let r (x : E) := e none (some x)
  obtain ⟨hne, hr⟩ := hi none (by rintro ⟨_, h⟩; cases h)
  let B (x : E) : Set E := {w | r w ≤ r x}
  have hB : IsBasis (fun _ : E ↦ True) B := {
    nonempty := hne.elim fun x ↦ ⟨x, trivial⟩
    inter := by
      intro x y _ _
      rcases le_total (r x) (r y) with hxy | hyx
      · exact ⟨x, trivial, fun _ hz ↦ ⟨hz, le_trans hz hxy⟩⟩
      · exact ⟨y, trivial, fun _ hz ↦ ⟨le_trans hz hyx, hz⟩⟩ }
  let L := hB.filter
  have hL := hB.hasBasis
  refine ⟨L, r, hL.neBot_iff.mpr (fun {x} _ ↦ ⟨x, le_rfl⟩), fun x ↦ ?_, hr⟩
  obtain ⟨w, hw⟩ := hr x
  filter_upwards [hL.mem_of_mem (i := w) trivial] with z hz
  have hzlt : e none (some z) < r x := lt_of_le_of_lt hz hw
  rw [← hiso]
  refine le_antisymm ((IsUltra.le_sup' (d := e) (some z) none (some x)).trans ?_) ?_
  · exact max_le ((e.symm _ _).trans_le hzlt.le) le_rfl
  · exact (le_max_iff.mp (IsUltra.le_sup' (d := e) none (some z) (some x))).resolve_left hzlt.not_ge

variable (K : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
variable [d.IsAddInvariant] [d.IsSMulMono K]

/-- In an immediate linear extension each vector has a representative in the base with
the same distance from zero after every scalar multiplication. The representative can be
chosen independently of the scalar. -/
theorem IsImmediate.exists_forall_smul_dist_eq {A : Type*} [AddCommGroup A] [Module K A]
    {i : A →ₗ[K] E} (hi : d.IsImmediate i) (z : E) :
    ∃ x : A, ∀ c : K, d (c • z) 0 = d (i (c • x)) 0 := by
  by_cases hz : z ∈ range i
  · obtain ⟨x, rfl⟩ := hz
    exact ⟨x, fun c ↦ by rw [i.map_smul]⟩
  obtain ⟨x, hx⟩ := (hi z hz).2 0
  rw [map_zero] at hx
  refine ⟨x, fun c ↦ ?_⟩
  by_cases hc : c = 0
  · simp [hc]
  have hlt := IsSMulMono.smul_dist_lt d hc hx
  rw [smul_zero] at hlt
  rw [i.map_smul]
  exact (d.eq_of_lt hlt).symm

/-- The initial inclusion into a one-dimensional immediate extension. The nontrivial filter
records how the extension distance is computed, so identities for the distances of the affine
evaluations (in particular scalar homogeneity) pass to the new distance. -/
theorem exists_isImmediate_linear_extension_of_not_isSphericallyComplete
    (h : ¬ d.IsSphericallyComplete) :
    ∃ (e : PseudoMetric (E × K) Γ) (L : Filter E), L.NeBot ∧ e.IsUltra ∧ e.IsAddInvariant ∧
      e.IsSMulMono K ∧ (∀ x y : E, e (x, 0) (y, 0) = d x y) ∧
      e.IsImmediate (LinearMap.inl K E K) ∧ ∀ p q : E × K, ∀ᶠ z in L,
        d (p.1 + p.2 • z) (q.1 + q.2 • z) = e p q := by
  classical
  obtain ⟨L, r, hL, hval, himprove⟩ := d.exists_filter_of_not_isSphericallyComplete h
  let ev (z : E) : E × K →ₗ[K] E := LinearMap.coprod LinearMap.id (LinearMap.toSpanSingleton K E z)
  have hev (z : E) (p : E × K) : ev z p = p.1 + p.2 • z := rfl
  have affine (x z : E) {a : K} (ha : a ≠ 0) :
      x + a • z = a • (z - (-(a⁻¹ • x))) := by
    rw [sub_neg_eq_add, smul_add, smul_inv_smul₀ ha, add_comm]
  have stable (p : E × K) : ∃ v : Γ, ∀ᶠ z in L, d (ev z p) 0 = v := by
    obtain ⟨x, a⟩ := p
    by_cases ha : a = 0
    · subst a
      exact ⟨d x 0, Eventually.of_forall fun z ↦ by simp [hev]⟩
    let t := -(a⁻¹ • x)
    obtain ⟨w, hw⟩ := (hval t).exists
    refine ⟨d (x + a • w) 0, ?_⟩
    filter_upwards [hval t] with z hz
    rw [hev, affine x z ha, affine x w ha]
    have heq : d (z - t) 0 = d (w - t) 0 := by rw [d.sub_zero_eq, d.sub_zero_eq, hz, hw]
    exact le_antisymm (IsSMulMono.smul_le (d := d) a heq.le)
      (IsSMulMono.smul_le (d := d) a heq.ge)
  choose N hN using stable
  let δ (p q : E × K) := N (p - q)
  have hδ (p q : E × K) : ∀ᶠ z in L, d (ev z p) (ev z q) = δ p q := by
    simpa only [map_sub, d.sub_zero_eq, δ] using hN (p - q)
  let e : PseudoMetric (E × K) Γ := {
    toFun := δ
    refl' p := by obtain ⟨z, hz⟩ := (hδ p p).exists; exact hz.symm.trans (d.refl _)
    symm' p q := by
      obtain ⟨z, hp, hq⟩ := ((hδ p q).and (hδ q p)).exists
      rw [← hp, ← hq, d.symm]
    triangle' p q t := by
      obtain ⟨z, hp, hq, ht⟩ := ((hδ p t).and ((hδ p q).and (hδ q t))).exists
      rw [← hp, ← hq, ← ht]
      apply d.triangle }
  have heval (p q : E × K) : ∀ᶠ z in L, d (ev z p) (ev z q) = e p q := hδ p q
  refine ⟨e, L, hL, ⟨fun p q t ↦ ?_⟩, ⟨fun p q t ↦ ?_⟩, ⟨fun a x y hxy ↦ ?_⟩,
    fun x y ↦ ?_, ?_, heval⟩
  · obtain ⟨z, hp, hq, ht⟩ := ((heval p t).and ((heval p q).and (heval q t))).exists
    rw [← hp, ← hq, ← ht]
    apply IsUltra.le_sup' (d := d)
  · obtain ⟨z, hp, hq⟩ := ((heval (p + t) (q + t)).and (heval p q)).exists
    rw [← hp, ← hq, (ev z).map_add, (ev z).map_add, IsAddInvariant.add_right]
  · obtain ⟨z, hx, hy, hax, hay⟩ := ((heval x 0).and ((heval y 0).and
      ((heval (a • x) 0).and (heval (a • y) 0)))).exists
    rw [← hx, ← hy, map_zero] at hxy
    rw [← hax, ← hay, map_zero, (ev z).map_smul, (ev z).map_smul]
    exact IsSMulMono.smul_le (d := d) a hxy
  · obtain ⟨z, hz⟩ := (heval (x, 0) (y, 0)).exists
    simpa only [hev, zero_smul, add_zero] using hz.symm
  · rintro ⟨x, a⟩ hout
    have ha : a ≠ 0 := by rintro rfl; exact hout ⟨x, rfl⟩
    refine ⟨inferInstance, fun u ↦ ?_⟩
    let t := -(a⁻¹ • (x - u))
    obtain ⟨w, hw⟩ := himprove t
    refine ⟨x + a • w, ?_⟩
    obtain ⟨z, hzw, hzt, hleft, hright⟩ := ((hval w).and ((hval t).and
      ((heval (x, a) (x + a • w, 0)).and (heval (x, a) (u, 0))))).exists
    change e (x, a) (x + a • w, 0) < e (x, a) (u, 0)
    rw [← hleft, ← hright]
    simp only [hev, zero_smul, add_zero]
    rw [← d.sub_zero_eq (x + a • z) (x + a • w), ← d.sub_zero_eq (x + a • z) u]
    have h1 : x + a • z - (x + a • w) = a • (z - w) := by rw [smul_sub]; abel
    have h2 : x + a • z - u = a • (z - t) := by rw [← affine (x - u) z ha]; abel
    rw [h1, h2]
    apply IsSMulMono.smul_lt d ha
    rwa [d.sub_zero_eq, d.sub_zero_eq, hzw, hzt]

/-- Spherical completeness is equivalent to admitting no proper immediate linear extension.
It suffices to test extensions in the universe of the product of the source and its scalars.
The linear maps are injective even when the pseudometrics have nontrivial zero fibers. -/
theorem isSphericallyComplete_iff_maximallyComplete_linear {E : Type u} {K : Type v}
    [DivisionRing K] [AddCommGroup E] [Module K E] (d : PseudoMetric E Γ)
    [d.IsUltra] [d.IsAddInvariant] [d.IsSMulMono K] :
    d.IsSphericallyComplete ↔ ∀ {F : Type (max u v)} [AddCommGroup F] [Module K F]
      (e : PseudoMetric F Γ) [e.IsUltra] [e.IsAddInvariant] [e.IsSMulMono K] (f : E →ₗ[K] F),
      Injective f → (∀ x y, e (f x) (f y) = d x y) → e.IsImmediate f → Surjective f := by
  constructor
  · intro _ F _ _ e _ _ _ f _ hd hi
    exact hi.surjective d e hd
  · intro h
    by_contra hn
    obtain ⟨e, _, _, _, _, _, hd, hi, _⟩ :=
      d.exists_isImmediate_linear_extension_of_not_isSphericallyComplete K hn
    have hs := h e (LinearMap.inl K E K) LinearMap.inl_injective hd hi
    obtain ⟨x, hx⟩ := hs (0, 1)
    exact zero_ne_one (congrArg Prod.snd hx)

end PseudoMetric
