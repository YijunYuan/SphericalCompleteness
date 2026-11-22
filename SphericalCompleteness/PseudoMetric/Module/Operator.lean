/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.Module.Extension

/-!
# Spherical completeness of spaces of bounded linear operators

A ball about an operator consists of the linear maps satisfying the corresponding pointwise
distance bound. Extending the zero map on the zero subspace subject to all the bounds in a
nest produces a common point of the nest.
-/

@[expose] public section

open Set

namespace PseudoMetric

variable {K E F V Γ Δ Ω : Type*} [DivisionRing K] [AddCommGroup E] [AddCommGroup F]
  [Module K E] [Module K F] [Zero Γ] [Add Γ] [LinearOrder Γ] [Zero Δ] [Add Δ] [LinearOrder Δ]
  [Zero Ω] [Add Ω] [LinearOrder Ω]
  (d : PseudoMetric E Γ) (e : PseudoMetric F Δ) (o : PseudoMetric V Ω)
  [d.IsUltra] [d.IsAddInvariant] [e.IsUltra] [e.IsAddInvariant] [e.IsSphericallyComplete]
  [o.IsUltra]

/-- A pointwise operator ball about `T` determined by the distance bound `φ`. -/
def linearMapBall (φ : Γ → Δ) (T : E →ₗ[K] F) : Set (E →ₗ[K] F) :=
  {g | ∀ x, e (g x) (T x) ≤ φ (d x 0)}

/-- Pairwise compatible bounds on a family of operators admit a simultaneous linear
approximant. This formulation does not require an operator norm to exist. -/
theorem nonempty_iInter_linearMapBall {ι : Type*} (T : ι → E →ₗ[K] F) (φ : ι → Γ → Δ)
    (hmono : ∀ i, Monotone (φ i)) (hcmp : ∀ i j, φ i ≤ φ j ∨ φ j ≤ φ i)
    (hsmul : ∀ i (c : K) {u : F} {x : E}, e u 0 ≤ φ i (d x 0) →
      e (c • u) 0 ≤ φ i (d (c • x) 0))
    (hT : ∀ i j x, e (T i x) (T j x) ≤ max (φ i (d x 0)) (φ j (d x 0))) :
    (⋂ i, d.linearMapBall e (φ i) (T i)).Nonempty := by
  obtain ⟨g, _, hg⟩ := exists_linearExtension_of_le_moduli d e T φ hmono hcmp hsmul hT ⊥ 0
    (fun i x ↦ by
      rw [Subsingleton.elim x 0]
      simpa only [map_zero, ZeroMemClass.coe_zero, LinearMap.zero_apply, max_self] using hT i i 0)
  exact ⟨g, mem_iInter.mpr hg⟩

/-- Arbitrary nests of nonempty pointwise operator balls intersect whenever the moduli form
a pointwise chain and respect distances under scalar multiplication. -/
theorem isDescendingCompleteFamily_linearMapBalls (M : Set (Γ → Δ))
    (hmono : ∀ φ ∈ M, Monotone φ) (hcmp : IsChain (· ≤ ·) M)
    (hsmul : ∀ φ ∈ M, ∀ (c : K) {u : F} {x : E}, e u 0 ≤ φ (d x 0) →
      e (c • u) 0 ≤ φ (d (c • x) 0)) :
    {B | ∃ φ ∈ M, ∃ T : E →ₗ[K] F, B = d.linearMapBall e φ T}.IsDescendingCompleteFamily := by
  intro S hs _ hn hc
  choose φ hφ T hB using fun B : S ↦ hs B.prop
  have hcenter (B : S) : T B ∈ B.val := by
    obtain ⟨g, hg⟩ := hn B B.prop
    rw [hB] at hg ⊢
    exact fun x ↦ (e.refl _).trans_le ((e.nonneg_of_ultra (g x) _).trans (hg x))
  have hle (A B : S) (hAB : A.val ⊆ B.val) (x : E) :
      e (T A x) (T B x) ≤ φ B (d x 0) := by
    have h := hAB (hcenter A)
    rw [hB] at h
    exact h x
  obtain ⟨g, hg⟩ := d.nonempty_iInter_linearMapBall e T φ (fun i ↦ hmono _ (hφ i))
    (fun i j ↦ hcmp.total (hφ i) (hφ j)) (fun i ↦ hsmul _ (hφ i)) (fun i j x ↦ by
      rcases hc.total i.prop j.prop with h | h
      · exact (hle i j h x).trans (le_max_right _ _)
      · exact ((e.symm _ _).trans_le (hle j i h x)).trans (le_max_left _ _))
  refine ⟨g, mem_sInter.mpr fun B h ↦ ?_⟩
  let b : S := ⟨B, h⟩
  change g ∈ b.val
  rw [hB]
  exact mem_iInter.mp hg b

/-- An operator space into a spherically complete target is spherically complete if its
closed balls express pointwise bounds, the bounds are monotone in radius and input distance,
and all linear maps bounded relative to an operator belong to the space. The three types of
distances may differ. -/
theorem IsSphericallyComplete.of_linearMap_bounds (L : V → E →ₗ[K] F) (φ : Ω → Γ → Δ)
    (hmono : ∀ r, 0 ≤ r → Monotone (φ r)) (hrad : ∀ r s, 0 ≤ r → r ≤ s → φ r ≤ φ s)
    (hsmul : ∀ r, 0 ≤ r → ∀ (c : K) {u : F} {x : E}, e u 0 ≤ φ r (d x 0) →
      e (c • u) 0 ≤ φ r (d (c • x) 0))
    (hball : ∀ A B r, 0 ≤ r → (o A B ≤ r ↔ ∀ x, e (L A x) (L B x) ≤ φ r (d x 0)))
    (hbounded : ∀ (g : E →ₗ[K] F) B r, 0 ≤ r →
      (∀ x, e (g x) (L B x) ≤ φ r (d x 0)) → ∃ A, L A = g) : o.IsSphericallyComplete := by
  classical
  constructor
  intro S hs hne hn hchain
  choose c r hrep using fun B : S ↦ hs B.prop
  have hr (B : S) : 0 ≤ r B := o.nonempty_closedBall.mp (hrep B ▸ hn B B.prop)
  have hcenter (B : S) : c B ∈ B.val := hrep B ▸ o.mem_closedBall_self.mpr (hr B)
  have hpair (A B : S) (hAB : A.val ⊆ B.val) (x : E) :
      e (L (c A) x) (L (c B) x) ≤ φ (r B) (d x 0) :=
    (hball _ _ _ (hr B)).mp (show c A ∈ o.closedBall (c B) (r B) from
      hrep B ▸ hAB (hcenter A)) x
  obtain ⟨g, h⟩ := d.nonempty_iInter_linearMapBall e (fun B : S ↦ L (c B))
    (fun B ↦ φ (r B)) (fun B ↦ hmono _ (hr B))
    (fun A B ↦ (le_total (r A) (r B)).imp (hrad _ _ (hr A)) (hrad _ _ (hr B)))
    (fun B ↦ hsmul _ (hr B)) (fun A B x ↦ by
      rcases hchain.total A.prop B.prop with h | h
      · exact (hpair _ _ h x).trans (le_max_right _ _)
      · exact ((e.symm _ _).trans_le (hpair _ _ h x)).trans (le_max_left _ _))
  have hg := mem_iInter.mp h
  obtain ⟨B, hB⟩ := hne
  obtain ⟨A, hA⟩ := hbounded g _ _ (hr ⟨B, hB⟩) (hg ⟨B, hB⟩)
  refine ⟨A, mem_sInter.mpr fun B hB ↦ ?_⟩
  let b : S := ⟨B, hB⟩
  change A ∈ b.val
  rw [hrep b, mem_closedBall, hball _ _ _ (hr b), hA]
  exact hg b

end PseudoMetric
