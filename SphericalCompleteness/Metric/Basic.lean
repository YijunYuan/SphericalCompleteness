/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import SphericalCompleteness.External.Complete
public import SphericalCompleteness.Metric.Defs
public import SphericalCompleteness.PseudoMetric.Compact
public import SphericalCompleteness.PseudoMetric.Constructions

/-!
# Spherical completeness of real-valued pseudometric spaces

Spherical completeness implies completeness and holds in proper spaces. It passes along
surjective isometries and to finite products. Nested sequences can be tested on strictly
decreasing radii. In an ultrametric space, `tfae` also gives a pairwise-intersection criterion.
-/

@[expose] public section

open Metric
open Filter

namespace SphericallyCompleteSpace

/--
Builds a `CompleteSpace` instance from a `SphericallyCompleteSpace`.

In a `PseudoMetricSpace`, completeness can be characterized by the property that every
antitone (nested) family of closed balls whose radii tend to `0` has a nonempty intersection.
A spherically complete space provides exactly this nonempty-intersection property for nested
balls, so we can rewrite completeness using
`completeSpace_iff_nonempty_iInter_closedBall_of_tendsto_zero` and discharge the
resulting goal via `SphericallyCompleteSpace.nonempty_iInter_of_antitone`.

This instance is useful for transferring results stated for `CompleteSpace` to contexts where
spherical completeness is assumed.
-/
instance (priority := low) instCompleteOfSphericallyComplete (α : Type*)
    [PseudoMetricSpace α] [sc : SphericallyCompleteSpace α] : CompleteSpace α := by
  rw [completeSpace_iff_nonempty_iInter_closedBall_of_tendsto_zero]
  exact fun _ _ hanti _ ↦ sc.nonempty_iInter_of_antitone hanti

/-- The closed balls in a proper pseudometric space are compact and closed, so the
space is spherically complete. -/
instance instSphericallyCompleteSpaceOfProperSpace (α : Type*)
    [PseudoMetricSpace α] [ProperSpace α] : SphericallyCompleteSpace α :=
  (sphericallyCompleteSpace_iff α).mpr <|
    .of_isCompact_closedBall (nnMetric α)
      (fun c r ↦ by rw [ball_nnMetric]; exact isCompact_closedBall ..)
      (fun c r ↦ by rw [ball_nnMetric]; exact isClosed_closedBall)

/-- Spherical completeness passes in both directions along a surjective isometry. -/
theorem iff_of_surjective_isometry {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f : E → F} (hf : Function.Surjective f) (hi : Isometry f) :
    SphericallyCompleteSpace E ↔ SphericallyCompleteSpace F := by
  rw [sphericallyCompleteSpace_iff, sphericallyCompleteSpace_iff]
  exact (nnMetric E).isSphericallyComplete_iff_of_surjective (nnMetric F) hf hi.nndist_eq

/-- Transport spherical completeness across an isometric equivalence. -/
theorem of_isometryEquiv {E F : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    [he : SphericallyCompleteSpace E]
    (f : E ≃ᵢ F) : SphericallyCompleteSpace F :=
  (iff_of_surjective_isometry f.surjective f.isometry).mp he

/-- A pseudometric space is spherically complete exactly when its metric separation quotient is. -/
theorem separationQuotient_iff (E : Type*) [PseudoMetricSpace E] :
    SphericallyCompleteSpace (SeparationQuotient E) ↔ SphericallyCompleteSpace E :=
  (iff_of_surjective_isometry SeparationQuotient.surjective_mk
    (fun _ _ ↦ SeparationQuotient.edist_mk _ _)).symm

/--
Constructs a `SphericallyCompleteSpace` instance for a type `α` under the assumptions that `α` is a
`NontriviallyNormedField` and a `WeaklyLocallyCompactSpace`.

The proof proceeds by first obtaining a `ProperSpace α` instance via
`ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`, and then letting typeclass
resolution infer `SphericallyCompleteSpace α` from `ProperSpace α`.
-/
instance instSphericallyCompleteSpaceOfWeaklyLocallyCompactNormedField
    {α : Type*} [NontriviallyNormedField α] [WeaklyLocallyCompactSpace α] :
    SphericallyCompleteSpace α := by
  have := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace α
  infer_instance

section
variable (α : Type*) [PseudoMetricSpace α]

/-- Spherical completeness of a pseudometric space can be tested on nested sequences
whose radii are nonincreasing. -/
theorem iff_antitone_radius :
    SphericallyCompleteSpace α ↔
    ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone ri →
    Antitone (fun i ↦ closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty := by
  refine ⟨fun h _ _ _ ha ↦ h.nonempty_iInter_of_antitone ha, fun h ↦ ?_⟩
  apply (Metric.sphericallyCompleteSpace_iff α).mpr
  apply ((nnMetric α).isSphericallyComplete_iff_strictAnti_radius
    (fun _ _ ↦ zero_le) exists_seq_le_of_nonempty_radii).mpr
  simpa only [ball_nnMetric] using fun c r (_ : ∀ n, 0 ≤ r n) (hr : StrictAnti r) ↦
    @h c r hr.antitone

/-- It suffices to test nested sequences with strictly decreasing radii. -/
theorem iff_strictAnti_radius :
    SphericallyCompleteSpace α ↔
    ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    StrictAnti ri →
    Antitone (fun i ↦ closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty := by
  rw [Metric.sphericallyCompleteSpace_iff, (nnMetric α).isSphericallyComplete_iff_strictAnti_radius
    (fun _ _ ↦ zero_le) exists_seq_le_of_nonempty_radii]
  simp only [ball_nnMetric]
  exact ⟨fun h {c r} ↦ h c r (fun _ ↦ zero_le), fun h c r _ ↦ @h c r⟩

end

section
variable (α : Type*) [PseudoMetricSpace α] [iud : IsUltrametricDist α]

/--
Characterization of spherical completeness using only pairwise intersection of closed balls.

Let `α` be a pseudo-metric space whose distance is ultrametric (`[IsUltrametricDist α]`).
This theorem states that `α` is spherically complete if and only if the following
finite-intersection-type condition holds:

For every nonempty family `S : Set (α × NNReal)` of centers and radii, if any two closed balls
from the family intersect (i.e. for all `w1 w2 : S`, the set
`closedBall w1.1 w1.2 ∩ closedBall w2.1 w2.2` is nonempty), then the intersection of the entire
family is nonempty:
`(⋂ w : S, closedBall w.1 w.2).Nonempty`.

In contrast to the usual definition of spherical completeness (often phrased in terms of chains
of nested balls), this formulation replaces nesting by a pairwise intersection hypothesis,
which is sufficient in the ultrametric setting.
-/
theorem iff_pairwise_inter_nonempty :
    SphericallyCompleteSpace α ↔ (
    ∀ S : Set (α × NNReal), S.Nonempty →
    (∀ w1 w2 : ↑S, (closedBall w1.val.1 w1.val.2 ∩ closedBall w2.val.1 w2.val.2).Nonempty) →
    (⋂ w : ↑S, closedBall w.val.1 w.val.2).Nonempty) := by
  refine ⟨fun h S hSne h'↦ ?_, fun h ↦ { nonempty_iInter_of_antitone := ?_ }⟩
  · have : Nonempty S := hSne.to_subtype
    have : (nnMetric α).IsSphericallyComplete := (Metric.sphericallyCompleteSpace_iff α).mp h
    simpa only [ball_nnMetric] using PseudoMetric.IsSphericallyComplete.nonempty_iInter_of_pairwise
      (nnMetric α) (fun w : S ↦ w.val.1) (fun w : S ↦ w.val.2)
      (by simpa only [ball_nnMetric] using h')
  · intro c r hanti
    specialize h {(c i, r i) | (i : ℕ)} (by
      use (c 0, r 0), 0
      ) (by
      intro w1 w2
      rcases w1.prop with ⟨i1, hi1⟩
      rcases w2.prop with ⟨i2, hi2⟩
      simp only [← hi1, ← hi2]
      rcases le_total i1 i2 with hi | hi
      · rw [Set.inter_eq_self_of_subset_right <| hanti hi]
        exact nonempty_closedBall.mpr NNReal.zero_le_coe
      · rw [Set.inter_eq_self_of_subset_left <| hanti hi]
        exact nonempty_closedBall.mpr NNReal.zero_le_coe)
    simp only [Set.nonempty_iInter] at h
    rcases h with ⟨z, hz⟩
    exact ⟨z, Set.mem_iInter.2 <| fun i ↦ hz ⟨(c i, r i), i, rfl⟩⟩

open List in
/--
The equivalent characterizations of spherical completeness, bundled as a `TFAE` list.

For an ultrametric pseudometric space the following are equivalent:
1. `SphericallyCompleteSpace α` (every nested family of closed balls meets);
2. the intersection property for nested balls with *antitone* radii;
3. the intersection property for nested balls with *strictly decreasing* radii;
4. the pairwise-intersection property for an arbitrary family of closed balls.

This packages `iff_antitone_radius`,
`iff_strictAnti_radius` and
`iff_pairwise_inter_nonempty` into a single statement, so that any one
form can be obtained from any other via `List.TFAE.out`.
-/
theorem tfae :
    TFAE [
    SphericallyCompleteSpace α,
    ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone ri →
    Antitone (fun i ↦ closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty,
    ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    StrictAnti ri →
    Antitone (fun i ↦ closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty,
    ∀ S : Set (α × NNReal), S.Nonempty →
    (∀ w1 w2 : ↑S, (closedBall w1.val.1 w1.val.2 ∩ closedBall w2.val.1 w2.val.2).Nonempty) →
    (⋂ w : ↑S, closedBall w.val.1 w.val.2).Nonempty
    ] := by
  tfae_have 1 ↔ 2 := iff_antitone_radius α
  tfae_have 1 ↔ 3 := iff_strictAnti_radius α
  tfae_have 1 ↔ 4 := iff_pairwise_inter_nonempty α
  tfae_finish

end

/-- Spherical completeness of a binary product with the supremum metric. -/
instance _root_.Prod.sphericallyCompleteSpace {E F : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    [SphericallyCompleteSpace E] [SphericallyCompleteSpace F] :
    SphericallyCompleteSpace (E × F) := by
  apply (sphericallyCompleteSpace_iff _).mpr
  have h : nnMetric (E × F) = (nnMetric E).prod (nnMetric F) := by
    ext x y
    rfl
  rw [h]
  infer_instance

/-- Spherical completeness of a finite dependent product with the supremum metric. -/
instance _root_.Pi.sphericallyCompleteSpace {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, PseudoMetricSpace (E i)] [∀ i, SphericallyCompleteSpace (E i)] :
    SphericallyCompleteSpace (∀ i, E i) := by
  apply (sphericallyCompleteSpace_iff _).mpr
  have h : nnMetric (∀ i, E i) = PseudoMetric.pi (fun i ↦ nnMetric (E i)) := by
    apply DFunLike.ext
    intro x
    funext y
    rw [PseudoMetric.pi_apply_eq_finset_sup _ bot_eq_zero]
    exact nndist_pi_def x y
  rw [h]
  infer_instance

/-- The one-point space `PUnit` is spherically complete. Being trivially proper (its closed balls
are compact), it inherits spherical completeness from
`instSphericallyCompleteSpaceOfProperSpace`. -/
instance instSphericallyCompleteSpacePUnit : SphericallyCompleteSpace PUnit := inferInstance

/-- The complex numbers `ℂ` are spherically complete. As a finite-dimensional normed field `ℂ` is
proper (closed balls are compact), so spherical completeness follows from
`instSphericallyCompleteSpaceOfProperSpace`. -/
instance instSphericallyCompleteSpaceComplex : SphericallyCompleteSpace ℂ := inferInstance

/-- The real numbers `ℝ` are spherically complete. Being locally compact, hence proper, `ℝ` inherits
spherical completeness from `instSphericallyCompleteSpaceOfProperSpace`. -/
instance instSphericallyCompleteSpaceReal : SphericallyCompleteSpace ℝ := inferInstance

end SphericallyCompleteSpace
