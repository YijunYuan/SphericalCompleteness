import Mathlib.NumberTheory.Padics.ProperSpace
import SphericalCompleteness.External.Complete
import SphericalCompleteness.External.NNReal
import SphericalCompleteness.External.Sequence
import SphericalCompleteness.External.Ultrametric

open Metric
open Filter

/--
A `PseudoMetricSpace` is *spherically complete* if every nested (antitone) sequence
of closed balls has nonempty intersection.

More precisely, given centers `ci : ℕ → α` and radii `ri : ℕ → NNReal`, if the family
of closed balls `i ↦ closedBall (ci i) (ri i)` is antitone with respect to inclusion
(i.e. the balls are decreasing as `i` increases), then the intersection
`⋂ i, closedBall (ci i) (ri i)` is nonempty.

This is a standard completeness-type axiom used in non-Archimedean/ultrametric settings,
but it is stated here for general pseudo-metric spaces.
-/
class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  isSphericallyComplete : ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone (fun i => closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty

namespace SphericallyCompleteSpace

/--
Builds a `CompleteSpace` instance from a `SphericallyCompleteSpace`.

In a `PseudoMetricSpace`, completeness can be characterized by the property that every
antitone (nested) family of closed balls whose radii tend to `0` has a nonempty intersection.
A spherically complete space provides exactly this nonempty-intersection property for nested
balls, so we can rewrite completeness using
`completeSpace_iff_nested_ball_with_radius_tendsto_zero_has_nonempty_inter` and discharge the
resulting goal via `SphericallyCompleteSpace.isSphericallyComplete`.

This instance is useful for transferring results stated for `CompleteSpace` to contexts where
spherical completeness is assumed.
-/
instance instCompleteOfSphericallyComplete (α : Type*)
  [PseudoMetricSpace α] [sc : SphericallyCompleteSpace α] : CompleteSpace α := by
  rw [completeSpace_iff_nested_ball_with_radius_tendsto_zero_has_nonempty_inter]
  exact fun _ _ hanti _ ↦ sc.isSphericallyComplete hanti

/--
Constructs a `SphericallyCompleteSpace` instance from `ProperSpace`.

In a proper pseudo-metric space, every closed ball is compact. This lemma uses that fact
to show spherical completeness: given a sequence of closed balls
`closedBall (ci i) (ri i)` that is antitone under inclusion (the `hanti` hypothesis),
the intersection of all these balls is nonempty.

The proof applies
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` to the family of
closed balls, using:
* `hanti` to provide the monotonicity (nestedness) condition,
* `nonempty_closedBall` (from `ri i` being nonnegative) for each ball’s nonemptiness,
* `isCompact_closedBall` (from `ProperSpace`) for compactness of an initial ball,
* `isClosed_closedBall` for closedness of each ball.
-/
instance instSphericallyCompleteSpaceOfProperSpace (α : Type*)
  [PseudoMetricSpace α] [ProperSpace α] : SphericallyCompleteSpace α where
  isSphericallyComplete := by
    intro ci ri hanti
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    <| fun i ↦ closedBall (ci i) ↑(ri i)
    · exact fun _ ↦  hanti (by linarith)
    · exact fun h ↦ nonempty_closedBall.mpr (ri h).prop
    · exact isCompact_closedBall (ci 0) ↑(ri 0)
    · exact fun i ↦ isClosed_closedBall

/--
Transport spherical completeness across an isometric equivalence.

Given pseudo-metric spaces `E` and `F`, an instance `[SphericallyCompleteSpace E]`,
and an isometry equivalence `f : E ≃ᵢ F`, this constructs `SphericallyCompleteSpace F`.

The proof pulls back any antitone family of closed balls in `F` along `f.symm` to an
antitone family of closed balls in `E`, uses spherical completeness of `E` to obtain a
point in the intersection, and then maps that point forward by `f`. Membership in each
ball is preserved because `f` is an isometry.

This is the standard “property invariant under isometric equivalence” argument.
-/
theorem sphericallyCompleteSpace_of_isometryEquiv {E F : Type*}
  [PseudoMetricSpace E] [PseudoMetricSpace F]
  [he : SphericallyCompleteSpace E]
  (f : E ≃ᵢ F) : SphericallyCompleteSpace F where
  isSphericallyComplete := by
    intro ci ri hanti
    let ci' := fun n => f.symm (ci n)
    have hanti' : Antitone (fun i => closedBall (ci' i) (ri i)) := by
      intro m n hmn
      simp only [Set.le_eq_subset]
      rw [← IsometryEquiv.preimage_closedBall f (ci m) ↑(ri m),
          ← IsometryEquiv.preimage_closedBall f (ci n) ↑(ri n)]
      specialize hanti hmn
      simp only [Set.le_eq_subset] at hanti
      grind only [= Set.subset_def, = Set.mem_preimage]
    rcases he.isSphericallyComplete hanti' with ⟨z',hz'⟩
    simp only [Set.mem_iInter, mem_closedBall, Set.nonempty_iInter] at *
    refine ⟨f z', fun i ↦ ?_⟩
    specialize hz' i
    unfold ci' at hz'
    rw [← IsometryEquiv.apply_symm_apply f (ci i), Isometry.dist_eq]
    · exact hz'
    · exact IsometryEquiv.isometry f

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
  haveI := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace α
  infer_instance

end SphericallyCompleteSpace
