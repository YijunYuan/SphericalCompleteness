import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy

open Metric
class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  isSphericallyComplete : ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → ℝ⦄,
    Antitone (fun i => ball (ci i) (ri i)) → (⋂ i, ball (ci i) (ri i)) ≠ ∅

instance instCompleteOfSphericallyComplete (α : Type*) [PseudoMetricSpace α] [SphericallyCompleteSpace α] : CompleteSpace α where
  complete := by

    sorry
