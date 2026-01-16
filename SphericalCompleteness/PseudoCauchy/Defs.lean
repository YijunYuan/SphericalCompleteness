import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Defs

def PseudoCauchySeq {α : Type*} [LinearOrder α] [IsWellOrder α (· < ·)]
{β : Type*} [Dist β] (f : α → β) : Prop :=
  ∀ a b c : α, a < b → b < c → Dist.dist (f a) (f b) < Dist.dist (f b) (f c)
