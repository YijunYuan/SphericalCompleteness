import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.LinearAlgebra.Basis.VectorSpace

import SphericalCompleteness.Orthogonal

open Metric
open Filter

namespace SphericallyCompleteSpace

theorem Quotient.sphericallyCompleteSpace
(𝕜 : Type*) [NontriviallyNormedField 𝕜] [scsk : SphericallyCompleteSpace 𝕜]
{E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
{F : Submodule 𝕜 E} [IsClosed (F : Set E)] :
SphericallyCompleteSpace (E ⧸ F) := sorry

theorem sphericallyComplete_ContinuousLinearMap
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]
[NormedSpace 𝕜 E]
{F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F] :
SphericallyCompleteSpace
  (ContinuousLinearMap (RingHom.id 𝕜) E F) := sorry

theorem exists_orthocomplement_of_spherically_complete_space
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F] :
∃ F' : Submodule 𝕜 E, IsCompl F F' ∧ 𝕆rthogonal 𝕜 F F':= sorry

-- `TODO` Hahn-Banach theorem for spherically complete spaces



end SphericallyCompleteSpace
