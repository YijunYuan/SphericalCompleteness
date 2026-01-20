import SphericalCompleteness.External.PadicAlgCl
import SphericalCompleteness.External.DenselyNormedField
import SphericalCompleteness.External.Ultrametric

open PadicComplex
open TopologicalSpace

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable instance instDenselyNormedFieldPadicComplex : DenselyNormedField ℂ_[p] :=
  inferInstance

instance instSeparableSpacePadicComplex : SeparableSpace ℂ_[p] := inferInstance

instance : @IsUltrametricDist ℂ_[p] UniformSpace.Completion.instMetricSpace.toDist := inferInstance
