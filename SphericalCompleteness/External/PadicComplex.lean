import SphericalCompleteness.External.PadicAlgCl
import SphericalCompleteness.External.DenselyNormedField

open PadicAlgCl
open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable instance : DenselyNormedField ℂ_[p] := inferInstance
