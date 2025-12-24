import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Analysis.Normed.Algebra.Ultra
import SphericalCompleteness.Dense
open Metric
open Filter
open TopologicalSpace
open NNReal
open PadicAlgCl
open PadicComplex

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

instance {p : ℕ} [hp : Fact (Nat.Prime p)] : SeparableSpace (PadicAlgCl p) := sorry

instance {p : ℕ} [hp : Fact (Nat.Prime p)] : SeparableSpace (ℂ_[p]) := sorry

noncomputable instance : SeminormedAddGroup ℂ_[p] where
  __ := PadicComplex.instNormedField p

#synth Norm (PadicComplex p)
instance {p : ℕ} [hp : Fact (Nat.Prime p)] : IsUltrametricDist (PadicComplex p) := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)



instance {p : ℕ} [hp : Fact (Nat.Prime p)] : DenselyNormedField (PadicComplex p) := sorry

instance {p : ℕ} [hp : Fact (Nat.Prime p)] : ¬ SphericallyCompleteSpace (PadicComplex p) := by
  have : DenselyNormedField (PadicComplex p) := by infer_instance
  #check this.toPseudoEMetricSpace
  have this' := @diam_eq_radius_of_dense_ultrametric (PadicComplex p) this sorry
  have := @not_spherically_complete_of_dense_separable_ultrametric (PadicComplex p) this.toMetricSpace sorry this' inferInstance sorry


  --apply not_spherically_complete_of_dense_separable_ultrametric
  sorry
