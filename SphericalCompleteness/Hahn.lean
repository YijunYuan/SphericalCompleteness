import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.HahnSeries.Summable
import SphericalCompleteness.External.Ultrametric
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.NormedValued

noncomputable instance {Γ : Type*} {R : Type*} [AddCommGroup Γ] [LinearOrderedCommGroupWithZero Γ] [IsOrderedAddMonoid Γ]
[Field R]
: Valued (HahnSeries Γ R) (Multiplicative (WithTop Γ)ᵒᵈ) := Valued.mk' (HahnSeries.addVal Γ R)

noncomputable instance {Γ : Type*} {R : Type*} [AddCommGroup Γ] [LinearOrderedCommGroupWithZero Γ] [IsOrderedAddMonoid Γ]
[Field R]
[h : Valuation.RankOne (HahnSeries.addVal Γ R)]
: NontriviallyNormedField (HahnSeries Γ R) :=
  @Valued.toNontriviallyNormedField (HahnSeries Γ R) _ (Multiplicative (WithTop Γ)ᵒᵈ) _  _ h
