import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Polynomial.GaussNorm

open Polynomial

instance {𝕜 : Type u_1} : FunLike (𝕜 → ℝ) 𝕜 ℝ where
  coe := fun f => f
  coe_injective' := fun _ _ stupid => stupid

noncomputable abbrev Polynomial.toAlgCl {𝕜 : Type u_1} [Field 𝕜] (f : Polynomial 𝕜) :=
  (Polynomial.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))) f

abbrev Polynomial.stdGaussNorm {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜] (f : Polynomial 𝕜) :=
(Polynomial.gaussNorm hn.norm 1) f

theorem ttt {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
[IsUltrametricDist 𝕜]
(f g : Polynomial 𝕜) (hf : Monic f) (hg : Monic g) (hfg : f.degree = g.degree)
(α : AlgebraicClosure 𝕜)
(hfz : f.toAlgCl.IsRoot α)
: spectralAlgNorm 𝕜 (AlgebraicClosure 𝕜) (g.toAlgCl.eval α)
  ≤ (f - g).stdGaussNorm * f.stdGaussNorm ^ (f.natDegree - 1)
:= by
  have : g.toAlgCl.eval α = (g - f).toAlgCl.eval α + f.toAlgCl.eval α := by
    simp
  unfold Polynomial.IsRoot at hfz
  rw [hfz, add_zero] at this
  nth_rw 2 [Polynomial.eval_eq_sum_range] at this
  have hh : (g - f).toAlgCl.natDegree < f.toAlgCl.natDegree := sorry
  rw [this]
  refine le_trans
    (IsNonarchimedean.apply_sum_le_sup_of_isNonarchimedean isNonarchimedean_spectralNorm
    (by simp : (Finset.range ((g - f).toAlgCl.natDegree + 1)).Nonempty)) ?_
  simp only [Finset.sup'_le_iff, Finset.mem_range]
  intro i hi
  refine le_trans (spectralNorm_mul ?_ ?_) ?_
  · exact Algebra.IsAlgebraic.isAlgebraic _
  · exact IsAlgebraic.pow (Algebra.IsAlgebraic.isAlgebraic α) i
  · apply mul_le_mul
    · sorry
    · sorry
    · exact spectralNorm_nonneg (α ^ i)
    · unfold stdGaussNorm

      sorry
