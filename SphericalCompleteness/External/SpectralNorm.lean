import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

theorem spectralAlgNorm_pow {K : Type u} [NontriviallyNormedField K] {L : Type v} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [hu : IsUltrametricDist K] [CompleteSpace K] (x : L) (n : ℕ):
  (spectralNorm K L) (x ^ n) = ((spectralNorm K L) x) ^ n := by
  induction n
  · simp [spectralNorm_one]
  · expose_names

    sorry
