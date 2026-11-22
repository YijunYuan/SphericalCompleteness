/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Ultrametric distances on quotient spaces and spaces of continuous linear maps
-/

@[expose] public section

namespace IsUltrametricDist

/--
Transfers an ultrametric distance from a seminormed `𝕜`-normed space `E` to the quotient `E ⧸ F`.

Assuming `[IsUltrametricDist E]`, this instance equips the quotient by a submodule
`F : Submodule 𝕜 E` with an `IsUltrametricDist` structure (for the quotient distance coming from the
seminormed additive group structure on `E ⧸ F`), i.e. the distance on `E ⧸ F` satisfies the strong
triangle inequality.

This is useful for working with non-Archimedean/ultrametric geometry in quotients while retaining
the ultrametric property needed for many standard arguments.
-/
instance instIsUltrametricDistQuotient
    (𝕜 : Type*) [NormedField 𝕜]
    {E : Type*} [inst_1 : SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [iud : IsUltrametricDist E]
    {F : Submodule 𝕜 E} : IsUltrametricDist (E ⧸ F) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm <| by
    intro x y
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨x', hx', hx'_norm⟩ := Submodule.Quotient.norm_mk_lt (S := F) x hε
    obtain ⟨y', hy', hy'_norm⟩ := Submodule.Quotient.norm_mk_lt (S := F) y hε
    rw [← hx', ← hy']
    refine le_of_lt <| calc
      ‖(Submodule.Quotient.mk x' : E ⧸ F) + Submodule.Quotient.mk y'‖
          = ‖(Submodule.Quotient.mk (x' + y') : E ⧸ F)‖ := by simp
      _ ≤ max ‖x'‖ ‖y'‖ :=
        (Submodule.Quotient.norm_mk_le (S := F) (x' + y')).trans <| iud.norm_add_le_max _ _
      _ < max (‖x‖ + ε) (‖y‖ + ε) := by
        simpa [hx', hy'] using max_lt_max hx'_norm hy'_norm
      _ = max ‖(Submodule.Quotient.mk x' : E ⧸ F)‖ ‖(Submodule.Quotient.mk y' : E ⧸ F)‖ + ε := by
        simpa [hx', hy'] using
          (max_add_add_right ‖(Submodule.Quotient.mk x' : E ⧸ F)‖
            ‖(Submodule.Quotient.mk y' : E ⧸ F)‖ ε)

/--
Provides an `IsUltrametricDist` instance on the space of continuous linear maps `E →L[𝕜] F`
whenever the codomain `F` has an ultrametric distance.

Intuitively, this lifts the ultrametric inequality from `F` to the operator norm distance on
`E →L[𝕜] F`, so that for `f g h : E →L[𝕜] F` one has an inequality of the form
`dist f h ≤ max (dist f g) (dist g h)`.

**Typeclass assumptions:**
- `𝕜` is a nontrivially normed field,
- `E` and `F` are seminormed additive commutative groups and normed spaces over `𝕜`,
- `F` carries an ultrametric distance via `[IsUltrametricDist F]`.

This instance is intended for use in developments involving non-Archimedean / ultrametric
normed spaces, where spaces of bounded linear operators inherit ultrametric behavior from
their codomain.
-/
instance instIsUltrametricDistContinuousLinearMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [SeminormedAddCommGroup F] [iud : IsUltrametricDist F]
    [NormedSpace 𝕜 F] :
    IsUltrametricDist (E →L[𝕜] F) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun f g ↦ by
    rw [ContinuousLinearMap.opNorm_le_iff (le_max_of_le_left (norm_nonneg _))]
    intro x
    rw [max_mul_of_nonneg _ _ (norm_nonneg x)]
    exact (iud.norm_add_le_max _ _).trans (max_le_max (f.le_opNorm x) (g.le_opNorm x))

end IsUltrametricDist
