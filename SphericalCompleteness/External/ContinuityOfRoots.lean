import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Algebra.Polynomial.Splits

open Polynomial

/--
`Polynomial.toAlgCl f` is the polynomial obtained from `f : Polynomial 𝕜` by base-changing
its coefficients to the algebraic closure `AlgebraicClosure 𝕜`.

This is defined as `Polynomial.map (algebraMap 𝕜 (AlgebraicClosure 𝕜)) f`, i.e. it applies
the canonical map `𝕜 →+* AlgebraicClosure 𝕜` coefficientwise.

This is an abbreviation (not a new definition) and is marked `noncomputable` because
`AlgebraicClosure 𝕜` is noncomputable in general.
-/
noncomputable abbrev Polynomial.toAlgCl {𝕜 : Type u_1} [Field 𝕜] (f : Polynomial 𝕜) :=
  (Polynomial.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))) f

/--
`toAlgCl` does not change the degree of a polynomial.

For a field `𝕜` and a polynomial `f : Polynomial 𝕜`, coercing `f` to the algebraic closure
(via `f.toAlgCl`) preserves `natDegree`. This is a common bookkeeping lemma used when
moving a polynomial to `AlgebraicClosure 𝕜` (e.g. to talk about roots there) while keeping
degree computations unchanged.
-/
lemma toAlgCl_natdeg_eq {𝕜 : Type u_1} [Field 𝕜] (f : Polynomial 𝕜) :
  (f.toAlgCl).natDegree = f.natDegree := by
  unfold toAlgCl
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap 𝕜 (AlgebraicClosure 𝕜)).injective]

/--
`Polynomial.stdGaussNorm f` is the Gauss norm of a polynomial `f : Polynomial 𝕜` computed with respect
to the given norm on `𝕜` and parameter `r = 1`.

Concretely, this is `gaussNorm` specialized to `Polynomial 𝕜` (via the identity coercion) using
`hn.norm` as the coefficient norm. It is often convenient as the “standard” Gauss norm appearing in
nonarchimedean/analytic arguments, where taking `r = 1` avoids additional scaling factors.
-/
abbrev Polynomial.stdGaussNorm {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜] (f : Polynomial 𝕜) :=
(@gaussNorm _ _ _ {coe := fun f => f, coe_injective' := fun _ _ stupid => stupid} hn.norm 1) f

/--
`stdGaussNorm_nonneg` states that the *standard Gauss norm* of a polynomial over a
nontrivially normed field is always nonnegative.

More precisely, for any polynomial `f : Polynomial 𝕜` (with `[NontriviallyNormedField 𝕜]`),
the value `f.stdGaussNorm` is a nonnegative real number, i.e. `0 ≤ f.stdGaussNorm`.
This follows from the fact that `stdGaussNorm` is defined via norms (and supremums/maxima)
which are nonnegative by construction.
-/
lemma stdGaussNorm_nonneg {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) : 0 ≤ f.stdGaussNorm := by
  unfold stdGaussNorm gaussNorm
  by_cases hp : f.support.Nonempty <;>
  simp only [hp, ↓reduceDIte, le_refl, one_pow, mul_one]
  rw [Finset.le_sup'_iff]
  exact ⟨hp.choose, ⟨hp.choose_spec, norm_nonneg _⟩⟩

/--
`stdGaussNorm_eq_zero_iff` characterizes when the (standard) Gauss norm of a polynomial
over a nontrivially normed field vanishes.

It states that for `f : Polynomial 𝕜`, the value `f.stdGaussNorm` is zero if and only if
the polynomial itself is the zero polynomial. This provides the basic nondegeneracy of
`stdGaussNorm` and is typically used to turn norm-vanishing goals into polynomial-vanishing
goals (and conversely).

**Assumptions:**
- `𝕜` is a `NontriviallyNormedField`.

**Conclusion:**
- `f.stdGaussNorm = 0 ↔ f = 0`.
-/
lemma stdGaussNorm_eq_zero_iff {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) :
  f.stdGaussNorm = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  unfold stdGaussNorm gaussNorm at h
  if hh : f.support.Nonempty then
    simp only [hh, ↓reduceDIte, one_pow, mul_one] at h
    have := (Finset.sup'_le_iff hh _).1 <| le_of_eq h
    replace : ∀ b ∈ f.support, f.coeff b = 0 :=
      fun b hb => norm_eq_zero.mp <| eq_of_le_of_ge (this b hb) (norm_nonneg _)
    refine support_eq_empty.mp ?_
    by_contra hc
    have t := Finset.nonempty_iff_ne_empty.2 hc
    exact Polynomial.mem_support_iff.1 t.choose_spec <| this t.choose t.choose_spec
  else
  have := Polynomial.nonempty_support_iff.not.1 hh
  tauto

/--
Characterization of the (standard) Gauss norm of a polynomial by its coefficients.

For a polynomial `f : Polynomial 𝕜` over a nontrivially normed field and a real bound `r ≥ 0`,
this lemma states that the standard Gauss norm `f.stdGaussNorm` is bounded above by `r`
if and only if every coefficient of `f` has norm bounded above by `r`.

In other words, `f.stdGaussNorm ≤ r` exactly expresses the uniform bound
`∀ i, ‖f.coeff i‖ ≤ r` on all coefficients.
-/
lemma le_gaussNorm_iff_coeff_le {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) {r : ℝ} (hr : 0 ≤ r) :
  f.stdGaussNorm ≤ r ↔ ∀ i : ℕ, ‖f.coeff i‖ ≤ r := by
  unfold stdGaussNorm gaussNorm
  if h : f.support.Nonempty then
    simp only [h, ↓reduceDIte, one_pow, mul_one, Finset.sup'_le_iff, mem_support_iff, ne_eq]
    refine ⟨fun hh i => ?_, fun hh i hi ↦ hh i⟩
    if ht : f.coeff i = 0 then simpa [ht]
    else exact hh i ht
  else
  simp only [h, ↓reduceDIte, hr, true_iff]
  intro i
  suffices tt : f.coeff i = 0 by simpa [tt]
  exact notMem_support_iff.mp <| forall_not_of_not_exists h i

/--
For a polynomial `f` over a nontrivially normed field `𝕜`, the (standard) Gauss norm
`f.stdGaussNorm` is positive if and only if `f` is nonzero.

This lemma packages the basic nondegeneracy of the Gauss norm: it vanishes exactly on
the zero polynomial and is strictly positive otherwise.
-/
lemma gaussNorm_pos_iff {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) :
  0 < f.stdGaussNorm ↔ f ≠ 0 := by
  refine iff_not_comm.mp ?_
  simpa [← stdGaussNorm_eq_zero_iff] using
    ⟨fun h => ge_of_eq (id (Eq.symm h)), fun h => eq_of_le_of_ge h (stdGaussNorm_nonneg f)⟩

/--
If `f` is a monic polynomial over a nontrivially normed field `𝕜`, then its
`stdGaussNorm` is at least `1`.

Intuition: monicity means the leading coefficient of `f` is `1`, whose norm is `1`,
and the standard Gauss norm is (by definition/lemmas) bounded below by the norm of
each coefficient, hence in particular by the leading coefficient.

This lemma is typically used to ensure the Gauss norm is nonzero and to obtain
basic lower bounds needed in continuity or root estimates.
-/
lemma one_le_stdGaussNorm_of_monic {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) (hf : Monic f) :
  1 ≤ f.stdGaussNorm := by
  unfold stdGaussNorm gaussNorm
  have : f.support.Nonempty := by
    refine support_nonempty.mpr ?_
    exact Monic.ne_zero hf
  simp only [this, ↓reduceDIte, one_pow, mul_one, Finset.le_sup'_iff, mem_support_iff, ne_eq]
  use f.natDegree
  simp only [coeff_natDegree, hf, Monic.leadingCoeff, one_ne_zero, not_false_eq_true, norm_one,
    le_refl, and_self]

/--
If a polynomial `f : 𝕜[X]` over a field is monic and has a root in the algebraic closure
(via `eval` after mapping coefficients to `AlgebraicClosure 𝕜`), then `f` is nonconstant.
Equivalently, its `natDegree` is strictly positive.

This lemma is typically used to rule out the constant-monic case (`f = 1`), since a monic
constant polynomial cannot vanish at any point in any extension field.
-/
lemma pos_deg_of_monic_of_root {𝕜 : Type u_1} [Field 𝕜]
(f : 𝕜[X]) (hf : Monic f) (α : AlgebraicClosure 𝕜) (hfz : eval α f.toAlgCl = 0) :
  0 < f.natDegree := by
  refine (Monic.natDegree_pos hf).mpr ?_
  by_contra hc
  simp [hc] at hfz

/--
Given monic polynomials `f` and `g` of the same (polynomial) degree, and assuming `f` has a root
`α` in an algebraic closure (expressed as `eval α f.toAlgCl = 0`), this lemma bounds the degree of
their difference: the polynomial `g - f` has `natDegree` at most `f.natDegree - 1`.

Intuitively, since `f` and `g` are monic with equal degree, their leading terms cancel in `g - f`,
so the resulting polynomial must drop in degree by at least one.
-/
lemma natDegree_sub_monic_le_natDegree_sub_one {𝕜 : Type*} [hn : NontriviallyNormedField 𝕜]
  (f g : 𝕜[X]) (hf : f.Monic) (hg : g.Monic) (hfg : f.degree = g.degree) (α : AlgebraicClosure 𝕜)
  (hfz : eval α f.toAlgCl = 0) :
  (g - f).natDegree ≤ f.natDegree - 1 := by
  rw [Nat.le_sub_one_iff_lt <| pos_deg_of_monic_of_root f hf α hfz]
  refine lt_of_le_of_ne ?_ ?_
  · rw [sub_eq_add_neg]
    refine le_trans (natDegree_add_le _ _) ?_
    simp [natDegree_le_iff_degree_le, ← hfg]
  · by_contra hc
    have hc' := hc
    apply_fun (g - f).coeff at hc
    rw [Polynomial.coeff_sub, hc'] at hc
    nth_rw 1 [natDegree_eq_of_degree_eq hfg] at hc
    nth_rw 2 [← hc'] at hc
    simp [hf, hg] at hc
    simp [leadingCoeff_eq_zero.1 hc.symm] at hc'
    simp [eq_one_of_monic_natDegree_zero hf (id (Eq.symm hc'))] at hfz

/--
Bounds the spectral norm of a root `α` of a monic polynomial `f` over a nontrivially normed
ultrametric field `𝕜` by the standard Gauss norm of `f`.

More precisely, assuming:
* `f : 𝕜[X]` is monic (`hf : f.Monic`),
* `α : AlgebraicClosure 𝕜` is a root of `f` in the algebraic closure (`hfz : eval α f.toAlgCl = 0`),

the theorem shows:
` spectralNorm 𝕜 (AlgebraicClosure 𝕜) α ≤ f.stdGaussNorm `.

This is an ultrametric analogue of a Cauchy-type bound, relating the size of an algebraic element
to the sizes of the coefficients of its minimal polynomial (here expressed via `stdGaussNorm`).
-/
theorem spectralNorm_le_gaussNorm {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
[IsUltrametricDist 𝕜]
  (f : 𝕜[X]) (hf : f.Monic) (α : AlgebraicClosure 𝕜)
  (hfz : eval α f.toAlgCl = 0) :
  spectralNorm 𝕜 (AlgebraicClosure 𝕜) α ≤ f.stdGaussNorm := by
  if hx : ¬ 1 ≤ spectralNorm 𝕜 (AlgebraicClosure 𝕜) α then
    simp only [not_le] at hx
    exact le_of_lt <| lt_of_lt_of_le hx (one_le_stdGaussNorm_of_monic f hf)
  else
  simp only [not_le, not_lt] at hx
  suffices hh : (spectralNorm 𝕜 (AlgebraicClosure 𝕜) α) ^ f.natDegree ≤
    f.stdGaussNorm * (spectralNorm 𝕜 (AlgebraicClosure 𝕜) α) ^ (f.natDegree - 1) by
    have := one_le_stdGaussNorm_of_monic f hf
    if hα : spectralNorm 𝕜 (AlgebraicClosure 𝕜) α = 0 then
      simp [hα]; linarith
    else
    have : f.natDegree = f.natDegree - 1 + 1 :=
      (Nat.sub_eq_iff_eq_add <| pos_deg_of_monic_of_root f hf α hfz).mp rfl
    nth_rw 1 [this, pow_succ'] at hh
    rwa [mul_le_mul_iff_of_pos_right] at hh
    exact pow_pos (lt_of_le_of_ne (spectralNorm_nonneg α)
      (fun a ↦ hα (id (Eq.symm a)))) (f.natDegree - 1)
  have t := pos_deg_of_monic_of_root f hf α hfz
  rw [eval_eq_sum_range, Finset.sum_range_succ_comm] at hfz
  simp only [hf, Monic.natDegree_map, coeff_map, coeff_natDegree, Monic.leadingCoeff, map_one,
    one_mul] at hfz
  rw [add_eq_zero_iff_eq_neg, ← Finset.sum_neg_distrib] at hfz
  apply_fun spectralNorm 𝕜 (AlgebraicClosure 𝕜) at hfz
  have : IsPowMul (spectralNorm 𝕜 (AlgebraicClosure 𝕜)) := isPowMul_spectralNorm
  rw [this α t] at hfz
  rw [hfz]
  refine le_trans (IsNonarchimedean.apply_sum_le_sup_of_isNonarchimedean
    isNonarchimedean_spectralNorm <| Finset.Aesop.range_nonempty <| Nat.ne_zero_of_lt t) ?_
  simp only [Finset.sup'_le_iff, Finset.mem_range]
  intro i hi
  rw [spectralNorm_neg <| Algebra.IsAlgebraic.isAlgebraic _]
  refine le_trans (spectralNorm_mul
    (Algebra.IsAlgebraic.isAlgebraic _) (Algebra.IsAlgebraic.isAlgebraic _)) ?_
  apply mul_le_mul ?_ ?_ (spectralNorm_nonneg (α ^ i)) <| stdGaussNorm_nonneg f
  · rw [spectralNorm_extends]
    if hff : f.coeff i = 0 then
      simpa [hff] using stdGaussNorm_nonneg f
    else
    unfold Polynomial.stdGaussNorm Polynomial.gaussNorm
    simp only [support_nonempty.mpr <| Monic.ne_zero hf, ↓reduceDIte, one_pow, mul_one,
      Finset.le_sup'_iff, mem_support_iff, ne_eq]
    use i
  · have : IsPowMul (spectralNorm 𝕜 (AlgebraicClosure 𝕜)) := isPowMul_spectralNorm
    if hi' : i = 0 then
      simpa only [hi', pow_zero, spectralNorm_one, ge_iff_le] using one_le_pow₀ hx
    else
    rw [this α (Nat.one_le_iff_ne_zero.2 hi')]
    exact pow_le_pow_right₀ hx <| (Nat.le_sub_one_iff_lt t).mpr hi

open Classical in
/--
`Finset.prod.multiplicative_mor` states that a function `g : M → β` which is a multiplicative
monoid morphism (in the sense that it maps `1 ↦ 1` and preserves multiplication) commutes with
finite products over a `Finset`.

More precisely, for a finset `s : Finset ι` and a function `f : ι → M`, if
* `hg1 : g 1 = 1`, and
* `hgmul : ∀ x y, g (x * y) = g x * g y`,
then applying `g` to the (double) finset product `∏ i ∈ s, f i` equals the product of the
images `∏ i ∈ s, g (f i)`.

This is useful when `g` is not bundled as a `MonoidHom`, but one still wants the standard
"map over product" lemma.
-/
lemma Finset.prod.multiplicative_mor {ι : Type*}
{M : Type*} [CommMonoid M] (s : Finset ι) (f : ι → M)
{β : Type*} [CommMonoid β] (g : M → β)
(hg1 : g 1 = 1) (hgmul : ∀ x y : M, g (x * y) = g x * g y) :
  g (∏ i ∈ s, f i) = ∏ i ∈ s, g (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa
  | insert a s ha ih =>
    nth_rw 2 [Finset.prod_insert ha]
    rw [← ih, ← hgmul, ← Finset.prod_insert ha]

/--
Bounds the spectral algebra norm of `g(α)` in terms of the Gauss norm of `f - g` and the
Gauss norm of `f`, assuming `α` is a root of `f`.

More precisely, over a nontrivially normed ultrametric field `𝕜`, for monic polynomials
`f g : Polynomial 𝕜` of the same degree, and `α : AlgebraicClosure 𝕜` with `f.toAlgCl.IsRoot α`,
one has
`‖g.toAlgCl.eval α‖ₛₚ ≤ ‖f - g‖₍Gauss₎ * ‖f‖₍Gauss₎^(f.natDegree - 1)`,
where the left-hand side is the `spectralAlgNorm` on `AlgebraicClosure 𝕜`.

This inequality is a continuity-type estimate for evaluating a polynomial at a root of a nearby
monic polynomial, measured using (standard) Gauss norms.
-/
theorem spectralNorm_eval_le_gaussNorm_sub {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
[IsUltrametricDist 𝕜]
(f g : Polynomial 𝕜) (hf : Monic f) (hg : Monic g) (hfg : f.degree = g.degree)
(α : AlgebraicClosure 𝕜)
(hfz : aeval α f = 0)
: spectralAlgNorm 𝕜 (AlgebraicClosure 𝕜) (g.toAlgCl.eval α)
  ≤ (f - g).stdGaussNorm * f.stdGaussNorm ^ (f.natDegree - 1)
:= by
  replace hfz : f.toAlgCl.IsRoot α := by
    simpa only [IsRoot.def, eval_map_algebraMap]
  have : g.toAlgCl.eval α = (g - f).toAlgCl.eval α + f.toAlgCl.eval α := by simp
  unfold Polynomial.IsRoot at hfz
  rw [hfz, add_zero] at this
  nth_rw 2 [Polynomial.eval_eq_sum_range] at this
  rw [this]
  refine le_trans
    (IsNonarchimedean.apply_sum_le_sup_of_isNonarchimedean isNonarchimedean_spectralNorm
    (by simp : (Finset.range ((g - f).toAlgCl.natDegree + 1)).Nonempty)) ?_
  simp only [Finset.sup'_le_iff, Finset.mem_range]
  intro i hi
  refine le_trans (spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic _) ?_) ?_
  · exact IsAlgebraic.pow (Algebra.IsAlgebraic.isAlgebraic α) i
  · apply mul_le_mul ?_ ?_ (spectralNorm_nonneg _) ?_
    · have : (g - f).toAlgCl.coeff i = algebraMap 𝕜 (AlgebraicClosure 𝕜) ((g - f).coeff i) := by
        simp
      rw [this, spectralNorm_extends]
      unfold Polynomial.stdGaussNorm Polynomial.gaussNorm
      if hp : (f - g).support.Nonempty then
        simp only [hp, ↓reduceDIte, one_pow, mul_one]
        rw [Finset.le_sup'_iff]
        if hi : i ∈ (f - g).support then
          use i
          simp [hi, norm_sub_rev]
        else
          have : (g - f).coeff i = 0 := by
            refine notMem_support_iff.mp ?_
            contrapose hi
            rw [mem_support_iff] at *
            simp only [coeff_sub, ne_eq] at *
            grind only
          simp only [mem_support_iff, ne_eq, this, norm_zero]
          exact ⟨hp.choose, ⟨mem_support_iff.mp hp.choose_spec, norm_nonneg _⟩⟩
      else
        simp at hp
        simp [sub_eq_zero.1 hp] at *
    · if hi' : i = 0 then
        simpa [hi', spectralNorm_one] using one_le_pow₀ <| one_le_stdGaussNorm_of_monic f hf
      else
      have : IsPowMul (spectralNorm 𝕜 (AlgebraicClosure 𝕜)) := isPowMul_spectralNorm
      rw [this α (Nat.one_le_iff_ne_zero.2 hi')]
      refine le_trans (?_ : spectralNorm 𝕜 (AlgebraicClosure 𝕜) α ^ i ≤ f.stdGaussNorm ^ i) ?_
      · apply pow_le_pow_left₀ (spectralNorm_nonneg α)
        exact spectralNorm_le_gaussNorm f hf α hfz
      · refine pow_le_pow_right₀ (one_le_stdGaussNorm_of_monic _ hf) ?_
        refine le_trans (Nat.lt_add_one_iff.1 hi) ?_
        rw [toAlgCl_natdeg_eq]
        exact natDegree_sub_monic_le_natDegree_sub_one f g hf hg hfg α hfz
    · exact stdGaussNorm_nonneg (f - g)

open Classical in
/--
`continuity_of_roots₀` is a quantitative continuity statement for roots of monic polynomials over a
complete nontrivially normed ultrametric field.

Given monic polynomials `f` and `g` of the same degree over `𝕜`, and a root `α` of `f` in the
algebraic closure `AlgebraicClosure 𝕜`, the theorem produces a root `β` of `g` such that the
distance between `α` and `β` (measured by `spectralAlgNorm` on the algebraic closure) is controlled
by the size of the perturbation `(f - g)` (measured by `stdGaussNorm`), with an exponent
`1 / f.natDegree` and scaled by `f.stdGaussNorm`.

More precisely, it asserts the existence of `β` with `g.toAlgCl.IsRoot β` and
`‖α - β‖ ≤ ‖f - g‖^(1 / natDegree f) * ‖f‖`, using the specific norms `spectralAlgNorm` and
`stdGaussNorm` in this development.

This lemma is intended as a “root stability” bound in the non-archimedean/ultrametric setting.
-/
theorem continuity_of_roots₀ {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [IsUltrametricDist 𝕜]
(f g : Polynomial 𝕜) (hf : Monic f) (hg : Monic g) (hfg : f.degree = g.degree)
(α : AlgebraicClosure 𝕜) (hα : aeval α f = 0) :
∃ β : AlgebraicClosure 𝕜,
  aeval β g = 0 ∧
  spectralAlgNorm 𝕜 (AlgebraicClosure 𝕜) (α - β)
    ≤ (f - g).stdGaussNorm ^ (1 / (f.natDegree : ℝ)) * f.stdGaussNorm := by
  if hfg' : f = g then
    use α
    simp only [← hfg', sub_self, map_zero, gaussNorm_zero, one_div]
    exact ⟨by simpa using hα, mul_nonneg (Real.zero_rpow_nonneg _) (stdGaussNorm_nonneg _)⟩
  else
  by_contra hc
  push_neg at hc
  have : IsAlgClosed (AlgebraicClosure 𝕜) := IsAlgClosure.isAlgClosed 𝕜
  have := Polynomial.Splits.aeval_eq_prod_aroots_of_monic (this.splits g.toAlgCl) hg α
  have t : (aeval α) g = g.toAlgCl.eval α := by
    simp [aeval, toAlgCl]
  rw [t, Multiset.prod_eq_prod_toEnumFinset] at this
  apply_fun (spectralNorm 𝕜 (AlgebraicClosure 𝕜)) at this
  rw [Finset.prod.multiplicative_mor _ _ (spectralNorm 𝕜 (AlgebraicClosure 𝕜))] at this
  · have this' : ∀ s ∈ (Multiset.map (fun a ↦ α - a) (g.aroots (AlgebraicClosure 𝕜))).toEnumFinset,
      (f - g).stdGaussNorm ^ (1 / (↑f.natDegree : ℝ)) * f.stdGaussNorm <
      spectralNorm 𝕜 (AlgebraicClosure 𝕜) s.1 := by
      intro s hs
      rcases Multiset.mem_map.1 (Multiset.mem_of_mem_toEnumFinset hs) with ⟨z, hz⟩
      simpa [← hz.2] using hc z (by simpa using isRoot_of_mem_roots hz.1)
    replace this' := Finset.prod_lt_prod_of_nonempty ?_ this' ?_
    · rw [← this] at this'
      simp only [one_div, Finset.prod_const, Multiset.card_toEnumFinset, Multiset.card_map,
        eval_map_algebraMap] at this'
      rw [IsAlgClosed.card_aroots_eq_natDegree, mul_pow] at this'
      rw [← natDegree_eq_of_degree_eq hfg, ← Real.rpow_natCast, Real.rpow_inv_rpow] at this'
      · have := spectralNorm_eval_le_gaussNorm_sub f g hf hg hfg α (by simpa only [IsRoot.def,
        eval_map_algebraMap] using hα)
        simp only [eval_map_algebraMap] at this
        replace := lt_of_lt_of_le this' this
        have t := (gaussNorm_pos_iff (f - g)).2 <| sub_ne_zero_of_ne hfg'
        replace := (mul_lt_mul_iff_right₀ t).1 this
        rw [pow_lt_pow_iff_right₀] at this
        · omega
        · have t := one_le_stdGaussNorm_of_monic f hf
          refine lt_of_le_of_ne t ?_
          by_contra hc
          rw [← hc] at this
          simp only [one_pow, lt_self_iff_false] at this
      · exact stdGaussNorm_nonneg (f - g)
      · simpa only [ne_eq, Nat.cast_eq_zero] using
        Nat.ne_zero_of_lt <| Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hf hα
    · intro _ _
      apply mul_pos
      · apply Real.rpow_pos_of_pos
        replace hfg' : f - g ≠ 0 := sub_ne_zero_of_ne hfg'
        exact (gaussNorm_pos_iff (f - g)).mpr hfg'
      · have := one_le_stdGaussNorm_of_monic f hf; linarith
    · suffices hw : (g.aroots (AlgebraicClosure 𝕜)).toFinset.Nonempty by
        rcases hw with ⟨a, ha⟩
        use (α - a,0)
        simp only [Multiset.mem_toEnumFinset]
        refine Multiset.count_pos.mpr <| Multiset.mem_map.mpr ?_
        use a
        simp at ha
        simp [ha]
      have := Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hf hα
      rw [natDegree_eq_of_degree_eq hfg] at this
      replace : g.toAlgCl.degree ≠ 0 := by
        simpa using ne_of_gt <| natDegree_pos_iff_degree_pos.1 this
      rcases IsAlgClosed.exists_root _ this with ⟨a, ha⟩
      use a
      simp at ha
      simpa [ha] using Polynomial.Monic.ne_zero_of_ne (zero_ne_one' 𝕜) hg
  · exact spectralNorm_one
  · exact fun x y => spectralAlgNorm_mul x y

/--
`continuity_of_roots` (informal): roots of a monic polynomial over a complete nontrivially normed
ultrametric field vary continuously with the coefficients, measured in `stdGaussNorm`, and the
distance between roots is controlled by `spectralAlgNorm`.

More precisely, given:
* a nontrivially normed field `𝕜` which is complete and ultrametric (`[IsUltrametricDist 𝕜]`),
* a polynomial `f : Polynomial 𝕜` which is monic (`hf : Monic f`),
* a chosen root `α : AlgebraicClosure 𝕜` of `f` (`hα : aeval α f = 0`),
* an error tolerance `ε > 0`,

the theorem produces `δ > 0` such that for every monic polynomial `g` of the same degree as `f`,
if `g` is `δ`-close to `f` in `stdGaussNorm` (i.e. `(f - g).stdGaussNorm ≤ δ`), then `g` admits
a root `β : AlgebraicClosure 𝕜` with:
* `aeval β g = 0`, and
* `spectralAlgNorm 𝕜 (AlgebraicClosure 𝕜) (α - β) ≤ ε`.

This is a quantitative continuity statement for roots in an algebraic closure, with the size of
perturbations measured by the Gauss norm on coefficients and the root displacement measured by the
spectral algebra norm.
-/
theorem continuity_of_roots {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [IsUltrametricDist 𝕜]
  (f : Polynomial 𝕜) (hf : Monic f) (α : AlgebraicClosure 𝕜) (hα : aeval α f = 0)
  {ε : ℝ} (hε : 0 < ε) :
∃ δ : ℝ, 0 < δ ∧
  ∀ g : Polynomial 𝕜, Monic g →
  f.degree = g.degree →
  (f - g).stdGaussNorm ≤ δ →
  ∃ β : AlgebraicClosure 𝕜,
    aeval β g = 0 ∧
    spectralAlgNorm 𝕜 (AlgebraicClosure 𝕜) (α - β) ≤ ε := by
  use (ε / f.stdGaussNorm) ^ (f.natDegree : ℝ)
  constructor
  · refine Real.rpow_pos_of_pos (div_pos hε ?_) ↑f.natDegree
    have := one_le_stdGaussNorm_of_monic f hf; linarith
  · intro g hg hfg hfgs
    rcases continuity_of_roots₀ f g hf hg hfg α (by simpa using hα) with ⟨β, hβroot, hβnorm⟩
    use β
    refine ⟨by simpa using hβroot, le_trans hβnorm ?_⟩
    suffices hh : (f - g).stdGaussNorm ^ (1 / (↑f.natDegree : ℝ)) ≤ ε / f.stdGaussNorm by
      refine (le_div_iff₀ ?_).mp hh
      have := one_le_stdGaussNorm_of_monic f hf; linarith
    simp only [one_div]
    rwa [Real.rpow_inv_le_iff_of_pos (stdGaussNorm_nonneg (f - g))]
    · exact div_nonneg (le_of_lt hε) (stdGaussNorm_nonneg f)
    · simpa using pos_deg_of_monic_of_root f hf α (by simpa using hα)
