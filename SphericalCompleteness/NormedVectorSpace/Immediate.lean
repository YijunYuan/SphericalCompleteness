/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.External.Ultrametric.Basic
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.HahnBanach
public import SphericalCompleteness.PseudoMetric.Module.ImmediateSubmodule
public import SphericalCompleteness.PseudoMetric.Module.SphericalCompletion.Basic

/-!
# Immediate extensions

This file develops the theory of *immediate extensions* of ultrametric normed vector spaces.

A linear isometry `f : E →ₗᵢ[𝕜] F` is *immediate* (`IsImmediate f`) when no nonzero vector of `F`
is metrically orthogonal to the range of `f`; equivalently, every `v : F` can be approximated by
vectors of `range f` strictly better than by `0`. Intuitively, `F` adds no genuinely new
"directions" beyond those already present in `E`. A space is *maximally complete*
(`MaximallyComplete 𝕜 E`) when it admits no proper immediate extension.

The central results are an *extension property* — an isometry out of `E` into a spherically
complete space extends along any immediate embedding of `E` — and a **Zorn's lemma** construction:
inside a fixed ambient space `E₀`, we collect the intermediate subspaces through which `f` factors
as an immediate extension into the set `immediateExtensionSubmodules` and extract a maximal such
subspace. When the ambient space `E₀` is *spherically complete*, this maximal subspace is again
spherically complete, and the induced embedding of `E` into it
(`maximalImmediateExtensionEmbedding`) is the space underlying the spherical completion of `E`.

## Main definitions

* `SphericallyCompleteSpace.IsImmediate`: the predicate that a linear isometry is an immediate
  embedding.
* `SphericallyCompleteSpace.MaximallyComplete`: the predicate that a space admits no proper
  immediate extension.
* `SphericallyCompleteSpace.IsImmediate.immediateExtensionSubmodules`: the set of intermediate
  subspaces of a fixed ambient space through which a linear isometry factors as an immediate
  extension.
* `SphericallyCompleteSpace.IsImmediate.maximalImmediateExtensionEmbedding`: the embedding of `E`
  into a maximal immediate-extension subspace of a spherically complete ambient space.

## Main statements

* `SphericallyCompleteSpace.IsImmediate.exists_linearIsometry_comp_eq`: any linear isometry from
  `E` into a spherically complete space extends along an immediate embedding of `E`.
* `SphericallyCompleteSpace.IsImmediate.exists_maximal_immediateExtensionSubmodule`: inside a
  fixed ambient space, **Zorn's lemma** produces a maximal immediate-extension subspace containing
  the range of `f`.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

/--
`IsImmediate f` means that the linear isometry `f : E →ₗᵢ[𝕜] F` has *immediate* image in `F`
(in the ultrametric sense): the only vector in `F` that is metrically orthogonal to the range
of `f` is `0`.

More precisely, it asserts:
`∀ v : F, (v ⟂ₘ LinearMap.range f) → v = 0`,
where `v ⟂ₘ S` is the predicate expressing metric orthogonality of `v` to the subspace `S`.
This rules out nontrivial orthogonal complements to `LinearMap.range f`.
-/
def IsImmediate {𝕜 : Type*} [NormedField 𝕜]
    {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type v} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    (f : E →ₗᵢ[𝕜] F) : Prop :=
∀ v : F, (v ⟂ₘ LinearMap.range f.toLinearMap) → v = 0

/-- In a seminormed space the normed-space definition also requires every vector of norm
zero to vanish. The strict approximation criterion alone applies to nonseparated spaces. -/
theorem isImmediate_iff_nnMetric_and_eq_zero {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    (f : E →ₗᵢ[𝕜] F) : IsImmediate f ↔
      (Metric.nnMetric F).IsImmediate f ∧ ∀ y : F, ‖y‖ = 0 → y = 0 := by
  constructor
  · intro h
    have hsep (y : F) (hy : ‖y‖ = 0) : y = 0 := by
      apply h y (isMOrtho_iff_nnMetric.mpr ?_)
      intro z _
      simpa only [nnMetric_apply, ← NNReal.coe_le_coe, coe_nndist, dist_zero_right, hy] using
        dist_nonneg (x := y) (y := z)
    refine ⟨?_, hsep⟩
    intro y hy
    refine ⟨inferInstance, fun x ↦ ?_⟩
    have hne : y - f x ≠ 0 := fun he ↦ hy ⟨x, (sub_eq_zero.mp he).symm⟩
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := IsMOrtho.not_iff_exists_dist_lt_norm.mp (mt (h _) hne)
    change dist (y - f x) (f z) < ‖y - f x‖ at hz
    refine ⟨x + z, ?_⟩
    change nndist y (f (x + z)) < nndist y (f x)
    rw [← NNReal.coe_lt_coe, coe_nndist, coe_nndist, dist_eq_norm, dist_eq_norm, map_add]
    simpa only [dist_eq_norm, sub_add_eq_sub_sub] using hz
  · rintro ⟨h, hsep⟩ y horth
    by_contra hne
    apply IsMOrtho.not_iff_exists_dist_lt_norm.mpr _ horth
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      refine ⟨f x, ⟨x, rfl⟩, ?_⟩
      rw [dist_self]
      exact lt_of_le_of_ne (norm_nonneg _) (fun he ↦ hne (hsep _ he.symm))
    · obtain ⟨x, hx⟩ := (h y hy).2 0
      refine ⟨f x, ⟨x, rfl⟩, ?_⟩
      simpa only [nnMetric_apply, map_zero, ← NNReal.coe_lt_coe, coe_nndist, dist_zero_right]
        using hx

/-- For a linear isometry into a normed space, immediacy of its range is equivalent
to the strict approximation criterion for the underlying pseudometric. -/
theorem isImmediate_iff_nnMetric {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    (f : E →ₗᵢ[𝕜] F) : IsImmediate f ↔ (Metric.nnMetric F).IsImmediate f :=
  (isImmediate_iff_nnMetric_and_eq_zero f).trans (and_iff_left fun _ ↦ norm_eq_zero.mp)

def IsImmediateExtension {𝕜 : Type*} [NormedField 𝕜]
    {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (D : Submodule 𝕜 E) : Prop :=
    ∀ v : E, (v ⟂ₘ D) → v = 0

/--
`MaximallyComplete 𝕜 E` expresses a maximal completeness (a spherical-completeness–style)
property of the ultrametric normed `𝕜`-vector space `E`.

It requires that for every ultrametric normed `𝕜`-vector space `F` and every linear isometry
`f : E →ₗᵢ[𝕜] F`, if `f` is *immediate* (in the sense of `IsImmediate f`),
then `f` is surjective.

In other words, `E` admits no proper immediate extensions: any immediate
linear isometry out of `E` must hit all of its codomain.
-/
def MaximallyComplete (𝕜 : Type*) [NormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] : Prop :=
∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
(f : E →ₗᵢ[𝕜] F), IsImmediate f → Function.Surjective f

namespace IsImmediate

/-- Extend a seminorm-preserving linear map across an injective immediate embedding. -/
theorem exists_linearIsometry_comp_eq_of_nnMetric {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    {H : Type*} [SeminormedAddCommGroup H] [NormedSpace 𝕜 H] [IsUltrametricDist H]
    [SphericallyCompleteSpace H] (f : E →ₗᵢ[𝕜] F) (hinj : Function.Injective f)
    (hf : (nnMetric F).IsImmediate f) (g : E →ₗᵢ[𝕜] H) :
    ∃ h : F →ₗᵢ[𝕜] H, h.comp f = g := by
  obtain ⟨T, hT, hiso⟩ := hf.exists_linearMap_comp_eq
    (nnMetric F) (nnMetric H) (fun c {u x} h ↦ by
      simp only [nnMetric_apply, nndist_zero_right, nnNorm_smul] at h ⊢
      exact mul_le_mul_of_nonneg_left h zero_le) f.toLinearMap hinj g.toLinearMap
    (fun x ↦ by simp only [nnMetric_apply, nndist_zero_right, LinearIsometry.coe_toLinearMap,
      LinearIsometry.nnNorm_map])
  refine ⟨⟨T, fun x ↦ ?_⟩, LinearIsometry.ext fun x ↦ LinearMap.congr_fun hT x⟩
  simpa only [map_zero, nnMetric_apply, nndist_zero_right, coe_nnNorm] using
    congrArg NNReal.toReal (hiso x 0)

/-- Every linear isometry into a spherically complete target extends along an immediate
linear isometry. The arbitrary-value extension theorem also applies to seminormed targets. -/
theorem exists_linearIsometry_comp_eq {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    {H : Type*} [SeminormedAddCommGroup H] [NormedSpace 𝕜 H] [IsUltrametricDist H]
    [SphericallyCompleteSpace H] (f : E →ₗᵢ[𝕜] F) (hf : IsImmediate f) (g : E →ₗᵢ[𝕜] H) :
    ∃ h : F →ₗᵢ[𝕜] H, h.comp f = g :=
  exists_linearIsometry_comp_eq_of_nnMetric f f.injective ((isImmediate_iff_nnMetric f).mp hf) g

/-- Metric orthogonality of `x : q` to the range of the inclusion `p ≤ q`, computed inside `q`,
is the same as metric orthogonality of `(x : E₀)` to `p` in the ambient space. This is the key
transport principle for immediate extensions built from submodule inclusions. -/
lemma isMOrtho_range_inclusion_iff {𝕜 : Type*} [NormedField 𝕜] {E₀ : Type*}
    [SeminormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    {p q : Submodule 𝕜 E₀} (h : p ≤ q) (x : q) :
    (IsMOrtho x (LinearMap.range (Submodule.inclusion h))) ↔
      Metric.infDist (x : E₀) p = ‖(x : E₀)‖ := by
  rw [IsMOrtho, show (p : Set E₀) =
      ((↑) : q → E₀) '' (LinearMap.range (Submodule.inclusion h)) from by
    rw [← Submodule.coe_subtype, ← Submodule.map_coe, Submodule.range_inclusion,
      Submodule.map_comap_subtype, inf_of_le_right h],
    Metric.infDist_image (Φ := ((↑) : q → E₀)) isometry_subtype_coe (x := x)]
  exact Iff.rfl

/--
`immediateExtensionSubmodules E E₀ f` is the set of `𝕜`-submodules `M ≤ E₀`
such that:

* the range of the linear isometry `f : E →ₗᵢ[𝕜] E₀` is contained in `M`, and
* the inclusion `Submodule.inclusion : (LinearMap.range f) →ₗ[𝕜] M` is an *immediate* extension,
  i.e. every `v : M` metrically orthogonal to its range is `0` (as in `IsImmediate`).

This is the collection of candidate intermediate spaces used to build a maximal immediate
extension inside a fixed ambient space `E₀`; taking `E₀` spherically complete yields the spherical
completion of `E`.
-/
def immediateExtensionSubmodules {𝕜 : Type*} [NormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    Set (Submodule 𝕜 E₀) := {M : Submodule 𝕜 E₀ | ∃ hc : f.range ≤ M,
      ∀ v : M, (v ⟂ₘ LinearMap.range (Submodule.inclusion hc)) → v = 0 }

/-- Membership criterion for `immediateExtensionSubmodules`, expressed entirely in the ambient
space `E₀`: `M` belongs to the set iff it contains `f.range` and every `v ∈ M` that is metrically
orthogonal to `f.range` (measured in `E₀`) is `0`. This transports the immediacy condition — stated
inside `M` via `Submodule.inclusion` — down to the ambient norm, which is what makes the Zorn
argument in `exists_maximal_immediateExtensionSubmodule` manageable. -/
lemma mem_immediateExtensionSubmodules_iff
    {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    {f : E →ₗᵢ[𝕜] E₀} {M : Submodule 𝕜 E₀} :
    M ∈ immediateExtensionSubmodules E E₀ f ↔
      ∃ _ : f.range ≤ M,
        ∀ v : M, Metric.infDist (v : E₀) f.range = ‖(v : E₀)‖ → v = 0 := by
  simp only [immediateExtensionSubmodules, Set.mem_ofPred_eq]
  refine exists_congr fun hc ↦ forall_congr' fun v ↦ ?_
  rw [isMOrtho_range_inclusion_iff]

/-- The normed-space candidates are exactly the immediate submodules of the bundled distance. -/
theorem immediateExtensionSubmodules_eq_nnMetric {𝕜 : Type*} [NormedField 𝕜]
    {E E₀ : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀] (f : E →ₗᵢ[𝕜] E₀) :
    immediateExtensionSubmodules E E₀ f = {M | (nnMetric E₀).IsImmediateSubmodule f.range M} := by
  ext M
  change (∃ hc : f.range ≤ M, _) ↔ (nnMetric E₀).IsImmediateSubmodule f.range M
  rw [PseudoMetric.isImmediateSubmodule_iff]
  refine exists_congr fun hc ↦ ?_
  let i : f.range →ₗᵢ[𝕜] M := { Submodule.inclusion hc with norm_map' := fun _ ↦ rfl }
  exact isImmediate_iff_nnMetric i

/--
The set of candidate intermediate spaces for immediate extensions is nonempty.
Specifically, the range of `f` itself is always a candidate, with the identity map
serving as an immediate extension.
-/
lemma immediateExtensionSubmodules_nonempty
    {𝕜 : Type*} [NormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    (f : E →ₗᵢ[𝕜] E₀)
    : (immediateExtensionSubmodules E E₀ f).Nonempty := by
  refine ⟨f.range, mem_immediateExtensionSubmodules_iff.2
    ⟨le_rfl, fun v hv ↦ ?_⟩⟩
  rw [Metric.infDist_zero_of_mem v.2] at hv
  exact Submodule.coe_eq_zero.mp (norm_eq_zero.mp hv.symm)

/--
Existence of a maximal *immediate* intermediate space inside a fixed ambient space.

Concretely, for a linear isometry `f : E →ₗᵢ[𝕜] E₀`, we consider the set
`immediateExtensionSubmodules E E₀ f` of submodules `M ≤ E₀` that contain the range of `f` and for
which the induced inclusion `LinearMap.range f →ₗᵢ[𝕜] M` is an immediate extension.

Ordered by inclusion, this set is closed under unions of chains — the union of a chain of immediate
extensions is again immediate, since any vector orthogonal to the union is orthogonal to some member
of the chain. **Zorn's lemma** then produces a maximal element. No hypothesis on `E₀` beyond the
ultrametric structure is needed here; when `E₀` is additionally spherically complete, the maximal
submodule is itself spherically complete
(`instSphericallyCompleteSpaceOfMaximalImmediateExtensionSubmodule`) and underlies the spherical
completion of `E`.
-/
theorem exists_maximal_immediateExtensionSubmodule
    (𝕜 : Type*) [NormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    ∃ m, Maximal (fun x ↦ x ∈ immediateExtensionSubmodules E E₀ f) m := by
  simpa only [immediateExtensionSubmodules_eq_nnMetric, Set.mem_ofPred_eq] using
    (nnMetric E₀).exists_maximal_isImmediateSubmodule f.range

/--
The maximal immediate-extension subspace of a spherically complete ambient space is itself
spherically complete.

For a point outside the maximal immediate submodule `K`, adjoining it yields a larger
submodule which contains a nonzero vector orthogonal to the image. Rescaling that vector gives
a nearest point in `K`. The nearest-point characterization of spherically complete subsets
then applies to `K` in the spherically complete ambient space.
-/
instance instSphericallyCompleteSpaceOfMaximalImmediateExtensionSubmodule
    {𝕜 : Type*} [NormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [iud : IsUltrametricDist E₀]
    [hsc : SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    SphericallyCompleteSpace
      (↥(exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose) := by
  let M := (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose
  have h : Maximal (fun x ↦ x ∈ immediateExtensionSubmodules E E₀ f) M :=
    (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose_spec
  rw [immediateExtensionSubmodules_eq_nnMetric] at h
  exact (sphericallyCompleteSpace_iff M).mpr <|
    (nnMetric E₀).isSphericallyComplete_of_maximal_isImmediateSubmodule h

/--
`maximalImmediateExtensionEmbedding f` is the canonical linear isometry embedding `E` into a
maximal immediate-extension subspace of the spherically complete ambient space `E₀`.

Given `f : E →ₗᵢ[𝕜] E₀` with `E₀` spherically complete,
`exists_maximal_immediateExtensionSubmodule` provides a maximal element `M` of
`immediateExtensionSubmodules E E₀ f`; in particular `M` contains `range f`. This definition sends
`x : E` to `f x`, viewed as an element of `M`. Since `f` is an isometry and the inclusion
`M ↪ E₀` preserves norms, the result is again an isometric embedding. Together with the spherical
completeness of `M` (`instSphericallyCompleteSpaceOfMaximalImmediateExtensionSubmodule`), this is
the isometry realising `M` as a spherical completion of `E`.
-/
noncomputable def maximalImmediateExtensionEmbedding {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    E →ₗᵢ[𝕜] ↥(exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose := {
    toFun x := ⟨f x, (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f
      ).choose_spec.1.out.choose <| LinearMap.mem_range_self _ _⟩
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    norm_map' := f.norm_map
  }

end IsImmediate
end SphericallyCompleteSpace
