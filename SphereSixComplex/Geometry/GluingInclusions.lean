/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Geometry.GluingCompatibility
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Regularity of the canonical gluing inclusions

The charted space on a topological glue is obtained by transporting the charts on each piece
along its canonical open embedding. This makes every canonical piece inclusion differentiable
for the resulting manifold structure. After specialization to complex manifolds, the `C¹`
result says that the inclusions are holomorphic.

The argument is adapted from Paul Lezeau's independent formalisation in
`ComplexStructures.S6.ConstructionStages.FinalGluingConstruction`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Set Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type w} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

/-- A transported piece chart agrees with the original chart after the canonical inclusion. -/
public theorem transportedPieceChart_inclusion_apply
    (D : TopCat.GlueData.{w}) [∀ j, Nonempty (D.U j)] (i : D.J)
    (c : OpenPartialHomeomorph (D.U i) H) (x : D.U i) :
    transportedPieceChart D i c (D.toGlueData.ι i x) = c x := by
  simp only [transportedPieceChart, pieceOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans_apply]
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

/-- Each canonical inclusion is `C^n` for the transported atlas on the glued space. -/
public theorem pieceInclusion_contMDiff
    (D : TopCat.GlueData.{w}) [Nonempty H] [∀ j, Nonempty (D.U j)]
    [∀ j, ChartedSpace H (D.U j)]
    (hcompat : GluingAtlasCompatible (I := I) (n := n) D) (i : D.J)
    [IsManifold I n (D.U i)] :
    letI := gluedChartedSpace (H := H) D
    ContMDiff I I n (D.toGlueData.ι i) := by
  letI := gluedChartedSpace (H := H) D
  letI : IsManifold I n (GluedSpace D) :=
    isManifold_gluedChartedSpace D hcompat
  intro x
  let e := chartAt H x
  let e' := transportedPieceChart D i e
  have he' : e' ∈ atlas H (GluedSpace D) := by
    apply Set.mem_iUnion.mpr
    exact ⟨i, e, chart_mem_atlas H x, rfl⟩
  have he'max : e' ∈ IsManifold.maximalAtlas I n (GluedSpace D) :=
    IsManifold.subset_maximalAtlas he'
  have hx : D.toGlueData.ι i x ∈ e'.source := by
    change D.toGlueData.ι i x ∈ (transportedPieceChart D i e).source
    rw [(transportedPieceChart_eqOnSource_lift D i e).source_eq,
      OpenPartialHomeomorph.lift_openEmbedding_source]
    exact ⟨x, mem_chart_source H x, rfl⟩
  rw [← contMDiffWithinAt_univ,
    contMDiffWithinAt_iff_target_of_mem_maximalAtlas he'max hx,
    continuousWithinAt_univ, contMDiffWithinAt_univ]
  refine ⟨(piece_isOpenEmbedding D i).continuous.continuousAt, ?_⟩
  have hfun :
      (e'.extend I) ∘ D.toGlueData.ι i = extChartAt I x := by
    funext y
    simp only [e', e, OpenPartialHomeomorph.extend_coe, Function.comp_apply, extChartAt]
    rw [transportedPieceChart_inclusion_apply]
  rw [hfun]
  exact contMDiffAt_extChartAt

/-- Cross-piece compatibility makes every canonical inclusion `C^n`. -/
public theorem pieceInclusion_contMDiff_of_crossPiece
    (D : TopCat.GlueData.{w}) [Nonempty H] [∀ j, Nonempty (D.U j)]
    [∀ j, ChartedSpace H (D.U j)] [∀ j, IsManifold I n (D.U j)]
    (hcross : CrossPieceGluingCompatible D (contDiffGroupoid n I)) (i : D.J) :
    letI := gluedChartedSpace (H := H) D
    ContMDiff I I n (D.toGlueData.ι i) :=
  pieceInclusion_contMDiff D (gluingAtlasCompatible_of_crossPiece D hcross) i

/-- Every canonical inclusion is manifold-differentiable under `C¹` cross-piece compatibility.
For complex model spaces, this is the corresponding holomorphicity statement. -/
public theorem pieceInclusion_mdifferentiable_of_crossPiece
    (D : TopCat.GlueData.{w}) [Nonempty H] [∀ j, Nonempty (D.U j)]
    [∀ j, ChartedSpace H (D.U j)] [∀ j, IsManifold I 1 (D.U j)]
    (hcross : CrossPieceGluingCompatible D (contDiffGroupoid 1 I)) (i : D.J) :
    letI := gluedChartedSpace (H := H) D
    MDifferentiable I I (D.toGlueData.ι i) := by
  letI := gluedChartedSpace (H := H) D
  exact (pieceInclusion_contMDiff_of_crossPiece D hcross i).mdifferentiable one_ne_zero

end SphereSixComplex
