/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Geometry.Gluing
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Cross-piece compatibility for gluing atlases

The compatibility predicate in `Gluing` quantifies over every pair of pieces. For two charts
transported from the same piece, however, their transition is equivalent to the original
transition on that piece. Its manifold structure therefore supplies compatibility automatically.

Consequently, a paper gluing only has to verify transitions between distinct pieces. This file
packages that smaller obligation and proves that it implies the existing
`GluingAtlasCompatible` contract. The reduction is adapted from Paul Lezeau's independent
formalisation in `ComplexStructures.Foundation.ComplexManifoldGluing`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Set Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

universe u v w

variable {H : Type w} [TopologicalSpace H]

/-- A piece chart transported to the glued space along its canonical open embedding. -/
public noncomputable def transportedPieceChart (D : TopCat.GlueData.{w})
    [∀ i, Nonempty (D.U i)] (i : D.J)
    (c : OpenPartialHomeomorph (D.U i) H) :
    OpenPartialHomeomorph (GluedSpace D) H :=
  (pieceOpenPartialHomeomorph D i).symm.trans c

/-- The upstream transported chart agrees on its source with Mathlib's lifted chart. -/
public theorem transportedPieceChart_eqOnSource_lift
    (D : TopCat.GlueData.{w}) [Nonempty H] [∀ i, Nonempty (D.U i)]
    (i : D.J) (c : OpenPartialHomeomorph (D.U i) H) :
    transportedPieceChart D i c ≈
      c.lift_openEmbedding (D.ι_isOpenEmbedding i) := by
  let p := pieceOpenPartialHomeomorph D i
  have hpSource : p.source = Set.univ := by
    simp [p, pieceOpenPartialHomeomorph]
  have hsource :
      (p.symm.trans c).source =
        (c.lift_openEmbedding (D.ι_isOpenEmbedding i)).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.lift_openEmbedding_source,
      ← p.image_source_inter_eq' c.source, hpSource, Set.univ_inter]
    rfl
  refine ⟨hsource, ?_⟩
  intro x hx
  have hxLift : x ∈ (c.lift_openEmbedding (D.ι_isOpenEmbedding i)).source := by
    rw [← hsource]
    exact hx
  have hx' : x ∈ D.toGlueData.ι i '' c.source := by
    simpa only [OpenPartialHomeomorph.lift_openEmbedding_source] using hxLift
  obtain ⟨y, hy, rfl⟩ := hx'
  have hpApply : p y = D.toGlueData.ι i y := rfl
  have hySource : y ∈ p.source := by rw [hpSource]; exact Set.mem_univ y
  have hpLeft : p.symm (D.toGlueData.ι i y) = y := by
    rw [← hpApply]
    exact p.left_inv hySource
  change c (p.symm (D.toGlueData.ι i y)) =
    c.lift_openEmbedding (D.ι_isOpenEmbedding i) (D.toGlueData.ι i y)
  rw [hpLeft, OpenPartialHomeomorph.lift_openEmbedding_apply]

/-! ## Automatic compatibility on a single piece -/

/-- Transitions between charts transported from the same piece belong to its structure
groupoid. -/
public theorem transportedPieceCharts_samePiece_compatible
    (D : TopCat.GlueData.{w}) [Nonempty H] [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] (G : StructureGroupoid H)
    (i : D.J) [HasGroupoid (D.U i) G]
    {c c' : OpenPartialHomeomorph (D.U i) H}
    (hc : c ∈ atlas H (D.U i)) (hc' : c' ∈ atlas H (D.U i)) :
    (transportedPieceChart D i c).symm.trans
        (transportedPieceChart D i c') ∈ G := by
  have heq := transportedPieceChart_eqOnSource_lift D i c
  have heq' := transportedPieceChart_eqOnSource_lift D i c'
  have htransition :
      (transportedPieceChart D i c).symm.trans
          (transportedPieceChart D i c') ≈
        (c.lift_openEmbedding (D.ι_isOpenEmbedding i)).symm.trans
          (c'.lift_openEmbedding (D.ι_isOpenEmbedding i)) :=
    OpenPartialHomeomorph.EqOnSource.trans' heq.symm' heq'
  apply G.mem_of_eqOnSource ?_ htransition
  rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
  exact G.compatible hc hc'

/-! ## The reduced cross-piece boundary -/

/-- Compatibility of transported charts from distinct pieces.

Unlike `GluingAtlasCompatible`, this predicate has no diagonal obligation. -/
public def CrossPieceGluingCompatible (D : TopCat.GlueData.{w})
    [Nonempty H] [∀ i, Nonempty (D.U i)] [∀ i, ChartedSpace H (D.U i)]
    (G : StructureGroupoid H) : Prop :=
  ∀ (i j : D.J), i ≠ j →
    ∀ (c : OpenPartialHomeomorph (D.U i) H)
      (c' : OpenPartialHomeomorph (D.U j) H),
      c ∈ atlas H (D.U i) → c' ∈ atlas H (D.U j) →
        (transportedPieceChart D i c).symm.trans
          (transportedPieceChart D j c') ∈ G

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

/-- Piece manifold structures reduce the full gluing-atlas obligation to distinct pieces. -/
public theorem gluingAtlasCompatible_of_crossPiece
    (D : TopCat.GlueData.{w}) [Nonempty H] [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] [∀ i, IsManifold I n (D.U i)]
    (hcross : CrossPieceGluingCompatible D (contDiffGroupoid n I)) :
    GluingAtlasCompatible (I := I) (n := n) D := by
  intro i j c c' hc hc'
  by_cases hij : i = j
  · subst j
    letI : HasGroupoid (D.U i) (contDiffGroupoid n I) :=
      (inferInstance : IsManifold I n (D.U i)).toHasGroupoid
    exact transportedPieceCharts_samePiece_compatible D _ i hc hc'
  · exact hcross i j hij c c' hc hc'

/-- Cross-piece compatibility therefore gives the manifold structure on the glued atlas. -/
public theorem isManifold_gluedChartedSpace_of_crossPiece
    (D : TopCat.GlueData.{w}) [Nonempty H] [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] [∀ i, IsManifold I n (D.U i)]
    (hcross : CrossPieceGluingCompatible D (contDiffGroupoid n I)) :
    @IsManifold 𝕜 inferInstance E inferInstance inferInstance H inferInstance I n
      (GluedSpace D) inferInstance (gluedChartedSpace D) :=
  isManifold_gluedChartedSpace D
    (gluingAtlasCompatible_of_crossPiece D hcross)

end SphereSixComplex
