/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Geometry.Gluing
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

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

/-! ## Piece transitions

The transition between two pieces of a gluing is the partial homeomorphism obtained by passing
through the glued space.  Cross-piece chart compatibility reduces to smoothness of those
transitions, which is where the analytic content of a gluing actually lives. -/

/-- The transition partial homeomorphism from the `i`th piece of a gluing to its `j`th piece. -/
public noncomputable def pieceTransition (D : TopCat.GlueData.{w}) [∀ i, Nonempty (D.U i)]
    (i j : D.J) : OpenPartialHomeomorph (D.U i) (D.U j) :=
  (pieceOpenPartialHomeomorph D i).trans (pieceOpenPartialHomeomorph D j).symm

/-- The transition between two pieces is defined exactly on their overlap. -/
public theorem pieceTransition_source (D : TopCat.GlueData.{w}) [∀ i, Nonempty (D.U i)]
    (i j : D.J) :
    (pieceTransition D i j).source = Set.range (D.toGlueData.f i j) := by
  unfold pieceTransition pieceOpenPartialHomeomorph
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.univ_inter]
  exact D.preimage_range j i

/-- Reversing a piece transition exchanges the two pieces. -/
public theorem pieceTransition_symm (D : TopCat.GlueData.{w}) [∀ i, Nonempty (D.U i)]
    (i j : D.J) : (pieceTransition D i j).symm = pieceTransition D j i := by
  unfold pieceTransition
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]

/-- On the overlap, the piece transition is the gluing datum's own transition map. -/
public theorem pieceTransition_apply (D : TopCat.GlueData.{w}) [∀ i, Nonempty (D.U i)]
    (i j : D.J) (y : D.toGlueData.V (i, j)) :
    pieceTransition D i j (D.toGlueData.f i j y) =
      D.toGlueData.f j i (D.toGlueData.t i j y) := by
  have hglue : D.toGlueData.ι j (D.toGlueData.f j i (D.toGlueData.t i j y)) =
      D.toGlueData.ι i (D.toGlueData.f i j y) := by
    have h := D.toGlueData.glue_condition i j
    exact congrFun (congrArg (fun g => ⇑(TopCat.Hom.hom g)) h) y
  change (pieceOpenPartialHomeomorph D j).symm
    (pieceOpenPartialHomeomorph D i (D.toGlueData.f i j y)) = _
  have h1 : pieceOpenPartialHomeomorph D i (D.toGlueData.f i j y)
      = D.toGlueData.ι i (D.toGlueData.f i j y) := rfl
  rw [h1, ← hglue]
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _

/-- The transition between charts transported from two pieces is the piece transition read in
those charts. -/
public theorem transportedPieceChart_symm_trans (D : TopCat.GlueData.{w}) [∀ i, Nonempty (D.U i)]
    (i j : D.J) (c : OpenPartialHomeomorph (D.U i) H) (c' : OpenPartialHomeomorph (D.U j) H) :
    (transportedPieceChart D i c).symm.trans (transportedPieceChart D j c') =
      (c.symm.trans (pieceTransition D i j)).trans c' := by
  unfold transportedPieceChart pieceTransition
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_assoc, OpenPartialHomeomorph.trans_assoc,
    OpenPartialHomeomorph.trans_assoc]

section ContMDiff

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I n N]

/-- A partial homeomorphism that is `C^n` in both directions carries any pair of atlas charts of
its two manifolds into the `C^n` groupoid. -/
public theorem mem_contDiffGroupoid_of_contMDiffOn {Φ : OpenPartialHomeomorph M N}
    (h : ContMDiffOn I I n Φ Φ.source) (h' : ContMDiffOn I I n Φ.symm Φ.target)
    {c : OpenPartialHomeomorph M H} {c' : OpenPartialHomeomorph N H}
    (hc : c ∈ atlas H M) (hc' : c' ∈ atlas H N) :
    (c.symm.trans Φ).trans c' ∈ contDiffGroupoid n I := by
  have hc'M : ContMDiffOn I I n c' c'.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (I := I) (n := n) hc')
  have hc'S : ContMDiffOn I I n c'.symm c'.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (I := I) (n := n) hc')
  have hΨ : Φ.trans c' ∈ IsManifold.maximalAtlas I n M := by
    rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · have hcomp : ContMDiffOn I I n (c' ∘ Φ) (Φ.trans c').source :=
        hc'M.comp (h.mono (fun x hx => hx.1)) (fun x hx => hx.2)
      simpa [OpenPartialHomeomorph.coe_trans] using hcomp
    · have hcomp : ContMDiffOn I I n (Φ.symm ∘ c'.symm) (Φ.trans c').target :=
        h'.comp (hc'S.mono (fun x hx => hx.1)) (fun x hx => hx.2)
      simpa [OpenPartialHomeomorph.coe_trans_symm] using hcomp
  have := StructureGroupoid.compatible_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := I) (n := n) hc) hΨ
  rwa [← OpenPartialHomeomorph.trans_assoc] at this

/-- Smooth piece transitions give the cross-piece chart compatibility of a gluing. -/
public theorem crossPieceGluingCompatible_of_pieceTransition_contMDiffOn
    (D : TopCat.GlueData.{w}) [Nonempty H] [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] [∀ i, IsManifold I n (D.U i)]
    (h : ∀ i j : D.J, i ≠ j →
      ContMDiffOn I I n (pieceTransition D i j) (pieceTransition D i j).source) :
    CrossPieceGluingCompatible D (contDiffGroupoid n I) := by
  intro i j hij c c' hc hc'
  rw [show (transportedPieceChart D i c).symm.trans (transportedPieceChart D j c') =
      (c.symm.trans (pieceTransition D i j)).trans c' from
    transportedPieceChart_symm_trans D i j c c']
  refine mem_contDiffGroupoid_of_contMDiffOn (h i j hij) ?_ hc hc'
  have hsymm : (pieceTransition D i j).symm = pieceTransition D j i := pieceTransition_symm D i j
  have htarget : (pieceTransition D i j).target = (pieceTransition D j i).source := by
    rw [← hsymm, OpenPartialHomeomorph.symm_source]
  rw [hsymm, htarget]
  exact h j i (Ne.symm hij)

end ContMDiff

end SphereSixComplex
