module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Gluing

/-!
# Gluing manifold atlases

This file builds a charted space on the topological space obtained from mathlib's `TopCat.GlueData`.
Each piece maps to the glued space by an open embedding. The remaining geometric obligation is the
pairwise compatibility of the transported piece charts.
-/

@[expose] public section

noncomputable section

open CategoryTheory Set OpenPartialHomeomorph Manifold Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type w} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

/-- The underlying type of the topological space obtained from a family of gluing data. -/
public abbrev GluedSpace (D : TopCat.GlueData.{w}) : Type w := D.toGlueData.glued

/-- The canonical open partial homeomorphism from a piece into the glued space. -/
public noncomputable def pieceOpenPartialHomeomorph (D : TopCat.GlueData.{w}) (i : D.J)
    [Nonempty (D.U i)] : OpenPartialHomeomorph (D.U i) (GluedSpace D) :=
  (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)

/-- Each piece is an open subspace of the glued space. -/
public theorem piece_isOpenEmbedding (D : TopCat.GlueData.{w}) (i : D.J) :
    IsOpenEmbedding (D.toGlueData.ι i) :=
  D.ι_isOpenEmbedding i

variable (D : TopCat.GlueData.{w})

/-- Choose a piece containing a given point of the glued space. -/
public noncomputable def gluedPieceIndex (x : GluedSpace D) : D.J :=
  (D.ι_jointly_surjective x).choose

/-- Choose a preimage of a glued point in its selected piece. -/
public noncomputable def gluedPiecePoint (x : GluedSpace D) : D.U (gluedPieceIndex D x) :=
  (D.ι_jointly_surjective x).choose_spec.choose

public theorem gluedPiecePoint_maps (x : GluedSpace D) :
    D.toGlueData.ι (gluedPieceIndex D x) (gluedPiecePoint D x) = x :=
  (D.ι_jointly_surjective x).choose_spec.choose_spec

/-- The atlas obtained by transporting every piece atlas through its canonical open embedding. -/
@[instance_reducible]
public noncomputable def gluedChartedSpace [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] : ChartedSpace H (GluedSpace D) where
  atlas := ⋃ i, (fun c ↦ (pieceOpenPartialHomeomorph D i).symm.trans c) '' atlas H (D.U i)
  chartAt x :=
    (pieceOpenPartialHomeomorph D (gluedPieceIndex D x)).symm.trans
      (chartAt H (gluedPiecePoint D x))
  mem_chart_source x := by
    let i := gluedPieceIndex D x
    let y := gluedPiecePoint D x
    have hxy : D.toGlueData.ι i y = x := gluedPiecePoint_maps D x
    change x ∈ (pieceOpenPartialHomeomorph D i).target ∩
      (pieceOpenPartialHomeomorph D i).symm ⁻¹' (chartAt H y).source
    constructor
    · unfold pieceOpenPartialHomeomorph
      rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
      exact ⟨y, hxy⟩
    · change (pieceOpenPartialHomeomorph D i).symm x ∈ (chartAt H y).source
      have hinv : (pieceOpenPartialHomeomorph D i).symm x = y := by
        rw [← hxy]
        exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _
      rw [hinv]
      exact mem_chart_source H _
  chart_mem_atlas x := by
    refine mem_iUnion.mpr ⟨gluedPieceIndex D x, ?_⟩
    exact ⟨chartAt H (gluedPiecePoint D x), chart_mem_atlas H _, rfl⟩

/-- Exact compatibility condition needed to make the transported piece atlas a manifold atlas. -/
public def GluingAtlasCompatible [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] : Prop :=
  ∀ (i j : D.J) (c : OpenPartialHomeomorph (D.U i) H)
    (c' : OpenPartialHomeomorph (D.U j) H), c ∈ atlas H (D.U i) →
      c' ∈ atlas H (D.U j) →
      ((pieceOpenPartialHomeomorph D i).symm.trans c).symm.trans
          ((pieceOpenPartialHomeomorph D j).symm.trans c') ∈ contDiffGroupoid n I

/-- Compatible transported piece charts make the glued space a manifold. -/
public theorem isManifold_gluedChartedSpace [∀ i, Nonempty (D.U i)]
    [∀ i, ChartedSpace H (D.U i)] (hcompat : GluingAtlasCompatible (I := I) (n := n) D) :
    @IsManifold 𝕜 inferInstance E inferInstance inferInstance H inferInstance I n (GluedSpace D)
      inferInstance (gluedChartedSpace D) := by
  let cG : ChartedSpace H (GluedSpace D) := gluedChartedSpace D
  let hG : @HasGroupoid H inferInstance (GluedSpace D) inferInstance cG
      (contDiffGroupoid n I) := by
    refine ⟨fun {e e'} he he' ↦ ?_⟩
    change e ∈ ⋃ i, _ at he
    change e' ∈ ⋃ i, _ at he'
    obtain ⟨i, c, hc, rfl⟩ := mem_iUnion.mp he
    obtain ⟨j, c', hc', rfl⟩ := mem_iUnion.mp he'
    exact hcompat i j c c' hc hc'
  exact @IsManifold.mk' 𝕜 inferInstance E inferInstance inferInstance H inferInstance I n
    (GluedSpace D) inferInstance cG hG

end SphereSixComplex
