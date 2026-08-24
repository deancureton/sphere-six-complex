module

public import SphereSixComplex.Geometry.PaperAssembly
public import SphereSixComplex.Geometry.FourPieceStarGluing
public import SphereSixComplex.Geometry.EstablishedBiholomorphicStarGluing
public import SphereSixComplex.Geometry.EstablishedComplexToRealManifold
public import SphereSixComplex.Topology.EstablishedMayerVietoris

/-!
# Exact gluing data for the completed paper threefold

This module packages every geometric and topological input consumed by `completedPaperThreefoldOfGluing`.
It is the concrete construction target upstream of the final existence theorem.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- Identify the central piece and three fillings with the four indices of the canonical cover. -/
@[expose] public def fourPieceStarIndex : Fin 4 → Option (Fin 3) :=
  Fin.cases none some

/-- The canonical cover of a star gluing by the open images of its four pieces. -/
@[expose] public noncomputable def FourPieceStarGluingData.openCover
    (A : FourPieceStarGluingData) : FourPieceOpenCover (GluedSpace A.glueData) where
  piece i := Set.range (A.glueData.toGlueData.ι (fourPieceStarIndex i))
  isOpen_piece i := (A.glueData.ι_isOpenEmbedding (fourPieceStarIndex i)).isOpen_range
  covers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := A.glueData.ι_jointly_surjective x
    cases i with
    | none => exact ⟨0, y, hy⟩
    | some i => exact ⟨i.succ, y, hy⟩

/-- All data required to assemble the paper's four pieces into a compact complex threefold with
the asserted fundamental group and integral homology. -/
public structure PaperGluingData where
  /-- The central family and three filling pieces, with their pairwise disjoint collar maps. -/
  star : FourPieceStarGluingData
  /-- Every piece is connected. -/
  connectedPiece : ∀ i, ConnectedSpace (star.glueData.U i)
  /-- Each of the three attaching collars is nonempty. -/
  nonemptyCentralCollar : ∀ i, Nonempty (star.centralCollar i)
  /-- The four pieces are complex manifolds and the collar maps are biholomorphic. -/
  biholomorphicStar :
    Geometry.EstablishedBiholomorphicStarGluing.BiholomorphicFourPieceStarData star
  /-- Every piece is second countable. -/
  pieceSecondCountable : ∀ i, SecondCountableTopology (star.glueData.U i)
  /-- The glued topology is Hausdorff. -/
  gluedT2 : T2Space (GluedSpace star.glueData)
  /-- The completed glued space is compact. -/
  gluedCompact : CompactSpace (GluedSpace star.glueData)
  /-- The selected filling twists give the required van Kampen presentation. -/
  vanKampen : Topology.HasVanKampenData (GluedSpace star.glueData) 0 1 (-1)
  /-- The integral Mayer--Vietoris calculation for the completed star. -/
  integralHomology : HasIntegralHomologyOfSixSphere (GluedSpace star.glueData)

namespace PaperGluingData

variable (A : PaperGluingData)

/-- The canonical gluing diagram built from the central piece and three collars. -/
public abbrev D : TopCat.GlueData := A.star.glueData

/-- The complex atlases on the central piece and three filling pieces. -/
@[instance_reducible] public def complexCharts :
    ∀ i, ChartedSpace ComplexModel (A.D.U i) :=
  A.biholomorphicStar.complexCharts

/-- Biholomorphic collar gluing makes the transported piece atlases compatible. -/
public theorem complexCompatible :
    letI := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
    letI := A.complexCharts
    GluingAtlasCompatible (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) A.D :=
  Geometry.EstablishedBiholomorphicStarGluing.establishedFourPieceBiholomorphicGluingAtlasCompatible
    A.star A.nonemptyCentralCollar A.biholomorphicStar

/-- Countability of the four-piece gluing follows from countability of its pieces. -/
public theorem gluedSecondCountable : SecondCountableTopology (GluedSpace A.D) := by
  let _ : Countable A.D.J := by
    change Countable (Option (Fin 3))
    infer_instance
  let _ (i : A.D.J) := A.pieceSecondCountable i
  exact secondCountableTopology_gluedSpace A.D

/-- The standard open-cover Mayer--Vietoris theorem applies to all three stages of the paper's
four-piece cover. -/
public theorem mayerVietorisExactness : FourPieceMayerVietorisExactness A.star.openCover :=
  establishedFourPieceMayerVietorisExactness A.star.openCover

/-- Restricting the glued complex atlas to real scalars supplies its smooth real
six-manifold atlas. -/
public theorem underlyingRealManifold :
    letI := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
    letI := A.connectedPiece
    letI := A.complexCharts
    @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      (modelWithCornersSelf ℝ RealModel) ∞ (GluedSpace A.D) inferInstance
      (underlyingRealChartedSpace (gluedChartedSpace A.D)) := by
  let _ := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
  let _ := A.connectedPiece
  let _ := A.complexCharts
  exact Geometry.EstablishedComplexToRealManifold.establishedUnderlyingRealIsManifold
    (gluedChartedSpace A.D) (isManifold_gluedChartedSpace A.D A.complexCompatible)

/-- Exact assembly of packaged gluing data into the completed-threefold contract. -/
@[expose] public noncomputable def toCompletedPaperThreefold : CompletedPaperThreefold := by
  let _ : Finite A.D.J := by
    change Finite (Option (Fin 3))
    infer_instance
  let _ : Nonempty A.D.J := by
    change Nonempty (Option (Fin 3))
    infer_instance
  let _ := A.star.nonemptyPieceOfCollars A.nonemptyCentralCollar
  let _ := A.connectedPiece
  let _ := A.complexCharts
  let _ := A.gluedT2
  let _ := A.gluedSecondCountable
  exact completedPaperThreefoldOfGluing A.D A.complexCompatible A.underlyingRealManifold A.gluedCompact
    (A.star.intersectionGraphConnected A.nonemptyCentralCollar) A.vanKampen A.integralHomology

end PaperGluingData

/-- Constructing the exact packaged gluing data suffices for the completed paper threefold. -/
public theorem exists_completedPaperThreefold_of_paperGluingData
    (h : Nonempty PaperGluingData) : Nonempty CompletedPaperThreefold :=
  h.map PaperGluingData.toCompletedPaperThreefold

end

end SphereSixComplex
