module

public import SphereSixComplex.Geometry.PaperAssembly
public import SphereSixComplex.Geometry.FourPieceStarGluing
public import SphereSixComplex.Topology.EstablishedMayerVietoris
public import SphereSixComplex.Topology.SectionSevenCoherentRealizationReduction

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
  /-- Finiteness of the set of pieces. -/
  finiteIndex : Finite star.glueData.J
  /-- The diagram has at least one piece. -/
  nonemptyIndex : Nonempty star.glueData.J
  /-- Every piece is nonempty. -/
  nonemptyPiece : ∀ i, Nonempty (star.glueData.U i)
  /-- Every piece is connected. -/
  connectedPiece : ∀ i, ConnectedSpace (star.glueData.U i)
  /-- Every piece carries its specified complex charts. -/
  complexCharts : ∀ i, ChartedSpace ComplexModel (star.glueData.U i)
  /-- Every piece is second countable. -/
  pieceSecondCountable : ∀ i, SecondCountableTopology (star.glueData.U i)
  /-- The glued topology is Hausdorff. -/
  gluedT2 : T2Space (GluedSpace star.glueData)
  /-- The completed glued space is compact. -/
  gluedCompact : CompactSpace (GluedSpace star.glueData)
  /-- The complex charts agree on every gluing overlap. -/
  complexCompatible :
    letI := finiteIndex
    letI := nonemptyIndex
    letI := nonemptyPiece
    letI := connectedPiece
    letI := complexCharts
    GluingAtlasCompatible (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) star.glueData
  /-- The underlying real atlas is a smooth six-manifold atlas. -/
  realManifold :
    letI := finiteIndex
    letI := nonemptyIndex
    letI := nonemptyPiece
    letI := connectedPiece
    letI := complexCharts
    @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      (modelWithCornersSelf ℝ RealModel) ∞ (GluedSpace star.glueData) inferInstance
      (underlyingRealChartedSpace (gluedChartedSpace star.glueData))
  /-- The intersection graph connects all pieces. -/
  intersectionConnected : GluingIntersectionGraphConnected star.glueData
  /-- The selected filling twists give the required van Kampen presentation. -/
  vanKampen : Topology.HasVanKampenData (GluedSpace star.glueData) 0 1 (-1)
  /-- The paper-specific comparison from the verified finite Section 7 model to chains small with
  respect to the canonical open images of these four pieces. -/
  homologyComparison : SectionSevenFourPieceSmallChainComparison
    (GluedSpace star.glueData) star.openCover

namespace PaperGluingData

variable (A : PaperGluingData)

/-- The canonical gluing diagram built from the central piece and three collars. -/
public abbrev D : TopCat.GlueData := A.star.glueData

/-- Countability of the four-piece gluing follows from countability of its pieces. -/
public theorem gluedSecondCountable : SecondCountableTopology (GluedSpace A.D) := by
  let _ := A.finiteIndex
  let _ (i : A.D.J) := A.pieceSecondCountable i
  exact secondCountableTopology_gluedSpace A.D

/-- The standard open-cover Mayer--Vietoris theorem applies to all three stages of the paper's
four-piece cover. -/
public theorem mayerVietorisExactness : FourPieceMayerVietorisExactness A.star.openCover :=
  establishedFourPieceMayerVietorisExactness A.star.openCover

/-- The paper-specific small-chain comparison for the actual four-piece cover, together with
general open-cover subdivision and the established homology of the standard sphere, gives the
assembly layer's homology contract. -/
public theorem integralHomology : HasIntegralHomologyOfSixSphere (GluedSpace A.D) :=
  A.homologyComparison.hasIntegralHomologyOfSixSphere

/-- Exact assembly of packaged gluing data into the completed-threefold contract. -/
@[expose] public noncomputable def toCompletedPaperThreefold : CompletedPaperThreefold := by
  letI := A.finiteIndex
  letI := A.nonemptyIndex
  letI := A.nonemptyPiece
  letI := A.connectedPiece
  letI := A.complexCharts
  letI := A.gluedT2
  letI := A.gluedSecondCountable
  exact completedPaperThreefoldOfGluing A.D A.complexCompatible A.realManifold A.gluedCompact
    A.intersectionConnected A.vanKampen A.integralHomology

end PaperGluingData

/-- Constructing the exact packaged gluing data suffices for the completed paper threefold. -/
public theorem exists_completedPaperThreefold_of_paperGluingData
    (h : Nonempty PaperGluingData) : Nonempty CompletedPaperThreefold :=
  h.map PaperGluingData.toCompletedPaperThreefold

end

end SphereSixComplex
