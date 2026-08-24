module

public import SphereSixComplex.Geometry.PaperAssembly
public import SphereSixComplex.Topology.EstablishedMayerVietoris
public import SphereSixComplex.Topology.EstablishedSphereHomology

/-!
# Exact gluing data for the completed paper threefold

This module packages every geometric and topological input consumed by `completedPaperThreefoldOfGluing`.
It is the concrete construction target upstream of the final existence theorem.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- All data required to assemble the paper's four pieces into a compact complex threefold with
the asserted fundamental group and integral homology. -/
public structure PaperGluingData where
  /-- The finite gluing diagram. -/
  D : TopCat.GlueData
  /-- Finiteness of the set of pieces. -/
  finiteIndex : Finite D.J
  /-- The diagram has at least one piece. -/
  nonemptyIndex : Nonempty D.J
  /-- Every piece is nonempty. -/
  nonemptyPiece : ∀ i, Nonempty (D.U i)
  /-- Every piece is connected. -/
  connectedPiece : ∀ i, ConnectedSpace (D.U i)
  /-- Every piece carries its specified complex charts. -/
  complexCharts : ∀ i, ChartedSpace ComplexModel (D.U i)
  /-- The glued topology is Hausdorff. -/
  gluedT2 : T2Space (GluedSpace D)
  /-- The glued topology is second countable. -/
  gluedSecondCountable : SecondCountableTopology (GluedSpace D)
  /-- The completed glued space is compact. -/
  gluedCompact : CompactSpace (GluedSpace D)
  /-- The complex charts agree on every gluing overlap. -/
  complexCompatible :
    letI := finiteIndex
    letI := nonemptyIndex
    letI := nonemptyPiece
    letI := connectedPiece
    letI := complexCharts
    GluingAtlasCompatible (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) D
  /-- The underlying real atlas is a smooth six-manifold atlas. -/
  realManifold :
    letI := finiteIndex
    letI := nonemptyIndex
    letI := nonemptyPiece
    letI := connectedPiece
    letI := complexCharts
    @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      (modelWithCornersSelf ℝ RealModel) ∞ (GluedSpace D) inferInstance
      (underlyingRealChartedSpace (gluedChartedSpace D))
  /-- The intersection graph connects all pieces. -/
  intersectionConnected : GluingIntersectionGraphConnected D
  /-- The selected filling twists give the required van Kampen presentation. -/
  vanKampen : Topology.HasVanKampenData (GluedSpace D) 0 1 (-1)
  /-- The four-piece cover used for the integral homology calculation. -/
  cover : FourPieceOpenCover (GluedSpace D)
  /-- One coherent comparison from the verified finite Section 7 model to the glued space's
  integral singular chains. -/
  homologyRealization : SectionSevenLerayCoherentRealization (GluedSpace D)

namespace PaperGluingData

variable (A : PaperGluingData)

/-- The standard open-cover Mayer--Vietoris theorem applies to all three stages of the paper's
four-piece cover. -/
public theorem mayerVietorisExactness : FourPieceMayerVietorisExactness A.cover :=
  establishedFourPieceMayerVietorisExactness A.cover

/-- The coherent Section 7 realization, compared with the established singular homology of the
standard sphere, gives the assembly layer's homology contract. -/
public theorem integralHomology : HasIntegralHomologyOfSixSphere (GluedSpace A.D) :=
  A.homologyRealization.hasIntegralHomologyOfSixSphere_established

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
