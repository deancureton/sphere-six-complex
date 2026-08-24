module

public import SphereSixComplex.Geometry.PaperBiholomorphicStar
public import SphereSixComplex.Geometry.PaperGluingData
public import SphereSixComplex.Geometry.PaperLocalCuspFillingConnected
public import SphereSixComplex.Geometry.PaperOpenEmbeddingStarNonempty
public import SphereSixComplex.Geometry.PaperStarCompactness
public import SphereSixComplex.Geometry.PaperStarHausdorff
public import SphereSixComplex.Geometry.PaperStarPieceTopology

/-!
# Instantiating the paper gluing package

All geometric and point-set-topological fields of `PaperGluingData` are supplied by the actual
analytic four-piece star.  The constructor below leaves only the two global topology calculations
as explicit inputs.
-/

namespace SphereSixComplex.Geometry

noncomputable section

namespace PaperAnalyticData

variable (P : PaperAnalyticData)

/-- Assemble the actual paper gluing once its van Kampen and Section 7 comparison calculations
have been supplied. -/
@[expose] public noncomputable def toPaperGluingData
    (vanKampen : Topology.HasVanKampenData
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) 0 1 (-1))
    (homologyComparison : SectionSevenFourPieceSmallChainComparison
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData)
      P.openEmbeddingStarData.toFourPieceStarGluingData.openCover) :
    SphereSixComplex.PaperGluingData where
  star := P.openEmbeddingStarData.toFourPieceStarGluingData
  connectedPiece := P.starPiece_connected
  nonemptyCentralCollar := P.fourPieceStarGluingData_nonemptyCentralCollar
  biholomorphicStar := P.biholomorphicFourPieceStarData
  pieceSecondCountable := P.starPiece_secondCountable
  gluedT2 := P.starGluedT2
  gluedCompact := P.starGluedCompact
  vanKampen := vanKampen
  homologyComparison := homologyComparison

end PaperAnalyticData

end

end SphereSixComplex.Geometry
