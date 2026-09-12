module

public import SphereSixComplex.Paper.Geometry.PaperBiholomorphicStar
public import SphereSixComplex.Prerequisites.Geometry.CompactComplexStar
public import SphereSixComplex.Paper.Geometry.PaperLocalCuspFillingConnected
public import SphereSixComplex.Paper.Geometry.PaperOpenEmbeddingStarNonempty
public import SphereSixComplex.Paper.Geometry.PaperStarCompactness
public import SphereSixComplex.Paper.Geometry.PaperStarHausdorff
public import SphereSixComplex.Paper.Geometry.PaperStarPieceTopology

/-!
# The compact complex star of the analytic family

The geometric gluing is constructed before its fundamental group and homology are computed.
-/

namespace SphereSixComplex.Geometry

noncomputable section

namespace AnalyticData

variable (P : AnalyticData)

/-- The actual analytic four-piece star with its compact complex gluing geometry. -/
@[expose] public noncomputable def compactComplexStar : CompactComplexStar where
  star := P.openEmbeddingStarData.toFourPieceStarGluingData
  connectedPiece := P.starPiece_connected
  nonemptyCentralCollar := P.fourPieceStarGluingData_nonemptyCentralCollar
  biholomorphicStar := P.biholomorphicFourPieceStarData
  pieceSecondCountable := P.starPiece_secondCountable
  gluedT2 := P.t2Space_starGlued
  gluedCompact := P.compactSpace_starGlued

end AnalyticData

end

end SphereSixComplex.Geometry
