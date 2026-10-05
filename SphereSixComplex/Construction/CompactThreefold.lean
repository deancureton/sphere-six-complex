module

public import SphereSixComplex.Construction.BiholomorphicGluing
public import SphereSixComplex.Prerequisites.Geometry.Gluing.CompactStar
public import SphereSixComplex.Cusp.FillingConnected
public import SphereSixComplex.Construction.GluingNonempty
public import SphereSixComplex.Construction.Compactness
public import SphereSixComplex.Construction.Hausdorff
public import SphereSixComplex.Construction.PieceTopology

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
