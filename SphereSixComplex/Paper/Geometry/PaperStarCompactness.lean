module

public import SphereSixComplex.Paper.Geometry.CuspFillingRadialCompactness
public import SphereSixComplex.Paper.Geometry.PaperCentralEndCover
public import SphereSixComplex.Paper.Geometry.PaperStarHausdorff

/-!
# Compactness of the concrete four-piece star

This module assembles the proved compact-cover machinery from the two remaining geometric
end-control obligations.  Neither obligation is assumed here: the cusp input is the explicit
two-chart representative theorem for the actual polarized `A₂` action, and the central input is
the thresholded coverage theorem for the three selected collar maps.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex.Geometry

open CuspFillingRadialCompactness

noncomputable section

namespace AnalyticData

variable (P : AnalyticData)

/-- The two exact end-control obligations provide compact-cover data for the concrete star. -/
public noncomputable def compactCoverData_of_endControl
    (hcusp : ActualA2TwoChartRadialSublevelRepresentatives P.starCuspWitness)
    (hcentral : P.ThresholdedCentralEndCoverData) :
    P.openEmbeddingStarData.CompactCoverData :=
  hcentral.toOpenEmbeddingStarCompactCoverData
    (P.actualLocalCuspRadialCoreCompactness_of_twoChartRepresentatives hcusp)

/-- Compact-cover data for the actual paper star. -/
@[expose] public noncomputable def compactCoverData :
    P.openEmbeddingStarData.CompactCoverData :=
  P.compactCoverData_of_endControl
    (actualA2TwoChartRadialSublevelRepresentatives P.starCuspWitness)
    P.thresholdedCentralEndCoverData


/-- The completed four-piece star is compact. -/
public theorem compactSpace_starGlued :
    CompactSpace
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) :=
  P.compactCoverData.compactSpace



end AnalyticData

end

end SphereSixComplex.Geometry
