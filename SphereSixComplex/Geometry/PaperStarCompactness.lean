module

public import SphereSixComplex.Geometry.CuspFillingRadialCompactness
public import SphereSixComplex.Geometry.PaperCentralCompactCore
public import SphereSixComplex.Geometry.PaperStarHausdorff

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

namespace PaperAnalyticData

variable (P : PaperAnalyticData)

/-- The two exact end-control obligations provide compact-cover data for the concrete star. -/
public noncomputable def compactCoverData_of_endControl
    (hcusp : ActualA2TwoChartRadialSublevelRepresentatives P.starCuspWitness)
    (hcentral : P.ThresholdedCentralEndCoverData) :
    P.openEmbeddingStarData.CompactCoverData :=
  hcentral.toOpenEmbeddingStarCompactCoverData
    (P.actualLocalCuspRadialCoreCompactness_of_twoChartRepresentatives hcusp)

/-- Conditional compactness of the completed four-piece star. -/
public theorem starGluedCompact_of_endControl
    (hcusp : ActualA2TwoChartRadialSublevelRepresentatives P.starCuspWitness)
    (hcentral : P.ThresholdedCentralEndCoverData) :
    CompactSpace
      (GluedSpace P.openEmbeddingStarData.toFourPieceStarGluingData.glueData) :=
  (P.compactCoverData_of_endControl hcusp hcentral).compactSpace

/-- The two end-control obligations and the proved closed collar pairs provide the exact
topological completion data consumed downstream by the paper assembly. -/
public noncomputable def gluingCompletionData_of_endControl
    (hcusp : ActualA2TwoChartRadialSublevelRepresentatives P.starCuspWitness)
    (hcentral : P.ThresholdedCentralEndCoverData) :
    GluingCompletionData P.openEmbeddingStarData.toFourPieceStarGluingData.glueData := by
  let _ : T2Space P.openEmbeddingStarData.central := by
    change T2Space P.CentralFamily
    exact P.centralFamily_t2
  let _ (i : Fin 3) : T2Space (P.openEmbeddingStarData.filling i) := by
    change T2Space (P.starFillingType i)
    exact P.starFilling_t2 i
  exact (P.compactCoverData_of_endControl hcusp hcentral).toGluingCompletionData
    P.closedCollarPairData.relComponent_isClosed

end PaperAnalyticData

end

end SphereSixComplex.Geometry
