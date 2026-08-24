module

public import SphereSixComplex.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Geometry.PaperEllipticCentralEscape
public import SphereSixComplex.Geometry.PaperStarClosedRelationReduction
public import SphereSixComplex.Geometry.PaperStarPieceHausdorff

/-!
# Hausdorffness of the concrete four-piece star

The two elliptic relation components are already closed.  This module isolates the remaining
cusp properness input and turns the three proper collar pairs into the Hausdorff glued topology.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex.Geometry

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Cusp properness, together with the proved elliptic cases, closes all three collar pairs. -/
public theorem closedCollarPairData_of_cuspProper
    (hcusp : IsProperMap
      (A.openEmbeddingStarData.collarPairMap (0 : Fin 3))) :
    A.openEmbeddingStarData.ClosedCollarPairData := by
  apply A.openEmbeddingStarData.closedCollarPairData_of_isProperMap
  intro i
  fin_cases i
  · exact hcusp
  · exact A.orderThreeCollarPairMap_isProper
  · exact A.orderFourCollarPairMap_isProper

/-- Once the cusp collar pair is proper, the concrete completed star is Hausdorff. -/
public theorem gluedT2_of_cuspProper
    (hcusp : IsProperMap
      (A.openEmbeddingStarData.collarPairMap (0 : Fin 3))) :
    T2Space
      (GluedSpace A.openEmbeddingStarData.toFourPieceStarGluingData.glueData) := by
  let _ : T2Space A.openEmbeddingStarData.central := by
    change T2Space A.CentralFamily
    exact A.centralFamily_t2
  let _ (i : Fin 3) : T2Space (A.openEmbeddingStarData.filling i) := by
    change T2Space (A.starFillingType i)
    exact A.starFilling_t2 i
  exact (A.closedCollarPairData_of_cuspProper hcusp).t2Space

/-- All three concrete collar-pair images are closed. -/
public theorem closedCollarPairData :
    A.openEmbeddingStarData.ClosedCollarPairData :=
  A.closedCollarPairData_of_cuspProper A.cuspCollarPairMap_isProper

/-- The concrete completed four-piece star is Hausdorff. -/
public theorem starGluedT2 :
    T2Space
      (GluedSpace A.openEmbeddingStarData.toFourPieceStarGluingData.glueData) :=
  A.gluedT2_of_cuspProper A.cuspCollarPairMap_isProper

end PaperAnalyticData

end

end SphereSixComplex.Geometry
