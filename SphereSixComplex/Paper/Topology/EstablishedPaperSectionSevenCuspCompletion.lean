module

public import SphereSixComplex.Paper.Topology.CuspFourthFiberUnit
public import SphereSixComplex.Paper.Topology.CuspCorrectedHomologyAssembly
public import SphereSixComplex.Paper.Topology.CuspCorrectedDegreeOneCoordinates
public import SphereSixComplex.Paper.Topology.CuspTranslationHomologyComparison

/-!
# Cusp completion with the corrected invariant marking

The boundary map, raw-four normalized splitting, meridian relation, and raw-five fibre
coefficient are proved from the actual marked geometry.
-/

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
namespace EstablishedSectionSevenCuspTopology

public def correctedPositiveDegreeAssembly_of_rawFive
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput)
    (hFive : A.cuspEllipticFiberCoordinate R (correctedCuspDegreeTwoSplitting R)
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) = 1) :
    A.PositiveDegreeHomologyAssembly :=
  correctedPositiveDegreeHomologyAssembly R.homologyAlignment.actualHomologyCoordinates
    (correctedCuspDegreeTwoSplitting R)
    (cuspDegreeOneUnionCoordinates_of_fullIterate R (A.cuspDegreeOneFullIterateRelation_proved R))
    (fun x ↦ congrFun (correctedCuspHomologyTwoCoordinates_of_rawFive R hFive x) 0)
    (correctedCuspDegreeTwoSplitting_boundary R)

public def correctedPositiveDegreeAssembly
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput) :
    A.PositiveDegreeHomologyAssembly :=
  correctedPositiveDegreeAssembly_of_rawFive R
    (A.cuspEllipticFiberCoordinate_rawFive R (correctedCuspDegreeTwoSplitting R))

end EstablishedSectionSevenCuspTopology

open EstablishedSectionSevenCuspTopology

/-- The actual degree-one cusp attachment difference map is bijective. -/
public theorem cuspAttachment_differenceMap_one_bijective
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput) :
    Function.Bijective (IntegralMayerVietoris.differenceMap
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage (2 : Fin 4))
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3) 1) :=
  (correctedPositiveDegreeAssembly R).toSectionSevenMayerVietorisHomologyAssembly.finalDifferenceOne_bijective

/-- The actual degree-two cusp attachment difference map is bijective. -/
public theorem cuspAttachment_differenceMap_two_bijective
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput) :
    Function.Bijective (IntegralMayerVietoris.differenceMap
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage (2 : Fin 4))
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3) 2) :=
  (correctedPositiveDegreeAssembly R).toSectionSevenMayerVietorisHomologyAssembly.finalDifferenceTwo_bijective

end SphereSixComplex.Geometry.PaperAnalyticData
