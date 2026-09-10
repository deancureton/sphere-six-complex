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

public structure ActualCuspFiberEllipticMarkedCoordinateResidual
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput) : Prop where
  degreeTwoIndexFive :
    A.cuspEllipticFiberCoordinate R (correctedCuspDegreeTwoSplitting R)
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) = 1

public theorem establishedActualCuspFiberEllipticMarkedCoordinateResidual
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput) :
    ActualCuspFiberEllipticMarkedCoordinateResidual R :=
  ⟨A.cuspEllipticFiberCoordinate_rawFive R (correctedCuspDegreeTwoSplitting R)⟩

public def correctedPositiveDegreeAssembly_of_residual
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput)
    (C : ActualCuspFiberEllipticMarkedCoordinateResidual R) :
    A.PositiveDegreeHomologyAssembly :=
  correctedPositiveDegreeHomologyAssembly R.homologyAlignment.actualHomologyCoordinates
    (correctedCuspDegreeTwoSplitting R)
    (cuspDegreeOneUnionCoordinates_of_fullIterate R (A.cuspDegreeOneFullIterateRelation_proved R))
    (fun x ↦ congrFun (correctedCuspHomologyTwoCoordinates_of_rawFive R C.degreeTwoIndexFive x) 0)
    (correctedCuspDegreeTwoSplitting_boundary R)

public def correctedPositiveDegreeAssembly
    {A : PaperAnalyticData} (R : A.AffineRadialCompletionInput) :
    A.PositiveDegreeHomologyAssembly :=
  correctedPositiveDegreeAssembly_of_residual R
    (establishedActualCuspFiberEllipticMarkedCoordinateResidual R)

end EstablishedSectionSevenCuspTopology
end SphereSixComplex.Geometry.PaperAnalyticData
