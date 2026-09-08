module

public import SphereSixComplex.Topology.CuspCorrectedEllipticSplitting
public import SphereSixComplex.Topology.CuspCorrectedHomologyAssembly
public import SphereSixComplex.Topology.CuspCorrectedDegreeOneCoordinates
public import SphereSixComplex.Topology.CuspTranslationHomologyComparison

/-!
# Cusp completion with the corrected invariant marking

The boundary map, raw-four normalized splitting, and meridian relation are proved. Only the
raw-five fibre coefficient remains as a transitional geometric input.
-/

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
namespace EstablishedSectionSevenCuspTopology

public structure ActualCuspFiberEllipticMarkedCoordinateResidual
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) : Prop where
  degreeTwoIndexFive :
    A.cuspEllipticFiberCoordinate R (correctedCuspDegreeTwoSplitting R)
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) = 1

public axiom establishedActualCuspFiberEllipticMarkedCoordinateResidual
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspFiberEllipticMarkedCoordinateResidual R

public def correctedPositiveDegreeAssembly_of_residual
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput)
    (C : ActualCuspFiberEllipticMarkedCoordinateResidual R) :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  correctedPositiveDegreeHomologyAssembly R.homologyAlignment.actualHomologyCoordinates
    (correctedCuspDegreeTwoSplitting R)
    (cuspDegreeOneUnionCoordinates_of_fullIterate R (A.actualCuspDegreeOneFullIterateRelation_proved R))
    (fun x ↦ congrFun (correctedCuspHomologyTwoCoordinates_of_rawFive R C.degreeTwoIndexFive x) 0)
    (correctedCuspDegreeTwoSplitting_boundary R)

public def correctedPositiveDegreeAssembly
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) :
    A.SectionSevenPositiveDegreeHomologyAssembly :=
  correctedPositiveDegreeAssembly_of_residual R
    (establishedActualCuspFiberEllipticMarkedCoordinateResidual R)

end EstablishedSectionSevenCuspTopology
end SphereSixComplex.Geometry.PaperAnalyticData
