module
public import SphereSixComplex.Paper.Topology.CuspFourthSweepNormalizationOfProjection

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology CuspPuncturedCollarBridge

public theorem actualCuspFourthSweepClass_raw_fiber_zero (A : PaperAnalyticData) (i : Fin 4) :
    A.actualCuspRawHomologyTwoEquiv (actualCuspFourthSweepClass A) (Fin.castAdd 2 i) = 0 :=
  actualCuspFourthSweepClass_raw_fiber_zero_of_projection A
    A.actualCuspFillingHomologyTwoEquiv.toAddMonoidHom
    (EstablishedStandardA2CuspSpecialization.degreeTwo A) i

public theorem actualCuspFourthSweepClass_eq_rawFive (A : PaperAnalyticData) :
    actualCuspFourthSweepClass A =
      A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) :=
  actualCuspFourthSweepClass_eq_rawFive_of_projection A
    A.actualCuspFillingHomologyTwoEquiv.toAddMonoidHom
    (EstablishedStandardA2CuspSpecialization.degreeTwo A)

end SphereSixComplex.Geometry.PaperAnalyticData
