module
public import SphereSixComplex.Paper.Topology.CuspFourthSweepNormalizationOfProjection

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology CuspPuncturedCollarBridge


public theorem cuspFourthSweepClass_eq_rawFive (A : PaperAnalyticData) :
    cuspFourthSweepClass A =
      A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) :=
  cuspFourthSweepClass_eq_rawFive_of_projection A
    A.actualCuspFillingHomologyTwoEquiv.toAddMonoidHom
    (EstablishedStandardA2CuspSpecialization.degreeTwo A)

end SphereSixComplex.Geometry.PaperAnalyticData
