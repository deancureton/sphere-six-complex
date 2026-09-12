module
public import SphereSixComplex.Paper.Topology.CuspFourthSweepNormalizationOfProjection

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology CuspCollar


public theorem cuspFourthSweepClass_eq_rawFive (A : AnalyticData) :
    cuspFourthSweepClass A =
      A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) :=
  cuspFourthSweepClass_eq_rawFive_of_projection A
    A.actualCuspFillingHomologyTwoEquiv.toAddMonoidHom
    (CuspSpecialization.degreeTwo A)

end SphereSixComplex.Geometry.AnalyticData
