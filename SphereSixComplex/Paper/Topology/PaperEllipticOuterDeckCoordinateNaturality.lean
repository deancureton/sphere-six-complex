module
public import SphereSixComplex.Prerequisites.Topology.QuotientCoverMonodromyTransport
public import SphereSixComplex.Paper.Topology.PaperGeometricCentralCore

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : AnalyticData)

public theorem regularCoordinate_isQuotientCoveringMap :
    letI := A.regularBaseDeckAction
    IsQuotientCoveringMap A.regularCoordinate Delta := by
  let _ := A.regularBaseDeckAction
  let hp := regularBaseQuotientMap_isQuotientCoveringMap
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.homeomorph_comp A.puncturedBaseHomeomorphTwicePuncturedComplex


end SphereSixComplex.Geometry.AnalyticData
