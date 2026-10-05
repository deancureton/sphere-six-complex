module
public import SphereSixComplex.Elliptic.Band.MarkedDisc
public import SphereSixComplex.Elliptic.Band.OverlapCompletionData
public import SphereSixComplex.Elliptic.Band.OverlapInterleaving
public import SphereSixComplex.Regular.Transport.PeriodCircleSideSupport
public import SphereSixComplex.Prerequisites.Topology.MappingTorus.TwoSliceBoundary

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory TopologicalSpace
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology GlobalTorusFamily TriangleGroup ComplexTorus
open EllipticTwoDiscHomologyCoordinates

public def centralToEllipticInterior (A : AnalyticData) :
    C(A.CentralFamily, A.ellipticInterior) :=
  ⟨fun x ↦ (A.ellipticCentralImageHomeomorph.symm x).1,
    continuous_subtype_val.comp A.ellipticCentralImageHomeomorph.symm.continuous⟩








end SphereSixComplex.Geometry.AnalyticData
end
end
