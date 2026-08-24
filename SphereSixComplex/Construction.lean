module

public import SphereSixComplex.Geometry.AtlasTransport
public import SphereSixComplex.Topology.FundamentalGroup
public import SphereSixComplex.Topology.SmoothRecognition

/-!
# Minimal construction target

The first two pages of the source reduce the main result to constructing a compact connected complex
threefold whose underlying smooth manifold is diffeomorphic to the standard six-sphere. This module
records that contract without including the paper's ancillary invariant calculations.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- A compact connected complex manifold of complex dimension three. -/
public structure ComplexThreefold where
  /-- The underlying type. -/
  Carrier : Type
  /-- The topology on the underlying type. -/
  topology : TopologicalSpace Carrier
  /-- The complex atlas. -/
  charts : ChartedSpace ComplexModel Carrier
  /-- Compatibility of the complex atlas. -/
  manifold :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel inferInstance
      𝓘(ℂ, ComplexModel) ∞ Carrier topology charts
  /-- Compatibility of the induced real atlas. -/
  realManifold :
    @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      𝓘(ℝ, RealModel) ∞ Carrier topology (underlyingRealChartedSpace charts)
  /-- Compactness. -/
  compact : @CompactSpace Carrier topology
  /-- Connectedness. -/
  connected : @ConnectedSpace Carrier topology
  /-- Hausdorffness of the underlying space. -/
  t2 : @T2Space Carrier topology
  /-- Second countability of the underlying space. -/
  secondCountable : @SecondCountableTopology Carrier topology

/-- The underlying real smooth manifold of a complex threefold is diffeomorphic to standard `S⁶`. -/
@[expose] public def DiffeomorphicToSixSphere (X : ComplexThreefold) : Prop :=
  Nonempty
    (@Diffeomorph ℝ inferInstance RealModel inferInstance inferInstance RealModel inferInstance
      inferInstance RealModel inferInstance RealModel inferInstance 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel)
      X.Carrier X.topology (@underlyingRealChartedSpace X.Carrier X.topology X.charts) SixSphere
      inferInstance inferInstance ∞)

/-- The exact geometric and topological output claimed for the completed torus family, before smooth
sphere recognition is applied. -/
public structure CompletedPaperThreefold where
  /-- The compact connected complex threefold obtained from the family and its three fillings. -/
  X : ComplexThreefold
  /-- The van Kampen computation with the selected twists. -/
  fundamentalGroup :
    @Topology.HasPaperFundamentalGroup X.Carrier X.topology
  /-- The integral Mayer--Vietoris computation. -/
  integralHomology :
    @HasIntegralHomologyOfSixSphere X.Carrier X.topology

/-- A completed paper threefold supplies all inputs to smooth six-sphere recognition. -/
public theorem CompletedPaperThreefold.smoothRecognitionInput
    (C : CompletedPaperThreefold) :
    letI := C.X.topology
    letI := underlyingRealChartedSpace C.X.charts
    SmoothSimplyConnectedIntegralHomologySixSphere C.X.Carrier := by
  let _ : TopologicalSpace C.X.Carrier := C.X.topology
  let _ : ChartedSpace ComplexModel C.X.Carrier := C.X.charts
  let _ : ChartedSpace RealModel C.X.Carrier :=
    underlyingRealChartedSpace C.X.charts
  let _ : ConnectedSpace C.X.Carrier := C.X.connected
  let _ : LocallyPathConnectedSpace C.X.Carrier :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel C.X.Carrier
  let _ : PathConnectedSpace C.X.Carrier :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  let hsimple : SimplyConnectedSpace C.X.Carrier :=
    Topology.simplyConnectedSpace_of_hasPaperFundamentalGroup C.fundamentalGroup
  exact
    { isManifold := C.X.realManifold
      compact := C.X.compact
      connected := C.X.connected
      integralHomology := C.integralHomology
      simplyConnected := hsimple }

end SphereSixComplex
