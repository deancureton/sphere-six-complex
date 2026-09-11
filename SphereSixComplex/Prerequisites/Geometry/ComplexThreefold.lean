module

public import SphereSixComplex.Prerequisites.Geometry.AtlasTransport
public import SphereSixComplex.Prerequisites.Geometry.EstablishedComplexToRealManifold

/-!
# Compact complex threefolds

A bundled carrier and atlas for existential statements about compact connected complex
threefolds. Results about a given manifold use Mathlib's unbundled manifold typeclasses.
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
  /-- Compactness. -/
  compact : @CompactSpace Carrier topology
  /-- Connectedness. -/
  connected : @ConnectedSpace Carrier topology
  /-- Hausdorffness of the underlying space. -/
  t2 : @T2Space Carrier topology
  /-- Second countability of the underlying space. -/
  secondCountable : @SecondCountableTopology Carrier topology

attribute [instance] ComplexThreefold.topology ComplexThreefold.charts
  ComplexThreefold.manifold ComplexThreefold.compact ComplexThreefold.connected
  ComplexThreefold.t2 ComplexThreefold.secondCountable

namespace ComplexThreefold

@[instance_reducible]
public noncomputable instance realCharts (X : ComplexThreefold) :
    ChartedSpace RealModel X.Carrier := underlyingRealChartedSpace X.charts

public instance realManifold (X : ComplexThreefold) :
    IsManifold 𝓘(ℝ, RealModel) ∞ X.Carrier :=
  RealAtlas.isManifold X.charts X.manifold

end ComplexThreefold

end SphereSixComplex
