module

public import ForMathlib.Geometry.Manifold.LocallyContractible
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic

/-- A charted space over a strongly locally contractible model is semilocally simply connected. -/

public theorem ChartedSpace.semilocallySimplyConnectedSpace
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [StronglyLocallyContractibleSpace H] : TauCeti.SemilocallySimplyConnectedSpace M := by
  have _ : StronglyLocallyContractibleSpace M :=
    ChartedSpace.stronglyLocallyContractibleSpace (H := H)
  exact TauCeti.SemilocallySimplyConnectedSpace.of_locallyContractibleSpace
    (StronglyLocallyContractibleSpace.locallyContractible)
