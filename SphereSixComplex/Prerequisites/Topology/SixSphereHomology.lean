module

public import SphereSixComplex.Prerequisites.Topology.SixSpherePositiveHomologyInputsProof

namespace SphereSixComplex

/-- The proved positive-degree integral homology calculation for the standard six-sphere. -/
public theorem sixSpherePositiveHomologyInputs :
    SixSpherePositiveHomologyInputs :=
  sixSpherePositiveHomologyInputs_via_boundarySeven

end SphereSixComplex
