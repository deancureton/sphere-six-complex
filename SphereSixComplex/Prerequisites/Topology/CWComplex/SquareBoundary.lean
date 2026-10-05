module

public import SphereSixComplex.Prerequisites.Topology.CWComplex.Homology
public import SphereSixComplex.Prerequisites.Topology.Sphere.LinearEquiv

@[expose] public section
noncomputable section

namespace SphereSixComplex

public def cwSquareBoundaryCircleHomeomorph : CWCharacteristicBoundarySphere 2 ≃ₜ Circle :=
  supNormUnitSphereCircleHomeomorph

end SphereSixComplex
