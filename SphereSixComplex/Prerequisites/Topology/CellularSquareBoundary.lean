module

public import SphereSixComplex.Prerequisites.Topology.CellularHomology
public import SphereSixComplex.Prerequisites.Topology.UnitSphereEquiv

@[expose] public section
noncomputable section

namespace SphereSixComplex

public def cwSquareBoundaryCircleHomeomorph : CWCharacteristicBoundarySphere 2 ≃ₜ Circle :=
  supNormUnitSphereCircleHomeomorph

end SphereSixComplex
