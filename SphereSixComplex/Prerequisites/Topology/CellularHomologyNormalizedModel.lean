module

public import SphereSixComplex.Prerequisites.Topology.CellularNormalizedFoundation

@[expose] public section
noncomputable section
namespace SphereSixComplex

namespace CellularHomology

/-- The cellular model with canonical point and interval orientations. -/
public noncomputable def normalizedModel
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] :
    IntegralCWCellularHomologyModel Y :=
  CellularHomology.IntegralComparison.objectwiseModel
    CellularHomology.integralComparison.normalized Y

end CellularHomology

end SphereSixComplex
