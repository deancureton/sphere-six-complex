module

public import SphereSixComplex.Prerequisites.Topology.CellularNormalizedFoundation

@[expose] public section
noncomputable section
namespace SphereSixComplex

namespace EstablishedCellularHomology

/-- The cellular model with canonical point and interval orientations. -/
public noncomputable def integralCWCellularHomologyModel
    (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] :
    IntegralCWCellularHomologyModel Y :=
  CellularHomology.IntegralComparison.objectwiseModel
    CellularHomology.integralComparison.normalized Y

end EstablishedCellularHomology

end SphereSixComplex
