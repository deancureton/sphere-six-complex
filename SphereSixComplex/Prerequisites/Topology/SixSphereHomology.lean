module

public import SphereSixComplex.Prerequisites.Topology.CellularChainModel
public import SphereSixComplex.Prerequisites.Topology.SphereFiniteCWModel
public import SphereSixComplex.Prerequisites.Topology.StandardSpherePositiveHomology
public import SphereSixComplex.Prerequisites.Topology.StandardSphereHomologyZeroCore

/-! # Homology of the six-sphere from its two-cell CW structure -/

@[expose] public section

noncomputable section

namespace SphereSixComplex

/-- The proved positive-degree integral homology calculation for the standard six-sphere. -/
public theorem sixSpherePositiveHomologyInputs : SixSpherePositiveHomologyInputs := by
  let _ := sixSphereFiniteCWComplex
  refine ⟨?_, fun n hn0 hn6 ↦ ?_⟩
  · let _ := sixSphereCell_isEmpty 5 (by decide) (by decide)
    let _ := sixSphereCell_isEmpty 7 (by decide) (by decide)
    let _ := sixSphereCell_unique 6 (Or.inr rfl)
    let e := IntegralCWCellularHomologyModel.homologyEquivCells SixSphereFiniteCWCarrier
      (CellularHomology.integralComparison.objectwiseModel SixSphereFiniteCWCarrier) 5
    exact ⟨((integralSingularHomologyEquiv 6 sixSphereFiniteCWHomeomorph).symm.trans e).trans
      (Finsupp.uniqueAddEquiv default)⟩
  · let _ := sixSphereCell_isEmpty n hn0 hn6
    let _ := subsingleton_integralSingularHomology_of_isEmpty_cell SixSphereFiniteCWCarrier n
    exact (integralSingularHomologyEquiv n sixSphereFiniteCWHomeomorph).symm.injective.subsingleton

end SphereSixComplex
