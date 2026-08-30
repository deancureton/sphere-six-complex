module

public import SphereSixComplex.Topology.PaperActualEllipticRelatorNormalClosure
public import SphereSixComplex.Topology.PaperActualEllipticOrderFourRelatorComparison

/-!
# Common-gauge reduction for the actual elliptic relators

The order-three and order-four common-gauge comparisons imply the connector-invariant
normal-closure residual used by the actual four-piece van Kampen bridge.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-- The two common-gauge comparisons imply the complete elliptic normal-closure residual. -/
public theorem actualEllipticRelatorNormalClosureResidual_of_commonGaugeComparisons
    {N : A.ActualCuspCentralNaturality}
    (H3 : A.OrderThreeCommonGaugeComparison N)
    (H4 : A.OrderFourCommonGaugeComparison N) :
    A.ActualEllipticRelatorNormalClosureResidual N := by
  constructor
  · change A.orderThreeCentralRelatorToCore N ∈
      Subgroup.normalClosure
        {A.actualEllipticThreeOverlapToCore A.orderThreeActualEllipticCanonicalRelator}
    have hrel :
        A.actualEllipticThreeOverlapToCore A.orderThreeActualEllipticCanonicalRelator =
          A.orderThreeActualPhysicalRelatorToCore :=
      A.orderThreeActualCanonicalRelatorToCore_eq_physical
    rw [hrel]
    exact H3.relator_mem_normalClosure
  · change A.orderFourCentralRelatorToCore N ∈
      Subgroup.normalClosure
        {A.actualEllipticFourOverlapToCore A.orderFourActualEllipticCanonicalRelator}
    have hrel :
        A.actualEllipticFourOverlapToCore A.orderFourActualEllipticCanonicalRelator =
          A.orderFourActualPhysicalRelatorToCore :=
      A.orderFourActualCanonicalRelatorToCore_eq_physical
    rw [hrel]
    exact H4.relator_mem_normalClosure

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
