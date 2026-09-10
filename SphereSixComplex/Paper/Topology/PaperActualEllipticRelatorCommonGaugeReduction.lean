module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorNormalClosureTypes
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourRelatorComparison

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
public theorem ellipticRelatorMembership_of_commonGaugeComparisons
    {N : A.CuspCentralNaturality}
    (H3 : A.OrderThreeCommonGaugeComparison N)
    (H4 : A.OrderFourCommonGaugeComparison N) :
    A.EllipticRelatorMembership N := by
  constructor
  · change A.orderThreeCentralRelatorToCore N ∈
      Subgroup.normalClosure
        {A.ellipticThreeOverlapToCore A.ellipticThreeCanonicalRelator}
    have hrel :
        A.ellipticThreeOverlapToCore A.ellipticThreeCanonicalRelator =
          A.ellipticThreePhysicalRelatorToCore :=
      A.ellipticThreeCanonicalRelatorToCore_eq_physical
    rw [hrel]
    exact H3.relator_mem_normalClosure
  · change A.orderFourCentralRelatorToCore N ∈
      Subgroup.normalClosure
        {A.ellipticFourOverlapToCore A.ellipticFourCanonicalRelator}
    have hrel :
        A.ellipticFourOverlapToCore A.ellipticFourCanonicalRelator =
          A.ellipticFourPhysicalRelatorToCore :=
      A.ellipticFourCanonicalRelatorToCore_eq_physical
    rw [hrel]
    exact H4.relator_mem_normalClosure

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
