module

public import SphereSixComplex.Periods.Uniformization.ExactBranchAnalyticOrder
import all SphereSixComplex.Periods.Uniformization.ExactBranchAnalyticOrder
public import SphereSixComplex.Periods.Uniformization.LocalBranchedLift
import all SphereSixComplex.Periods.Uniformization.LocalBranchedLift

@[expose] public section

noncomputable section

namespace SphereSixComplex.Periods

open Complex Metric

/-- In the exact source and target uniformizer charts, the order-three branch admits a local
analytic degree-one lift. -/
theorem exists_exact_orderThree_chartLift
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) :
    ∃ r > 0, ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (ball 0 r) ∧ L 0 = 0 ∧
        ∀ z ∈ ball 0 r,
          J.branch_three.complexGerm (L z) = C.branch_one.complexGerm z := by
  apply TauCeti.exists_local_branchedLift_order_three
  · exact C.branch_one.complexGerm_analyticAt C.coordinate_holomorphic
  · exact J.branch_three.complexGerm_analyticAt
      normalizedModularJCoordinate_holomorphic
  · exact C.branch_one.complexGerm_analyticOrderAt C.coordinate_holomorphic
  · exact J.branch_three.complexGerm_analyticOrderAt
      normalizedModularJCoordinate_holomorphic

/-- In the exact source and target uniformizer charts, the order-four source / order-two target
branch admits the required local analytic degree-two lift. -/
theorem exists_exact_orderFourTwo_chartLift
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) :
    ∃ r > 0, ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (ball 0 r) ∧ L 0 = 0 ∧
        ∀ z ∈ ball 0 r,
          J.branch_two.complexGerm (L z) = C.branch_two.complexGerm z := by
  apply TauCeti.exists_local_branchedLift_order_four_two
  · exact C.branch_two.complexGerm_analyticAt C.coordinate_holomorphic
  · exact J.branch_two.complexGerm_analyticAt
      normalizedModularJCoordinate_holomorphic
  · exact C.branch_two.complexGerm_analyticOrderAt C.coordinate_holomorphic
  · exact J.branch_two.complexGerm_analyticOrderAt
      normalizedModularJCoordinate_holomorphic


end SphereSixComplex.Periods
