module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open scoped ContinuousMap
namespace SphereSixComplex.Topology
noncomputable section

/-- A path-connected space with a trivial fundamental group at one basepoint is simply connected. -/
public theorem simplyConnectedSpace_of_fundamentalGroup_subsingleton
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (x₀ : X) [Subsingleton (FundamentalGroup X x₀)] : SimplyConnectedSpace X := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x γ ↦ ?_⟩
  let e : FundamentalGroup X x ≃* FundamentalGroup X x₀ :=
    FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x x₀
  rw [← Path.Homotopic.Quotient.eq]
  apply e.injective
  exact Subsingleton.elim _ _

end
end SphereSixComplex.Topology
