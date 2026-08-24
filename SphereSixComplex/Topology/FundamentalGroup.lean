module

public import SphereSixComplex.Topology.TwistObstruction
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The fundamental-group recognition step

This file isolates the exact conclusion of the van Kampen computation in the paper and proves that
its value for the chosen twists implies simple connectedness.
-/

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

/-- The precise group-theoretic output claimed by the paper for the selected fillings. -/
@[expose] public def HasPaperFundamentalGroup (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ x₀ : X, Nonempty
    (FundamentalGroup X x₀ ≃* Multiplicative TwistObstruction.ObstructionGroup)

/-- The paper's fundamental-group calculation makes a path-connected glued space simply connected. -/
public theorem simplyConnectedSpace_of_hasPaperFundamentalGroup
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (hπ₁ : HasPaperFundamentalGroup X) : SimplyConnectedSpace X := by
  obtain ⟨x₀, ⟨e⟩⟩ := hπ₁
  let _ : Subsingleton (FundamentalGroup X x₀) :=
    ⟨fun a b ↦ e.injective (Subsingleton.elim _ _)⟩
  exact simplyConnectedSpace_of_fundamentalGroup_subsingleton x₀

end

end SphereSixComplex.Topology
