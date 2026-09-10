module

public import SphereSixComplex.Paper.Topology.TwistObstruction
public import SphereSixComplex.Prerequisites.Topology.FundamentalGroupSimplyConnected

/-!
# The fundamental-group recognition step

This file isolates the exact conclusion of the van Kampen computation in the paper and proves that
its value for the chosen twists implies simple connectedness.
-/

open scoped ContinuousMap

namespace SphereSixComplex.Topology

noncomputable section

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
