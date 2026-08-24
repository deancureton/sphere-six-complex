module

public import SphereSixComplex.Geometry.CuspPhaseEstimates

/-!
# Component preservation in the standard infinite `A₂` toric model

This file connects the standard dense-torus orbit-closure datum to the interface used by the
cusp fixed-point estimate.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model

open SphereSixComplex.Geometry.CuspPhaseEstimates

/-- Dense-torus multiplication in the standard model preserves every central-fibre ray
component. -/
public theorem toTorusActionPreservesComponents (M : Model) :
    TorusActionPreservesComponents M where
  torusAction_component := M.torusAction_centralComponent

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspPhaseEstimates

/-- The established standard fan model comes with its canonical component-preservation
witness. -/
public theorem exists_model_and_torusActionPreservesComponents :
    ∃ M : Model, TorusActionPreservesComponents M := by
  obtain ⟨M⟩ := model
  exact ⟨M, M.toTorusActionPreservesComponents⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
