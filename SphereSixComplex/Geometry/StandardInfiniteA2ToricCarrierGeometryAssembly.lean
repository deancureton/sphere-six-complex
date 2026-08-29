/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCentralComponents
public import SphereSixComplex.Geometry.StandardInfiniteA2ToricResidualAnalytic
public import SphereSixComplex.Geometry.StandardInfiniteA2ToricSublevelSimplyConnected

/-!
# Remaining geometry for the standard infinite `A₂` toric model

The glued carrier, height, dense torus, affine charts, and full holomorphic torus action are
constructed upstream.  This module isolates the smaller residual interface needed to assemble the
existing `StandardInfiniteA2ToricModel.Model` without changing its statement.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Manifold
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The geometric facts not yet supplied by the glued-carrier construction. -/
public structure RemainingGeometry where
  closedUnitPolydisc_union_below_closed :
    letI := chartedSpace
    ∀ c : ℝ, c < 1 → IsClosed (⋃ a : ChartIndex,
      {p | p ∈ (toricChart a).source ∧ ∀ i, ‖toricChart a p i‖ ≤ 1} ∩
        {p | ‖carrierHeight p‖ ≤ c})
  fanShear : ParameterLattice →+ Additive (Equiv.Perm Carrier)
  fanShear_holomorphic :
    letI := chartedSpace
    ∀ lambda, ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun p ↦ Additive.toMul (fanShear lambda) p)
  fanShear_preserves_t :
    ∀ lambda p, carrierHeight (Additive.toMul (fanShear lambda) p) = carrierHeight p
  fanShear_torus :
    ∀ lambda x, Additive.toMul (fanShear lambda) (carrierTorusEmbedding x) =
      carrierTorusEmbedding (denseTorusShear lambda x)
  fanShear_chart :
    letI := chartedSpace
    ∀ lambda a p, p ∈ (toricChart a).source ↔
      Additive.toMul (fanShear lambda) p ∈
        (toricChart (a.1, a.2 + shearVector lambda)).source
  fanShear_component :
    ∀ lambda v,
      (fun p ↦ Additive.toMul (fanShear lambda) p) '' carrierCentralComponent v =
        carrierCentralComponent (v + shearVector lambda)

/-- Assemble the exact public toric-model interface from the constructed carrier and the residual
geometric package. -/
public noncomputable def RemainingGeometry.toModel (R : RemainingGeometry) : Model where
  Carrier := Carrier
  topology := inferInstance
  charts := chartedSpace
  manifold := isManifold
  t2 := t2Space
  secondCountable := secondCountableTopology
  connected := carrierConnectedSpace
  t := carrierHeight
  localCarrierSimplyConnected := carrierHeightSublevel_simplyConnected
  t_holomorphic := carrierHeight_contMDiff
  torusEmbedding := carrierTorusEmbedding
  torus_openEmbedding := carrierTorusEmbedding_isOpenEmbedding
  torusEmbedding_isLocalDiffeomorph := carrierTorusEmbedding_isLocalDiffeomorph
  torus_dense := carrierTorusEmbedding_denseRange
  torus_range := carrierTorusEmbedding_range
  t_torus := carrierHeight_torus
  torusAction := carrierTorusAction
  torusAction_holomorphic := carrierTorusAction_contMDiff
  variableTorusAction_holomorphic := carrierVariableTorusAction_contMDiff
  torusAction_torus := carrierTorusAction_torus
  t_torusAction := carrierHeight_torusAction
  toricChart := fun upper v ↦ toricChart (upper, v)
  toricChart_target := fun upper v ↦ toricChart_target (upper, v)
  toricChart_cover := fun p ↦ by
    obtain ⟨⟨upper, v⟩, hp⟩ := toricChart_cover p
    exact ⟨upper, v, hp⟩
  torus_mem_toricChart := fun upper v ↦ carrierTorusEmbedding_mem_toricChart (upper, v)
  toricChart_torus_character := fun upper v ↦ toricChart_torus_character (upper, v)
  closedUnitPolydisc_union_below_closed := R.closedUnitPolydisc_union_below_closed
  toricChart_t := fun upper v ↦ carrierHeight_toricChart (upper, v)
  centralComponent := carrierCentralComponent
  centralFiber_eq_iUnion := carrierCentralFiber_eq_iUnion
  centralComponent_in_chart := fun upper v ↦ carrierCentralComponent_in_chart (upper, v)
  otherCentralComponent_disjoint_chart := fun upper v ↦
    otherCarrierCentralComponent_disjoint_chart (upper, v)
  torusAction_centralComponent := carrierTorusAction_centralComponent
  fanShear := R.fanShear
  fanShear_holomorphic := R.fanShear_holomorphic
  fanShear_preserves_t := R.fanShear_preserves_t
  fanShear_torus := R.fanShear_torus
  fanShear_chart := fun lambda upper v ↦ R.fanShear_chart lambda (upper, v)
  fanShear_component := R.fanShear_component

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
