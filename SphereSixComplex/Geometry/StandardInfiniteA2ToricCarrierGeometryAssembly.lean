/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCentralComponents
public import SphereSixComplex.Geometry.StandardInfiniteA2ToricClosedPolydisc
public import SphereSixComplex.Geometry.StandardInfiniteA2ToricFanShears
public import SphereSixComplex.Geometry.StandardInfiniteA2ToricResidualAnalytic
public import SphereSixComplex.Geometry.StandardInfiniteA2ToricSublevelSimplyConnected

/-!
# Assembly of the standard infinite `A₂` toric model

The glued carrier, height, dense torus, affine charts, full holomorphic torus action, fan shears,
simply connected sublevels, and closed bounded region are constructed upstream.  This module
assembles them into the existing `StandardInfiniteA2ToricModel.Model` without changing its
statement.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Manifold
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- Assemble the exact public toric-model interface from the constructed carrier. -/
public noncomputable def constructedModel : Model where
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
  closedUnitPolydisc_union_below_closed := closedUnitPolydisc_union_below_closed
  toricChart_t := fun upper v ↦ carrierHeight_toricChart (upper, v)
  centralComponent := carrierCentralComponent
  centralFiber_eq_iUnion := carrierCentralFiber_eq_iUnion
  centralComponent_in_chart := fun upper v ↦ carrierCentralComponent_in_chart (upper, v)
  otherCentralComponent_disjoint_chart := fun upper v ↦
    otherCarrierCentralComponent_disjoint_chart (upper, v)
  torusAction_centralComponent := carrierTorusAction_centralComponent
  fanShear := carrierFanShear
  fanShear_holomorphic := carrierFanShear_holomorphic
  fanShear_preserves_t := carrierFanShear_preserves_t
  fanShear_torus := carrierFanShear_on_torus
  fanShear_chart := fun lambda upper v ↦ carrierFanShear_chart lambda (upper, v)
  fanShear_component := carrierFanShear_component_exact

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

/-- The explicit standard toric model for the countable smooth fan obtained by coning the `A₂`
triangulation at height one. -/
public theorem model : Nonempty Model :=
  ⟨Construction.constructedModel⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
