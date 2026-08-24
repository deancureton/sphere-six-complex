/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-!
# Unimodularity of the height-one `A₂` cones

This is the determinant calculation in Lemma 4.2(i) of the source paper. It is adapted from
`ComplexStructures.S6.Cusp.A2Triangulation` in the companion formalization and applied directly
to `StandardInfiniteA2ToricModel.a2ConeMatrix`.
-/

open Matrix
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-- The lifted generators of a lower `A₂` triangle have determinant one. -/
public theorem a2ConeMatrix_det_false (v : ToricLattice) :
  (a2ConeMatrix false v).det = 1 := by
  simp [Matrix.det_fin_three, a2ConeMatrix, heightOneRay, a2Triangle];
    ring

/-- The lifted generators of an upper `A₂` triangle have determinant negative one. -/
public theorem a2ConeMatrix_det_true (v : ToricLattice) :
  (a2ConeMatrix true v).det = -1 := by
  simp [Matrix.det_fin_three, a2ConeMatrix, heightOneRay, a2Triangle];
    ring

/-- Every maximal height-one `A₂` cone has determinant determined by its triangle class. -/
public theorem a2ConeMatrix_det (upper : Bool) (v : ToricLattice) :
    (a2ConeMatrix upper v).det = if upper then -1 else 1 := by
  cases upper with
  | false => exact a2ConeMatrix_det_false v
  | true => exact a2ConeMatrix_det_true v

/-- Lemma 4.2(i): every maximal cone of the explicit infinite `A₂` fan is unimodular. -/
public theorem a2ConeMatrix_isUnit_det (upper : Bool) (v : ToricLattice) :
    IsUnit (a2ConeMatrix upper v).det := by
  rw [a2ConeMatrix_det]
  cases upper <;> simp

/-- Compatibility accessor for models: unimodularity is a theorem of the fixed fan, rather than
data that every model must supply. -/
public theorem Model.cone_unimodular (_M : Model) (upper : Bool) (v : ToricLattice) :
    IsUnit (a2ConeMatrix upper v).det :=
  a2ConeMatrix_isUnit_det upper v

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
