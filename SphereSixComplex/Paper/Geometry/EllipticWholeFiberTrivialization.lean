module

public import SphereSixComplex.Paper.Geometry.EllipticLocalTrivialization
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SphereSixComplex.Prerequisites.Geometry.ComplexUnitDisc

/-!
# Whole-fibre elliptic trivializations

This file isolates the precise gluing input that is not supplied by pointwise quotient charts.
Compatible local analytic representatives glue to a partial diffeomorphism on one open
neighbourhood.  Restricting its target away from the central fibre gives the collar used for an
elliptic filling.
-/

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry.EllipticWholeFiberTrivialization

open Filter Set SphereSixComplex.Geometry
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLocalTrivialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.TriangleGroup SphereSixComplex.Periods

noncomputable section

universe u v w

section ActualEllipticFamilies

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- A family deck map as a permutation of the actual varying-lattice quotient. -/
@[expose] public noncomputable def familyDeckEquiv (g : Delta) :
    Equiv.Perm (TotalSpace (parameterMap F)) where
  toFun := familyDeckMap F g
  invFun := familyDeckMap F g⁻¹
  left_inv x := by
    rw [← familyDeckMap_mul, inv_mul_cancel, familyDeckMap_one]
  right_inv x := by
    rw [← familyDeckMap_mul, mul_inv_cancel, familyDeckMap_one]

@[simp]
public theorem familyDeckEquiv_apply (g : Delta) (x : TotalSpace (parameterMap F)) :
    familyDeckEquiv F g x = familyDeckMap F g x :=
  rfl

/-- The order-three subgroup acting on the actual torus family. -/
@[expose] public noncomputable def familyDeckRepresentation :
    Delta →* Equiv.Perm (TotalSpace (parameterMap F)) where
  toFun := familyDeckEquiv F
  map_one' := by
    apply Equiv.ext
    exact familyDeckMap_one F
  map_mul' := by
    intro g h
    apply Equiv.ext
    exact familyDeckMap_mul F g h

/-- The order-three subgroup acting on the actual torus family. -/
@[expose] public noncomputable def orderThreeFamilyRepresentation :
    FiniteCyclic 3 →* Equiv.Perm (TotalSpace (parameterMap F)) :=
  (familyDeckRepresentation F).comp
    (Monoid.Coprod.inl : FiniteCyclic 3 →* Delta)

/-- The order-four subgroup acting on the actual torus family. -/
@[expose] public noncomputable def orderFourFamilyRepresentation :
    FiniteCyclic 4 →* Equiv.Perm (TotalSpace (parameterMap F)) :=
  (familyDeckRepresentation F).comp
    (Monoid.Coprod.inr : FiniteCyclic 4 →* Delta)





end ActualEllipticFamilies

end

end SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
