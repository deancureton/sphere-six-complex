module

public import SphereSixComplex.Paper.Geometry.AdditiveTorusTopology
public import SphereSixComplex.Paper.Geometry.EllipticFixedPointCriterion

/-!
# Topology of the two actual elliptic filling actions

The affine fibre maps used in the order-three and order-four fillings act on the actual period
tori.  This module proves continuity of every finite cyclic action map and records the resulting
connected and second-countable orbit quotients.
-/

namespace SphereSixComplex.Geometry.EllipticActualActionTopology

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.FamilyEquivariance
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.AdditiveTorusTopology

noncomputable section

/-- A cast between equal period parameters is continuous on their orbit presentations. -/
public theorem additiveTorusCast_continuous {x y : Parameters} (h : x = y) :
    Continuous (additiveTorusCast h) := by
  subst y
  exact continuous_id

/-- Every natural power of a continuous permutation is continuous. -/
public theorem continuous_equiv_pow {X : Type*} [TopologicalSpace X]
    (e : Equiv.Perm X) (he : Continuous e) :
    ∀ n : ℕ, Continuous (e ^ n)
  | 0 => by
      change Continuous fun x : X ↦ x
      exact continuous_id
  | n + 1 => by
      rw [pow_succ']
      exact he.comp (continuous_equiv_pow e he n)

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- Continuity of the actual order-three fibre automorphism. -/
public theorem orderThreeFiberAutomorphism_continuous :
    Continuous (orderThreeFiberAutomorphism F) := by
  exact (additiveTorusCast_continuous (transformOne_parameterMap_zOne F)).comp
    (generatorOneTorusHomeomorph (parameterMap F U.zOne).1
      (parameterMap F U.zOne).tau_ne_zero).continuous

/-- Continuity of the actual order-four fibre automorphism. -/
public theorem orderFourFiberAutomorphism_continuous :
    Continuous (orderFourFiberAutomorphism F) := by
  exact (additiveTorusCast_continuous (transformTwo_parameterMap_zTwo F)).comp
    (generatorTwoTorusHomeomorph (parameterMap F U.zTwo).1
      (parameterMap F U.zTwo).tau_ne_zero).continuous

/-- Continuity of the translated order-three fibre generator. -/
public theorem orderThreeFiberGenerator_continuous :
    Continuous (orderThreeActionData F).fiberGenerator := by
  change Continuous (fun q ↦
    orderThreeFiberAutomorphism F q +
      orderThreeTranslation (parameterMap F U.zOne).1)
  exact (orderThreeFiberAutomorphism_continuous F).add continuous_const

/-- Continuity of the translated order-four fibre generator. -/
public theorem orderFourFiberGenerator_continuous :
    Continuous (orderFourActionData F).fiberGenerator := by
  change Continuous (fun q ↦
    orderFourFiberAutomorphism F q +
      orderFourTranslation (parameterMap F U.zTwo).1)
  exact (orderFourFiberAutomorphism_continuous F).add continuous_const

/-- Continuity of rotation of the order-three Cayley disc. -/
public theorem orderThreeDiscRotation_continuous :
    Continuous orderThreeDiscRotation := by
  apply Continuous.subtype_mk
  exact continuous_const.mul continuous_subtype_val

/-- Continuity of rotation of the order-four Cayley disc. -/
public theorem orderFourDiscRotation_continuous :
    Continuous orderFourDiscRotation := by
  apply Continuous.subtype_mk
  exact continuous_const.mul continuous_subtype_val

/-- Continuity of the diagonal generator of the order-three filling. -/
public theorem orderThreeDiagonalGenerator_continuous :
    Continuous (orderThreeActionData F).diagonalGenerator := by
  change Continuous (fun p :
      ComplexUnitDisc × AdditiveTorus (parameterMap F U.zOne).1 ↦
    (orderThreeDiscRotation p.1, (orderThreeActionData F).fiberGenerator p.2))
  exact (orderThreeDiscRotation_continuous.comp continuous_fst).prodMk
    ((orderThreeFiberGenerator_continuous F).comp continuous_snd)

/-- Continuity of the diagonal generator of the order-four filling. -/
public theorem orderFourDiagonalGenerator_continuous :
    Continuous (orderFourActionData F).diagonalGenerator := by
  change Continuous (fun p :
      ComplexUnitDisc × AdditiveTorus (parameterMap F U.zTwo).1 ↦
    (orderFourDiscRotation p.1, (orderFourActionData F).fiberGenerator p.2))
  exact (orderFourDiscRotation_continuous.comp continuous_fst).prodMk
    ((orderFourFiberGenerator_continuous F).comp continuous_snd)

/-- Every element of the actual order-three filling action is continuous. -/
public theorem orderThreeRepresentation_continuous (g : FiniteCyclic 3) :
    Continuous ((orderThreeActionData F).representation g) := by
  rw [cyclic_eq_generator_pow g, map_pow,
    (orderThreeActionData F).representation_generator]
  exact continuous_equiv_pow _ (orderThreeDiagonalGenerator_continuous F) _

/-- Every element of the actual order-four filling action is continuous. -/
public theorem orderFourRepresentation_continuous (g : FiniteCyclic 4) :
    Continuous ((orderFourActionData F).representation g) := by
  rw [cyclic_eq_generator_pow g, map_pow,
    (orderFourActionData F).representation_generator]
  exact continuous_equiv_pow _ (orderFourDiagonalGenerator_continuous F) _









end


end SphereSixComplex.Geometry.EllipticActualActionTopology
