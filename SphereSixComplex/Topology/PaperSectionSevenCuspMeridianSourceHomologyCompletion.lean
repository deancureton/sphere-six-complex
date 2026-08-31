module

public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianSourceCircleMapCompletion
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasisProof

/-!
# Homology evaluations of the explicit cusp source circle map

This file computes the complete fibre contribution of the source circle map.  The sole remaining
evaluation is on the specialization-adjusted Wang section, rather than on a fibre class.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix Topology
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open Geometry.GlobalTorusFamily Geometry.CuspRadialClutchingConstruction
open Periods

/-- Winding after the degree-`n` circle power map is multiplication by `n`. -/
public theorem unitCircleHomologyWinding_powerMap
    (n : ℤ) (z : IntegralSingularHomology 1 UnitAddCircle) :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (StandardCircleHomologyLiftDegree.unitCirclePowerMap n) z) =
      n * StandardCircleHomologyLiftDegree.unitCircleHomologyWinding z := by
  open StandardCircleHomologyLiftDegree in
  have hz : z = unitCircleHomologyWinding z • unitCirclePositiveHomologyClass := by
    apply StandardTorusHomology.unitCircleHomologyWinding_injective
    simp [unitCircleHomologyWinding_positive]
  calc
    unitCircleHomologyWinding (integralSingularHomologyMap 1 (unitCirclePowerMap n) z) =
        unitCircleHomologyWinding
          (integralSingularHomologyMap 1 (unitCirclePowerMap n)
            (unitCircleHomologyWinding z • unitCirclePositiveHomologyClass)) :=
      congrArg unitCircleHomologyWinding
        (congrArg (integralSingularHomologyMap 1 (unitCirclePowerMap n)) hz)
    _ = unitCircleHomologyWinding z • n := by
      rw [map_zsmul, unitCirclePowerMap_positiveHomologyClass,
        map_zsmul, unitCircleHomologyWinding_integerLoop]
    _ = n * unitCircleHomologyWinding z := by
      rw [smul_eq_mul, mul_comm]

/-- The fibre character induces twelve times the first marked period coordinate on `H₁`. -/
public theorem cuspFiberTwelveFirstCoordinate_homology
    (x : PeriodDomain) (z : IntegralSingularHomology 1 (AdditiveTorus x.1)) :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (cuspFiberTwelveFirstCoordinate x) z) =
      12 * (EstablishedTorusHomology.additiveTorusHomologyBasis x.1
        (fullRankDomain x)).degreeOne z 0 := by
  let s : C(AdditiveTorus x.1, StandardTorusHomology.StdTorus 4) :=
    ⟨StandardTorusHomology.additiveTorusStdMap x.1 (fullRankDomain x),
      (StandardTorusHomology.additiveTorusStdHomeomorph x.1
        (fullRankDomain x)).continuous⟩
  let p := StandardTorusHomology.standardFourTorusCoordinateProjection (0 : Fin 4)
  let e : C(StandardTorusHomology.StdTorus 1, UnitAddCircle) :=
    StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph
  let pow := StandardCircleHomologyLiftDegree.unitCirclePowerMap 12
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
      (integralSingularHomologyMap 1 (pow.comp (e.comp (p.comp s))) z) = _
  rw [← integralSingularHomologyMap_comp_wang 1 (e.comp (p.comp s)) pow z]
  rw [unitCircleHomologyWinding_powerMap]
  rw [← integralSingularHomologyMap_comp_wang 1 (p.comp s) e z]
  rw [← integralSingularHomologyMap_comp_wang 1 s p z]
  rfl

/-- Restricting the full source map to the mapping-torus fibre gives the same `12 q₀`
homology functional. -/
public theorem cuspMeridianSourceCircleMap_fiber_homology
    (x : PeriodDomain) (z : IntegralSingularHomology 1 (AdditiveTorus x.1)) :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (cuspMeridianSourceCircleMap x)
          (integralSingularHomologyMap 1
            (finiteBouquetMappingTorusFiberInclusion
              (fun _ : Unit ↦ cuspFiberClutching x)) z)) =
      12 * (EstablishedTorusHomology.additiveTorusHomologyBasis x.1
        (fullRankDomain x)).degreeOne z 0 := by
  rw [integralSingularHomologyMap_comp_wang]
  have hmaps :
      (cuspMeridianSourceCircleMap x).comp
          (finiteBouquetMappingTorusFiberInclusion
            (fun _ : Unit ↦ cuspFiberClutching x)) =
        cuspFiberTwelveFirstCoordinate x := by
    ext y
    exact cuspMeridianSourceCircleMap_fiberInclusion x y
  rw [hmaps]
  exact cuspFiberTwelveFirstCoordinate_homology x z

/-- On the four marked fibre generators, the source winding values are `[12, 0, 0, 0]`. -/
public theorem cuspMeridianSourceCircleMap_fiberBasisValues (x : PeriodDomain) :
    (fun i : Fin 4 ↦
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1 (cuspMeridianSourceCircleMap x)
          (integralSingularHomologyMap 1
            (finiteBouquetMappingTorusFiberInclusion
              (fun _ : Unit ↦ cuspFiberClutching x))
            ((EstablishedTorusHomology.additiveTorusHomologyBasis x.1
              (fullRankDomain x)).degreeOne.symm (Pi.single i 1))))) =
      ![12, 0, 0, 0] := by
  funext i
  rw [cuspMeridianSourceCircleMap_fiber_homology]
  rw [(EstablishedTorusHomology.additiveTorusHomologyBasis x.1
    (fullRankDomain x)).degreeOne.apply_symm_apply]
  fin_cases i <;> simp

end SphereSixComplex

end
