module

public import SphereSixComplex.Paper.Topology.FiniteCoverPerfectPairing

@[expose] public section
noncomputable section
open AlgebraicTopology Matrix
namespace SphereSixComplex.Topology.EllipticDegreeTwoRelations
open Geometry Geometry.GlobalTorusFamily Geometry.EllipticFamilySpecialization LatticeData EllipticFilling
open AffineCyclicQuotientHomology AffineCyclicCoverDegreeTwoInvariance
open FiniteCoverPerfectPairing TriangleGroup
variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

public theorem orderThree_projected_relation :
    orderThreeProjectedDegreeTwoGenerator F 0 -
      2 • orderThreeProjectedDegreeTwoGenerator F 1 +
      2 • orderThreeProjectedDegreeTwoGenerator F 4 -
      2 • orderThreeProjectedDegreeTwoGenerator F 5 = 0 := by
  let p := (integralSingularHomologyMap 2
    (RadialEllipticActionData.centralFiberCoverProjection (orderThreeRadialActionData F))).comp
    (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm.toAddMonoidHom
  have he : exteriorSquareMap (rhoLambda g₁) (Pi.single (1 : Fin 6) 1) =
      Pi.single 0 1 - Pi.single 1 1 +
        (2 : ℤ) • Pi.single 4 1 - (2 : ℤ) • Pi.single 5 1 := by
    funext i
    fin_cases i <;>
      norm_num [exteriorSquareMap, exteriorSquareMatrix, integralMatrix_rhoLambda_gOne,
        secondCompoundMatrix, A₁, periodPairFirst, periodPairSecond, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ] <;> decide
  have hi : p (exteriorSquareMap (rhoLambda g₁) (Pi.single (1 : Fin 6) 1)) =
      p (Pi.single 1 1) :=
    coverProjection_degreeTwo_invariant (orderThreeCentralFiberPresentationData F) _
  rw [he, map_sub, map_add, map_sub, map_zsmul, map_zsmul] at hi
  change p (Pi.single 0 1) - 2 • p (Pi.single 1 1) +
    2 • p (Pi.single 4 1) - 2 • p (Pi.single 5 1) = 0
  calc
    _ = (p (Pi.single 0 1) - p (Pi.single 1 1) +
      (2 : ℤ) • p (Pi.single 4 1) - (2 : ℤ) • p (Pi.single 5 1)) -
        p (Pi.single 1 1) := by abel
    _ = 0 := sub_eq_zero.mpr hi

public theorem orderThree_map_zero_eq_two_smul_one
    {G : Type*} [AddCommGroup G]
    (f : IntegralSingularHomology 2 (orderThreeReducedCentralFiber F) →+ G)
    (h4 : f (orderThreeProjectedDegreeTwoGenerator F 4) = 0)
    (h5 : f (orderThreeProjectedDegreeTwoGenerator F 5) = 0) :
    f (orderThreeProjectedDegreeTwoGenerator F 0) =
      2 • f (orderThreeProjectedDegreeTwoGenerator F 1) := by
  have h := congrArg f (orderThree_projected_relation F)
  simpa only [map_sub, map_add, map_nsmul, h4, h5, smul_zero, add_zero, sub_zero,
    map_zero, sub_eq_zero] using h

end SphereSixComplex.Topology.EllipticDegreeTwoRelations
