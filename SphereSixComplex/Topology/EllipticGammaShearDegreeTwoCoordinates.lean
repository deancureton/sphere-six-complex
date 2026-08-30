module

public import SphereSixComplex.Topology.PaperAffineCyclicReducedFiberMappingTorus
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasisProof
public import SphereSixComplex.Topology.StandardThreeTorusProductDegreeTwoCoordinates

/-!
# Degree-two coordinates of the elliptic gamma shears
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix
open scoped ContinuousMap

namespace SphereSixComplex.Topology.EllipticGammaShearDegreeTwoCoordinates

open StandardTorusHomology
open Geometry.ComplexTorus
open PaperAffineCyclicReducedFiberMappingTorus

/-- The standard four-torus basis transported to gamma-circle times three-torus coordinates. -/
public noncomputable def gammaProductHomologyTwo :
    IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3) ≃+ (Fin 6 → ℤ) :=
  standardCircleProdThreeTorusHomologyTwo

@[simp]
public theorem gammaProductHomologyTwo_apply (x) :
    gammaProductHomologyTwo x =
      naturalStdTorusFourHomologyTwo
        (integralSingularHomologyMap 2 standardFourTorusGammaSplit.symm x) :=
  standardCircleProdThreeTorusHomologyTwo_apply x

private def orderThreeShearAsFourTorus : StdTorus 4 ≃ₜ StdTorus 4 where
  toFun u := ![-u 0, u 1 - 2 • u 0, u 2 + 4 • u 0, u 3]
  invFun u := ![-u 0, u 1 - 2 • u 0, u 2 + 4 • u 0, u 3]
  left_inv u := by funext i; fin_cases i <;> simp
  right_inv u := by funext i; fin_cases i <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def orderFourShearAsFourTorus : StdTorus 4 ≃ₜ StdTorus 4 where
  toFun u := ![u 0, u 1 - 3 • u 0, u 2 + 3 • u 0, u 3]
  invFun u := ![u 0, u 1 + 3 • u 0, u 2 - 3 • u 0, u 3]
  left_inv u := by funext i; fin_cases i <;> simp
  right_inv u := by funext i; fin_cases i <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def orderThreeShearInteger : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun u := ![-u 0, u 1 - 2 * u 0, u 2 + 4 * u 0, u 3]
  invFun u := ![-u 0, u 1 - 2 * u 0, u 2 + 4 * u 0, u 3]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' n x := by funext i; fin_cases i <;> simp <;> ring

private def orderFourShearInteger : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun u := ![u 0, u 1 - 3 * u 0, u 2 + 3 * u 0, u 3]
  invFun u := ![u 0, u 1 + 3 * u 0, u 2 - 3 * u 0, u 3]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' n x := by funext i; fin_cases i <;> simp <;> ring

private def orderThreeShearReal : (Fin 4 → ℝ) ≃+ (Fin 4 → ℝ) where
  toFun u := ![-u 0, u 1 - 2 * u 0, u 2 + 4 * u 0, u 3]
  invFun u := ![-u 0, u 1 - 2 * u 0, u 2 + 4 * u 0, u 3]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring

private def orderFourShearReal : (Fin 4 → ℝ) ≃+ (Fin 4 → ℝ) where
  toFun u := ![u 0, u 1 - 3 * u 0, u 2 + 3 * u 0, u 3]
  invFun u := ![u 0, u 1 + 3 * u 0, u 2 - 3 * u 0, u 3]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring

private def orderThreeShearLift :
    StandardFourTorusEquivariantLift
      (orderThreeShearAsFourTorus : C(StdTorus 4, StdTorus 4))
      orderThreeShearInteger where
  lift := orderThreeShearReal
  map_projection r := by
    funext i
    fin_cases i <;>
      simp [orderThreeShearAsFourTorus, orderThreeStandardGammaShear,
        standardFourTorusGammaSplit, orderThreeShearReal, standardFourTorusProjection]
    all_goals rw [← QuotientAddGroup.mk_nsmul]; congr 1 <;> norm_num
  map_integer n := by
    funext i
    fin_cases i <;>
      norm_num [orderThreeShearReal, orderThreeShearInteger, integerToReal] <;> ring

private def orderFourShearLift :
    StandardFourTorusEquivariantLift
      (orderFourShearAsFourTorus : C(StdTorus 4, StdTorus 4))
      orderFourShearInteger where
  lift := orderFourShearReal
  map_projection r := by
    funext i
    fin_cases i <;>
      simp [orderFourShearAsFourTorus, orderFourStandardGammaShear,
        standardFourTorusGammaSplit, orderFourShearReal, standardFourTorusProjection]
    all_goals rw [← QuotientAddGroup.mk_nsmul]; congr 1 <;> norm_num
  map_integer n := by
    funext i
    fin_cases i <;>
      norm_num [orderFourShearReal, orderFourShearInteger, integerToReal] <;> ring

private theorem orderThreeShear_homologyTwo (x) :
    gammaProductHomologyTwo
        (integralSingularHomologyMap 2 orderThreeStandardGammaShear x) =
      standardExteriorSquareMap orderThreeShearInteger
        (naturalStdTorusFourHomologyTwo x) := by
  have hnat := (naturalStdTorusFourHomology_naturality
    (orderThreeShearAsFourTorus : C(StdTorus 4, StdTorus 4))
    orderThreeShearInteger orderThreeShearLift).2 x
  have hmaps :
      (standardFourTorusGammaSplit.symm : C(UnitAddCircle × StdTorus 3, StdTorus 4)).comp
          (orderThreeStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3)) =
        (orderThreeShearAsFourTorus : C(StdTorus 4, StdTorus 4)) := by
          ext u i
          fin_cases i <;> rfl
  have hcomp :
      integralSingularHomologyMap 2 standardFourTorusGammaSplit.symm
          (integralSingularHomologyMap 2
            (orderThreeStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3)) x) =
        integralSingularHomologyMap 2
          (orderThreeShearAsFourTorus : C(StdTorus 4, StdTorus 4)) x := by
    rw [integralSingularHomologyMap_comp_wang]
    rw [hmaps]
  rw [gammaProductHomologyTwo_apply]
  rw [hcomp]
  exact hnat

private theorem orderFourShear_homologyTwo (x) :
    gammaProductHomologyTwo
        (integralSingularHomologyMap 2 orderFourStandardGammaShear x) =
      standardExteriorSquareMap orderFourShearInteger
        (naturalStdTorusFourHomologyTwo x) := by
  have hnat := (naturalStdTorusFourHomology_naturality
    (orderFourShearAsFourTorus : C(StdTorus 4, StdTorus 4))
    orderFourShearInteger orderFourShearLift).2 x
  have hmaps :
      (standardFourTorusGammaSplit.symm : C(UnitAddCircle × StdTorus 3, StdTorus 4)).comp
          (orderFourStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3)) =
        (orderFourShearAsFourTorus : C(StdTorus 4, StdTorus 4)) := by
          ext u i
          fin_cases i <;> rfl
  have hcomp :
      integralSingularHomologyMap 2 standardFourTorusGammaSplit.symm
          (integralSingularHomologyMap 2
            (orderFourStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3)) x) =
        integralSingularHomologyMap 2
          (orderFourShearAsFourTorus : C(StdTorus 4, StdTorus 4)) x := by
    rw [integralSingularHomologyMap_comp_wang]
    rw [hmaps]
  rw [gammaProductHomologyTwo_apply]
  rw [hcomp]
  exact hnat

/-- The order-three gamma shear on `(01,02,03,12,13,23)`. -/
public theorem orderThreeGammaShear_homologyTwo_coordinates (x) :
    gammaProductHomologyTwo
        (integralSingularHomologyMap 2 orderThreeStandardGammaShear
          (naturalStdTorusFourHomologyTwo.symm x)) =
      ![-x 0, -x 1, -x 2, x 3 - 4 * x 0 - 2 * x 1,
        x 4 - 2 * x 2, x 5 + 4 * x 2] := by
  rw [orderThreeShear_homologyTwo,
    naturalStdTorusFourHomologyTwo.apply_symm_apply]
  funext i
  fin_cases i <;>
    simp [standardExteriorSquareMap, standardSecondCompoundMatrix,
      orderThreeShearInteger, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      standardPeriodPairFirst, standardPeriodPairSecond] <;> ring

/-- The order-four gamma shear on `(01,02,03,12,13,23)`. -/
public theorem orderFourGammaShear_homologyTwo_coordinates (x) :
    gammaProductHomologyTwo
        (integralSingularHomologyMap 2 orderFourStandardGammaShear
          (naturalStdTorusFourHomologyTwo.symm x)) =
      ![x 0, x 1, x 2, x 3 - 3 * x 0 - 3 * x 1,
        x 4 - 3 * x 2, x 5 + 3 * x 2] := by
  rw [orderFourShear_homologyTwo,
    naturalStdTorusFourHomologyTwo.apply_symm_apply]
  funext i
  fin_cases i <;>
    simp [standardExteriorSquareMap, standardSecondCompoundMatrix,
      orderFourShearInteger, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      standardPeriodPairFirst, standardPeriodPairSecond] <;> ring

end SphereSixComplex.Topology.EllipticGammaShearDegreeTwoCoordinates

end

end
