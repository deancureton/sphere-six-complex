module

public import SphereSixComplex.Topology.StandardThreeTorusDegreeTwoCoordinates
public import SphereSixComplex.Topology.StandardThreeTorusDegreeOneCoordinates
public import SphereSixComplex.Topology.PaperAffineCyclicReducedFiberMappingTorus

/-!
# Degree-two action of the elliptic three-torus clutching maps

The explicit clutching maps extend over the head coordinate of the standard four-torus.  The
established natural four-torus calculation then gives their action on `H₂(T³;ℤ)`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix
open scoped ContinuousMap

namespace SphereSixComplex.Topology.EllipticThreeTorusClutchingDegreeTwo

open StandardTorusHomology
open Geometry.ComplexTorus
open PaperAffineCyclicReducedFiberMappingTorus

private def orderThreeExtension : StdTorus 4 ≃ₜ StdTorus 4 where
  toFun u := Fin.cons (u 0) (orderThreeThreeTorusClutching (Fin.tail u))
  invFun u := Fin.cons (u 0) (orderThreeThreeTorusClutching.symm (Fin.tail u))
  left_inv u := by
    funext i
    fin_cases i <;> simp [orderThreeThreeTorusClutching, Fin.tail] <;> abel
  right_inv u := by
    funext i
    fin_cases i <;> simp [orderThreeThreeTorusClutching, Fin.tail]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def orderFourExtension : StdTorus 4 ≃ₜ StdTorus 4 where
  toFun u := Fin.cons (u 0) (orderFourThreeTorusClutching (Fin.tail u))
  invFun u := Fin.cons (u 0) (orderFourThreeTorusClutching.symm (Fin.tail u))
  left_inv u := by
    funext i
    fin_cases i <;> simp [orderFourThreeTorusClutching, Fin.tail]
  right_inv u := by
    funext i
    fin_cases i <;> simp [orderFourThreeTorusClutching, Fin.tail]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def orderThreeIntegerExtension : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun u := ![u 0, u 2, -u 1 - u 2, u 1 + u 3]
  invFun u := ![u 0, -u 1 - u 2, u 1, u 3 + u 1 + u 2]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' n x := by funext i; fin_cases i <;> simp <;> ring

private def orderFourIntegerExtension : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun u := ![u 0, -u 2, u 1, u 2 + u 3]
  invFun u := ![u 0, u 2, -u 1, u 3 + u 1]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' n x := by funext i; fin_cases i <;> simp <;> ring

private def orderThreeRealExtension : (Fin 4 → ℝ) ≃+ (Fin 4 → ℝ) where
  toFun u := ![u 0, u 2, -u 1 - u 2, u 1 + u 3]
  invFun u := ![u 0, -u 1 - u 2, u 1, u 3 + u 1 + u 2]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring

private def orderFourRealExtension : (Fin 4 → ℝ) ≃+ (Fin 4 → ℝ) where
  toFun u := ![u 0, -u 2, u 1, u 2 + u 3]
  invFun u := ![u 0, u 2, -u 1, u 3 + u 1]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring

private def orderThreeExtensionLift :
    StandardFourTorusEquivariantLift
      (orderThreeExtension : C(StdTorus 4, StdTorus 4)) orderThreeIntegerExtension where
  lift := orderThreeRealExtension
  map_projection r := by
    funext i
    fin_cases i <;>
      simp [orderThreeExtension, orderThreeRealExtension, Fin.tail,
        orderThreeThreeTorusClutching, standardFourTorusProjection]
  map_integer n := by
    funext i
    fin_cases i <;>
      norm_num [orderThreeRealExtension, orderThreeIntegerExtension, integerToReal] <;> ring

private def orderFourExtensionLift :
    StandardFourTorusEquivariantLift
      (orderFourExtension : C(StdTorus 4, StdTorus 4)) orderFourIntegerExtension where
  lift := orderFourRealExtension
  map_projection r := by
    funext i
    fin_cases i <;>
      simp [orderFourExtension, orderFourRealExtension, Fin.tail,
        orderFourThreeTorusClutching, standardFourTorusProjection]
  map_integer n := by
    funext i
    fin_cases i <;>
      norm_num [orderFourRealExtension, orderFourIntegerExtension, integerToReal] <;> ring

private theorem orderThreeExtension_comp_tailInclusion :
    (orderThreeExtension : C(StdTorus 4, StdTorus 4)).comp
        standardThreeTorusTailInclusion =
      standardThreeTorusTailInclusion.comp orderThreeThreeTorusClutching := by
  ext z i
  fin_cases i <;> rfl

private theorem orderFourExtension_comp_tailInclusion :
    (orderFourExtension : C(StdTorus 4, StdTorus 4)).comp
        standardThreeTorusTailInclusion =
      standardThreeTorusTailInclusion.comp orderFourThreeTorusClutching := by
  ext z i
  fin_cases i <;> rfl

/-- Matrix of the order-three clutching action on `(12,13,23)`. -/
public def orderThreeClutchingDegreeTwoMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     -1, 0, 1;
     1, -1, -1]

/-- Matrix of the order-four clutching action on `(12,13,23)`. -/
public def orderFourClutchingDegreeTwoMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, -1;
     1, 1, 0]

public def orderThreeClutchingDegreeOneMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     -1, -1, 0;
     1, 0, 1]

public def orderFourClutchingDegreeOneMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, -1, 0;
     1, 0, 0;
     0, 1, 1]

private theorem orderThreeExtension_comp_tailInclusionOne :
    (orderThreeExtension : C(StdTorus 4, StdTorus 4)).comp
        standardThreeTorusTailInclusionOne =
      standardThreeTorusTailInclusionOne.comp orderThreeThreeTorusClutching := by
  ext z i
  fin_cases i <;> rfl

private theorem orderFourExtension_comp_tailInclusionOne :
    (orderFourExtension : C(StdTorus 4, StdTorus 4)).comp
        standardThreeTorusTailInclusionOne =
      standardThreeTorusTailInclusionOne.comp orderFourThreeTorusClutching := by
  ext z i
  fin_cases i <;> rfl

public theorem orderThreeThreeTorusClutching_homologyOne (x) :
    standardThreeTorusHomologyOne
        (integralSingularHomologyMap 1 orderThreeThreeTorusClutching x) =
      orderThreeClutchingDegreeOneMatrix *ᵥ standardThreeTorusHomologyOne x := by
  have hnat := (naturalStdTorusFourHomology_naturality
    (orderThreeExtension : C(StdTorus 4, StdTorus 4))
    orderThreeIntegerExtension orderThreeExtensionLift).1
  have hcomp :
      integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne
          (integralSingularHomologyMap 1 orderThreeThreeTorusClutching x) =
        integralSingularHomologyMap 1 orderThreeExtension
          (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x) := by
    rw [integralSingularHomologyMap_comp_wang,
      integralSingularHomologyMap_comp_wang,
      orderThreeExtension_comp_tailInclusionOne]
  have h := hnat (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x)
  rw [← hcomp, standardThreeTorusTailInclusion_homologyOne_coordinates] at h
  have hx := standardThreeTorusTailInclusion_homologyOne_coordinates x
  rw [hx] at h
  simp [orderThreeIntegerExtension] at h
  rcases h with ⟨h0, h1, h2⟩
  funext i
  fin_cases i
  · simpa [orderThreeClutchingDegreeOneMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using h0
  · norm_num [orderThreeClutchingDegreeOneMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h1 ⊢
    omega
  · simpa [orderThreeClutchingDegreeOneMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using h2

public theorem orderFourThreeTorusClutching_homologyOne (x) :
    standardThreeTorusHomologyOne
        (integralSingularHomologyMap 1 orderFourThreeTorusClutching x) =
      orderFourClutchingDegreeOneMatrix *ᵥ standardThreeTorusHomologyOne x := by
  have hnat := (naturalStdTorusFourHomology_naturality
    (orderFourExtension : C(StdTorus 4, StdTorus 4))
    orderFourIntegerExtension orderFourExtensionLift).1
  have hcomp :
      integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne
          (integralSingularHomologyMap 1 orderFourThreeTorusClutching x) =
        integralSingularHomologyMap 1 orderFourExtension
          (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x) := by
    rw [integralSingularHomologyMap_comp_wang,
      integralSingularHomologyMap_comp_wang,
      orderFourExtension_comp_tailInclusionOne]
  have h := hnat (integralSingularHomologyMap 1 standardThreeTorusTailInclusionOne x)
  rw [← hcomp, standardThreeTorusTailInclusion_homologyOne_coordinates] at h
  have hx := standardThreeTorusTailInclusion_homologyOne_coordinates x
  rw [hx] at h
  simp [orderFourIntegerExtension] at h
  rcases h with ⟨h0, h1, h2⟩
  funext i
  fin_cases i
  · simpa [orderFourClutchingDegreeOneMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using h0
  · simpa [orderFourClutchingDegreeOneMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using h1
  · simpa [orderFourClutchingDegreeOneMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using h2

public theorem orderThreeThreeTorusClutching_homologyTwo (x) :
    standardThreeTorusHomologyTwo
        (integralSingularHomologyMap 2 orderThreeThreeTorusClutching x) =
      orderThreeClutchingDegreeTwoMatrix *ᵥ standardThreeTorusHomologyTwo x := by
  have hnat := (naturalStdTorusFourHomology_naturality
    (orderThreeExtension : C(StdTorus 4, StdTorus 4))
    orderThreeIntegerExtension orderThreeExtensionLift).2
  have hcomp :
      integralSingularHomologyMap 2 standardThreeTorusTailInclusion
          (integralSingularHomologyMap 2 orderThreeThreeTorusClutching x) =
        integralSingularHomologyMap 2 orderThreeExtension
          (integralSingularHomologyMap 2 standardThreeTorusTailInclusion x) := by
    rw [integralSingularHomologyMap_comp_wang,
      integralSingularHomologyMap_comp_wang,
      orderThreeExtension_comp_tailInclusion]
  have h := hnat (integralSingularHomologyMap 2 standardThreeTorusTailInclusion x)
  rw [← hcomp, standardThreeTorusTailInclusion_homologyTwo_coordinates] at h
  have hx := standardThreeTorusTailInclusion_homologyTwo_coordinates x
  rw [hx] at h
  funext i
  have hi := congrFun h (tailDegreeTwoIndex i)
  fin_cases i <;>
    simpa [standardExteriorSquareMap, standardSecondCompoundMatrix,
      orderThreeIntegerExtension, orderThreeClutchingDegreeTwoMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      standardPeriodPairFirst, standardPeriodPairSecond, tailDegreeTwoIndex] using hi

public theorem orderFourThreeTorusClutching_homologyTwo (x) :
    standardThreeTorusHomologyTwo
        (integralSingularHomologyMap 2 orderFourThreeTorusClutching x) =
      orderFourClutchingDegreeTwoMatrix *ᵥ standardThreeTorusHomologyTwo x := by
  have hnat := (naturalStdTorusFourHomology_naturality
    (orderFourExtension : C(StdTorus 4, StdTorus 4))
    orderFourIntegerExtension orderFourExtensionLift).2
  have hcomp :
      integralSingularHomologyMap 2 standardThreeTorusTailInclusion
          (integralSingularHomologyMap 2 orderFourThreeTorusClutching x) =
        integralSingularHomologyMap 2 orderFourExtension
          (integralSingularHomologyMap 2 standardThreeTorusTailInclusion x) := by
    rw [integralSingularHomologyMap_comp_wang,
      integralSingularHomologyMap_comp_wang,
      orderFourExtension_comp_tailInclusion]
  have h := hnat (integralSingularHomologyMap 2 standardThreeTorusTailInclusion x)
  rw [← hcomp, standardThreeTorusTailInclusion_homologyTwo_coordinates] at h
  have hx := standardThreeTorusTailInclusion_homologyTwo_coordinates x
  rw [hx] at h
  funext i
  have hi := congrFun h (tailDegreeTwoIndex i)
  fin_cases i <;>
    simpa [standardExteriorSquareMap, standardSecondCompoundMatrix,
      orderFourIntegerExtension, orderFourClutchingDegreeTwoMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      standardPeriodPairFirst, standardPeriodPairSecond, tailDegreeTwoIndex] using hi

end SphereSixComplex.Topology.EllipticThreeTorusClutchingDegreeTwo

end

end
