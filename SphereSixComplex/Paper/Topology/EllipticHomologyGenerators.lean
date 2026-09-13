module

public import SphereSixComplex.Paper.Topology.EllipticDegreeTwoBasisFromOrbitSweep
import all SphereSixComplex.Paper.Topology.EllipticDegreeTwoBasisFromOrbitSweep

open AlgebraicTopology

namespace SphereSixComplex.Topology.EllipticHomologyGenerators

open EllipticReducedFiberMappingTorus
open EllipticSpecializedNormalizedCoverSweep
open EllipticDegreeTwoBasisFromOrbitSweep EllipticThreeTorusExplicitOrbitSweepHomology
open EllipticThreeTorusRankOneMappingTorusCoordinates EllipticThreeTorusClutchingDegreeTwo
open SphereSixComplex.CircleMappingTorusHomologyBases StandardTorusHomology

private theorem generated {H : Type} [AddCommGroup H] (e : H ≃+ (Fin 2 → ℤ))
    (s t : H) (hs : e s = ![1, 0]) (ht : e t = ![0, 1]) (x : H) :
    ∃ a b : ℤ, x = a • s + b • t := by
  refine ⟨e x 0, e x 1, e.injective ?_⟩
  rw [map_add, map_zsmul, map_zsmul, hs, ht]
  funext i
  fin_cases i <;> simp

public theorem orderThree_homologyTwo_generated :
    let s := -orderThreeFixedLoopSweep
    let t := (circleMappingTorusWangPresentationOfCover orderThreeThreeTorusClutching 1).inclusion
      (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))
    ∀ x, ∃ a b : ℤ, x = a • s + b • t :=
  generated orderThreeMappingTorusCoordinates orderThreeSweepGenerator
    orderThreeFiberGenerator (orderThreeNegatedTotalAddEquiv_section _ _)
      (orderThreeNegatedTotalAddEquiv_fiberCoordinateZero _ _)

public theorem orderFour_homologyTwo_generated :
    let s := orderFourFixedLoopSweep
    let t := (circleMappingTorusWangPresentationOfCover orderFourThreeTorusClutching 1).inclusion
      (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))
    ∀ x, ∃ a b : ℤ, x = a • s + b • t :=
  generated orderFourMappingTorusCoordinates orderFourSweepGenerator
    orderFourFiberGenerator (orderFourTotalAddEquiv_section _ _)
      (orderFourTotalAddEquiv_fiberCoordinateZero _ _)

open scoped ContinuousMap
open Geometry.EllipticFamilySpecialization FiniteCoverPerfectPairing EllipticFilling

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

public theorem orderThree_projected_planes :
    integralSingularHomologyMap 2
      (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F : C(_, _))
      (orderThreeProjectedDegreeTwoGenerator F 1 +
        2 • orderThreeProjectedDegreeTwoGenerator F 3) =
      -orderThreeFixedLoopSweep := by
  have h := orderThree_projection_in_mappingTorus F orderThreeBasisCombination
  rw [orderThree_cover_basisCombination] at h
  simpa only [orderThreeBasisCombination, map_add, map_nsmul,
    orderThreeProjectedDegreeTwoGenerator, orderThreeSweepGenerator] using h

public theorem orderThree_projected_transverse :
    integralSingularHomologyMap 2
      (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F : C(_, _))
      (orderThreeProjectedDegreeTwoGenerator F 3) =
    (circleMappingTorusWangPresentationOfCover orderThreeThreeTorusClutching 1).inclusion
      (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) := by
  have h := orderThree_projection_in_mappingTorus F (Pi.single 3 1)
  rw [orderThree_cover_coordinateThree] at h
  exact h

public theorem orderFour_projected_planes :
    integralSingularHomologyMap 2
      (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F : C(_, _))
      (orderFourProjectedDegreeTwoGenerator F 0 +
        3 • orderFourProjectedDegreeTwoGenerator F 3) =
      2 • orderFourFixedLoopSweep := by
  have h := orderFour_projection_in_mappingTorus F orderFourBasisCombination
  rw [orderFour_cover_basisCombination] at h
  simpa only [orderFourBasisCombination, map_add, map_nsmul,
    orderFourProjectedDegreeTwoGenerator, orderFourSweepGenerator] using h

public theorem orderFour_projected_transverse :
    integralSingularHomologyMap 2
      (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F : C(_, _))
      (orderFourProjectedDegreeTwoGenerator F 3) =
    (circleMappingTorusWangPresentationOfCover orderFourThreeTorusClutching 1).inclusion
      (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) := by
  have h := orderFour_projection_in_mappingTorus F (Pi.single 3 1)
  rw [orderFour_cover_coordinateThree] at h
  exact h

public theorem orderThree_homologyTwo_map_eq_zero
    {G : Type} [AddCommGroup G]
    (f : IntegralSingularHomology 2 (orderThreeReducedCentralFiber F) →+ G)
    (hs : f ((integralSingularHomologyEquiv 2
      (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F)).symm
        (-orderThreeFixedLoopSweep)) = 0)
    (ht : f (orderThreeProjectedDegreeTwoGenerator F 3) = 0) : f = 0 := by
  let e := integralSingularHomologyEquiv 2
    (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F)
  ext x
  change f x = 0
  obtain ⟨a, b, h⟩ := orderThree_homologyTwo_generated (e x)
  have hx : x = a • e.symm (-orderThreeFixedLoopSweep) +
      b • orderThreeProjectedDegreeTwoGenerator F 3 := by
    apply e.injective
    rw [map_add, map_zsmul, map_zsmul, e.apply_symm_apply]
    exact h.trans (congrArg (fun y => a • (-orderThreeFixedLoopSweep) + b • y)
      (orderThree_projected_transverse F).symm)
  rw [hx, map_add, map_zsmul, map_zsmul, hs, ht]
  simp

public theorem orderFour_homologyTwo_map_eq_zero
    {G : Type} [AddCommGroup G]
    (f : IntegralSingularHomology 2 (orderFourReducedCentralFiber F) →+ G)
    (hs : f ((integralSingularHomologyEquiv 2
      (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F)).symm
        (orderFourFixedLoopSweep)) = 0)
    (ht : f (orderFourProjectedDegreeTwoGenerator F 3) = 0) : f = 0 := by
  let e := integralSingularHomologyEquiv 2
    (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F)
  ext x
  change f x = 0
  obtain ⟨a, b, h⟩ := orderFour_homologyTwo_generated (e x)
  have hx : x = a • e.symm (orderFourFixedLoopSweep) +
      b • orderFourProjectedDegreeTwoGenerator F 3 := by
    apply e.injective
    rw [map_add, map_zsmul, map_zsmul, e.apply_symm_apply]
    exact h.trans (congrArg (fun y => a • (orderFourFixedLoopSweep) + b • y)
      (orderFour_projected_transverse F).symm)
  rw [hx, map_add, map_zsmul, map_zsmul, hs, ht]
  simp

public theorem orderThree_projected_planes_map_eq_zero
    {G : Type} [AddCommGroup G]
    (f : IntegralSingularHomology 2 (orderThreeReducedCentralFiber F) →+ G)
    (hs : f ((integralSingularHomologyEquiv 2
      (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F)).symm
        (-orderThreeFixedLoopSweep)) = 0) :
    f (orderThreeProjectedDegreeTwoGenerator F 1) +
      2 • f (orderThreeProjectedDegreeTwoGenerator F 3) = 0 := by
  let e := integralSingularHomologyEquiv 2
    (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F)
  have h : e (orderThreeProjectedDegreeTwoGenerator F 1 +
      2 • orderThreeProjectedDegreeTwoGenerator F 3) =
      (-orderThreeFixedLoopSweep) := orderThree_projected_planes F
  have hh := congrArg (fun z => f (e.symm z)) h
  change f (e.symm (-orderThreeFixedLoopSweep)) = 0 at hs
  simpa only [e.symm_apply_apply, map_add, map_nsmul, hs, nsmul_zero] using hh

public theorem orderFour_projected_planes_map_eq_zero
    {G : Type} [AddCommGroup G]
    (f : IntegralSingularHomology 2 (orderFourReducedCentralFiber F) →+ G)
    (hs : f ((integralSingularHomologyEquiv 2
      (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F)).symm
        (orderFourFixedLoopSweep)) = 0) :
    f (orderFourProjectedDegreeTwoGenerator F 0) +
      3 • f (orderFourProjectedDegreeTwoGenerator F 3) = 0 := by
  let e := integralSingularHomologyEquiv 2
    (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F)
  have h : e (orderFourProjectedDegreeTwoGenerator F 0 +
      3 • orderFourProjectedDegreeTwoGenerator F 3) =
      2 • (orderFourFixedLoopSweep) := orderFour_projected_planes F
  have hh := congrArg (fun z => f (e.symm z)) h
  change f (e.symm orderFourFixedLoopSweep) = 0 at hs
  simpa only [e.symm_apply_apply, map_add, map_nsmul, hs, nsmul_zero] using hh

public theorem homologyTwo_maps_eq_zero
    {G : Type} [AddCommGroup G]
    (f₃ : IntegralSingularHomology 2 (orderThreeReducedCentralFiber F) →+ G)
    (f₄ : IntegralSingularHomology 2 (orderFourReducedCentralFiber F) →+ G)
    (hs₃ : f₃ ((integralSingularHomologyEquiv 2
      (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F)).symm
        (-orderThreeFixedLoopSweep)) = 0)
    (hs₄ : f₄ ((integralSingularHomologyEquiv 2
      (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F)).symm
        orderFourFixedLoopSweep) = 0)
    (h₀ : f₃ (orderThreeProjectedDegreeTwoGenerator F 0) =
      f₄ (orderFourProjectedDegreeTwoGenerator F 0))
    (h₃ : f₃ (orderThreeProjectedDegreeTwoGenerator F 3) =
      f₄ (orderFourProjectedDegreeTwoGenerator F 3))
    (hrel : f₃ (orderThreeProjectedDegreeTwoGenerator F 0) =
      2 • f₃ (orderThreeProjectedDegreeTwoGenerator F 1)) : f₃ = 0 ∧ f₄ = 0 := by
  have hthree := orderThree_projected_planes_map_eq_zero F f₃ hs₃
  have hfour := orderFour_projected_planes_map_eq_zero F f₄ hs₄
  rw [← h₀, ← h₃] at hfour
  have ht : f₃ (orderThreeProjectedDegreeTwoGenerator F 3) = 0 := by
    calc
      _ = 2 • (f₃ (orderThreeProjectedDegreeTwoGenerator F 1) +
          2 • f₃ (orderThreeProjectedDegreeTwoGenerator F 3)) -
          (f₃ (orderThreeProjectedDegreeTwoGenerator F 0) +
            3 • f₃ (orderThreeProjectedDegreeTwoGenerator F 3)) := by
        rw [hrel]
        abel
      _ = 0 := by rw [hthree, hfour]; simp
  exact ⟨orderThree_homologyTwo_map_eq_zero F f₃ hs₃ ht,
    orderFour_homologyTwo_map_eq_zero F f₄ hs₄ (h₃.symm.trans ht)⟩

end SphereSixComplex.Topology.EllipticHomologyGenerators
