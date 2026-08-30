module

public import SphereSixComplex.Topology.NormalizedFiniteOrderAdditiveCircleSweep
public import SphereSixComplex.Topology.StandardThreeTorusProductWangBoundary
public import SphereSixComplex.Topology.StandardThreeTorusProductDegreeTwoCoordinates
public import SphereSixComplex.Topology.StandardThreeTorusDegreeOneCoordinates

/-!
# The circle-slant formula for the product Wang boundary

The finite-order orbit-sweep theorem at order one identifies the canonical product Wang boundary
on positive circle cross-products.  The explicit torus coordinates then determine the boundary
on all of `H₂(S¹ × T³)`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.CanonicalProductWangBoundarySlant

open CircleProductIdentityMappingTorus
open FiniteCyclicMappingTorusWangNaturality
open FiniteCyclicThreeTorusWangNaturality
open NormalizedFiniteOrderAdditiveCircleSweep
open NormalizedAffineMappingTorusCover
open PaperAffineCyclicReducedFiberMappingTorus
open PositiveCircleCross
open StandardThreeTorusProductWangBoundary
open StandardTorusHomology

/-- At order one, orbit-sweep naturality identifies the canonical product boundary on every
positive circle cross-product. -/
public theorem canonicalProductWangBoundary_positiveCircleCross
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G]
    (c : C(StdTorus 1, G)) :
    canonicalProductWangBoundary 1 (positiveCircleCross c) =
      integralSingularHomologyMap 1 c standardCircleHomologyGenerator := by
  let phi : G ≃ₜ+ G := ContinuousAddEquiv.refl G
  have hpow : phi.toHomeomorph ^ 1 = 1 := by rfl
  obtain ⟨S⟩ := normalizedFiniteOrderAdditiveCircleSweep 1 phi hpow
  calc
    canonicalProductWangBoundary 1 (positiveCircleCross c) =
        (circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross c)) := by
      symm
      rw [S.boundary_square]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, pow_zero]
      rw [show ((1 : G ≃ₜ G) : C(G, G)) = ContinuousMap.id G by rfl,
        integralSingularHomologyMap_id_wang]
    _ = (circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1).boundary
        (S.fixedSweep (orbitNorm 1 phi hpow c)) := by rw [S.normalizedCover_cross]
    _ = integralSingularHomologyMap 1 (orbitNorm 1 phi hpow c).1
        standardCircleHomologyGenerator := S.boundary_fixedSweep _
    _ = integralSingularHomologyMap 1 c standardCircleHomologyGenerator := by
      rw [orbitNorm_value]
      simp [loopAction]

public theorem canonicalProductWangBoundary_positiveGenerator :
    canonicalProductWangBoundary 1 positiveCircleProductGenerator =
      standardCircleHomologyGenerator := by
  have hcross : positiveCircleCross (ContinuousMap.id (StdTorus 1)) =
      positiveCircleProductGenerator := by
    unfold positiveCircleCross
    rw [show circleProductMap (ContinuousMap.id (StdTorus 1)) =
      ContinuousMap.id (UnitAddCircle × StdTorus 1) by
        ext x <;> rfl]
    rw [integralSingularHomologyMap_id_wang]
  rw [← hcross, canonicalProductWangBoundary_positiveCircleCross]
  rw [integralSingularHomologyMap_id_wang]

public def degreeTwoCoordinateToInt : (Fin (stdTorusTwoRank 2) → ℤ) ≃+ ℤ where
  toFun f := f standardTwoTorusDegreeTwoIndex
  invFun z := fun _ ↦ z
  left_inv f := by
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Integral coordinate on the second homology of the product of two positive circles. -/
public def circleProdCircleHomologyTwo :
  IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1) ≃+ ℤ :=
  (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).trans
    ((stdTorusHomologyTwo 2).trans degreeTwoCoordinateToInt)

@[simp]
public theorem circleProdCircleHomologyTwo_positiveGenerator :
    circleProdCircleHomologyTwo positiveCircleProductGenerator = 1 := by
  simp [circleProdCircleHomologyTwo, positiveCircleProductGenerator,
    standardTwoTorusHomologyGenerator, degreeTwoCoordinateToInt]

/-- The slant theorem evaluates the product boundary on every two-dimensional class of the
circle product. -/
public theorem canonicalProductWangBoundary_circle_coordinates
    (z : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1)) :
    canonicalProductWangBoundary 1 z =
      circleProdCircleHomologyTwo z • standardCircleHomologyGenerator := by
  have hz : z = circleProdCircleHomologyTwo z • positiveCircleProductGenerator := by
    apply circleProdCircleHomologyTwo.injective
    simp
  calc
    canonicalProductWangBoundary 1 z =
        canonicalProductWangBoundary 1
          (circleProdCircleHomologyTwo z • positiveCircleProductGenerator) :=
      congrArg _ hz
    _ = circleProdCircleHomologyTwo z •
        canonicalProductWangBoundary 1 positiveCircleProductGenerator :=
      map_zsmul (canonicalProductWangBoundary 1) _ _
    _ = _ := by
      rw [canonicalProductWangBoundary_positiveGenerator]

private theorem gammaSplit_cross_coordinateCircle (i : Fin 3) :
    ((standardFourTorusGammaSplit.symm :
        C(UnitAddCircle × StdTorus 3, StdTorus 4)).comp
      (circleProductMap (standardThreeTorusCoordinateCircle i))).comp
        (circleProdStandardCircleHomeomorph.symm :
          C(StdTorus 2, UnitAddCircle × StdTorus 1)) =
      standardFourTorusCoordinateTwoTorus ⟨i.val, by omega⟩ := by
  ext z j
  fin_cases i <;> fin_cases j <;> rfl

@[simp]
public theorem productHomologyTwo_positiveCircleCross_coordinateCircle (i : Fin 3) :
    productHomologyTwo (positiveCircleCross (standardThreeTorusCoordinateCircle i)) =
      Pi.single ⟨i.val, by omega⟩ 1 := by
  change naturalStdTorusFourHomologyTwo
      (integralSingularHomologyMap 2 standardFourTorusGammaSplit.symm
        (integralSingularHomologyMap 2
          (circleProductMap (standardThreeTorusCoordinateCircle i))
          (integralSingularHomologyMap 2 circleProdStandardCircleHomeomorph.symm
            standardTwoTorusHomologyGenerator))) = _
  rw [integralSingularHomologyMap_comp_wang,
    integralSingularHomologyMap_comp_wang,
    gammaSplit_cross_coordinateCircle]
  change standardFourTorusCanonicalHomologyTwo
      (standardFourTorusCoordinateTwoTorusHomologyClass ⟨i.val, by omega⟩) = _
  exact standardFourTorusCoordinateTwoTorusHom_coordinateHomologyClass _

private theorem canonicalBoundary_cross_coordinateCircle (i : Fin 3) :
    canonicalProductWangBoundary 1
        (positiveCircleCross (standardThreeTorusCoordinateCircle i)) =
      standardThreeTorusCoordinateHomologyClass i := by
  exact canonicalProductWangBoundary_positiveCircleCross _

private theorem orientedBoundary_cross_coordinateCircle (i : Fin 3) :
    orientedProductBoundary
        (positiveCircleCross (standardThreeTorusCoordinateCircle i)) =
      standardThreeTorusCoordinateHomologyClass i := by
  apply standardThreeTorusHomologyOne.injective
  rw [standardThreeTorusHomologyOne_orientedProductBoundary,
    productHomologyTwo_positiveCircleCross_coordinateCircle]
  change _ = standardThreeTorusDegreeOneCoordinateHom
    (standardThreeTorusCoordinateHomologyClass i)
  rw [standardThreeTorusDegreeOneCoordinateHom_coordinateClass]
  funext j
  fin_cases i <;> fin_cases j <;> simp [baseCrossDegreeOne]

private def crossPart
    (z : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3)) :=
  ∑ i, (baseCrossDegreeOne (productHomologyTwo z)) i •
    positiveCircleCross (standardThreeTorusCoordinateCircle i)

private def fibrePart
    (z : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3)) :=
  integralSingularHomologyMap 2 (circleProductFiberInclusion (X := StdTorus 3))
    (standardThreeTorusHomologyTwo.symm (fibreDegreeTwo (productHomologyTwo z)))

private theorem crossPart_add_fibrePart
    (z : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3)) :
    crossPart z + fibrePart z = z := by
  apply productHomologyTwo.injective
  rw [map_add, crossPart, map_sum]
  simp only [map_zsmul, productHomologyTwo_positiveCircleCross_coordinateCircle]
  rw [fibrePart, productHomologyTwo_fiberInclusion,
    standardThreeTorusHomologyTwo.apply_symm_apply]
  funext j
  fin_cases j <;> simp [joinCoordinates, baseCrossDegreeOne, fibreDegreeTwo,
    Fin.sum_univ_succ]

private theorem canonicalBoundary_eq_orientedProductBoundary
    (z : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3)) :
    canonicalProductWangBoundary 1 z = orientedProductBoundary z := by
  rw [← crossPart_add_fibrePart z, map_add, map_add, crossPart, map_sum, map_sum]
  simp only [map_zsmul, canonicalBoundary_cross_coordinateCircle,
    orientedBoundary_cross_coordinateCircle]
  have hcanonical : canonicalProductWangBoundary 1 (fibrePart z) = 0 := by
    apply canonicalProductWang_exact 1 |>.apply_apply_eq_zero
  have horiented : orientedProductBoundary (fibrePart z) = 0 := by
    apply exact_fiberInclusion_orientedProductBoundary.apply_apply_eq_zero
  rw [hcanonical, horiented]

/-- Exact formula for the canonical product Wang boundary on `S¹ × T³`. -/
public theorem canonicalProductWangBoundary_standardThreeTorus
    (z : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3)) :
    standardThreeTorusHomologyOne (canonicalProductWangBoundary 1 z) =
      fun (i : Fin 3) ↦
        standardCircleProdThreeTorusHomologyTwo z ⟨i.val, by omega⟩ := by
  rw [canonicalBoundary_eq_orientedProductBoundary,
    standardThreeTorusHomologyOne_orientedProductBoundary]
  funext i
  fin_cases i <;> rfl

end SphereSixComplex.Topology.CanonicalProductWangBoundarySlant

end

end
