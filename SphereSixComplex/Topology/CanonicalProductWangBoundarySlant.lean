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
open CyclicAngularFundamentalDomain

private theorem splitOfFreeQuotient_snd
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] {m : ℕ}
    (i : A →+ B) (q : B →+ (Fin m → ℤ))
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : Function.Exact i q) (z : B) :
    (splitOfFreeQuotient i q hi hq hex z).2 = q z := by
  let e := splitOfFreeQuotient i q hi hq hex
  have h := congrArg q (e.symm_apply_apply z)
  change q (i (e z).1 + freeSection q hq (e z).2) = q z at h
  rw [map_add, hex.apply_apply_eq_zero, zero_add, freeSection_spec] at h
  exact h

private theorem reflMappingTorusHomologySplit_right
    {F : Type} [TopologicalSpace F] (k a m : ℕ)
    (e1 : IntegralSingularHomology (k + 1) F ≃+ (Fin a → ℤ))
    (e0 : IntegralSingularHomology k F ≃+ (Fin m → ℤ))
    (z : IntegralSingularHomology (k + 1)
      (CircleMappingTorus (Homeomorph.refl F))) (j : Fin m) :
    reflMappingTorusHomologySplit k a m e1 e0 z
        (finSumFinEquiv (Sum.inr j)) =
      e0 ((circleMappingTorusWangPresentationOfCover
        (Homeomorph.refl F) k).boundary z) j := by
  classical
  set P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) k
  have hhigh : P.highDifference = 0 :=
    circleMonodromyDifference_refl (F := F) (k + 1)
  have hlow : P.lowDifference = 0 := circleMonodromyDifference_refl (F := F) k
  have hi : Function.Injective P.inclusion := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨c, hc⟩ := (P.exact_highDifference_inclusion b).mp hb
    rw [hhigh] at hc
    simpa using hc.symm
  have hbsurj : Function.Surjective P.boundary := by
    intro y
    exact (P.exact_boundary_lowDifference y).mp (by rw [hlow]; rfl)
  let q : IntegralSingularHomology (k + 1)
      (CircleMappingTorus (Homeomorph.refl F)) →+ (Fin m → ℤ) :=
    e0.toAddMonoidHom.comp P.boundary
  have hq : Function.Surjective q := e0.surjective.comp hbsurj
  have hex : Function.Exact P.inclusion q := by
    intro b
    rw [← P.exact_inclusion_boundary b]
    constructor
    · intro h
      have h' : e0 (P.boundary b) = 0 := h
      exact e0.injective (by rw [h', map_zero])
    · intro h
      show e0 (P.boundary b) = 0
      rw [h, map_zero]
  have hs := splitOfFreeQuotient_snd P.inclusion q hi hq hex z
  unfold reflMappingTorusHomologySplit
  simp only [AddEquiv.trans_apply, finArrowProdAddEquiv, AddEquiv.coe_mk,
    Equiv.coe_fn_mk, Equiv.symm_apply_apply, Sum.elim_inr]
  have ht :
      ((e1.prodCongr (AddEquiv.refl _))
        ((splitOfFreeQuotient P.inclusion q hi hq hex) z)).2 = q z := by
    change (splitOfFreeQuotient P.inclusion q hi hq hex z).2 = q z
    exact hs
  simpa [q] using congrFun ht j

private theorem realMappingTorusHomeomorph_intervalProjection
    {X : Type} [TopologicalSpace X] (phi : X ≃ₜ X) (p : unitInterval × X) :
    realMappingTorusHomeomorph phi (realMappingTorusIntervalProjection phi p) =
      circleMappingTorusCylinderProjection phi p := by
  let D := realMappingTorusClutchingData phi
  let e : CircleMappingTorus phi ≃ RealMappingTorus phi :=
    Equiv.ofBijective D.circleToTotal D.circleToTotal_bijective
  apply e.injective
  change D.circleToTotal
      (D.totalHomeomorphCircleMappingTorus (D.projection p)) =
    D.circleToTotal (circleMappingTorusCylinderProjection phi p)
  rw [show D.circleToTotal
      (D.totalHomeomorphCircleMappingTorus (D.projection p)) = D.projection p by
    exact D.totalHomeomorphCircleMappingTorus.symm_apply_apply _]
  exact D.circleToTotal_mk p

private theorem circleProduct_stdTorus_homeomorph :
    (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1)).trans
        (stdTorusMappingTorusHomeomorph 1) =
      circleProdStandardCircleHomeomorph := by
  apply Homeomorph.ext
  rintro ⟨s, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) s
  let u : unitInterval :=
    ⟨Int.fract t, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hreal :
      realMappingTorusIntervalProjection (Homeomorph.refl (StdTorus 1)) (u, x) =
        Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x) := by
    exact ((realMappingTorusMk_eq_iff (Homeomorph.refl (StdTorus 1))
      (t, x) ((u : ℝ), x)).mpr ⟨⌊t⌋, by
        rw [mappingTorusShift_apply]
        apply Prod.ext
        · simp [u]
        · change x = ((1 : StdTorus 1 ≃ₜ StdTorus 1) ^ ⌊t⌋) x
          rw [one_zpow]
          rfl⟩).symm
  have hcircle : (((u : ℝ) : UnitAddCircle)) = (t : UnitAddCircle) := by
    apply (unitAddCircle_eq_iff _ _).mpr
    refine ⟨-⌊t⌋, ?_⟩
    change Int.fract t - t = ((-⌊t⌋ : ℤ) : ℝ)
    rw [show Int.fract t = t - ⌊t⌋ by rfl]
    push_cast
    ring
  change stdTorusOfMappingTorus 1
      (realMappingTorusHomeomorph (Homeomorph.refl (StdTorus 1))
        (circleProductRealMappingTorusHomeomorph
          (realToCircleProduct (t, x)))) =
    Fin.cons (t : UnitAddCircle) x
  rw [circleProductRealMappingTorusHomeomorph_real, ← hreal,
    realMappingTorusHomeomorph_intervalProjection]
  exact congrArg
    (fun z : UnitAddCircle ↦ @Fin.cons 1 (fun _ : Fin 2 ↦ UnitAddCircle) z x) hcircle

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

/-- The canonical product Wang boundary of the selected degree-two generator has winding
coordinate `+1`. -/
public theorem canonicalProductWangBoundary_positiveGenerator_coordinate :
    standardCircleCanonicalHomologyOne
        (canonicalProductWangBoundary 1 positiveCircleProductGenerator) =
      Pi.single (0 : Fin 1) 1 := by
  let P := circleMappingTorusWangPresentationOfCover
    (Homeomorph.refl (StdTorus 1)) 1
  let eT := integralSingularHomologyEquiv 2 (stdTorusMappingTorusHomeomorph 1)
  let y := eT.symm standardTwoTorusHomologyGenerator
  have hcomp :
      (stdTorusMappingTorusHomeomorph 1 :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), StdTorus 2)).comp
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1)))) =
        (circleProdStandardCircleHomeomorph :
          C(UnitAddCircle × StdTorus 1, StdTorus 2)) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg (fun e : (UnitAddCircle × StdTorus 1) ≃ₜ StdTorus 2 ↦ e p)
      circleProduct_stdTorus_homeomorph
  have hy :
      integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
          positiveCircleProductGenerator = y := by
    apply eT.injective
    rw [eT.apply_symm_apply]
    change integralSingularHomologyMap 2
        (stdTorusMappingTorusHomeomorph 1 :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), StdTorus 2))
        (integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
          positiveCircleProductGenerator) = standardTwoTorusHomologyGenerator
    rw [integralSingularHomologyMap_comp_wang, hcomp]
    exact (integralSingularHomologyEquiv 2
      circleProdStandardCircleHomeomorph).apply_symm_apply _
  have hcoordinate :
      standardCircleCanonicalHomologyOne (P.boundary y) = Pi.single (0 : Fin 1) 1 := by
    funext j
    fin_cases j
    change standardCircleCanonicalHomologyOne (P.boundary y) 0 = 1
    dsimp [P]
    rw [← reflMappingTorusHomologySplit_right 1 0 1
      (stdTorusHomologyTwo 1) standardCircleCanonicalHomologyOne y 0]
    rw [← eT.symm_apply_apply y]
    change stdTorusHomologyTwo 2 (eT y)
      (finSumFinEquiv (Sum.inr (0 : Fin 1))) = 1
    rw [eT.apply_symm_apply]
    rw [show stdTorusHomologyTwo 2 standardTwoTorusHomologyGenerator =
        Pi.single standardTwoTorusDegreeTwoIndex 1 by
      exact (stdTorusHomologyTwo 2).apply_symm_apply _]
    rw [show finSumFinEquiv (Sum.inr (0 : Fin 1)) =
        standardTwoTorusDegreeTwoIndex by
      apply Fin.ext
      rfl]
    exact Pi.single_eq_same _ _
  change standardCircleCanonicalHomologyOne
      (P.boundary
        (integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
          positiveCircleProductGenerator)) = Pi.single (0 : Fin 1) 1
  rw [hy, hcoordinate]

public theorem canonicalProductWangBoundary_positiveGenerator :
    canonicalProductWangBoundary 1 positiveCircleProductGenerator =
      standardCircleHomologyGenerator := by
  apply standardCircleCanonicalHomologyOne.injective
  rw [canonicalProductWangBoundary_positiveGenerator_coordinate,
    standardCircleCanonicalHomologyOne_generator]

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
