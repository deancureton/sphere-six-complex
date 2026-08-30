module

public import SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality
public import SphereSixComplex.Topology.EllipticThreeTorusAdditiveOrbitSweep
public import SphereSixComplex.Topology.EllipticThreeTorusRankOneMappingTorusCoordinates

/-!
# Explicit homology of the elliptic three-torus orbit sweeps

The fibre part of finite-cover Wang naturality follows directly from the point-set formula for
the normalized affine cover.  A quotient homotopy also identifies clutching translates after
the cover, and explicit four-torus coordinates give the resulting order-three and order-four
cross-class relations without any orbit-sweep input.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.EllipticThreeTorusExplicitOrbitSweepHomology

open CanonicalProductWangBoundaryNaturality
open CanonicalProductWangBoundarySlant
open EllipticThreeTorusAdditiveOrbitSweep
open EllipticThreeTorusRankOneMappingTorusCoordinates
open FiniteCyclicMappingTorusWangNaturality
open FiniteCyclicThreeTorusWangNaturality
open Geometry.ComplexTorus
open NormalizedAffineMappingTorusCover
open NormalizedFiniteOrderAdditiveCircleSweep
open PaperAffineCyclicReducedFiberMappingTorus
open PositiveCircleCross
open StandardTorusHomology

variable {m : ℕ} [NeZero m]

private def orderThreeProductExtension : StdTorus 4 ≃ₜ StdTorus 4 where
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

private def orderFourProductExtension : StdTorus 4 ≃ₜ StdTorus 4 where
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

private def orderThreeProductIntegerExtension : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun u := ![u 0, u 2, -u 1 - u 2, u 1 + u 3]
  invFun u := ![u 0, -u 1 - u 2, u 1, u 3 + u 1 + u 2]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' n x := by funext i; fin_cases i <;> simp <;> ring

private def orderFourProductIntegerExtension : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun u := ![u 0, -u 2, u 1, u 2 + u 3]
  invFun u := ![u 0, u 2, -u 1, u 3 + u 1]
  left_inv u := by funext i; fin_cases i <;> simp
  right_inv u := by funext i; fin_cases i <;> simp
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' n x := by funext i; fin_cases i <;> simp <;> ring

private def orderThreeProductRealExtension : (Fin 4 → ℝ) ≃+ (Fin 4 → ℝ) where
  toFun u := ![u 0, u 2, -u 1 - u 2, u 1 + u 3]
  invFun u := ![u 0, -u 1 - u 2, u 1, u 3 + u 1 + u 2]
  left_inv u := by funext i; fin_cases i <;> simp <;> ring
  right_inv u := by funext i; fin_cases i <;> simp
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring

private def orderFourProductRealExtension : (Fin 4 → ℝ) ≃+ (Fin 4 → ℝ) where
  toFun u := ![u 0, -u 2, u 1, u 2 + u 3]
  invFun u := ![u 0, u 2, -u 1, u 3 + u 1]
  left_inv u := by funext i; fin_cases i <;> simp
  right_inv u := by funext i; fin_cases i <;> simp
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring

private def orderThreeProductExtensionLift :
    StandardFourTorusEquivariantLift
      (orderThreeProductExtension : C(StdTorus 4, StdTorus 4))
      orderThreeProductIntegerExtension where
  lift := orderThreeProductRealExtension
  map_projection r := by
    funext i
    fin_cases i <;>
      simp [orderThreeProductExtension, orderThreeProductRealExtension, Fin.tail,
        orderThreeThreeTorusClutching, standardFourTorusProjection]
  map_integer n := by
    funext i
    fin_cases i <;>
      norm_num [orderThreeProductRealExtension, orderThreeProductIntegerExtension,
        integerToReal]

private def orderFourProductExtensionLift :
    StandardFourTorusEquivariantLift
      (orderFourProductExtension : C(StdTorus 4, StdTorus 4))
      orderFourProductIntegerExtension where
  lift := orderFourProductRealExtension
  map_projection r := by
    funext i
    fin_cases i <;>
      simp [orderFourProductExtension, orderFourProductRealExtension, Fin.tail,
        orderFourThreeTorusClutching, standardFourTorusProjection]
  map_integer n := by
    funext i
    fin_cases i <;>
      norm_num [orderFourProductRealExtension, orderFourProductIntegerExtension,
        integerToReal]

private theorem orderThreeProductExtension_square :
    (orderThreeProductExtension : C(StdTorus 4, StdTorus 4)).comp
        (standardFourTorusGammaSplit.symm : C(UnitAddCircle × StdTorus 3, StdTorus 4)) =
      (standardFourTorusGammaSplit.symm : C(UnitAddCircle × StdTorus 3, StdTorus 4)).comp
        (circleProductMap
          (orderThreeThreeTorusClutching : C(StdTorus 3, StdTorus 3))) := by
  ext p i
  fin_cases i <;> rfl

private theorem orderFourProductExtension_square :
    (orderFourProductExtension : C(StdTorus 4, StdTorus 4)).comp
        (standardFourTorusGammaSplit.symm : C(UnitAddCircle × StdTorus 3, StdTorus 4)) =
      (standardFourTorusGammaSplit.symm : C(UnitAddCircle × StdTorus 3, StdTorus 4)).comp
        (circleProductMap
          (orderFourThreeTorusClutching : C(StdTorus 3, StdTorus 3))) := by
  ext p i
  fin_cases i <;> rfl

private theorem orderThreeProductClutching_homologyTwo
    (z : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3)) :
    productHomologyTwo
        (integralSingularHomologyMap 2
          (circleProductMap
            (orderThreeThreeTorusClutching : C(StdTorus 3, StdTorus 3))) z) =
      standardExteriorSquareMap orderThreeProductIntegerExtension
        (productHomologyTwo z) := by
  have hnat := (naturalStdTorusFourHomology_naturality
    (orderThreeProductExtension : C(StdTorus 4, StdTorus 4))
    orderThreeProductIntegerExtension orderThreeProductExtensionLift).2
  change naturalStdTorusFourHomologyTwo
      (integralSingularHomologyMap 2 standardFourTorusGammaSplit.symm
        (integralSingularHomologyMap 2
          (circleProductMap
            (orderThreeThreeTorusClutching : C(StdTorus 3, StdTorus 3))) z)) = _
  rw [integralSingularHomologyMap_comp_wang, ← orderThreeProductExtension_square,
    ← integralSingularHomologyMap_comp_wang]
  exact hnat _

private theorem orderFourProductClutching_homologyTwo
    (z : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3)) :
    productHomologyTwo
        (integralSingularHomologyMap 2
          (circleProductMap
            (orderFourThreeTorusClutching : C(StdTorus 3, StdTorus 3))) z) =
      standardExteriorSquareMap orderFourProductIntegerExtension
        (productHomologyTwo z) := by
  have hnat := (naturalStdTorusFourHomology_naturality
    (orderFourProductExtension : C(StdTorus 4, StdTorus 4))
    orderFourProductIntegerExtension orderFourProductExtensionLift).2
  change naturalStdTorusFourHomologyTwo
      (integralSingularHomologyMap 2 standardFourTorusGammaSplit.symm
        (integralSingularHomologyMap 2
          (circleProductMap
            (orderFourThreeTorusClutching : C(StdTorus 3, StdTorus 3))) z)) = _
  rw [integralSingularHomologyMap_comp_wang, ← orderFourProductExtension_square,
    ← integralSingularHomologyMap_comp_wang]
  exact hnat _

private theorem positiveCircleCross_loopAction
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : C(StdTorus 1, G)) :
    positiveCircleCross (loopAction phi c) =
      integralSingularHomologyMap 2
        (circleProductMap (phi.toHomeomorph : C(G, G)))
        (positiveCircleCross c) := by
  rw [positiveCircleCross, positiveCircleCross]
  rw [integralSingularHomologyMap_comp_wang]
  congr 1

private theorem orderThreeCross_action_zero :
    positiveCircleCross
        (loopAction orderThreeClutchingAddEquiv
          (standardThreeTorusCoordinateCircle 0)) =
      -positiveCircleCross (standardThreeTorusCoordinateCircle 1) +
        positiveCircleCross (standardThreeTorusCoordinateCircle 2) := by
  apply productHomologyTwo.injective
  rw [positiveCircleCross_loopAction,
    orderThreeClutchingAddEquiv_toHomeomorph,
    orderThreeProductClutching_homologyTwo,
    productHomologyTwo_positiveCircleCross_coordinateCircle]
  simp only [map_add, map_neg, productHomologyTwo_positiveCircleCross_coordinateCircle]
  funext i
  fin_cases i <;>
    norm_num [standardExteriorSquareMap, standardSecondCompoundMatrix,
      orderThreeProductIntegerExtension, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, standardPeriodPairFirst, standardPeriodPairSecond,
      Pi.single_apply] <;> decide

private theorem orderThreeCross_action_one :
    positiveCircleCross
        (loopAction orderThreeClutchingAddEquiv
          (standardThreeTorusCoordinateCircle 1)) =
      positiveCircleCross (standardThreeTorusCoordinateCircle 0) -
        positiveCircleCross (standardThreeTorusCoordinateCircle 1) := by
  apply productHomologyTwo.injective
  rw [positiveCircleCross_loopAction,
    orderThreeClutchingAddEquiv_toHomeomorph,
    orderThreeProductClutching_homologyTwo,
    productHomologyTwo_positiveCircleCross_coordinateCircle]
  simp only [map_sub, productHomologyTwo_positiveCircleCross_coordinateCircle]
  funext i
  fin_cases i <;>
    norm_num [standardExteriorSquareMap, standardSecondCompoundMatrix,
      orderThreeProductIntegerExtension, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, standardPeriodPairFirst, standardPeriodPairSecond,
      Pi.single_apply] <;> decide

private theorem orderFourCross_action_zero :
    positiveCircleCross
        (loopAction orderFourClutchingAddEquiv
          (standardThreeTorusCoordinateCircle 0)) =
      positiveCircleCross (standardThreeTorusCoordinateCircle 1) := by
  apply productHomologyTwo.injective
  rw [positiveCircleCross_loopAction,
    orderFourClutchingAddEquiv_toHomeomorph,
    orderFourProductClutching_homologyTwo,
    productHomologyTwo_positiveCircleCross_coordinateCircle,
    productHomologyTwo_positiveCircleCross_coordinateCircle]
  funext i
  fin_cases i <;>
    norm_num [standardExteriorSquareMap, standardSecondCompoundMatrix,
      orderFourProductIntegerExtension, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, standardPeriodPairFirst, standardPeriodPairSecond,
      Pi.single_apply] <;> decide

private theorem orderFourCross_action_one :
    positiveCircleCross
        (loopAction orderFourClutchingAddEquiv
          (standardThreeTorusCoordinateCircle 1)) =
      -positiveCircleCross (standardThreeTorusCoordinateCircle 0) +
        positiveCircleCross (standardThreeTorusCoordinateCircle 2) := by
  apply productHomologyTwo.injective
  rw [positiveCircleCross_loopAction,
    orderFourClutchingAddEquiv_toHomeomorph,
    orderFourProductClutching_homologyTwo,
    productHomologyTwo_positiveCircleCross_coordinateCircle]
  simp only [map_add, map_neg, productHomologyTwo_positiveCircleCross_coordinateCircle]
  funext i
  fin_cases i <;>
    norm_num [standardExteriorSquareMap, standardSecondCompoundMatrix,
      orderFourProductIntegerExtension, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, standardPeriodPairFirst, standardPeriodPairSecond,
      Pi.single_apply] <;> decide

/-- Translation of the source base circle by one normalized deck step. -/
private def normalizedBaseStep (X : Type) [TopologicalSpace X] :
    C(UnitAddCircle × X, UnitAddCircle × X) where
  toFun p :=
    (p.1 + ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle), p.2)
  continuous_toFun := by fun_prop

/-- The normalized base step is homotopic to the identity through circle translations. -/
private def normalizedBaseStepHomotopy (X : Type) [TopologicalSpace X] :
    ContinuousMap.Homotopy (ContinuousMap.id (UnitAddCircle × X))
      (normalizedBaseStep (m := m) X) where
  toFun p :=
    (p.2.1 + (((((p.1 : ℝ) / (m : ℝ) : ℝ))) : UnitAddCircle), p.2.2)
  continuous_toFun := by fun_prop
  map_zero_left p := by
    apply Prod.ext <;> simp
  map_one_left p := by
    apply Prod.ext <;> simp [normalizedBaseStep]

/-- Applying the clutching map to a fibre loop can be absorbed by one source-base translation
before passing to the normalized affine quotient. -/
private theorem normalizedCover_loopAction_square
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (hpow : phi.toHomeomorph ^ m = 1)
    (c : C(StdTorus 1, G)) :
    (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow).comp
        (circleProductMap (loopAction phi c)) =
      (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow).comp
        ((normalizedBaseStep (m := m) G).comp (circleProductMap c)) := by
  ext p
  change (normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph
      phi.toHomeomorph hpow)
        (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
          (p.1, phi (c p.2))) =
    (normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph
      phi.toHomeomorph hpow)
        (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
          (p.1 + ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle), c p.2))
  rw [(normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph
    phi.toHomeomorph hpow).injective.eq_iff]
  change Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
      (p.1, phi (c p.2)) =
    Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
      (p.1 + ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle), c p.2)
  symm
  apply Quotient.sound
  refine ⟨1, ?_⟩
  apply Prod.ext
  · change p.1 =
      p.1 + ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) -
        (((((1 : ℤ) : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle)
    rw [show (((((1 : ℤ) : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) =
        ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) by norm_num]
    abel
  · change phi (c p.2) = (phi.toHomeomorph ^ (1 : ℤ)) (c p.2)
    rw [zpow_one]
    rfl

/-- The normalized cover sends a fibre loop and its clutching translate to the same homology
class.  This is a direct quotient calculation plus homotopy invariance, not an orbit-sweep
theorem. -/
public theorem normalizedCover_positiveCircleCross_loopAction
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (hpow : phi.toHomeomorph ^ m = 1)
    (c : C(StdTorus 1, G)) :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (positiveCircleCross (loopAction phi c)) =
      integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (positiveCircleCross c) := by
  rw [positiveCircleCross, positiveCircleCross]
  rw [integralSingularHomologyMap_comp_wang,
    integralSingularHomologyMap_comp_wang]
  rw [normalizedCover_loopAction_square phi hpow c]
  rw [← integralSingularHomologyMap_comp_wang]
  rw [← integralSingularHomologyMap_comp_wang]
  have hstep := integralSingularHomologyMap_eq_of_homotopy 2
    (normalizedBaseStepHomotopy (m := m) G)
  rw [← hstep]
  rw [integralSingularHomologyMap_id_wang]
  rw [← integralSingularHomologyMap_comp_wang]

/-- The image of a base-circle cross coordinate in the normalized order-three cover. -/
public noncomputable def orderThreeNormalizedCross (i : Fin 3) :
    IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching) :=
  integralSingularHomologyMap 2
    (normalizedAffineCoverToCircleMappingTorus orderThreeThreeTorusClutching
      orderThreeThreeTorusClutching_pow)
    (positiveCircleCross (standardThreeTorusCoordinateCircle i))

/-- The image of a base-circle cross coordinate in the normalized order-four cover. -/
public noncomputable def orderFourNormalizedCross (i : Fin 3) :
    IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching) :=
  integralSingularHomologyMap 2
    (normalizedAffineCoverToCircleMappingTorus orderFourThreeTorusClutching
      orderFourThreeTorusClutching_pow)
    (positiveCircleCross (standardThreeTorusCoordinateCircle i))

/-- In the order-three cover, the zeroth cross coordinate is twice the first. -/
public theorem orderThreeNormalizedCross_zero_eq_two_one :
    orderThreeNormalizedCross 0 = 2 • orderThreeNormalizedCross 1 := by
  have h := normalizedCover_positiveCircleCross_loopAction
    orderThreeClutchingAddEquiv orderThreeClutchingAddEquiv_pow
    (standardThreeTorusCoordinateCircle 1)
  rw [orderThreeCross_action_one, map_sub] at h
  change orderThreeNormalizedCross 0 - orderThreeNormalizedCross 1 =
    orderThreeNormalizedCross 1 at h
  simpa only [two_nsmul] using sub_eq_iff_eq_add.mp h

/-- In the order-three cover, the second cross coordinate is three times the first. -/
public theorem orderThreeNormalizedCross_two_eq_three_one :
    orderThreeNormalizedCross 2 = 3 • orderThreeNormalizedCross 1 := by
  have h := normalizedCover_positiveCircleCross_loopAction
    orderThreeClutchingAddEquiv orderThreeClutchingAddEquiv_pow
    (standardThreeTorusCoordinateCircle 0)
  rw [orderThreeCross_action_zero, map_add, map_neg] at h
  change -orderThreeNormalizedCross 1 + orderThreeNormalizedCross 2 =
    orderThreeNormalizedCross 0 at h
  rw [orderThreeNormalizedCross_zero_eq_two_one] at h
  calc
    orderThreeNormalizedCross 2 =
        orderThreeNormalizedCross 1 + 2 • orderThreeNormalizedCross 1 :=
      neg_add_eq_iff_eq_add.mp h
    _ = 2 • orderThreeNormalizedCross 1 + orderThreeNormalizedCross 1 :=
      add_comm _ _
    _ = 3 • orderThreeNormalizedCross 1 :=
      (succ_nsmul (orderThreeNormalizedCross 1) 2).symm

/-- In the order-four cover, the first and zeroth cross coordinates agree. -/
public theorem orderFourNormalizedCross_one_eq_zero :
    orderFourNormalizedCross 1 = orderFourNormalizedCross 0 := by
  have h := normalizedCover_positiveCircleCross_loopAction
    orderFourClutchingAddEquiv orderFourClutchingAddEquiv_pow
    (standardThreeTorusCoordinateCircle 0)
  rw [orderFourCross_action_zero] at h
  exact h

/-- In the order-four cover, the second cross coordinate is twice the zeroth. -/
public theorem orderFourNormalizedCross_two_eq_two_zero :
    orderFourNormalizedCross 2 = 2 • orderFourNormalizedCross 0 := by
  have h := normalizedCover_positiveCircleCross_loopAction
    orderFourClutchingAddEquiv orderFourClutchingAddEquiv_pow
    (standardThreeTorusCoordinateCircle 1)
  rw [orderFourCross_action_one, map_add, map_neg] at h
  change -orderFourNormalizedCross 0 + orderFourNormalizedCross 2 =
    orderFourNormalizedCross 1 at h
  rw [orderFourNormalizedCross_one_eq_zero] at h
  simpa only [two_nsmul] using neg_add_eq_iff_eq_add.mp h

/-- Fibre naturality for the normalized order-three cover, without any sweep input. -/
public theorem orderThreeNormalizedCover_fibreSquare
    (x : IntegralSingularHomology 2 (StdTorus 3)) :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderThreeThreeTorusClutching
          orderThreeThreeTorusClutching_pow)
        (integralSingularHomologyMap 2
          (circleProductFiberInclusion (X := StdTorus 3)) x) =
      OrderThreePresentation.inclusion x := by
  exact normalizedAffineCover_fiber_square orderThreeThreeTorusClutching
    orderThreeThreeTorusClutching_pow 1 x

/-- Fibre naturality for the normalized order-four cover, without any sweep input. -/
public theorem orderFourNormalizedCover_fibreSquare
    (x : IntegralSingularHomology 2 (StdTorus 3)) :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderFourThreeTorusClutching
          orderFourThreeTorusClutching_pow)
        (integralSingularHomologyMap 2
          (circleProductFiberInclusion (X := StdTorus 3)) x) =
      OrderFourPresentation.inclusion x := by
  exact normalizedAffineCover_fiber_square orderFourThreeTorusClutching
    orderFourThreeTorusClutching_pow 1 x

/-- The selected order-three fibre generator is preserved by the normalized cover. -/
public theorem orderThreeNormalizedCover_fibreGenerator :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderThreeThreeTorusClutching
          orderThreeThreeTorusClutching_pow)
        (integralSingularHomologyMap 2
          (circleProductFiberInclusion (X := StdTorus 3))
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) =
      OrderThreePresentation.inclusion
        (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) :=
  orderThreeNormalizedCover_fibreSquare _

/-- The selected order-four fibre generator is preserved by the normalized cover. -/
public theorem orderFourNormalizedCover_fibreGenerator :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderFourThreeTorusClutching
          orderFourThreeTorusClutching_pow)
        (integralSingularHomologyMap 2
          (circleProductFiberInclusion (X := StdTorus 3))
          (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))) =
      OrderFourPresentation.inclusion
        (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) :=
  orderFourNormalizedCover_fibreSquare _

end SphereSixComplex.Topology.EllipticThreeTorusExplicitOrbitSweepHomology

end

end
