module

public import SphereSixComplex.Paper.Topology.EllipticDiscCircleCentral
public import SphereSixComplex.Paper.Topology.EllipticDiscCircleRelation

@[expose] public section
noncomputable section
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.EllipticDiscCircle

open SphereSixComplex.Topology SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Periods.SourceAutomaticBranch SphereSixComplex.TriangleGroup
open EllipticCayleyHomeomorph GlobalTorusFamily AnalyticData
open Metric

public theorem orderThreeProductToCentral_zero (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderThree.radius) :
    orderThreeProductToCentral A (b, 0) =
      A.markedBaseToCentralZeroSection
        (A.centralFamilyCoordinate (orderThreeProductToCentral A (b, 0))) := by
  let x := orderThreeProductToRegular A (b, 0)
  let z := regularTotalSpaceBase A.periods x
  have hx : x = regularFamilyZeroSection A.periods z :=
    orderThreeProductToRegular_zero A b
  have hz : orderThreeProductToCentral A (b, 0) =
      A.centralZeroSection (regularBaseQuotientMap z) := by
    change A.centralQuotientProjection x = puncturedGlobalZeroSection A.periods (regularBaseQuotientMap z)
    rw [hx, puncturedGlobalZeroSection_mk]
    rfl
  change orderThreeProductToCentral A (b, 0) =
    A.centralZeroSection (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
      (A.centralFamilyCoordinate (orderThreeProductToCentral A (b, 0))))
  rw [hz]
  apply congrArg A.centralZeroSection
  apply A.puncturedBaseHomeomorphTwicePuncturedComplex.injective
  rw [A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply,
    A.puncturedBaseHomeomorphTwicePuncturedComplex_mk]
  rw [← hz]
  exact (A.centralFamilyCoordinate_centralQuotientProjection x).symm

public theorem orderThreeProductToCentral_coordinate (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderThree.radius) :
    (A.centralFamilyCoordinate (orderThreeProductToCentral A (b, 0)) : ℂ) =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint b.val.val.val := by
  change (A.centralFamilyCoordinate
    (A.centralQuotientProjection (orderThreeProductToRegular A (b, 0))) : ℂ) = _
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  change A.modular.sourceCoordinate.coordinate
    (regularTotalSpaceBase A.periods (orderThreeProductToRegular A (b, 0))).val = _
  rw [orderThreeProductToRegular_base,
    ← orderThreeCayleyRegularCoordinate_chartFunction A]
  rw [orderThreeCayleyHomeomorph.apply_symm_apply]

public theorem orderFourProductToCentral_zero (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderFour.radius) :
    orderFourProductToCentral A (b, 0) =
      A.markedBaseToCentralZeroSection
        (A.centralFamilyCoordinate (orderFourProductToCentral A (b, 0))) := by
  let x := orderFourProductToRegular A (b, 0)
  let z := regularTotalSpaceBase A.periods x
  have hx : x = regularFamilyZeroSection A.periods z :=
    orderFourProductToRegular_zero A b
  have hz : orderFourProductToCentral A (b, 0) =
      A.centralZeroSection (regularBaseQuotientMap z) := by
    change A.centralQuotientProjection x = puncturedGlobalZeroSection A.periods (regularBaseQuotientMap z)
    rw [hx, puncturedGlobalZeroSection_mk]
    rfl
  change orderFourProductToCentral A (b, 0) =
    A.centralZeroSection (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
      (A.centralFamilyCoordinate (orderFourProductToCentral A (b, 0))))
  rw [hz]
  apply congrArg A.centralZeroSection
  apply A.puncturedBaseHomeomorphTwicePuncturedComplex.injective
  rw [A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply,
    A.puncturedBaseHomeomorphTwicePuncturedComplex_mk]
  rw [← hz]
  exact (A.centralFamilyCoordinate_centralQuotientProjection x).symm

public theorem orderFourProductToCentral_coordinate (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderFour.radius) :
    (A.centralFamilyCoordinate (orderFourProductToCentral A (b, 0)) : ℂ) =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint b.val.val.val := by
  change (A.centralFamilyCoordinate
    (A.centralQuotientProjection (orderFourProductToRegular A (b, 0))) : ℂ) = _
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  change A.modular.sourceCoordinate.coordinate
    (regularTotalSpaceBase A.periods (orderFourProductToRegular A (b, 0))).val = _
  rw [orderFourProductToRegular_base,
    ← orderFourCayleyRegularCoordinate_chartFunction A]
  rw [orderFourCayleyHomeomorph.apply_symm_apply]

public theorem orderThree_baseLoop_homology (A : AnalyticData)
    (u : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianOneFixedPoint z = z ^ 3 * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ 3 * ‖u z‖ < 1)
    {b : PuncturedDiscBall A.starSeparation.orderThree.radius} (p : Path b b)
    (hp : ∀ t, (p t).val.val.val = localDegreeCirclePoint a t) :
    loopHomologyClass ((p.prod (Path.refl 0)).map (orderThreeProductToCentral A).continuous) =
      (3 : ℕ) • hurewiczFunction A.cuspCentralBase A.geometricCentralRhoOne := by
  let q := (p.prod (Path.refl 0)).map (orderThreeProductToCentral A).continuous
  let base := q.map A.centralFamilyCoordinate_continuous
  have hq : loopHomologyClass q =
      loopHomologyClass (base.map A.markedBaseToCentralZeroSection.continuous) := by
    apply loopHomologyClass_eq_of_toContinuousMap_eq
    ext t
    exact orderThreeProductToCentral_zero A (p t)
  refine hq.trans (A.factorizedDiscCircle_zero_central_homology
    (fun z ↦ ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianOneFixedPoint z)
    u 3 a ha hu hune hf (by simpa using hb) base ?_)
  intro t
  change (A.centralFamilyCoordinate (orderThreeProductToCentral A (p t, 0)) : ℂ) = _
  rw [orderThreeProductToCentral_coordinate, hp]

public theorem orderThree_smallDiscCircle_base_homology (A : AnalyticData)
    (u : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (hrR : r < A.starSeparation.orderThree.radius)
    (hu : ContinuousOn u (closedBall (0 : ℂ) r))
    (hune : ∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) r,
      ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianOneFixedPoint z = z ^ 3 * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) r, r ^ 3 * ‖u z‖ < 1) :
    let hR := A.starSeparation.orderThree.radius_pos
    let hR1 := A.starSeparation.orderThree.radius_lt_one
    let p := smallDiscCircle hR r hr hrR
    let hp := smallDiscCircle_ne_zero hR r hr hrR
    let hb0 : ((p 0 : ComplexUnitDisc) : ℂ) ≠ 0 := hp 0
    loopHomologyClass
      (((scaledPuncturedLoop hR hR1 hb0 p hp).prod (Path.refl 0)).map
        (orderThreeProductToCentral A).continuous) =
      (3 : ℕ) • hurewiczFunction A.cuspCentralBase A.geometricCentralRhoOne := by
  dsimp only
  apply orderThree_baseLoop_homology A u (r : ℂ)
    (Complex.ofReal_ne_zero.mpr hr.ne')
    (by simpa [Complex.norm_real, abs_of_pos hr] using hu)
    (by simpa [Complex.norm_real, abs_of_pos hr] using hune)
    (by simpa [Complex.norm_real, abs_of_pos hr] using hf)
    (by simpa [Complex.norm_real, abs_of_pos hr] using hb)
  intro t
  change (discBallScale A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
    (smallDiscCircle A.starSeparation.orderThree.radius_pos r hr hrR t)).val.val = _
  rw [smallDiscCircle_scaled, ComplexUnitDisc.circle_coe]
  unfold localDegreeCirclePoint
  congr 2
  ring

public theorem orderFour_baseLoop_homology (A : AnalyticData)
    (u : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianTwoFixedPoint z - 1 = z ^ 4 * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, ‖a‖ ^ 4 * ‖u z‖ < 1)
    {b : PuncturedDiscBall A.starSeparation.orderFour.radius} (p : Path b b)
    (hp : ∀ t, (p t).val.val.val = localDegreeCirclePoint a t) :
    loopHomologyClass ((p.prod (Path.refl 0)).map (orderFourProductToCentral A).continuous) =
      (4 : ℕ) • hurewiczFunction A.cuspCentralBase A.geometricCentralRhoTwo := by
  let q := (p.prod (Path.refl 0)).map (orderFourProductToCentral A).continuous
  let base := q.map A.centralFamilyCoordinate_continuous
  have hq : loopHomologyClass q =
      loopHomologyClass (base.map A.markedBaseToCentralZeroSection.continuous) := by
    apply loopHomologyClass_eq_of_toContinuousMap_eq
    ext t
    exact orderFourProductToCentral_zero A (p t)
  refine hq.trans (A.factorizedDiscCircle_one_central_homology
    (fun z ↦ ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianTwoFixedPoint z - 1)
    u 4 a ha hu hune hf (by simpa using hb) base ?_)
  intro t
  change (A.centralFamilyCoordinate (orderFourProductToCentral A (p t, 0)) : ℂ) = _
  rw [orderFourProductToCentral_coordinate, hp]
  ring

public theorem orderFour_smallDiscCircle_base_homology (A : AnalyticData)
    (u : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (hrR : r < A.starSeparation.orderFour.radius)
    (hu : ContinuousOn u (closedBall (0 : ℂ) r))
    (hune : ∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0)
    (hf : ∀ z ∈ closedBall (0 : ℂ) r,
      ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianTwoFixedPoint z - 1 = z ^ 4 * u z)
    (hb : ∀ z ∈ closedBall (0 : ℂ) r, r ^ 4 * ‖u z‖ < 1) :
    let hR := A.starSeparation.orderFour.radius_pos
    let hR1 := A.starSeparation.orderFour.radius_lt_one
    let p := smallDiscCircle hR r hr hrR
    let hp := smallDiscCircle_ne_zero hR r hr hrR
    let hb0 : ((p 0 : ComplexUnitDisc) : ℂ) ≠ 0 := hp 0
    loopHomologyClass
      (((scaledPuncturedLoop hR hR1 hb0 p hp).prod (Path.refl 0)).map
        (orderFourProductToCentral A).continuous) =
      (4 : ℕ) • hurewiczFunction A.cuspCentralBase A.geometricCentralRhoTwo := by
  dsimp only
  apply orderFour_baseLoop_homology A u (r : ℂ)
    (Complex.ofReal_ne_zero.mpr hr.ne')
    (by simpa [Complex.norm_real, abs_of_pos hr] using hu)
    (by simpa [Complex.norm_real, abs_of_pos hr] using hune)
    (by simpa [Complex.norm_real, abs_of_pos hr] using hf)
    (by simpa [Complex.norm_real, abs_of_pos hr] using hb)
  intro t
  change (discBallScale A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
    (smallDiscCircle A.starSeparation.orderFour.radius_pos r hr hrR t)).val.val = _
  rw [smallDiscCircle_scaled, ComplexUnitDisc.circle_coe]
  unfold localDegreeCirclePoint
  congr 2
  ring

end SphereSixComplex.Geometry.EllipticDiscCircle
