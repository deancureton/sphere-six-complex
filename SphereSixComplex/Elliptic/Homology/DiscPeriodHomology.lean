module

public import SphereSixComplex.Elliptic.DiscCircle.Splitting
public import SphereSixComplex.Regular.Homology.Period

@[expose] public section
noncomputable section
open scoped ContinuousMap
open SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Hurewicz.Chains

namespace SphereSixComplex.Geometry.EllipticDiscCircle

open SphereSixComplex.Periods
open AnalyticTorusFamily ComplexTorus RealPeriodTrivialization GlobalTorusFamily
open EllipticLinearCollarGlobalDescent EllipticCayleyHomeomorph

variable {U : TriangleUniformization}

theorem fixedToMovingCover_period_segment (F : PeriodFunctions U)
    (z₀ z : UpperHalfPlane) (a : IntegerPeriods) (v : ComplexTwoSpace) (t : unitInterval) :
    (fixedToMovingCover F z₀
      (z, Path.segment v (periodVector (parameterMap F z₀).1 a + v) t)).2 =
      (t : ℝ) • periodVector (parameterMap F z).1 a +
        (fixedToMovingCover F z₀ (z, v)).2 := by
  have hp := congrArg Prod.snd (fixedToMovingCover_period_add F z₀ z a 0)
  simp only [fixedToMovingCover, map_zero, add_zero] at hp
  simp only [fixedToMovingCover, Path.segment_apply, AffineMap.lineMap_apply_module,
    map_add, map_smul]
  rw [hp]
  module

theorem orderThreeProductToRegular_periodPoint (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderThree.radius) (v : ComplexTwoSpace) :
    let z := regularTotalSpaceBase A.periods (orderThreeProductToRegular A (b, 0))
    orderThreeProductToRegular A (b, Quotient.mk _ v) =
      regularFamilyCoverProjection A.periods (z,
        (fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne (z.1, v)).2) := by
  dsimp only
  apply regularFamilyInclusion_injective A.periods
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  have hproj (q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) : regularFamilyCoverProjection A.periods q = Quotient.mk _ q := rfl
  rw [hproj]
  rw [orderThreeProductToRegular_coordinates, regularFamilyInclusion_mk,
    orderThreeRealPeriodProductHomeomorph_mk]
  simp only [regularBundleInclusion]
  apply Prod.ext
  · rw [orderThreeProductToRegular_base, Homeomorph.apply_symm_apply]
  · apply congrArg (Quotient.mk _)
    have h := congrArg Prod.snd (movingToFixedCover_fixedToMovingCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne
      ((regularTotalSpaceBase A.periods (orderThreeProductToRegular A (b, 0))).val, v))
    simpa only [fixedToMovingCover] using h.symm

theorem orderThreeProductToCentral_fixedPeriodLoop_homology (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderThree.radius)
    (a : IntegerPeriods) (v : ComplexTwoSpace)
    (q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    loopHomologyClass (((Path.refl b).prod
      (fixedPeriodLoop A.periods A.modular.modularParameter.toTriangleUniformization.zOne
        a v)).map (orderThreeProductToCentral A).continuous) =
      loopHomologyClass ((regularFamilyPeriodLoop A.periods q a).map
        (regularFamilyQuotientMap A.periods).continuous) := by
  let _ := regularFamilyDeckAction A.periods
  let z := regularTotalSpaceBase A.periods (orderThreeProductToRegular A (b, 0))
  let w := (fixedToMovingCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne (z.1, v)).2
  trans loopHomologyClass ((regularFamilyPeriodLoop A.periods (z, w) a).map
    (regularFamilyQuotientMap A.periods).continuous)
  · apply loopHomologyClass_eq_of_toContinuousMap_eq
    ext t
    change quotientProjection (orderThreeProductToRegular A
      (b, Quotient.mk _ (Path.segment v
        (periodVector (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 a + v) t))) = _
    rw [orderThreeProductToRegular_periodPoint, fixedToMovingCover_period_segment]
    rfl
  · exact loopHomologyClass_regularFamilyPeriodLoop A.periods (z, w) q a
      (regularFamilyQuotientMap A.periods)

theorem orderFourProductToRegular_periodPoint (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderFour.radius) (v : ComplexTwoSpace) :
    let z := regularTotalSpaceBase A.periods (orderFourProductToRegular A (b, 0))
    orderFourProductToRegular A (b, Quotient.mk _ v) =
      regularFamilyCoverProjection A.periods (z,
        (fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo (z.1, v)).2) := by
  dsimp only
  apply regularFamilyInclusion_injective A.periods
  apply (orderFourRealPeriodProductHomeomorph A.periods).injective
  have hproj (q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) : regularFamilyCoverProjection A.periods q = Quotient.mk _ q := rfl
  rw [hproj]
  rw [orderFourProductToRegular_coordinates, regularFamilyInclusion_mk,
    orderFourRealPeriodProductHomeomorph_mk]
  simp only [regularBundleInclusion]
  apply Prod.ext
  · rw [orderFourProductToRegular_base, Homeomorph.apply_symm_apply]
  · apply congrArg (Quotient.mk _)
    have h := congrArg Prod.snd (movingToFixedCover_fixedToMovingCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo
      ((regularTotalSpaceBase A.periods (orderFourProductToRegular A (b, 0))).val, v))
    simpa only [fixedToMovingCover] using h.symm

theorem orderFourProductToCentral_fixedPeriodLoop_homology (A : AnalyticData)
    (b : PuncturedDiscBall A.starSeparation.orderFour.radius)
    (a : IntegerPeriods) (v : ComplexTwoSpace)
    (q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    loopHomologyClass (((Path.refl b).prod
      (fixedPeriodLoop A.periods A.modular.modularParameter.toTriangleUniformization.zTwo
        a v)).map (orderFourProductToCentral A).continuous) =
      loopHomologyClass ((regularFamilyPeriodLoop A.periods q a).map
        (regularFamilyQuotientMap A.periods).continuous) := by
  let _ := regularFamilyDeckAction A.periods
  let z := regularTotalSpaceBase A.periods (orderFourProductToRegular A (b, 0))
  let w := (fixedToMovingCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo (z.1, v)).2
  trans loopHomologyClass ((regularFamilyPeriodLoop A.periods (z, w) a).map
    (regularFamilyQuotientMap A.periods).continuous)
  · apply loopHomologyClass_eq_of_toContinuousMap_eq
    ext t
    change quotientProjection (orderFourProductToRegular A
      (b, Quotient.mk _ (Path.segment v
        (periodVector (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 a + v) t))) = _
    rw [orderFourProductToRegular_periodPoint, fixedToMovingCover_period_segment]
    rfl
  · exact loopHomologyClass_regularFamilyPeriodLoop A.periods (z, w) q a
      (regularFamilyQuotientMap A.periods)

end SphereSixComplex.Geometry.EllipticDiscCircle
