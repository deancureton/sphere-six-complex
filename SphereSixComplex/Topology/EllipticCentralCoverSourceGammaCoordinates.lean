module

public import SphereSixComplex.Topology.EllipticGammaShearDegreeTwoCoordinates
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasis

/-!
# Gamma-product coordinates on the elliptic central covering sources
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.EllipticCentralCoverSourceGammaCoordinates

open Geometry Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open Geometry.AnalyticTorusFamily Geometry.GlobalTorusFamily
open StandardTorusHomology
open PaperAffineCyclicReducedFiberMappingTorus
open PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels
open EllipticGammaShearDegreeTwoCoordinates

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

private theorem homologyEquiv_eq_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (z : IntegralSingularHomology 2 X) :
    integralSingularHomologyEquiv 2 e z =
      integralSingularHomologyMap 2 (e : C(X, Y)) z :=
  rfl

public def orderThreeSourceToGammaProduct :
    RadialEllipticActionData.centralFiberCoverSource (orderThreeRadialActionData F) ≃ₜ
      UnitAddCircle × StdTorus 3 :=
  (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderThreeRadialActionData F)).trans (orderThreeGammaNormalFormHomeomorph F)

public def orderFourSourceToGammaProduct :
    RadialEllipticActionData.centralFiberCoverSource (orderFourRadialActionData F) ≃ₜ
      UnitAddCircle × StdTorus 3 :=
  (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderFourRadialActionData F)).trans (orderFourGammaNormalFormHomeomorph F)

private theorem orderThreeGammaNormalFormHomeomorph_coe :
    (orderThreeGammaNormalFormHomeomorph F :
      C(AdditiveTorus (parameterMap F U.zOne), UnitAddCircle × StdTorus 3)) =
      (orderThreeStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3)).comp
        (additiveTorusStdHomeomorph _
          (fullRankDomain (parameterMap F U.zOne)) :
          C(AdditiveTorus (parameterMap F U.zOne), StdTorus 4)) :=
  rfl

private theorem orderFourGammaNormalFormHomeomorph_coe :
    (orderFourGammaNormalFormHomeomorph F :
      C(AdditiveTorus (parameterMap F U.zTwo), UnitAddCircle × StdTorus 3)) =
      (orderFourStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3)).comp
        (additiveTorusStdHomeomorph _
          (fullRankDomain (parameterMap F U.zTwo)) :
          C(AdditiveTorus (parameterMap F U.zTwo), StdTorus 4)) :=
  rfl

private theorem orderThreeSource_afterHomeomorph (x : Fin 6 → ℤ) :
    integralSingularHomologyMap 2
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData F)) :
          C(RadialEllipticActionData.centralFiberCoverSource
              (orderThreeRadialActionData F),
            AdditiveTorus (parameterMap F U.zOne)))
        ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x) =
      (orderThreeTorusHomologyBasis F).degreeTwo.symm x := by
  apply (orderThreeTorusHomologyBasis F).degreeTwo.injective
  have h := (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.apply_symm_apply x
  have hleft :
      (orderThreeTorusHomologyBasis F).degreeTwo
          (integralSingularHomologyMap 2
            (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
              (orderThreeRadialActionData F))
            ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) = x := by
    simpa only [orderThreeCentralFiberCoverSourceHomologyBasis,
      FourTorusHomologyBasis.homeomorph, AddEquiv.trans_apply,
      homologyEquiv_eq_map] using h
  rw [hleft, (orderThreeTorusHomologyBasis F).degreeTwo.apply_symm_apply]

private theorem orderFourSource_afterHomeomorph (x : Fin 6 → ℤ) :
    integralSingularHomologyMap 2
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderFourRadialActionData F)) :
          C(RadialEllipticActionData.centralFiberCoverSource
              (orderFourRadialActionData F),
            AdditiveTorus (parameterMap F U.zTwo)))
        ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x) =
      (orderFourTorusHomologyBasis F).degreeTwo.symm x := by
  apply (orderFourTorusHomologyBasis F).degreeTwo.injective
  have h := (orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.apply_symm_apply x
  have hleft :
      (orderFourTorusHomologyBasis F).degreeTwo
          (integralSingularHomologyMap 2
            (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
              (orderFourRadialActionData F))
            ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) = x := by
    simpa only [orderFourCentralFiberCoverSourceHomologyBasis,
      FourTorusHomologyBasis.homeomorph, AddEquiv.trans_apply,
      homologyEquiv_eq_map] using h
  rw [hleft, (orderFourTorusHomologyBasis F).degreeTwo.apply_symm_apply]

private theorem orderThreeTorusBasis_afterStandardHomeomorph (x : Fin 6 → ℤ) :
    integralSingularHomologyMap 2
        (additiveTorusStdHomeomorph _
          (fullRankDomain (parameterMap F U.zOne)))
        ((orderThreeTorusHomologyBasis F).degreeTwo.symm x) =
      naturalStdTorusFourHomologyTwo.symm x := by
  change integralSingularHomologyEquiv 2
      (additiveTorusStdHomeomorph _
        (fullRankDomain (parameterMap F U.zOne)))
      ((orderThreeTorusHomologyBasis F).degreeTwo.symm x) = _
  rw [orderThreeTorusHomologyBasis,
    EstablishedTorusHomology.additiveTorusHomologyBasis_degreeTwo,
    StandardTorusHomology.additiveTorusHomologyDegreeTwo,
    StandardTorusHomology.stdTorusFourHomologyTwo]
  exact (integralSingularHomologyEquiv 2
    (additiveTorusStdHomeomorph _
      (fullRankDomain (parameterMap F U.zOne)))).apply_symm_apply _

private theorem orderFourTorusBasis_afterStandardHomeomorph (x : Fin 6 → ℤ) :
    integralSingularHomologyMap 2
        (additiveTorusStdHomeomorph _
          (fullRankDomain (parameterMap F U.zTwo)))
        ((orderFourTorusHomologyBasis F).degreeTwo.symm x) =
      naturalStdTorusFourHomologyTwo.symm x := by
  change integralSingularHomologyEquiv 2
      (additiveTorusStdHomeomorph _
        (fullRankDomain (parameterMap F U.zTwo)))
      ((orderFourTorusHomologyBasis F).degreeTwo.symm x) = _
  rw [orderFourTorusHomologyBasis,
    EstablishedTorusHomology.additiveTorusHomologyBasis_degreeTwo,
    StandardTorusHomology.additiveTorusHomologyDegreeTwo,
    StandardTorusHomology.stdTorusFourHomologyTwo]
  exact (integralSingularHomologyEquiv 2
    (additiveTorusStdHomeomorph _
      (fullRankDomain (parameterMap F U.zTwo)))).apply_symm_apply _

/-- The order-three covering-source basis after the explicit gamma shear. -/
public theorem orderThreeSourceToGammaProduct_homologyTwo (x : Fin 6 → ℤ) :
    gammaProductHomologyTwo
        (integralSingularHomologyMap 2
          (orderThreeSourceToGammaProduct F : C(_, _))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) =
      ![-x 0, -x 1, -x 2, x 3 - 4 * x 0 - 2 * x 1,
        x 4 - 2 * x 2, x 5 + 4 * x 2] := by
  have hcomp :
      integralSingularHomologyMap 2 (orderThreeSourceToGammaProduct F : C(_, _))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x) =
        integralSingularHomologyMap 2
          (orderThreeGammaNormalFormHomeomorph F :
            C(AdditiveTorus (parameterMap F U.zOne), UnitAddCircle × StdTorus 3))
          (integralSingularHomologyMap 2
            ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
              (orderThreeRadialActionData F)) :
              C(RadialEllipticActionData.centralFiberCoverSource
                  (orderThreeRadialActionData F),
                AdditiveTorus (parameterMap F U.zOne)))
            ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) := by
    exact (integralSingularHomologyMap_comp_wang 2
      ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
        (orderThreeRadialActionData F)) :
        C(RadialEllipticActionData.centralFiberCoverSource
            (orderThreeRadialActionData F),
          AdditiveTorus (parameterMap F U.zOne)))
      (orderThreeGammaNormalFormHomeomorph F :
        C(AdditiveTorus (parameterMap F U.zOne), UnitAddCircle × StdTorus 3))
      ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)).symm
  rw [hcomp, orderThreeSource_afterHomeomorph]
  have hgamma :
      integralSingularHomologyMap 2
          (orderThreeGammaNormalFormHomeomorph F : C(_, _))
          ((orderThreeTorusHomologyBasis F).degreeTwo.symm x) =
        integralSingularHomologyMap 2
          (orderThreeStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3))
          (integralSingularHomologyMap 2
            (additiveTorusStdHomeomorph _
              (fullRankDomain (parameterMap F U.zOne)) :
              C(AdditiveTorus (parameterMap F U.zOne), StdTorus 4))
            ((orderThreeTorusHomologyBasis F).degreeTwo.symm x)) := by
    rw [orderThreeGammaNormalFormHomeomorph_coe]
    exact (integralSingularHomologyMap_comp_wang 2
      (additiveTorusStdHomeomorph _
        (fullRankDomain (parameterMap F U.zOne)) :
        C(AdditiveTorus (parameterMap F U.zOne), StdTorus 4))
      (orderThreeStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3))
      ((orderThreeTorusHomologyBasis F).degreeTwo.symm x)).symm
  rw [hgamma]
  rw [orderThreeTorusBasis_afterStandardHomeomorph]
  exact orderThreeGammaShear_homologyTwo_coordinates x

/-- The order-four covering-source basis after the explicit gamma shear. -/
public theorem orderFourSourceToGammaProduct_homologyTwo (x : Fin 6 → ℤ) :
    gammaProductHomologyTwo
        (integralSingularHomologyMap 2
          (orderFourSourceToGammaProduct F : C(_, _))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) =
      ![x 0, x 1, x 2, x 3 - 3 * x 0 - 3 * x 1,
        x 4 - 3 * x 2, x 5 + 3 * x 2] := by
  have hcomp :
      integralSingularHomologyMap 2 (orderFourSourceToGammaProduct F : C(_, _))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x) =
        integralSingularHomologyMap 2
          (orderFourGammaNormalFormHomeomorph F :
            C(AdditiveTorus (parameterMap F U.zTwo), UnitAddCircle × StdTorus 3))
          (integralSingularHomologyMap 2
            ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
              (orderFourRadialActionData F)) :
              C(RadialEllipticActionData.centralFiberCoverSource
                  (orderFourRadialActionData F),
                AdditiveTorus (parameterMap F U.zTwo)))
            ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) := by
    exact (integralSingularHomologyMap_comp_wang 2
      ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
        (orderFourRadialActionData F)) :
        C(RadialEllipticActionData.centralFiberCoverSource
            (orderFourRadialActionData F),
          AdditiveTorus (parameterMap F U.zTwo)))
      (orderFourGammaNormalFormHomeomorph F :
        C(AdditiveTorus (parameterMap F U.zTwo), UnitAddCircle × StdTorus 3))
      ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)).symm
  rw [hcomp, orderFourSource_afterHomeomorph]
  have hgamma :
      integralSingularHomologyMap 2
          (orderFourGammaNormalFormHomeomorph F : C(_, _))
          ((orderFourTorusHomologyBasis F).degreeTwo.symm x) =
        integralSingularHomologyMap 2
          (orderFourStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3))
          (integralSingularHomologyMap 2
            (additiveTorusStdHomeomorph _
              (fullRankDomain (parameterMap F U.zTwo)) :
              C(AdditiveTorus (parameterMap F U.zTwo), StdTorus 4))
            ((orderFourTorusHomologyBasis F).degreeTwo.symm x)) := by
    rw [orderFourGammaNormalFormHomeomorph_coe]
    exact (integralSingularHomologyMap_comp_wang 2
      (additiveTorusStdHomeomorph _
        (fullRankDomain (parameterMap F U.zTwo)) :
        C(AdditiveTorus (parameterMap F U.zTwo), StdTorus 4))
      (orderFourStandardGammaShear : C(StdTorus 4, UnitAddCircle × StdTorus 3))
      ((orderFourTorusHomologyBasis F).degreeTwo.symm x)).symm
  rw [hgamma]
  rw [orderFourTorusBasis_afterStandardHomeomorph]
  exact orderFourGammaShear_homologyTwo_coordinates x

end SphereSixComplex.Topology.EllipticCentralCoverSourceGammaCoordinates

end

end
