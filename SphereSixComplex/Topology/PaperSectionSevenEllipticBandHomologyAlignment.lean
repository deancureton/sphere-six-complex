module

public import SphereSixComplex.Topology.PaperSectionSevenCentralBandSplit

/-!
# Homology alignment for the Section 7 elliptic band

The real-period-coordinate homeomorphism between two full-rank period tori preserves the
standard integral period bases.  This standard naturality fact supplies the common band basis
for the genuine height-split Section 7 cover.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization
open Topology.PaperEllipticFillingRadialRetraction
open Topology.PaperEllipticReducedCentralFiberCoverModels

private theorem homologyEquiv_map_symm
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (e : X ≃ₜ Y) (z : IntegralSingularHomology k Y) :
    integralSingularHomologyEquiv k e
        (integralSingularHomologyMap k ⟨e.symm, e.symm.continuous⟩ z) = z :=
  (integralSingularHomologyEquiv k e).apply_symm_apply z

private theorem homologyEquiv_map_trans_symm
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (k : ℕ) (e : X ≃ₜ Y) (h : Z ≃ₜ Y) (z : IntegralSingularHomology k Z) :
    integralSingularHomologyEquiv k e
        (integralSingularHomologyMap k
          ⟨h.trans e.symm, (h.trans e.symm).continuous⟩ z) =
      integralSingularHomologyMap k ⟨h, h.continuous⟩ z := by
  change integralSingularHomologyEquiv k e
      (integralSingularHomologyMap k
        ((⟨e.symm, e.symm.continuous⟩ : C(Y, X)).comp
          (⟨h, h.continuous⟩ : C(Z, Y))) z) = _
  rw [Geometry.PaperAnalyticData.EllipticBandHomologyAlignment.integralHomologyMap_comp]
  exact (integralSingularHomologyEquiv k e).apply_symm_apply _

namespace EstablishedTorusHomology

/-- The real-period-coordinate homeomorphism between full-rank period tori preserves the
standard integral period bases in degrees one and two.  This is the cross-parameter naturality
part of the usual homology calculation for a real four-torus. -/
public axiom fullRankAdditiveTorusHomeomorph_naturality
    (x y : Periods.Parameters) (hx : FullRank x) (hy : FullRank y) :
    let e := Geometry.PaperAnalyticData.fullRankAdditiveTorusHomeomorph x y hx hy
    let Bx := additiveTorusHomologyBasis x hx
    let By := additiveTorusHomologyBasis y hy
    (∀ z, By.degreeOne (integralSingularHomologyMap 1 e z) = Bx.degreeOne z) ∧
      (∀ z, By.degreeTwo (integralSingularHomologyMap 2 e z) = Bx.degreeTwo z)

end EstablishedTorusHomology

namespace Geometry.PaperAnalyticData

variable {A : PaperAnalyticData} {S : A.SectionSevenCentralHeightSplit}

/-- The canonical period-coordinate identifications in a genuine height-split radial input
induce the same integral period basis from both sides of its central band. -/
public theorem SectionSevenCentralHeightSplit.RadialInput.bandHomologyAlignment
    (R : S.RadialInput) :
    A.EllipticBandHomologyAlignment
      R.toRadialRealization.toSectionSevenEllipticTwoDiscCoverData where
  degreeOne z := by
    change IntegralSingularHomology 1
      (AdditiveTorus (AnalyticTorusFamily.parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1) at z
    have h := (EstablishedTorusHomology.fullRankAdditiveTorusHomeomorph_naturality
      A.duplicatedSectionSevenBandParameter
      (AnalyticTorusFamily.parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1
      A.duplicatedSectionSevenBandFullRank
      (FullRank.ofSetupInequalities
        (AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1
        (AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).2)).1 z
    dsimp only [SectionSevenCentralHeightSplit.RadialInput.toRadialRealization,
      SectionSevenEllipticCentralAllocation.RadialRealization.toSectionSevenEllipticTwoDiscCoverData,
      duplicatedSectionSevenBandToOrderThreeCoverSource,
      duplicatedSectionSevenBandToOrderFourCoverSource,
      orderThreeCentralFiberCoverSourceHomologyBasis,
      orderFourCentralFiberCoverSourceHomologyBasis,
      FourTorusHomologyBasis.homeomorph]
    change (orderFourTorusHomologyBasis A.periods).degreeOne
        (integralSingularHomologyEquiv 1
          (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderFourRadialActionData A.periods))
          (integralSingularHomologyMap 1
            ⟨A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.trans
                (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
                  (orderFourRadialActionData A.periods)).symm,
              (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.trans
                (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
                  (orderFourRadialActionData A.periods)).symm).continuous⟩ z)) =
      (orderThreeTorusHomologyBasis A.periods).degreeOne
        (integralSingularHomologyEquiv 1
          (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderThreeRadialActionData A.periods))
          (integralSingularHomologyMap 1
            ⟨(RadialEllipticActionData.centralFiberCoverSourceHomeomorph
                (orderThreeRadialActionData A.periods)).symm,
              (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
                (orderThreeRadialActionData A.periods)).symm.continuous⟩ z))
    rw [homologyEquiv_map_trans_symm 1
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
        (orderFourRadialActionData A.periods))
      A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph z,
      homologyEquiv_map_symm 1
        (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData A.periods)) z]
    exact h
  degreeTwo z := by
    change IntegralSingularHomology 2
      (AdditiveTorus (AnalyticTorusFamily.parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1) at z
    have h := (EstablishedTorusHomology.fullRankAdditiveTorusHomeomorph_naturality
      A.duplicatedSectionSevenBandParameter
      (AnalyticTorusFamily.parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1
      A.duplicatedSectionSevenBandFullRank
      (FullRank.ofSetupInequalities
        (AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1
        (AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).2)).2 z
    dsimp only [SectionSevenCentralHeightSplit.RadialInput.toRadialRealization,
      SectionSevenEllipticCentralAllocation.RadialRealization.toSectionSevenEllipticTwoDiscCoverData,
      duplicatedSectionSevenBandToOrderThreeCoverSource,
      duplicatedSectionSevenBandToOrderFourCoverSource,
      orderThreeCentralFiberCoverSourceHomologyBasis,
      orderFourCentralFiberCoverSourceHomologyBasis,
      FourTorusHomologyBasis.homeomorph]
    change (orderFourTorusHomologyBasis A.periods).degreeTwo
        (integralSingularHomologyEquiv 2
          (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderFourRadialActionData A.periods))
          (integralSingularHomologyMap 2
            ⟨A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.trans
                (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
                  (orderFourRadialActionData A.periods)).symm,
              (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.trans
                (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
                  (orderFourRadialActionData A.periods)).symm).continuous⟩ z)) =
      (orderThreeTorusHomologyBasis A.periods).degreeTwo
        (integralSingularHomologyEquiv 2
          (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderThreeRadialActionData A.periods))
          (integralSingularHomologyMap 2
            ⟨(RadialEllipticActionData.centralFiberCoverSourceHomeomorph
                (orderThreeRadialActionData A.periods)).symm,
              (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
                (orderThreeRadialActionData A.periods)).symm.continuous⟩ z))
    rw [homologyEquiv_map_trans_symm 2
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
        (orderFourRadialActionData A.periods))
      A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph z,
      homologyEquiv_map_symm 2
        (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData A.periods)) z]
    exact h

end Geometry.PaperAnalyticData

end SphereSixComplex
