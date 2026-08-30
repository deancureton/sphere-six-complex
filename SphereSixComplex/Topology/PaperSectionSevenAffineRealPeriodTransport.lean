module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandEndpointFormula

/-!
# Real-period coordinates under the affine radial transports

The lifted radial inverses used at the order-three and order-four ends move only the base point
of the regular torus family.  Their canonical real-period coordinate is unchanged.  These two
formulas remove the radial-transport part of the marked-band endpoint calculation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent

/-- The explicit order-three fibre transfer preserves the fixed order-three real-period torus
coordinate. -/
public theorem orderThreeRealPeriodProductHomeomorph_fiberTransfer_snd
    (A : PaperAnalyticData)
    (w : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (q : RegularTotalSpace A.periods) :
    (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods (A.fiberTransfer w q))).2 =
    (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods q)).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [A.fiberTransfer_mk, regularFamilyInclusion_mk, regularFamilyInclusion_mk,
      orderThreeRealPeriodProductHomeomorph_mk,
      orderThreeRealPeriodProductHomeomorph_mk]
    apply congrArg (Quotient.mk _)
    change (fullRankDomain
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne)).realEquiv
      (periodCoordinates (regularParameterMap A.periods w)
        ((fullRankDomain (regularParameterMap A.periods w)).realEquiv
          (periodCoordinates (regularParameterMap A.periods p.1) p.2))) =
      (fullRankDomain
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne)).realEquiv
        (periodCoordinates (regularParameterMap A.periods p.1) p.2)
    simp [periodCoordinates]

/-- The explicit order-four flat transport preserves the fixed order-four real-period torus
coordinate. -/
public theorem orderFourRealPeriodProductHomeomorph_regularFlatTransport_snd
    (A : PaperAnalyticData)
    (w : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (q : RegularTotalSpace A.periods) :
    (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods (A.regularFlatTransport (w, q)))).2 =
    (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods q)).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [A.regularFlatTransport_mk, regularFamilyInclusion_mk, regularFamilyInclusion_mk,
      orderFourRealPeriodProductHomeomorph_mk,
      orderFourRealPeriodProductHomeomorph_mk]
    apply congrArg (Quotient.mk _)
    change (fullRankDomain
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo)).realEquiv
      (periodCoordinates (regularParameterMap A.periods w)
        ((fullRankDomain (regularParameterMap A.periods w)).realEquiv
          (periodCoordinates (regularParameterMap A.periods p.1) p.2))) =
      (fullRankDomain
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo)).realEquiv
        (periodCoordinates (regularParameterMap A.periods p.1) p.2)
    simp [periodCoordinates]

/-- The two remaining star-coordinate endpoint equations imply the original marked-band
compatibility statement. -/
public theorem markedBandHomotopies_of_starEndpointCompatibility
    (A : PaperAnalyticData) (H : A.SectionSevenAffineMarkedStarEndpointCompatibility) :
    A.SectionSevenAffineOverlapBandCompatibility :=
  markedBandHomotopies_of_discEndpointCompatibility A H.toDiscEndpointCompatibility

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
