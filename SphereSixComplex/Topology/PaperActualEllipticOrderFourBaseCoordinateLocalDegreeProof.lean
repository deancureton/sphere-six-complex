module

public import SphereSixComplex.Topology.PaperActualEllipticWholeRelatorClassificationProof
public import SphereSixComplex.Periods.ExactFuchsianRamification

/-!
# The quartic order-four base coordinate

The normalized affine coordinate minus one has exact analytic order four when written in the
order-four Cayley chart. This is the local analytic input for identifying the complete filling
loop with the fourth power of the counterclockwise one meridian.
-/

@[expose] public section

noncomputable section

open Complex Filter Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Periods
open SphereSixComplex.Periods.SourceAutomaticBranch
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- Evaluating the local chart function on the Cayley coordinate recovers the original
normalized affine coordinate. -/
public theorem orderFourCayleyRegularCoordinate_chartFunction
    (z : UpperHalfPlane) :
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint
        ((orderFourCayleyHomeomorph z :
          SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) =
      A.modular.sourceCoordinate.coordinate z := by
  unfold ellipticChartFunction
  let w := orderFourCayleyHomeomorph z
  have him : 0 < (cayleyRawInverse fuchsianTwoFixedPoint (w : ℂ)).im :=
    cayleyRawInverse_im_pos w.property
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  change A.modular.sourceCoordinate.coordinate
      (cayleyInverseUpper fuchsianTwoFixedPoint w) =
    A.modular.sourceCoordinate.coordinate z
  rw [show cayleyInverseUpper fuchsianTwoFixedPoint w = z by
    exact orderFourCayleyHomeomorph.symm_apply_apply z]

/-- The normalized affine coordinate minus one has exact order four in the order-four Cayley
chart. -/
public theorem orderFourCayleyRegularCoordinate_sub_one_analyticOrderAt :
    analyticOrderAt
      (fun w : ℂ ↦
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint w - 1) 0 = 4 := by
  change analyticOrderAt
      (fun w : ℂ ↦
        A.modular.sourceCoordinate.coordinate
          (UpperHalfPlane.ofComplex
            (cayleyRawInverse fuchsianTwoFixedPoint w)) - 1) 0 = 4
  let f : ℂ → ℂ := fun z ↦
    A.modular.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex z) - 1
  have hbase :
      analyticOrderAt f (fuchsianTwoFixedPoint : ℂ) = 4 := by
    simpa [f] using
      A.modular.sourceCoordinate.branch_two.analyticOrderAt
        A.modular.sourceCoordinate.coordinate_holomorphic
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) (g := cayleyRawInverse fuchsianTwoFixedPoint) (z₀ := (0 : ℂ))
    (cayleyRawInverse_analyticAt_zero fuchsianTwoFixedPoint)
    (cayleyRawInverse_deriv_zero_ne fuchsianTwoFixedPoint)
  rw [cayleyRawInverse_zero, hbase] at hcomp
  simpa [f, Function.comp_def] using hcomp

/-- Near the order-four centre, the affine coordinate minus one is a Cayley-coordinate fourth
power times a nonvanishing analytic unit. -/
public theorem exists_orderFourCayleyRegularCoordinate_quarticUnit :
    ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧
      u 0 ≠ 0 ∧
      ∀ᶠ w in 𝓝 0,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
            fuchsianTwoFixedPoint w - 1 = w ^ 4 * u w := by
  let G : ℂ → ℂ := fun w ↦
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianTwoFixedPoint w - 1
  have hG : AnalyticAt ℂ G 0 :=
    (ellipticChartFunction_analyticAt_zero
      A.modular.sourceCoordinate.coordinate_holomorphic fuchsianTwoFixedPoint).sub
        analyticAt_const
  have horder : analyticOrderAt G 0 = (4 : ℕ∞) := by
    simpa [G] using A.orderFourCayleyRegularCoordinate_sub_one_analyticOrderAt
  obtain ⟨u, hu, hu0, hfac⟩ :=
    (hG.analyticOrderAt_eq_natCast (n := 4)).mp horder
  refine ⟨u, hu, hu0, ?_⟩
  simpa [G, smul_eq_mul] using hfac

/-- The affine base coordinate of the projected complete order-four filling loop is obtained by
applying the quartic local chart function to its explicit one-turn Cayley loop. -/
public theorem orderFourFillingRelation_baseCoordinate_eq_chartFunction
    (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    (A.centralFamilyCoordinate
      (((A.orderFourFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderFourCollarRegularRepresentative_base_projects.symm
          A.orderFourCollarRegularRepresentative_base_projects.symm) t)).1 =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint (A.orderFourFillingRelationCayleyLoop t).1 := by
  let _ := A.orderFourActualEllipticBoundaryAction
  change (A.centralFamilyCoordinate
    (A.centralQuotientProjection (A.orderFourFillingRelationRegularLoop t))).1 = _
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  change A.modular.sourceCoordinate.coordinate
      (regularTotalSpaceBase A.periods
        (A.orderFourCollarRegularRepresentativeMap
          (A.orderFourActualEllipticBoundaryDeckStraightLift
            A.orderFourActualEllipticBoundaryDeckData.fillingRelation t))).1 = _
  let _ := A.totalSpaceCharts
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let lift :=
    A.orderFourActualEllipticBoundaryDeckStraightLift
      A.orderFourActualEllipticBoundaryDeckData.fillingRelation t
  let q :=
    orderFourPuncturedCollarGaugeEquiv A.periods
      A.starSeparation.orderFour.radius
      (A.orderFourCollarInverseRepresentative lift)
  change A.modular.sourceCoordinate.coordinate
      (regularTotalSpaceBase A.periods
        (orderFourCollarToRegular A.periods hproper
          A.starSeparation.orderFour.sourceData q)).1 = _
  have hbase :=
    orderFourCollarToRegular_base A.periods hproper
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.sourceData q
  have hqbase :
      familyTotalSpaceBase A.periods q =
        familyTotalSpaceBase A.periods
          (A.orderFourCollarInverseRepresentative lift).1 := by
    change familyTotalSpaceBase A.periods
        (orderFourPrincipalGaugeEquiv A.periods
          (A.orderFourCollarInverseRepresentative lift).1) =
      familyTotalSpaceBase A.periods
        (A.orderFourCollarInverseRepresentative lift).1
    rw [orderFourPrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply,
      familyTotalSpaceBase_familyTranslationMap]
  calc
    _ = A.modular.sourceCoordinate.coordinate
        (familyTotalSpaceBase A.periods q) :=
      congrArg A.modular.sourceCoordinate.coordinate hbase
    _ = A.modular.sourceCoordinate.coordinate
        (familyTotalSpaceBase A.periods
          (A.orderFourCollarInverseRepresentative lift).1) :=
      congrArg A.modular.sourceCoordinate.coordinate hqbase
    _ = ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint
        ((orderFourCayleyHomeomorph
          (familyTotalSpaceBase A.periods
            (A.orderFourCollarInverseRepresentative lift).1) :
              SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) :=
      (A.orderFourCayleyRegularCoordinate_chartFunction _).symm
    _ = _ := congrArg
      (ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianTwoFixedPoint)
      (A.orderFourFillingRelationCayleyLoop_apply t)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
