module

public import SphereSixComplex.Topology.PaperActualEllipticWholeRelatorClassificationProof
public import SphereSixComplex.Periods.ExactFuchsianRamification

/-!
# The cubic order-three base coordinate

The normalized affine coordinate has exact analytic order three when written in the
order-three Cayley chart.  This is the local analytic input for identifying the complete
filling loop with the cube of the counterclockwise zero meridian.
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
public theorem orderThreeCayleyRegularCoordinate_chartFunction
    (z : UpperHalfPlane) :
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint
        ((orderThreeCayleyHomeomorph z :
          SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) =
      A.modular.sourceCoordinate.coordinate z := by
  unfold ellipticChartFunction
  let w := orderThreeCayleyHomeomorph z
  have him : 0 < (cayleyRawInverse fuchsianOneFixedPoint (w : ℂ)).im :=
    cayleyRawInverse_im_pos w.property
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  change A.modular.sourceCoordinate.coordinate
      (cayleyInverseUpper fuchsianOneFixedPoint w) =
    A.modular.sourceCoordinate.coordinate z
  rw [show cayleyInverseUpper fuchsianOneFixedPoint w = z by
    exact orderThreeCayleyHomeomorph.symm_apply_apply z]

/-- The normalized affine coordinate has exact order three in the order-three Cayley chart. -/
public theorem orderThreeCayleyRegularCoordinate_analyticOrderAt :
    analyticOrderAt
      (ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint) 0 = 3 := by
  change analyticOrderAt
      (fun w : ℂ =>
        A.modular.sourceCoordinate.coordinate
          (UpperHalfPlane.ofComplex
            (cayleyRawInverse fuchsianOneFixedPoint w))) 0 = 3
  let f : ℂ → ℂ := fun z =>
    A.modular.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex z) - 0
  have hbase :
      analyticOrderAt f (fuchsianOneFixedPoint : ℂ) = 3 := by
    simpa [f] using
      A.modular.sourceCoordinate.branch_one.analyticOrderAt
        A.modular.sourceCoordinate.coordinate_holomorphic
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) (g := cayleyRawInverse fuchsianOneFixedPoint) (z₀ := (0 : ℂ))
    (cayleyRawInverse_analyticAt_zero fuchsianOneFixedPoint)
    (cayleyRawInverse_deriv_zero_ne fuchsianOneFixedPoint)
  rw [cayleyRawInverse_zero, hbase] at hcomp
  simpa [f, Function.comp_def] using hcomp

/-- Near the order-three centre, the affine coordinate is a Cayley-coordinate cube times a
nonvanishing analytic unit. -/
public theorem exists_orderThreeCayleyRegularCoordinate_cubicUnit :
    ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧
      u 0 ≠ 0 ∧
      ∀ᶠ w in 𝓝 0,
        ellipticChartFunction A.modular.sourceCoordinate.coordinate
            fuchsianOneFixedPoint w = w ^ 3 * u w := by
  let G : ℂ → ℂ :=
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianOneFixedPoint
  have hG : AnalyticAt ℂ G 0 :=
    ellipticChartFunction_analyticAt_zero
      A.modular.sourceCoordinate.coordinate_holomorphic fuchsianOneFixedPoint
  have horder : analyticOrderAt G 0 = (3 : ℕ∞) := by
    simpa [G] using A.orderThreeCayleyRegularCoordinate_analyticOrderAt
  obtain ⟨u, hu, hu0, hfac⟩ :=
    (hG.analyticOrderAt_eq_natCast (n := 3)).mp horder
  refine ⟨u, hu, hu0, ?_⟩
  simpa [G, smul_eq_mul] using hfac

/-- The affine base coordinate of the projected complete order-three filling loop is obtained by
applying the cubic local chart function to its explicit one-turn Cayley loop. -/
public theorem orderThreeFillingRelation_baseCoordinate_eq_chartFunction
    (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    (A.centralFamilyCoordinate
      (((A.orderThreeFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderThreeCollarRegularRepresentative_base_projects.symm
          A.orderThreeCollarRegularRepresentative_base_projects.symm) t)).1 =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint (A.orderThreeFillingRelationCayleyLoop t).1 := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  change (A.centralFamilyCoordinate
    (A.centralQuotientProjection (A.orderThreeFillingRelationRegularLoop t))).1 = _
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  change A.modular.sourceCoordinate.coordinate
      (regularTotalSpaceBase A.periods
        (A.orderThreeCollarRegularRepresentativeMap
          (A.orderThreeActualEllipticBoundaryDeckStraightLift
            A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t))).1 = _
  let _ := A.totalSpaceCharts
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let lift :=
    A.orderThreeActualEllipticBoundaryDeckStraightLift
      A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t
  let q :=
    orderThreePuncturedCollarGaugeEquiv A.periods
      A.starSeparation.orderThree.radius
      (A.orderThreeCollarInverseRepresentative lift)
  change A.modular.sourceCoordinate.coordinate
      (regularTotalSpaceBase A.periods
        (orderThreeCollarToRegular A.periods hproper
          A.starSeparation.orderThree.sourceData q)).1 = _
  have hbase :=
    orderThreeCollarToRegular_base A.periods hproper
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderThree.sourceData q
  have hqbase :
      familyTotalSpaceBase A.periods q =
        familyTotalSpaceBase A.periods
          (A.orderThreeCollarInverseRepresentative lift).1 := by
    change familyTotalSpaceBase A.periods
        (orderThreePrincipalGaugeEquiv A.periods
          (A.orderThreeCollarInverseRepresentative lift).1) =
      familyTotalSpaceBase A.periods
        (A.orderThreeCollarInverseRepresentative lift).1
    rw [orderThreePrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply,
      familyTotalSpaceBase_familyTranslationMap]
  calc
    _ = A.modular.sourceCoordinate.coordinate
        (familyTotalSpaceBase A.periods q) :=
      congrArg A.modular.sourceCoordinate.coordinate hbase
    _ = A.modular.sourceCoordinate.coordinate
        (familyTotalSpaceBase A.periods
          (A.orderThreeCollarInverseRepresentative lift).1) :=
      congrArg A.modular.sourceCoordinate.coordinate hqbase
    _ = ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint
        ((orderThreeCayleyHomeomorph
          (familyTotalSpaceBase A.periods
            (A.orderThreeCollarInverseRepresentative lift).1) :
              SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) :=
      (A.orderThreeCayleyRegularCoordinate_chartFunction _).symm
    _ = _ := congrArg
      (ellipticChartFunction A.modular.sourceCoordinate.coordinate
        fuchsianOneFixedPoint)
      (A.orderThreeFillingRelationCayleyLoop_apply t)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
