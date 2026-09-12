module

public import SphereSixComplex.Paper.Topology.PaperEllipticCollarLoopClassProof

/-!
# Principal-gauge winding along the elliptic filling relations
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLogarithmicGauge
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily

variable (A : AnalyticData)

public theorem angleMap_three_linear_fullTurn (θ s : ℝ) :
    angleMap 3 (θ + 3 * s) =
      angleMap 3 θ * Circle.exp (2 * Real.pi * s) := by
  rw [angleMap, angleMap, ← Circle.exp_add]
  congr 1
  norm_num
  ring

public theorem angleMap_four_linear_fullTurn (θ s : ℝ) :
    angleMap 4 (θ + 4 * s) =
      angleMap 4 θ * Circle.exp (2 * Real.pi * s) := by
  rw [angleMap, angleMap, ← Circle.exp_add]
  congr 1
  norm_num
  ring

public theorem orderThreeCollarInverseRepresentative_cayley
    (q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace)) :
    ((orderThreeCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderThreeCollarInverseRepresentative q).1) : ComplexUnitDisc) : ℂ) =
      ((q.1 : ℝ) : ℂ) * ((angleMap 3 q.2.1 : Circle) : ℂ) := by
  have h := congrArg (fun z => ((z.1.1 : ComplexUnitDisc) : ℂ))
    (A.orderThreePuncturedProductHomeomorph_inverseRepresentative q)
  exact h.trans (angularCover_fst 3
    A.starSeparation.orderThree.radius_lt_one.le
    (q.1, q.2.1, Quotient.mk _ q.2.2))

public theorem orderFourCollarInverseRepresentative_cayley
    (q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace)) :
    ((orderFourCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderFourCollarInverseRepresentative q).1) : ComplexUnitDisc) : ℂ) =
      ((q.1 : ℝ) : ℂ) * ((angleMap 4 q.2.1 : Circle) : ℂ) := by
  have h := congrArg (fun z => ((z.1.1 : ComplexUnitDisc) : ℂ))
    (A.orderFourPuncturedProductHomeomorph_inverseRepresentative q)
  exact h.trans (angularCover_fst 4
    A.starSeparation.orderFour.radius_lt_one.le
    (q.1, q.2.1, Quotient.mk _ q.2.2))

public theorem orderThreeFillingRelationStraightLift_angle
    (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    (A.ellipticThreeBoundaryDeckStraightLift
      A.ellipticThreeBoundaryDeckData.fillingRelation t).2.1 =
        A.ellipticThreeBoundaryBase.2.1 + 3 * (t : ℝ) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticThreeBoundaryAction
  have h : A.ellipticThreeBoundaryDeckData.fillingRelation •
      A.ellipticThreeBoundaryBase.2 =
        (A.ellipticThreeBoundaryBase.2.1 + 3,
          A.ellipticThreeBoundaryBase.2.2) := by
    change (A.ellipticThreeBoundaryDeckData.fillingRelation •
      A.ellipticThreeBoundaryBase).2 = _
    rw [A.ellipticThreeFillingRelation_boundary_smul]
  simp [ellipticThreeBoundaryDeckStraightLift, h,
    AffineMap.lineMap_apply]
  ring

public theorem orderFourFillingRelationStraightLift_angle
    (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    (A.ellipticFourBoundaryDeckStraightLift
      A.ellipticFourBoundaryDeckData.fillingRelation t).2.1 =
        A.ellipticFourBoundaryBase.2.1 + 4 * (t : ℝ) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticFourBoundaryAction
  have h : A.ellipticFourBoundaryDeckData.fillingRelation •
      A.ellipticFourBoundaryBase.2 =
        (A.ellipticFourBoundaryBase.2.1 + 4,
          A.ellipticFourBoundaryBase.2.2) := by
    change (A.ellipticFourBoundaryDeckData.fillingRelation •
      A.ellipticFourBoundaryBase).2 = _
    rw [A.ellipticFourFillingRelation_boundary_smul]
  simp [ellipticFourBoundaryDeckStraightLift, h,
    AffineMap.lineMap_apply]
  ring

public theorem orderThreeFillingRelationInverseRepresentative_cayley
    (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    ((orderThreeCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderThreeCollarInverseRepresentative
          (A.ellipticThreeBoundaryDeckStraightLift
            A.ellipticThreeBoundaryDeckData.fillingRelation t)).1) :
          ComplexUnitDisc) : ℂ) =
      ((A.ellipticThreeBoundaryBase.1 : ℝ) : ℂ) *
        ((angleMap 3
          (A.ellipticThreeBoundaryBase.2.1 + 3 * (t : ℝ)) : Circle) : ℂ) := by
  let _ := A.ellipticThreeBoundaryAction
  rw [A.orderThreeCollarInverseRepresentative_cayley]
  rw [A.orderThreeFillingRelationStraightLift_angle]
  rfl

public theorem orderFourFillingRelationInverseRepresentative_cayley
    (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    ((orderFourCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderFourCollarInverseRepresentative
          (A.ellipticFourBoundaryDeckStraightLift
            A.ellipticFourBoundaryDeckData.fillingRelation t)).1) :
          ComplexUnitDisc) : ℂ) =
      ((A.ellipticFourBoundaryBase.1 : ℝ) : ℂ) *
        ((angleMap 4
          (A.ellipticFourBoundaryBase.2.1 + 4 * (t : ℝ)) : Circle) : ℂ) := by
  let _ := A.ellipticFourBoundaryAction
  rw [A.orderFourCollarInverseRepresentative_cayley]
  rw [A.orderFourFillingRelationStraightLift_angle]
  rfl

public theorem orderThreeFillingRelationInverseRepresentative_cayley_fullTurn
    (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    ((orderThreeCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderThreeCollarInverseRepresentative
          (A.ellipticThreeBoundaryDeckStraightLift
            A.ellipticThreeBoundaryDeckData.fillingRelation t)).1) :
          ComplexUnitDisc) : ℂ) =
      (((A.ellipticThreeBoundaryBase.1 : ℝ) : ℂ) *
          ((angleMap 3 A.ellipticThreeBoundaryBase.2.1 : Circle) : ℂ)) *
        ((Circle.exp (2 * Real.pi * (t : ℝ)) : Circle) : ℂ) := by
  let _ := A.ellipticThreeBoundaryAction
  rw [A.orderThreeFillingRelationInverseRepresentative_cayley]
  have h := congrArg (fun z : Circle => (z : ℂ))
    (angleMap_three_linear_fullTurn
      A.ellipticThreeBoundaryBase.2.1 (t : ℝ))
  rw [h, Circle.coe_mul]
  ring

public theorem orderFourFillingRelationInverseRepresentative_cayley_fullTurn
    (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    ((orderFourCayleyHomeomorph
      (familyTotalSpaceBase A.periods
        (A.orderFourCollarInverseRepresentative
          (A.ellipticFourBoundaryDeckStraightLift
            A.ellipticFourBoundaryDeckData.fillingRelation t)).1) :
          ComplexUnitDisc) : ℂ) =
      (((A.ellipticFourBoundaryBase.1 : ℝ) : ℂ) *
          ((angleMap 4 A.ellipticFourBoundaryBase.2.1 : Circle) : ℂ)) *
        ((Circle.exp (2 * Real.pi * (t : ℝ)) : Circle) : ℂ) := by
  let _ := A.ellipticFourBoundaryAction
  rw [A.orderFourFillingRelationInverseRepresentative_cayley]
  have h := congrArg (fun z : Circle => (z : ℂ))
    (angleMap_four_linear_fullTurn
      A.ellipticFourBoundaryBase.2.1 (t : ℝ))
  rw [h, Circle.coe_mul]
  ring

public noncomputable def orderThreeFillingRelationCayleyLogLift :
    C(unitInterval, ℂ) where
  toFun t := (Real.log (A.ellipticThreeBoundaryBase.1 : ℝ) : ℂ) +
    (((2 * Real.pi / 3) *
      (A.ellipticThreeBoundaryBase.2.1 + 3 * (t : ℝ)) : ℝ) : ℂ) *
      Complex.I
  continuous_toFun := by fun_prop

public noncomputable def orderFourFillingRelationCayleyLogLift :
    C(unitInterval, ℂ) where
  toFun t := (Real.log (A.ellipticFourBoundaryBase.1 : ℝ) : ℂ) +
    (((2 * Real.pi / 4) *
      (A.ellipticFourBoundaryBase.2.1 + 4 * (t : ℝ)) : ℝ) : ℂ) *
      Complex.I
  continuous_toFun := by fun_prop

public theorem orderThreeFillingRelationCayleyLogLift_exp
    (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    Complex.exp (A.orderThreeFillingRelationCayleyLogLift t) =
      ((orderThreeCayleyHomeomorph
        (familyTotalSpaceBase A.periods
          (A.orderThreeCollarInverseRepresentative
            (A.ellipticThreeBoundaryDeckStraightLift
              A.ellipticThreeBoundaryDeckData.fillingRelation t)).1) :
            ComplexUnitDisc) : ℂ) := by
  let _ := A.ellipticThreeBoundaryAction
  rw [A.orderThreeFillingRelationInverseRepresentative_cayley]
  change Complex.exp
      ((Real.log (A.ellipticThreeBoundaryBase.1 : ℝ) : ℂ) +
        (((2 * Real.pi / 3) *
          (A.ellipticThreeBoundaryBase.2.1 + 3 * (t : ℝ)) : ℝ) : ℂ) *
          Complex.I) = _
  rw [angleMap_coe, Complex.exp_add]
  rw [show Complex.exp
      (Real.log (A.ellipticThreeBoundaryBase.1 : ℝ) : ℂ) =
        ((A.ellipticThreeBoundaryBase.1 : ℝ) : ℂ) by
    rw [← Complex.ofReal_exp,
      Real.exp_log A.ellipticThreeBoundaryBase.1.2.1]]
  rfl

public theorem orderFourFillingRelationCayleyLogLift_exp
    (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    Complex.exp (A.orderFourFillingRelationCayleyLogLift t) =
      ((orderFourCayleyHomeomorph
        (familyTotalSpaceBase A.periods
          (A.orderFourCollarInverseRepresentative
            (A.ellipticFourBoundaryDeckStraightLift
              A.ellipticFourBoundaryDeckData.fillingRelation t)).1) :
            ComplexUnitDisc) : ℂ) := by
  let _ := A.ellipticFourBoundaryAction
  rw [A.orderFourFillingRelationInverseRepresentative_cayley]
  change Complex.exp
      ((Real.log (A.ellipticFourBoundaryBase.1 : ℝ) : ℂ) +
        (((2 * Real.pi / 4) *
          (A.ellipticFourBoundaryBase.2.1 + 4 * (t : ℝ)) : ℝ) : ℂ) *
          Complex.I) = _
  rw [angleMap_coe, Complex.exp_add]
  rw [show Complex.exp
      (Real.log (A.ellipticFourBoundaryBase.1 : ℝ) : ℂ) =
        ((A.ellipticFourBoundaryBase.1 : ℝ) : ℂ) by
    rw [← Complex.ofReal_exp,
      Real.exp_log A.ellipticFourBoundaryBase.1.2.1]]
  rfl

public theorem orderThreeFillingRelationCayleyLogLift_endpoint :
    A.orderThreeFillingRelationCayleyLogLift 1 =
      A.orderThreeFillingRelationCayleyLogLift 0 +
        (2 : ℂ) * Real.pi * Complex.I := by
  simp [orderThreeFillingRelationCayleyLogLift]
  ring

public theorem orderFourFillingRelationCayleyLogLift_endpoint :
    A.orderFourFillingRelationCayleyLogLift 1 =
      A.orderFourFillingRelationCayleyLogLift 0 +
        (2 : ℂ) * Real.pi * Complex.I := by
  simp [orderFourFillingRelationCayleyLogLift]
  ring

public theorem orderThreeFillingRelationGaugeScalar_endpoint :
    logarithmicGaugeScalar (A.orderThreeFillingRelationCayleyLogLift 1) =
      logarithmicGaugeScalar (A.orderThreeFillingRelationCayleyLogLift 0) + 1 := by
  rw [A.orderThreeFillingRelationCayleyLogLift_endpoint]
  simpa using logarithmicGaugeScalar_add_period
    (1 : ℤ) (A.orderThreeFillingRelationCayleyLogLift 0)

public theorem orderFourFillingRelationGaugeScalar_endpoint :
    logarithmicGaugeScalar (A.orderFourFillingRelationCayleyLogLift 1) =
      logarithmicGaugeScalar (A.orderFourFillingRelationCayleyLogLift 0) + 1 := by
  rw [A.orderFourFillingRelationCayleyLogLift_endpoint]
  simpa using logarithmicGaugeScalar_add_period
    (1 : ℤ) (A.orderFourFillingRelationCayleyLogLift 0)

public noncomputable def orderThreeFillingRelationPrincipalGaugeCoverLift
    (t : unitInterval) : ComplexTwoSpace :=
  let z := familyTotalSpaceBase A.periods
    (A.orderThreeCollarInverseRepresentative
      (A.ellipticThreeBoundaryDeckStraightLift
        A.ellipticThreeBoundaryDeckData.fillingRelation t)).1
  (movingToFixedCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
    (z, logarithmicGaugeScalar (A.orderThreeFillingRelationCayleyLogLift t) •
      periodVector (parameterMap A.periods z).1 epsilon)).2

public noncomputable def orderFourFillingRelationPrincipalGaugeCoverLift
    (t : unitInterval) : ComplexTwoSpace :=
  let z := familyTotalSpaceBase A.periods
    (A.orderFourCollarInverseRepresentative
      (A.ellipticFourBoundaryDeckStraightLift
        A.ellipticFourBoundaryDeckData.fillingRelation t)).1
  (movingToFixedCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo
    (z, logarithmicGaugeScalar (A.orderFourFillingRelationCayleyLogLift t) •
      periodVector (parameterMap A.periods z).1 (-epsilon'))).2

public theorem orderThreeFillingRelationPrincipalGaugeCoverLift_projects
    (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    let z := familyTotalSpaceBase A.periods
      (A.orderThreeCollarInverseRepresentative
        (A.ellipticThreeBoundaryDeckStraightLift
          A.ellipticThreeBoundaryDeckData.fillingRelation t)).1
    torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1
        (A.orderThreeFillingRelationPrincipalGaugeCoverLift t) =
      A.orderThreePrincipalRealPeriodGauge z := by
  let _ := A.ellipticThreeBoundaryAction
  let z := familyTotalSpaceBase A.periods
    (A.orderThreeCollarInverseRepresentative
      (A.ellipticThreeBoundaryDeckStraightLift
        A.ellipticThreeBoundaryDeckData.fillingRelation t)).1
  let w := orderThreeCayleyHomeomorph z
  have hw : (w : ℂ) ≠ 0 := by
    rw [show (w : ℂ) =
        ((A.ellipticThreeBoundaryBase.1 : ℝ) : ℂ) *
          ((angleMap 3
            (A.ellipticThreeBoundaryBase.2.1 + 3 * (t : ℝ)) : Circle) : ℂ) by
      exact A.orderThreeFillingRelationInverseRepresentative_cayley t]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr
        (ne_of_gt A.ellipticThreeBoundaryBase.1.2.1))
      (Circle.coe_ne_zero _)
  have hexp : Complex.exp (Complex.log w) =
      Complex.exp (A.orderThreeFillingRelationCayleyLogLift t) := by
    rw [Complex.exp_log hw]
    exact (A.orderThreeFillingRelationCayleyLogLift_exp t).symm
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hk' : Complex.log w =
      A.orderThreeFillingRelationCayleyLogLift t +
        ((2 : ℂ) * Real.pi * Complex.I) * k := by
    rw [hk]
    ring
  let q : TotalSpace (parameterMap A.periods) := Quotient.mk _ (z, 0)
  have hmap := logarithmicGaugeMap_mk_eq_of_branch_change A.periods
    orderThreeCayleyHomeomorph epsilon
    (fun _ => A.orderThreeFillingRelationCayleyLogLift t)
    (fun u => Complex.log u) z 0 k hk'
  have hcoord := congrArg
    (fun u => (orderThreeRealPeriodProductHomeomorph A.periods u).2) hmap
  rw [familyTranslationMap_mk, familyTranslationMap_mk,
    orderThreeRealPeriodProductHomeomorph_mk,
    orderThreeRealPeriodProductHomeomorph_mk] at hcoord
  simp only [familyTranslationCover, logarithmicGaugeSection, add_zero] at hcoord
  change (torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (z, logarithmicGaugeScalar
          (A.orderThreeFillingRelationCayleyLogLift t) •
            periodVector (parameterMap A.periods z).1 epsilon)).2) =
    torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (z, orderThreePrincipalGaugeSection A.periods z)).2
  change torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (z, orderThreePrincipalGaugeSection A.periods z)).2 =
    torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (z, logarithmicGaugeScalar
          (A.orderThreeFillingRelationCayleyLogLift t) •
            periodVector (parameterMap A.periods z).1 epsilon)).2 at hcoord
  exact hcoord.symm

public theorem orderFourFillingRelationPrincipalGaugeCoverLift_projects
    (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    let z := familyTotalSpaceBase A.periods
      (A.orderFourCollarInverseRepresentative
        (A.ellipticFourBoundaryDeckStraightLift
          A.ellipticFourBoundaryDeckData.fillingRelation t)).1
    torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1
        (A.orderFourFillingRelationPrincipalGaugeCoverLift t) =
      A.orderFourPrincipalRealPeriodGauge z := by
  let _ := A.ellipticFourBoundaryAction
  let z := familyTotalSpaceBase A.periods
    (A.orderFourCollarInverseRepresentative
      (A.ellipticFourBoundaryDeckStraightLift
        A.ellipticFourBoundaryDeckData.fillingRelation t)).1
  let w := orderFourCayleyHomeomorph z
  have hw : (w : ℂ) ≠ 0 := by
    rw [show (w : ℂ) =
        ((A.ellipticFourBoundaryBase.1 : ℝ) : ℂ) *
          ((angleMap 4
            (A.ellipticFourBoundaryBase.2.1 + 4 * (t : ℝ)) : Circle) : ℂ) by
      exact A.orderFourFillingRelationInverseRepresentative_cayley t]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr
        (ne_of_gt A.ellipticFourBoundaryBase.1.2.1))
      (Circle.coe_ne_zero _)
  have hexp : Complex.exp (Complex.log w) =
      Complex.exp (A.orderFourFillingRelationCayleyLogLift t) := by
    rw [Complex.exp_log hw]
    exact (A.orderFourFillingRelationCayleyLogLift_exp t).symm
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hk' : Complex.log w =
      A.orderFourFillingRelationCayleyLogLift t +
        ((2 : ℂ) * Real.pi * Complex.I) * k := by
    rw [hk]
    ring
  let q : TotalSpace (parameterMap A.periods) := Quotient.mk _ (z, 0)
  have hmap := logarithmicGaugeMap_mk_eq_of_branch_change A.periods
    orderFourCayleyHomeomorph (-epsilon')
    (fun _ => A.orderFourFillingRelationCayleyLogLift t)
    (fun u => Complex.log u) z 0 k hk'
  have hcoord := congrArg
    (fun u => (orderFourRealPeriodProductHomeomorph A.periods u).2) hmap
  rw [familyTranslationMap_mk, familyTranslationMap_mk,
    orderFourRealPeriodProductHomeomorph_mk,
    orderFourRealPeriodProductHomeomorph_mk] at hcoord
  simp only [familyTranslationCover, logarithmicGaugeSection, add_zero] at hcoord
  change (torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (z, logarithmicGaugeScalar
          (A.orderFourFillingRelationCayleyLogLift t) •
            periodVector (parameterMap A.periods z).1 (-epsilon'))).2) =
    torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (z, orderFourPrincipalGaugeSection A.periods z)).2
  change torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (z, orderFourPrincipalGaugeSection A.periods z)).2 =
    torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (z, logarithmicGaugeScalar
          (A.orderFourFillingRelationCayleyLogLift t) •
            periodVector (parameterMap A.periods z).1 (-epsilon'))).2 at hcoord
  exact hcoord.symm

public theorem orderThreeFillingRelationInverseRepresentative_endpoint :
    letI := A.ellipticThreeBoundaryAction
    A.orderThreeCollarInverseRepresentative
        (A.ellipticThreeBoundaryDeckStraightLift
          A.ellipticThreeBoundaryDeckData.fillingRelation 1) =
      A.orderThreeCollarInverseRepresentative
        (A.ellipticThreeBoundaryDeckStraightLift
          A.ellipticThreeBoundaryDeckData.fillingRelation 0) := by
  let _ := A.ellipticThreeBoundaryAction
  rw [(A.ellipticThreeBoundaryDeckStraightLift
    A.ellipticThreeBoundaryDeckData.fillingRelation).target]
  rw [(A.ellipticThreeBoundaryDeckStraightLift
    A.ellipticThreeBoundaryDeckData.fillingRelation).source]
  rw [A.ellipticThreeFillingRelation_boundary_smul]
  exact A.orderThreeCollarInverseRepresentative_fullTurn
    A.ellipticThreeBoundaryBase

public theorem orderFourFillingRelationInverseRepresentative_endpoint :
    letI := A.ellipticFourBoundaryAction
    A.orderFourCollarInverseRepresentative
        (A.ellipticFourBoundaryDeckStraightLift
          A.ellipticFourBoundaryDeckData.fillingRelation 1) =
      A.orderFourCollarInverseRepresentative
        (A.ellipticFourBoundaryDeckStraightLift
          A.ellipticFourBoundaryDeckData.fillingRelation 0) := by
  let _ := A.ellipticFourBoundaryAction
  rw [(A.ellipticFourBoundaryDeckStraightLift
    A.ellipticFourBoundaryDeckData.fillingRelation).target]
  rw [(A.ellipticFourBoundaryDeckStraightLift
    A.ellipticFourBoundaryDeckData.fillingRelation).source]
  rw [A.ellipticFourFillingRelation_boundary_smul]
  exact A.orderFourCollarInverseRepresentative_fullTurn
    A.ellipticFourBoundaryBase

public theorem orderThreeFillingRelationPrincipalGaugeCoverLift_endpoint :
    letI := A.ellipticThreeBoundaryAction
    A.orderThreeFillingRelationPrincipalGaugeCoverLift 1 =
      periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon +
        A.orderThreeFillingRelationPrincipalGaugeCoverLift 0 := by
  let _ := A.ellipticThreeBoundaryAction
  let z₀ := familyTotalSpaceBase A.periods
    (A.orderThreeCollarInverseRepresentative
      (A.ellipticThreeBoundaryDeckStraightLift
        A.ellipticThreeBoundaryDeckData.fillingRelation 0)).1
  let z₁ := familyTotalSpaceBase A.periods
    (A.orderThreeCollarInverseRepresentative
      (A.ellipticThreeBoundaryDeckStraightLift
        A.ellipticThreeBoundaryDeckData.fillingRelation 1)).1
  have hz : z₁ = z₀ := congrArg
    (fun q => familyTotalSpaceBase A.periods q.1)
    A.orderThreeFillingRelationInverseRepresentative_endpoint
  change (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne
      (z₁, logarithmicGaugeScalar
        (A.orderThreeFillingRelationCayleyLogLift 1) •
          periodVector (parameterMap A.periods z₁).1 epsilon)).2 = _
  rw [hz]
  change (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne
      (z₀, logarithmicGaugeScalar
        (A.orderThreeFillingRelationCayleyLogLift 1) •
          periodVector (parameterMap A.periods z₀).1 epsilon)).2 =
    periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon +
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (z₀, logarithmicGaugeScalar
          (A.orderThreeFillingRelationCayleyLogLift 0) •
            periodVector (parameterMap A.periods z₀).1 epsilon)).2
  rw [A.orderThreeFillingRelationGaugeScalar_endpoint]
  have hvec :
      (logarithmicGaugeScalar (A.orderThreeFillingRelationCayleyLogLift 0) + 1) •
          periodVector (parameterMap A.periods z₀).1 epsilon =
        periodVector (parameterMap A.periods z₀).1 epsilon +
          logarithmicGaugeScalar (A.orderThreeFillingRelationCayleyLogLift 0) •
            periodVector (parameterMap A.periods z₀).1 epsilon := by
    rw [add_smul, one_smul, add_comm]
  rw [hvec]
  exact congrArg Prod.snd
    (movingToFixedCover_period_add A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne z₀ epsilon
      (logarithmicGaugeScalar
        (A.orderThreeFillingRelationCayleyLogLift 0) •
          periodVector (parameterMap A.periods z₀).1 epsilon))

public theorem orderFourFillingRelationPrincipalGaugeCoverLift_endpoint :
    letI := A.ellipticFourBoundaryAction
    A.orderFourFillingRelationPrincipalGaugeCoverLift 1 =
      periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') +
        A.orderFourFillingRelationPrincipalGaugeCoverLift 0 := by
  let _ := A.ellipticFourBoundaryAction
  let z₀ := familyTotalSpaceBase A.periods
    (A.orderFourCollarInverseRepresentative
      (A.ellipticFourBoundaryDeckStraightLift
        A.ellipticFourBoundaryDeckData.fillingRelation 0)).1
  let z₁ := familyTotalSpaceBase A.periods
    (A.orderFourCollarInverseRepresentative
      (A.ellipticFourBoundaryDeckStraightLift
        A.ellipticFourBoundaryDeckData.fillingRelation 1)).1
  have hz : z₁ = z₀ := congrArg
    (fun q => familyTotalSpaceBase A.periods q.1)
    A.orderFourFillingRelationInverseRepresentative_endpoint
  change (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo
      (z₁, logarithmicGaugeScalar
        (A.orderFourFillingRelationCayleyLogLift 1) •
          periodVector (parameterMap A.periods z₁).1 (-epsilon'))).2 = _
  rw [hz]
  change (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo
      (z₀, logarithmicGaugeScalar
        (A.orderFourFillingRelationCayleyLogLift 1) •
          periodVector (parameterMap A.periods z₀).1 (-epsilon'))).2 =
    periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') +
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (z₀, logarithmicGaugeScalar
          (A.orderFourFillingRelationCayleyLogLift 0) •
            periodVector (parameterMap A.periods z₀).1 (-epsilon'))).2
  rw [A.orderFourFillingRelationGaugeScalar_endpoint]
  have hvec :
      (logarithmicGaugeScalar (A.orderFourFillingRelationCayleyLogLift 0) + 1) •
          periodVector (parameterMap A.periods z₀).1 (-epsilon') =
        periodVector (parameterMap A.periods z₀).1 (-epsilon') +
          logarithmicGaugeScalar (A.orderFourFillingRelationCayleyLogLift 0) •
            periodVector (parameterMap A.periods z₀).1 (-epsilon') := by
    rw [add_smul, one_smul, add_comm]
  rw [hvec]
  exact congrArg Prod.snd
    (movingToFixedCover_period_add A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo z₀ (-epsilon')
      (logarithmicGaugeScalar
        (A.orderFourFillingRelationCayleyLogLift 0) •
          periodVector (parameterMap A.periods z₀).1 (-epsilon')))

public noncomputable def orderThreeFillingRelationPrincipalGaugeCoverLiftMap :
    letI := A.ellipticThreeBoundaryAction
    C(unitInterval, ComplexTwoSpace) where
  toFun := A.orderThreeFillingRelationPrincipalGaugeCoverLift
  continuous_toFun := by
    let _ := A.ellipticThreeBoundaryAction
    unfold orderThreeFillingRelationPrincipalGaugeCoverLift
    let z : unitInterval → UpperHalfPlane := fun t =>
      familyTotalSpaceBase A.periods
        (A.orderThreeCollarInverseRepresentative
          (A.ellipticThreeBoundaryDeckStraightLift
            A.ellipticThreeBoundaryDeckData.fillingRelation t)).1
    have hz : Continuous z :=
      familyTotalSpaceBase_continuous A.periods |>.comp
        (continuous_subtype_val.comp
          (A.orderThreeCollarInverseRepresentativeMap.continuous.comp
            (A.ellipticThreeBoundaryDeckStraightLift
              A.ellipticThreeBoundaryDeckData.fillingRelation).continuous))
    have hv : Continuous (fun t =>
        logarithmicGaugeScalar (A.orderThreeFillingRelationCayleyLogLift t) •
          periodVector (parameterMap A.periods (z t)).1 epsilon) := by
      have hs : Continuous (fun t =>
          logarithmicGaugeScalar (A.orderThreeFillingRelationCayleyLogLift t)) := by
        unfold logarithmicGaugeScalar
        exact continuous_const.mul
          A.orderThreeFillingRelationCayleyLogLift.continuous
      have hp : Continuous (fun t =>
          periodVector (parameterMap A.periods (z t)).1 epsilon) := by
        have htU : Continuous (fun t => A.periods.tau (z t)) :=
          A.periods.tau_holomorphic.continuous.comp hz
        have ht : Continuous (fun t => (A.periods.tau (z t) : ℂ)) := by
          fun_prop
        have hm : Continuous (fun t => A.periods.mu (z t)) :=
          A.periods.mu_holomorphic.continuous.comp hz
        have hb : Continuous (fun t => A.periods.beta (z t)) :=
          A.periods.beta_holomorphic.continuous.comp hz
        apply continuous_pi
        intro i
        fin_cases i <;>
          simp [periodVector, SphereSixComplex.Periods.periodMatrix,
            Matrix.mulVec, parameterMap, SphereSixComplex.Periods.periodValues] <;>
          fun_prop
      exact hs.smul hp
    exact continuous_snd.comp
      ((movingToFixedCover_continuous A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).comp
          (hz.prodMk hv))

public noncomputable def orderFourFillingRelationPrincipalGaugeCoverLiftMap :
    letI := A.ellipticFourBoundaryAction
    C(unitInterval, ComplexTwoSpace) where
  toFun := A.orderFourFillingRelationPrincipalGaugeCoverLift
  continuous_toFun := by
    let _ := A.ellipticFourBoundaryAction
    unfold orderFourFillingRelationPrincipalGaugeCoverLift
    let z : unitInterval → UpperHalfPlane := fun t =>
      familyTotalSpaceBase A.periods
        (A.orderFourCollarInverseRepresentative
          (A.ellipticFourBoundaryDeckStraightLift
            A.ellipticFourBoundaryDeckData.fillingRelation t)).1
    have hz : Continuous z :=
      familyTotalSpaceBase_continuous A.periods |>.comp
        (continuous_subtype_val.comp
          (A.orderFourCollarInverseRepresentativeMap.continuous.comp
            (A.ellipticFourBoundaryDeckStraightLift
              A.ellipticFourBoundaryDeckData.fillingRelation).continuous))
    have hv : Continuous (fun t =>
        logarithmicGaugeScalar (A.orderFourFillingRelationCayleyLogLift t) •
          periodVector (parameterMap A.periods (z t)).1 (-epsilon')) := by
      have hs : Continuous (fun t =>
          logarithmicGaugeScalar (A.orderFourFillingRelationCayleyLogLift t)) := by
        unfold logarithmicGaugeScalar
        exact continuous_const.mul
          A.orderFourFillingRelationCayleyLogLift.continuous
      have hp : Continuous (fun t =>
          periodVector (parameterMap A.periods (z t)).1 (-epsilon')) := by
        have htU : Continuous (fun t => A.periods.tau (z t)) :=
          A.periods.tau_holomorphic.continuous.comp hz
        have ht : Continuous (fun t => (A.periods.tau (z t) : ℂ)) := by
          fun_prop
        have hm : Continuous (fun t => A.periods.mu (z t)) :=
          A.periods.mu_holomorphic.continuous.comp hz
        have hb : Continuous (fun t => A.periods.beta (z t)) :=
          A.periods.beta_holomorphic.continuous.comp hz
        apply continuous_pi
        intro i
        fin_cases i <;>
          simp [periodVector, SphereSixComplex.Periods.periodMatrix,
            Matrix.mulVec, parameterMap, SphereSixComplex.Periods.periodValues] <;>
          fun_prop
      exact hs.smul hp
    exact continuous_snd.comp
      ((movingToFixedCover_continuous A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).comp
          (hz.prodMk hv))

end SphereSixComplex.Geometry.AnalyticData

end

end
