module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourRadialFillingLift

/-!
# Sign audit for the elliptic filling relations

The actual collar presentation uses the inverse mapping-torus meridian. Consequently its full
iterate has the opposite translation from the positive affine clutching generator. The formulas
below exhibit the nonzero residue produced by the legacy twist signs and verify the corrected
physical filling relations.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology

variable (A : PaperAnalyticData)

/-- Adding one full angular period does not change the radial angular cover. -/
public theorem angularCover_fullTurn {T : Type} [TopologicalSpace T]
    {r : ℝ} (m : ℕ) [NeZero m] (hr : r ≤ 1)
    (q : OpenRadialInterval r × (ℝ × T)) :
    angularCover (T := T) m hr (q.1, q.2.1 + m, q.2.2) =
      angularCover (T := T) m hr q := by
  apply congrArg (polarHomeomorph hr)
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply (angleMap_eq_iff (m := m) (q.2.1 + m) q.2.1).mpr
      exact ⟨1, by norm_num⟩
    · rfl

/-- A full order-three angular turn is invisible to the actual radial filling lift. -/
public theorem orderThreeActualEllipticRadialFillingLift_fullTurn
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    A.orderThreeActualEllipticRadialFillingLift (q.1, q.2.1 + 3, q.2.2) =
      A.orderThreeActualEllipticRadialFillingLift q := by
  let f : puncturedProduct ComplexTwoSpace A.starSeparation.orderThree.radius →
      ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace := fun u =>
    (⟨u.1.1, u.2.2⟩,
      (fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (orderThreeCayleyHomeomorph.symm u.1.1, u.1.2)).2)
  change f (angularCover (T := ComplexTwoSpace) 3
      A.starSeparation.orderThree.radius_lt_one.le (q.1, q.2.1 + 3, q.2.2)) =
    f (angularCover (T := ComplexTwoSpace) 3
      A.starSeparation.orderThree.radius_lt_one.le q)
  exact congrArg f (angularCover_fullTurn 3
    A.starSeparation.orderThree.radius_lt_one.le q)

/-- A full order-four angular turn is invisible to the actual radial filling lift. -/
public theorem orderFourActualEllipticRadialFillingLift_fullTurn
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    A.orderFourActualEllipticRadialFillingLift (q.1, q.2.1 + 4, q.2.2) =
      A.orderFourActualEllipticRadialFillingLift q := by
  let f : puncturedProduct ComplexTwoSpace A.starSeparation.orderFour.radius →
      ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace := fun u =>
    (⟨u.1.1, u.2.2⟩,
      (fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (orderFourCayleyHomeomorph.symm u.1.1, u.1.2)).2)
  change f (angularCover (T := ComplexTwoSpace) 4
      A.starSeparation.orderFour.radius_lt_one.le (q.1, q.2.1 + 4, q.2.2)) =
    f (angularCover (T := ComplexTwoSpace) 4
      A.starSeparation.orderFour.radius_lt_one.le q)
  exact congrArg f (angularCover_fullTurn 4
    A.starSeparation.orderFour.radius_lt_one.le q)

private theorem orderThreeAffineEquiv_inv_three (z : ComplexTwoSpace) :
    (affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
        ((3 : ℂ)⁻¹ • periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon) ^ (-3 : ℤ)) z =
      z - periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon := by
  let P := SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.orderThreeCentralFiberPresentationData
    A.periods
  let E := affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
    ((3 : ℂ)⁻¹ • periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon)
  have hE3 (w : ComplexTwoSpace) :
      (E ^ 3) w = w + periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon := by
    have h := P.lift_full_iterate w
    change (affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
        ((3 : ℝ)⁻¹ • periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon) ^ 3) w =
      w + periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon at h
    have hb : ((3 : ℂ)⁻¹ • periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon) =
      (3 : ℝ)⁻¹ • periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon := by
      ext i
      norm_num
    change (affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
        ((3 : ℂ)⁻¹ • periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon) ^ 3) w = _
    rw [hb]
    exact h
  change (E ^ (-3 : ℤ)) z = _
  apply (E ^ 3).injective
  have hcancel : (E ^ 3) ((E ^ (-3 : ℤ)) z) = z := by
    calc
      (E ^ 3) ((E ^ (-3 : ℤ)) z) =
          (E ^ (3 : ℤ) * E ^ (-3 : ℤ)) z := by rfl
      _ = z := by rw [← zpow_add]; simp
  rw [hcancel]
  rw [hE3]
  abel

private theorem orderThreeInverseMeridian_smul (w : ℝ × ComplexTwoSpace) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    (affineTorusMappingTorusDeckMeridian
      (orderThreeDescendedAffineTorusAutomorphism A.periods))⁻¹ • w =
      (w.1 + 1,
        (affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
          ((3 : ℂ)⁻¹ • periodVector
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon))⁻¹ w.2) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  rw [inv_smul_eq_iff]
  rw [affineTorusMappingTorusDeckMeridian_smul]
  apply Prod.ext
  · dsimp
    ring
  · let E := affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
      ((3 : ℂ)⁻¹ • periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon)
    change w.2 = E (E.symm w.2)
    exact (E.apply_symm_apply w.2).symm

private theorem orderThreeInverseMeridian_cube_smul (w : ℝ × ComplexTwoSpace) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    (affineTorusMappingTorusDeckMeridian
      (orderThreeDescendedAffineTorusAutomorphism A.periods))⁻¹ ^ 3 • w =
      (w.1 + 3,
        (affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
          ((3 : ℂ)⁻¹ • periodVector
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon) ^ (-3 : ℤ))
          w.2) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  simp only [pow_succ, pow_zero, one_mul, mul_smul]
  rw [orderThreeInverseMeridian_smul,
    orderThreeInverseMeridian_smul, orderThreeInverseMeridian_smul]
  let E := affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
    ((3 : ℂ)⁻¹ • periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon)
  apply Prod.ext
  · ring
  · change E.symm (E.symm (E.symm w.2)) = (E ^ (-3 : ℤ)) w.2
    rw [show (-3 : ℤ) = -1 + -1 + -1 by norm_num,
      zpow_add, zpow_add, zpow_neg_one]
    rfl

/-- The legacy order-three positive-twist relation translates the vector coordinate by minus
twice the marked period. -/
public theorem orderThreeLegacyPositiveTwistFillingRelation_boundary_smul
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderThreeActualEllipticBoundaryAction
    ((affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods))⁻¹ ^ 3 *
      (Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods)) epsilon))⁻¹) • q =
      (q.1, q.2.1 + 3, periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 (-2 • epsilon) + q.2.2) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  change (q.1,
    (((affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods))⁻¹ ^ 3) *
      (Additive.toMul
        ((affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods)) epsilon))⁻¹) • q.2) = _
  rw [mul_smul]
  have htrans :
      (Additive.toMul
        ((affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods)) epsilon))⁻¹ =
      Additive.toMul
        ((affineTorusMappingTorusDeckTranslation
          (orderThreeDescendedAffineTorusAutomorphism A.periods)) (-epsilon)) := by
    rw [map_neg]
    rfl
  rw [htrans, affineTorusMappingTorusDeckTranslation_smul]
  simp only [pow_succ, pow_zero, one_mul, mul_smul]
  rw [orderThreeInverseMeridian_smul,
    orderThreeInverseMeridian_smul, orderThreeInverseMeridian_smul]
  let E := affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
    ((3 : ℂ)⁻¹ • periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon)
  change (q.1, ((q.2.1 + 1) + 1) + 1,
      E.symm (E.symm (E.symm (periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 (-epsilon) + q.2.2)))) = _
  rw [show E.symm (E.symm (E.symm (periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 (-epsilon) + q.2.2))) =
      (E ^ (-3 : ℤ)) (periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 (-epsilon) + q.2.2) by
    change (E⁻¹ * E⁻¹ * E⁻¹) _ = (E ^ (-3 : ℤ)) _
    rw [show (-3 : ℤ) = -1 + -1 + -1 by norm_num,
      zpow_add, zpow_add, zpow_neg_one]]
  rw [orderThreeAffineEquiv_inv_three]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · ring
    · dsimp only
      rw [show periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 (-epsilon) =
      -periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon by
        change periodHom _ (-epsilon) = -periodHom _ epsilon
        simp]
      rw [show periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 (-2 • epsilon) =
      -(2 : ℤ) • periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon by
        change periodHom _ (-2 • epsilon) = -(2 : ℤ) • periodHom _ epsilon
        exact map_zsmul (periodHom _) (-2) epsilon]
      abel

/-- The corrected actual order-three filling relation acts by one full angular turn and fixes the
vector coordinate. -/
public theorem orderThreeActualFillingRelation_boundary_smul
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeActualEllipticBoundaryDeckData.fillingRelation • q =
      (q.1, q.2.1 + 3, q.2.2) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  change (q.1,
    (((affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods))⁻¹ ^ 3) *
      (Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods)) (-epsilon)))⁻¹) • q.2) = _
  rw [mul_smul]
  have htrans :
      (Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods)) (-epsilon)))⁻¹ =
      Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderThreeDescendedAffineTorusAutomorphism A.periods)) epsilon) := by
    rw [map_neg]
    rw [toMul_neg, inv_inv]
  rw [htrans, affineTorusMappingTorusDeckTranslation_smul,
    orderThreeInverseMeridian_cube_smul, orderThreeAffineEquiv_inv_three]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · ring
    · change periodHom _ epsilon + q.2.2 - periodHom _ epsilon = q.2.2
      abel

/-- The corrected actual order-three filling relation is killed by the radial filling lift. -/
public theorem orderThreeActualFillingRelation_radialLift
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeActualEllipticRadialFillingLift
        (A.orderThreeActualEllipticBoundaryDeckData.fillingRelation • q) =
      A.orderThreeActualEllipticRadialFillingLift q := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rw [A.orderThreeActualFillingRelation_boundary_smul]
  exact A.orderThreeActualEllipticRadialFillingLift_fullTurn q


private theorem orderFourAffineEquiv_inv_four (z : ComplexTwoSpace) :
    (affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
        ((4 : ℂ)⁻¹ • periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon')) ^ (-4 : ℤ)) z =
      z - periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') := by
  let P := SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.orderFourCentralFiberPresentationData
    A.periods
  let E := affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
    ((4 : ℂ)⁻¹ • periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon'))
  have hE4 (w : ComplexTwoSpace) :
      (E ^ 4) w = w + periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') := by
    have h := P.lift_full_iterate w
    change (affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
        ((4 : ℝ)⁻¹ • periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon')) ^ 4) w =
      w + periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') at h
    have hb : ((4 : ℂ)⁻¹ • periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon')) =
      (4 : ℝ)⁻¹ • periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') := by
      ext i
      norm_num
    change (affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
        ((4 : ℂ)⁻¹ • periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon')) ^ 4) w = _
    rw [hb]
    exact h
  change (E ^ (-4 : ℤ)) z = _
  apply (E ^ 4).injective
  have hcancel : (E ^ 4) ((E ^ (-4 : ℤ)) z) = z := by
    calc
      (E ^ 4) ((E ^ (-4 : ℤ)) z) =
          (E ^ (4 : ℤ) * E ^ (-4 : ℤ)) z := by rfl
      _ = z := by rw [← zpow_add]; simp
  rw [hcancel, hE4]
  abel

private theorem orderFourInverseMeridian_smul (w : ℝ × ComplexTwoSpace) :
    letI := orderFourAffineMappingTorusDeckAction A.periods
    (affineTorusMappingTorusDeckMeridian
      (orderFourDescendedAffineTorusAutomorphism A.periods))⁻¹ • w =
      (w.1 + 1,
        (affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
          ((4 : ℂ)⁻¹ • periodVector
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon')))⁻¹ w.2) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  rw [inv_smul_eq_iff, affineTorusMappingTorusDeckMeridian_smul]
  apply Prod.ext
  · dsimp
    ring
  · let E := affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
      ((4 : ℂ)⁻¹ • periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon'))
    change w.2 = E (E.symm w.2)
    exact (E.apply_symm_apply w.2).symm

private theorem orderFourInverseMeridian_fourth_smul (w : ℝ × ComplexTwoSpace) :
    letI := orderFourAffineMappingTorusDeckAction A.periods
    (affineTorusMappingTorusDeckMeridian
      (orderFourDescendedAffineTorusAutomorphism A.periods))⁻¹ ^ 4 • w =
      (w.1 + 4,
        (affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
          ((4 : ℂ)⁻¹ • periodVector
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon')) ^ (-4 : ℤ))
          w.2) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  simp only [pow_succ, pow_zero, one_mul, mul_smul]
  rw [orderFourInverseMeridian_smul, orderFourInverseMeridian_smul,
    orderFourInverseMeridian_smul, orderFourInverseMeridian_smul]
  let E := affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
    ((4 : ℂ)⁻¹ • periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon'))
  apply Prod.ext
  · ring
  · change E.symm (E.symm (E.symm (E.symm w.2))) = (E ^ (-4 : ℤ)) w.2
    rw [show (-4 : ℤ) = -1 + -1 + -1 + -1 by norm_num,
      zpow_add, zpow_add, zpow_add, zpow_neg_one]
    rfl

/-- The legacy order-four negative-twist relation translates the vector coordinate by twice the
marked period. -/
public theorem orderFourLegacyNegativeTwistFillingRelation_boundary_smul
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderFourActualEllipticBoundaryAction
    ((affineTorusMappingTorusDeckMeridian
        (orderFourDescendedAffineTorusAutomorphism A.periods))⁻¹ ^ 4 *
      (Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderFourDescendedAffineTorusAutomorphism A.periods)) (-epsilon')))⁻¹) • q =
      (q.1, q.2.1 + 4, periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (2 • epsilon') + q.2.2) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  change (q.1,
    (((affineTorusMappingTorusDeckMeridian
        (orderFourDescendedAffineTorusAutomorphism A.periods))⁻¹ ^ 4) *
      (Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderFourDescendedAffineTorusAutomorphism A.periods)) (-epsilon')))⁻¹) • q.2) = _
  rw [mul_smul]
  have htrans :
      (Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderFourDescendedAffineTorusAutomorphism A.periods)) (-epsilon')))⁻¹ =
      Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderFourDescendedAffineTorusAutomorphism A.periods)) epsilon') := by
    rw [map_neg, toMul_neg, inv_inv]
  rw [htrans, affineTorusMappingTorusDeckTranslation_smul,
    orderFourInverseMeridian_fourth_smul, orderFourAffineEquiv_inv_four]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · ring
    · dsimp only
      rw [show periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') =
          -periodVector
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zTwo).1 epsilon' by
        change periodHom _ (-epsilon') = -periodHom _ epsilon'
        simp]
      rw [show periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1 (2 • epsilon') =
          (2 : ℤ) • periodVector
            (parameterMap A.periods
              A.modular.modularParameter.toTriangleUniformization.zTwo).1 epsilon' by
        exact map_zsmul (periodHom _) 2 epsilon']
      abel

/-- The corrected actual order-four filling relation acts by one full angular turn and fixes the
vector coordinate. -/
public theorem orderFourActualFillingRelation_boundary_smul
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourActualEllipticBoundaryDeckData.fillingRelation • q =
      (q.1, q.2.1 + 4, q.2.2) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  change (q.1,
    (((affineTorusMappingTorusDeckMeridian
        (orderFourDescendedAffineTorusAutomorphism A.periods))⁻¹ ^ 4) *
      (Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderFourDescendedAffineTorusAutomorphism A.periods)) epsilon'))⁻¹) • q.2) = _
  rw [mul_smul]
  have htrans :
      (Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderFourDescendedAffineTorusAutomorphism A.periods)) epsilon'))⁻¹ =
      Additive.toMul ((affineTorusMappingTorusDeckTranslation
        (orderFourDescendedAffineTorusAutomorphism A.periods)) (-epsilon')) := by
    rw [map_neg]
    rfl
  rw [htrans, affineTorusMappingTorusDeckTranslation_smul,
    orderFourInverseMeridian_fourth_smul, orderFourAffineEquiv_inv_four]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · ring
    · change periodHom _ (-epsilon') + q.2.2 - periodHom _ (-epsilon') = q.2.2
      abel

/-- The corrected actual order-four filling relation is killed by the radial filling lift. -/
public theorem orderFourActualFillingRelation_radialLift
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourActualEllipticRadialFillingLift
        (A.orderFourActualEllipticBoundaryDeckData.fillingRelation • q) =
      A.orderFourActualEllipticRadialFillingLift q := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rw [A.orderFourActualFillingRelation_boundary_smul]
  exact A.orderFourActualEllipticRadialFillingLift_fullTurn q


public theorem orderThreeLegacyFillingRelation_latticeTranslation_ne_zero :
    (-2 • epsilon : Lattice) ≠ 0 := by
  intro h
  have h' := congrFun h 0
  norm_num [epsilon] at h'

public theorem orderFourLegacyFillingRelation_latticeTranslation_ne_zero :
    (2 • epsilon' : Lattice) ≠ 0 := by
  intro h
  have h' := congrFun h 0
  norm_num [epsilon'] at h'

/-- The residual order-three vector translation is genuinely nonzero in the actual period
coordinates. -/
public theorem orderThreeLegacyFillingRelation_vectorTranslation_ne_zero :
    periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 (-2 • epsilon) ≠ 0 := by
  let P := SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.orderThreeCentralFiberPresentationData
    A.periods
  intro h
  apply orderThreeLegacyFillingRelation_latticeTranslation_ne_zero
  apply (periodHom_injective P.fullRank)
  change periodVector _ (-2 • epsilon) = periodVector _ 0
  simpa only [periodVector_zero] using h

/-- The residual order-four vector translation is genuinely nonzero in the actual period
coordinates. -/
public theorem orderFourLegacyFillingRelation_vectorTranslation_ne_zero :
    periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1 (2 • epsilon') ≠ 0 := by
  let P := SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.orderFourCentralFiberPresentationData
    A.periods
  intro h
  apply orderFourLegacyFillingRelation_latticeTranslation_ne_zero
  apply (periodHom_injective P.fullRank)
  change periodVector _ (2 • epsilon') = periodVector _ 0
  simpa only [periodVector_zero] using h

end SphereSixComplex.Geometry.PaperAnalyticData
