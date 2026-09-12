module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourRadialFillingLift

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

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.RealPeriodTrivialization
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.AffineCyclicQuotientHomology
open _root_.SphereSixComplex.AffineCyclicQuotientHomology

variable (A : AnalyticData)

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



private theorem orderThreeAffineEquiv_inv_three (z : ComplexTwoSpace) :
    (affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
        ((3 : ℂ)⁻¹ • periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon) ^ (-3 : ℤ)) z =
      z - periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon := by
  let P := SphereSixComplex.AffineCyclicQuotientHomology.orderThreeCentralFiberPresentationData
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


/-- The corrected actual order-three filling relation acts by one full angular turn and fixes the
vector coordinate. -/
public theorem ellipticThreeFillingRelation_boundary_smul
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.ellipticThreeBoundaryAction
    A.ellipticThreeBoundaryDeckData.fillingRelation • q =
      (q.1, q.2.1 + 3, q.2.2) := by
  let _ := A.ellipticThreeBoundaryAction
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



private theorem orderFourAffineEquiv_inv_four (z : ComplexTwoSpace) :
    (affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
        ((4 : ℂ)⁻¹ • periodVector
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon')) ^ (-4 : ℤ)) z =
      z - periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') := by
  let P := SphereSixComplex.AffineCyclicQuotientHomology.orderFourCentralFiberPresentationData
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


/-- The corrected actual order-four filling relation acts by one full angular turn and fixes the
vector coordinate. -/
public theorem ellipticFourFillingRelation_boundary_smul
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.ellipticFourBoundaryAction
    A.ellipticFourBoundaryDeckData.fillingRelation • q =
      (q.1, q.2.1 + 4, q.2.2) := by
  let _ := A.ellipticFourBoundaryAction
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







end SphereSixComplex.Geometry.AnalyticData
