module
public import SphereSixComplex.Topology.PaperEllipticBoundaryBaseMarking
import all SphereSixComplex.TriangleGroup.Representation

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

public theorem orderFourCollarInverseRepresentative_forwardMeridian
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourCollarInverseRepresentative
        (affineTorusMappingTorusDeckMeridian
          (orderFourDescendedAffineTorusAutomorphism A.periods) • q) =
      restrictedActionMap
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderFour.radius)
        (cyclicGenerator 4) (A.orderFourCollarInverseRepresentative q) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := orderFourCyclicPuncturedProductData A.periods
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  let e := orderFourPuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  apply e.toHomeomorph.injective
  rw [e.equivariant]
  rw [A.orderFourPuncturedProductHomeomorph_inverseRepresentative,
    A.orderFourPuncturedProductHomeomorph_inverseRepresentative]
  apply Subtype.ext
  change _ = actionMap D.action (cyclicGenerator 4) _
  rw [D.generator_formula]
  apply Prod.ext
  · apply Subtype.ext
    change ((q.1 : ℝ) : ℂ) *
        ((angleMap 4 ((affineTorusMappingTorusDeckMeridian
          (orderFourDescendedAffineTorusAutomorphism A.periods) • q).2.1) : Circle) : ℂ) =
      orderFourMultiplier * (((q.1 : ℝ) : ℂ) * ((angleMap 4 q.2.1 : Circle) : ℂ))
    have hang : (affineTorusMappingTorusDeckMeridian
        (orderFourDescendedAffineTorusAutomorphism A.periods) • q).2.1 = q.2.1 - 1 := by
      exact congrArg Prod.fst (affineTorusMappingTorusDeckMeridian_smul
        (orderFourDescendedAffineTorusAutomorphism A.periods) _ q.2)
    rw [hang, orderFourMultiplier_eq_standardMultiplier,
      ← standardMultiplier_mul_angleMap]
    ring
  · change (Quotient.mk _
      ((affineTorusMappingTorusDeckMeridian
        (orderFourDescendedAffineTorusAutomorphism A.periods) • q).2.2)) =
      orderFourAffineClutchingHomeomorph A.periods (Quotient.mk _ q.2.2)
    rw [orderFourAffineClutchingHomeomorph_apply,
      (orderFourDescendedAffineTorusAutomorphism A.periods).map_mk]
    have hs := affineTorusMappingTorusDeckMeridian_smul
      (orderFourDescendedAffineTorusAutomorphism A.periods)
      ((4 : ℂ)⁻¹ • periodVector
        (AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-LatticeData.epsilon')) q.2
    change Quotient.mk _ ((affineTorusMappingTorusDeckMeridian
      (orderFourDescendedAffineTorusAutomorphism A.periods) • q.2).2) = _
    rw [hs]
    rfl

public theorem orderFourCollarRegularRepresentative_forwardMeridian
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourCollarRegularRepresentativeMap
        (affineTorusMappingTorusDeckMeridian
          (orderFourDescendedAffineTorusAutomorphism A.periods) • q) =
      regularFamilyDeckMap A.periods g₂ (A.orderFourCollarRegularRepresentativeMap q) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderFourActualEllipticBoundaryAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let e := orderFourPuncturedGaugeEquivariantHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius
  change orderFourCollarToRegular A.periods hproper
      A.starSeparation.orderFour.sourceData
      (e.toHomeomorph (A.orderFourCollarInverseRepresentative _)) = _
  rw [A.orderFourCollarInverseRepresentative_forwardMeridian, e.equivariant,
    orderFourCollarToRegular_action]
  rfl

public theorem orderFourCollarRegularRepresentative_meridian
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourCollarRegularRepresentativeMap
        (A.orderFourActualEllipticBoundaryDeckData.meridian • q) =
      regularFamilyDeckMap A.periods g₂⁻¹ (A.orderFourCollarRegularRepresentativeMap q) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := regularFamilyDeckAction A.periods
  have h := A.orderFourCollarRegularRepresentative_forwardMeridian
    (A.orderFourActualEllipticBoundaryDeckData.meridian • q)
  change A.orderFourCollarRegularRepresentativeMap
      (affineTorusMappingTorusDeckMeridian
        (orderFourDescendedAffineTorusAutomorphism A.periods) •
        ((affineTorusMappingTorusDeckMeridian
          (orderFourDescendedAffineTorusAutomorphism A.periods))⁻¹ • q)) =
      g₂ • A.orderFourCollarRegularRepresentativeMap
        (A.orderFourActualEllipticBoundaryDeckData.meridian • q) at h
  rw [smul_inv_smul] at h
  change _ = g₂⁻¹ • A.orderFourCollarRegularRepresentativeMap q
  rw [h, inv_smul_smul]

public theorem orderThreeCollarInverseRepresentative_forwardMeridian
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeCollarInverseRepresentative
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods) • q) =
      restrictedActionMap
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderThree.radius)
        (cyclicGenerator 3) (A.orderThreeCollarInverseRepresentative q) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := orderThreeCyclicPuncturedProductData A.periods
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  let e := orderThreePuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  apply e.toHomeomorph.injective
  rw [e.equivariant]
  rw [A.orderThreePuncturedProductHomeomorph_inverseRepresentative,
    A.orderThreePuncturedProductHomeomorph_inverseRepresentative]
  apply Subtype.ext
  change _ = actionMap D.action (cyclicGenerator 3) _
  rw [D.generator_formula]
  apply Prod.ext
  · apply Subtype.ext
    change ((q.1 : ℝ) : ℂ) *
        ((angleMap 3 ((affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods) • q).2.1) : Circle) : ℂ) =
      orderThreeMultiplier * (((q.1 : ℝ) : ℂ) * ((angleMap 3 q.2.1 : Circle) : ℂ))
    have hang : (affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods) • q).2.1 = q.2.1 - 1 := by
      exact congrArg Prod.fst (affineTorusMappingTorusDeckMeridian_smul
        (orderThreeDescendedAffineTorusAutomorphism A.periods) _ q.2)
    rw [hang, orderThreeMultiplier_eq_standardMultiplier,
      ← standardMultiplier_mul_angleMap]
    ring
  · change (Quotient.mk _
      ((affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods) • q).2.2)) =
      orderThreeAffineClutchingHomeomorph A.periods (Quotient.mk _ q.2.2)
    rw [orderThreeAffineClutchingHomeomorph_apply,
      (orderThreeDescendedAffineTorusAutomorphism A.periods).map_mk]
    have hs := affineTorusMappingTorusDeckMeridian_smul
      (orderThreeDescendedAffineTorusAutomorphism A.periods)
      ((3 : ℂ)⁻¹ • periodVector
        (AnalyticTorusFamily.parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 (LatticeData.epsilon)) q.2
    change Quotient.mk _ ((affineTorusMappingTorusDeckMeridian
      (orderThreeDescendedAffineTorusAutomorphism A.periods) • q.2).2) = _
    rw [hs]
    rfl

public theorem orderThreeCollarRegularRepresentative_forwardMeridian
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeCollarRegularRepresentativeMap
        (affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods) • q) =
      regularFamilyDeckMap A.periods g₁ (A.orderThreeCollarRegularRepresentativeMap q) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderThreeActualEllipticBoundaryAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let e := orderThreePuncturedGaugeEquivariantHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius
  change orderThreeCollarToRegular A.periods hproper
      A.starSeparation.orderThree.sourceData
      (e.toHomeomorph (A.orderThreeCollarInverseRepresentative _)) = _
  rw [A.orderThreeCollarInverseRepresentative_forwardMeridian, e.equivariant,
    orderThreeCollarToRegular_action]
  rfl

public theorem orderThreeCollarRegularRepresentative_meridian
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeCollarRegularRepresentativeMap
        (A.orderThreeActualEllipticBoundaryDeckData.meridian • q) =
      regularFamilyDeckMap A.periods g₁⁻¹ (A.orderThreeCollarRegularRepresentativeMap q) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ := regularFamilyDeckAction A.periods
  have h := A.orderThreeCollarRegularRepresentative_forwardMeridian
    (A.orderThreeActualEllipticBoundaryDeckData.meridian • q)
  change A.orderThreeCollarRegularRepresentativeMap
      (affineTorusMappingTorusDeckMeridian
        (orderThreeDescendedAffineTorusAutomorphism A.periods) •
        ((affineTorusMappingTorusDeckMeridian
          (orderThreeDescendedAffineTorusAutomorphism A.periods))⁻¹ • q)) =
      g₁ • A.orderThreeCollarRegularRepresentativeMap
        (A.orderThreeActualEllipticBoundaryDeckData.meridian • q) at h
  rw [smul_inv_smul] at h
  change _ = g₁⁻¹ • A.orderThreeCollarRegularRepresentativeMap q
  rw [h, inv_smul_smul]

public theorem orderFourCollarRegularBase_projects :
    regularFamilyQuotientMap A.periods
      (A.orderFourCollarRegularRepresentativeMap A.orderFourActualEllipticBoundaryBase) =
      A.orderFourActualEllipticCentralBase := by
  let _ := A.orderFourActualEllipticBoundaryAction
  have h := A.orderFourDeckStraightCentralLoop_projects_representative 1 0
  rw [(A.orderFourActualEllipticBoundaryDeckStraightCentralLoop 1).source] at h
  change A.centralQuotientProjection _ = _
  simpa only [(A.orderFourActualEllipticBoundaryDeckStraightLift 1).source] using h.symm

public theorem orderFourBoundaryMeridian_outerLabel :
    letI := A.orderFourActualEllipticBoundaryAction
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.fundamentalGroupToMulOpposite
      ⟨A.orderFourCollarRegularRepresentativeMap A.orderFourActualEllipticBoundaryBase,
        A.orderFourCollarRegularBase_projects⟩
      (Path.Homotopic.Quotient.mk (A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
        A.orderFourActualEllipticBoundaryDeckData.meridian)) = MulOpposite.op g₂⁻¹ := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let e : (regularFamilyQuotientMap A.periods) ⁻¹' {A.orderFourActualEllipticCentralBase} :=
    ⟨A.orderFourCollarRegularRepresentativeMap A.orderFourActualEllipticBoundaryBase,
      A.orderFourCollarRegularBase_projects⟩
  let e' : (regularFamilyQuotientMap A.periods) ⁻¹' {A.orderFourActualEllipticCentralBase} :=
    ⟨regularFamilyDeckMap A.periods g₂⁻¹ e.val,
      (regularFamilyQuotientMap_deck A.periods e.val g₂⁻¹).trans e.property⟩
  let W := A.orderFourActualEllipticBoundaryDeckStraightLift
    A.orderFourActualEllipticBoundaryDeckData.meridian
  let L := A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
    A.orderFourActualEllipticBoundaryDeckData.meridian
  let Q : Path e.val e'.val :=
    (W.map A.orderFourCollarRegularRepresentativeMap.continuous).cast rfl
      (A.orderFourCollarRegularRepresentative_meridian A.orderFourActualEllipticBoundaryBase).symm
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := e) (ey := e') (Path.Homotopic.Quotient.mk Q) (γ := Path.Homotopic.Quotient.mk L) (by
      erw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      exact (A.orderFourDeckStraightCentralLoop_projects_representative _ t).symm)
  apply hp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
  exact (congrArg Subtype.val hm).symm

public theorem orderThreeCollarRegularBase_projects :
    regularFamilyQuotientMap A.periods
      (A.orderThreeCollarRegularRepresentativeMap A.orderThreeActualEllipticBoundaryBase) =
      A.orderThreeActualEllipticCentralBase := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  have h := A.orderThreeDeckStraightCentralLoop_projects_representative 1 0
  rw [(A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop 1).source] at h
  change A.centralQuotientProjection _ = _
  simpa only [(A.orderThreeActualEllipticBoundaryDeckStraightLift 1).source] using h.symm

public theorem orderThreeBoundaryMeridian_outerLabel :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.fundamentalGroupToMulOpposite
      ⟨A.orderThreeCollarRegularRepresentativeMap A.orderThreeActualEllipticBoundaryBase,
        A.orderThreeCollarRegularBase_projects⟩
      (Path.Homotopic.Quotient.mk (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
        A.orderThreeActualEllipticBoundaryDeckData.meridian)) = MulOpposite.op g₁⁻¹ := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ := regularFamilyDeckAction A.periods
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let e : (regularFamilyQuotientMap A.periods) ⁻¹' {A.orderThreeActualEllipticCentralBase} :=
    ⟨A.orderThreeCollarRegularRepresentativeMap A.orderThreeActualEllipticBoundaryBase,
      A.orderThreeCollarRegularBase_projects⟩
  let e' : (regularFamilyQuotientMap A.periods) ⁻¹' {A.orderThreeActualEllipticCentralBase} :=
    ⟨regularFamilyDeckMap A.periods g₁⁻¹ e.val,
      (regularFamilyQuotientMap_deck A.periods e.val g₁⁻¹).trans e.property⟩
  let W := A.orderThreeActualEllipticBoundaryDeckStraightLift
    A.orderThreeActualEllipticBoundaryDeckData.meridian
  let L := A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
    A.orderThreeActualEllipticBoundaryDeckData.meridian
  let Q : Path e.val e'.val :=
    (W.map A.orderThreeCollarRegularRepresentativeMap.continuous).cast rfl
      (A.orderThreeCollarRegularRepresentative_meridian A.orderThreeActualEllipticBoundaryBase).symm
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := e) (ey := e') (Path.Homotopic.Quotient.mk Q) (γ := Path.Homotopic.Quotient.mk L) (by
      erw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      exact (A.orderThreeDeckStraightCentralLoop_projects_representative _ t).symm)
  apply hp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
  exact (congrArg Subtype.val hm).symm

end SphereSixComplex.Geometry.PaperAnalyticData
