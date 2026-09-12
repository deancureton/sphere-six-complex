module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticStraightLoopGeometricConnectorReduction

/-!
# Physical elliptic relators as loops in the central family

The canonical cyclic filling relators are represented by straight deck paths. Their images in
the central family and the core agree with the corresponding transported loop classes.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology

private theorem fundamentalGroupElementOfBaseEq_pow_mul_inv
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (a b : FundamentalGroup X x) (n : ℕ) :
    fundamentalGroupElementOfBaseEq h a ^ n *
        (fundamentalGroupElementOfBaseEq h b)⁻¹ =
      fundamentalGroupElementOfBaseEq h (a ^ n * b⁻¹) := by
  subst y
  rfl

variable (A : AnalyticData)


/-- The canonical order-three relator is the loop of the complete physical filling relation. -/
public theorem ellipticThreeCanonicalRelator_eq_fillingRelationClass :
    letI := A.ellipticThreeBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.ellipticThreeBoundaryCover_simplyConnected
    A.ellipticThreeCanonicalRelator =
      fundamentalGroupElementOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
          A.ellipticThreeBoundaryBase
          A.ellipticThreeBoundaryDeckData.fillingRelation) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let hp := A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
  let D := A.ellipticThreeBoundaryDeckData
  let hb := A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
  have hcomm : Commute D.meridian (Additive.toMul (D.translation D.twist)) := by
    rw [commute_iff_eq]
    have h := D.conjugate D.twist
    rw [D.twist_fixed] at h
    exact eq_mul_of_mul_inv_eq h
  unfold ellipticThreeCanonicalRelator
  rw [A.ellipticThreeCanonicalChosenCover_meridian_eq_ofDeck]
  simp only [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
  rw [A.ellipticThreeCanonicalChosenCover_translation_eq_ofDeck]
  change fundamentalGroupElementOfBaseEq hb
          (ofDeck hp A.ellipticThreeBoundaryBase D.meridian) ^ 3 *
        (fundamentalGroupElementOfBaseEq hb
          (ofDeck hp A.ellipticThreeBoundaryBase
            (Additive.toMul (D.translation D.twist))))⁻¹ =
      fundamentalGroupElementOfBaseEq hb
        (ofDeck hp A.ellipticThreeBoundaryBase D.fillingRelation)
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    ofDeck_mul, ofDeck_pow, ofDeck_inv]
  have hloop := ofDeck_mul_comm hp A.ellipticThreeBoundaryBase
    (hcomm.pow_left 3).inv_right.eq
  have hloop' :
      ofDeck hp A.ellipticThreeBoundaryBase D.meridian ^ 3 *
          (ofDeck hp A.ellipticThreeBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹ =
        (ofDeck hp A.ellipticThreeBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹ *
          ofDeck hp A.ellipticThreeBoundaryBase D.meridian ^ 3 := by
    simpa only [ofDeck_pow, ofDeck_inv] using hloop
  calc
    _ = fundamentalGroupElementOfBaseEq hb
        (ofDeck hp A.ellipticThreeBoundaryBase D.meridian ^ 3 *
          (ofDeck hp A.ellipticThreeBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹) := by
      exact fundamentalGroupElementOfBaseEq_pow_mul_inv hb _ _ 3
    _ = _ := congrArg
      (fundamentalGroupElementOfBaseEq hb) hloop'

/-- The canonical order-four relator is the loop of the complete physical filling relation. -/
public theorem ellipticFourCanonicalRelator_eq_fillingRelationClass :
    letI := A.ellipticFourBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    A.ellipticFourCanonicalRelator =
      fundamentalGroupElementOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          A.ellipticFourBoundaryDeckData.fillingRelation) := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let hp := A.ellipticFourBoundaryProjection_isQuotientCoveringMap
  let D := A.ellipticFourBoundaryDeckData
  let hb := A.ellipticFourCanonicalChosenCover_boundaryBase_eq
  have hcomm : Commute D.meridian (Additive.toMul (D.translation D.twist)) := by
    rw [commute_iff_eq]
    have h := D.conjugate D.twist
    rw [D.twist_fixed] at h
    exact eq_mul_of_mul_inv_eq h
  unfold ellipticFourCanonicalRelator
  rw [A.ellipticFourCanonicalChosenCover_meridian_eq_ofDeck]
  simp only [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
  rw [A.ellipticFourCanonicalChosenCover_translation_eq_ofDeck]
  change fundamentalGroupElementOfBaseEq hb
          (ofDeck hp A.ellipticFourBoundaryBase D.meridian) ^ 4 *
        (fundamentalGroupElementOfBaseEq hb
          (ofDeck hp A.ellipticFourBoundaryBase
            (Additive.toMul (D.translation D.twist))))⁻¹ =
      fundamentalGroupElementOfBaseEq hb
        (ofDeck hp A.ellipticFourBoundaryBase D.fillingRelation)
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    ofDeck_mul, ofDeck_pow, ofDeck_inv]
  have hloop := ofDeck_mul_comm hp A.ellipticFourBoundaryBase
    (hcomm.pow_left 4).inv_right.eq
  have hloop' :
      ofDeck hp A.ellipticFourBoundaryBase D.meridian ^ 4 *
          (ofDeck hp A.ellipticFourBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹ =
        (ofDeck hp A.ellipticFourBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹ *
          ofDeck hp A.ellipticFourBoundaryBase D.meridian ^ 4 := by
    simpa only [ofDeck_pow, ofDeck_inv] using hloop
  calc
    _ = fundamentalGroupElementOfBaseEq hb
        (ofDeck hp A.ellipticFourBoundaryBase D.meridian ^ 4 *
          (ofDeck hp A.ellipticFourBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹) := by
      exact fundamentalGroupElementOfBaseEq_pow_mul_inv hb _ _ 4
    _ = _ := congrArg
      (fundamentalGroupElementOfBaseEq hb) hloop'

/-- Equivalently, the order-three relator is represented by the straight complete-relation
deck loop. -/
public theorem ellipticThreeCanonicalRelator_eq_fillingRelationStraightLoop :
    letI := A.ellipticThreeBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.ellipticThreeBoundaryCover_simplyConnected
    A.ellipticThreeCanonicalRelator =
      fundamentalGroupElementOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
        (Path.Homotopic.Quotient.mk
          (A.ellipticThreeBoundaryDeckStraightLoop
            A.ellipticThreeBoundaryDeckData.fillingRelation)) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  calc
    A.ellipticThreeCanonicalRelator =
        fundamentalGroupElementOfBaseEq
          A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
          (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
            A.ellipticThreeBoundaryBase
            A.ellipticThreeBoundaryDeckData.fillingRelation) :=
      A.ellipticThreeCanonicalRelator_eq_fillingRelationClass
    _ = _ := congrArg
      (fundamentalGroupElementOfBaseEq
        A.ellipticThreeCanonicalChosenCover_boundaryBase_eq)
      (A.ellipticThreeBoundaryDeckStraightLoop_class_eq_ofDeck
        A.ellipticThreeBoundaryDeckData.fillingRelation).symm

/-- Equivalently, the order-four relator is represented by the straight complete-relation
deck loop. -/
public theorem ellipticFourCanonicalRelator_eq_fillingRelationStraightLoop :
    letI := A.ellipticFourBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    A.ellipticFourCanonicalRelator =
      fundamentalGroupElementOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq
        (Path.Homotopic.Quotient.mk
          (A.ellipticFourBoundaryDeckStraightLoop
            A.ellipticFourBoundaryDeckData.fillingRelation)) := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  calc
    A.ellipticFourCanonicalRelator =
        fundamentalGroupElementOfBaseEq
          A.ellipticFourCanonicalChosenCover_boundaryBase_eq
          (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
            A.ellipticFourBoundaryBase
            A.ellipticFourBoundaryDeckData.fillingRelation) :=
      A.ellipticFourCanonicalRelator_eq_fillingRelationClass
    _ = _ := congrArg
      (fundamentalGroupElementOfBaseEq
        A.ellipticFourCanonicalChosenCover_boundaryBase_eq)
      (A.ellipticFourBoundaryDeckStraightLoop_class_eq_ofDeck
        A.ellipticFourBoundaryDeckData.fillingRelation).symm

/-- The canonical order-three physical relator, viewed at the literal central overlap base. -/
public noncomputable def ellipticThreeCanonicalRelatorInCentral :
    FundamentalGroup A.CentralFamily A.ellipticThreeOverlapCentralBase :=
  fundamentalGroupElementOfBaseEq (by rfl)
    (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
      A.ellipticThreeCanonicalRelator)

/-- The canonical order-four physical relator, viewed at the literal central overlap base. -/
public noncomputable def ellipticFourCanonicalRelatorInCentral :
    FundamentalGroup A.CentralFamily A.ellipticFourOverlapCentralBase :=
  fundamentalGroupElementOfBaseEq (by rfl)
    (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
      A.ellipticFourCanonicalRelator)

/-- Pointwise description of the order-three central relator as the mapped straight complete
filling-relation loop. -/
public theorem ellipticThreeCanonicalRelatorInCentral_eq_fillingRelationStraightLoop :
    letI := A.ellipticThreeBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.ellipticThreeBoundaryCover_simplyConnected
    A.ellipticThreeCanonicalRelatorInCentral =
      fundamentalGroupElementOfBaseEq (by rfl)
        (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
          (fundamentalGroupElementOfBaseEq
            A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
            (Path.Homotopic.Quotient.mk
              (A.ellipticThreeBoundaryDeckStraightLoop
                A.ellipticThreeBoundaryDeckData.fillingRelation)))) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  unfold ellipticThreeCanonicalRelatorInCentral
  rw [A.ellipticThreeCanonicalRelator_eq_fillingRelationStraightLoop]

/-- Pointwise description of the order-four central relator as the mapped straight complete
filling-relation loop. -/
public theorem ellipticFourCanonicalRelatorInCentral_eq_fillingRelationStraightLoop :
    letI := A.ellipticFourBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    A.ellipticFourCanonicalRelatorInCentral =
      fundamentalGroupElementOfBaseEq (by rfl)
        (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
          (fundamentalGroupElementOfBaseEq
            A.ellipticFourCanonicalChosenCover_boundaryBase_eq
            (Path.Homotopic.Quotient.mk
              (A.ellipticFourBoundaryDeckStraightLoop
                A.ellipticFourBoundaryDeckData.fillingRelation)))) := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  unfold ellipticFourCanonicalRelatorInCentral
  rw [A.ellipticFourCanonicalRelator_eq_fillingRelationStraightLoop]


public theorem ellipticThreeCanonicalRelatorInCentral_toCore :
    A.ellipticThreeCentralToCoreEquiv A.ellipticThreeCanonicalRelatorInCentral =
      A.ellipticThreeOverlapToCore A.ellipticThreeCanonicalRelator := by
  rw [A.ellipticThreeOverlapToCore_eq_central]
  rfl

public theorem ellipticFourCanonicalRelatorInCentral_toCore :
    A.ellipticFourCentralToCoreEquiv A.ellipticFourCanonicalRelatorInCentral =
      A.ellipticFourOverlapToCore A.ellipticFourCanonicalRelator := by
  rw [A.ellipticFourOverlapToCore_eq_central]
  rfl


end SphereSixComplex.Geometry.AnalyticData

end

end
