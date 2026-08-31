module

public import SphereSixComplex.Topology.PaperActualEllipticStraightLoopGeometricConnectorReduction

/-!
# Whole-relator reduction for the actual elliptic collars

Normal closure does not require separate normalizations of the meridian and translation
generators.  This file reduces each field of the remaining elliptic residual to one loop-class
identity for the complete local filling relation.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology

private theorem fundamentalGroupElementOfBaseEq_pow_mul_inv
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (a b : FundamentalGroup X x) (n : ℕ) :
    fundamentalGroupElementOfBaseEq h a ^ n *
        (fundamentalGroupElementOfBaseEq h b)⁻¹ =
      fundamentalGroupElementOfBaseEq h (a ^ n * b⁻¹) := by
  subst y
  rfl

variable (A : PaperAnalyticData)

/-- The expected order-three affine relator at the central-family basepoint. -/
public noncomputable def orderThreeCentralExpectedRelator :
    FundamentalGroup A.CentralFamily A.centralAffineBase :=
  A.centralAffineCorePiOneData.rhoOne ^ 3 *
    (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))⁻¹

/-- The expected order-four affine relator at the central-family basepoint. -/
public noncomputable def orderFourCentralExpectedRelator :
    FundamentalGroup A.CentralFamily A.centralAffineBase :=
  A.centralAffineCorePiOneData.rhoTwo ^ 4 *
    (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))⁻¹

/-- The canonical order-three relator is the loop of the complete physical filling relation. -/
public theorem orderThreeActualEllipticCanonicalRelator_eq_fillingRelationClass :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    A.orderThreeActualEllipticCanonicalRelator =
      fundamentalGroupElementOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.fillingRelation) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let hp := A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
  let D := A.orderThreeActualEllipticBoundaryDeckData
  let hb := A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
  have hcomm : Commute D.meridian (Additive.toMul (D.translation D.twist)) := by
    rw [commute_iff_eq]
    have h := D.conjugate D.twist
    rw [D.twist_fixed] at h
    exact eq_mul_of_mul_inv_eq h
  unfold orderThreeActualEllipticCanonicalRelator
  rw [A.orderThreeActualEllipticCanonicalChosenCover_meridian_eq_ofDeck]
  simp only [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
  rw [A.orderThreeActualEllipticCanonicalChosenCover_translation_eq_ofDeck]
  change fundamentalGroupElementOfBaseEq hb
          (ofDeck hp A.orderThreeActualEllipticBoundaryBase D.meridian) ^ 3 *
        (fundamentalGroupElementOfBaseEq hb
          (ofDeck hp A.orderThreeActualEllipticBoundaryBase
            (Additive.toMul (D.translation D.twist))))⁻¹ =
      fundamentalGroupElementOfBaseEq hb
        (ofDeck hp A.orderThreeActualEllipticBoundaryBase D.fillingRelation)
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    ofDeck_mul, ofDeck_pow, ofDeck_inv]
  have hloop := ofDeck_mul_comm hp A.orderThreeActualEllipticBoundaryBase
    (hcomm.pow_left 3).inv_right.eq
  have hloop' :
      ofDeck hp A.orderThreeActualEllipticBoundaryBase D.meridian ^ 3 *
          (ofDeck hp A.orderThreeActualEllipticBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹ =
        (ofDeck hp A.orderThreeActualEllipticBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹ *
          ofDeck hp A.orderThreeActualEllipticBoundaryBase D.meridian ^ 3 := by
    simpa only [ofDeck_pow, ofDeck_inv] using hloop
  calc
    _ = fundamentalGroupElementOfBaseEq hb
        (ofDeck hp A.orderThreeActualEllipticBoundaryBase D.meridian ^ 3 *
          (ofDeck hp A.orderThreeActualEllipticBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹) := by
      exact fundamentalGroupElementOfBaseEq_pow_mul_inv hb _ _ 3
    _ = _ := congrArg
      (fundamentalGroupElementOfBaseEq hb) hloop'

/-- The canonical order-four relator is the loop of the complete physical filling relation. -/
public theorem orderFourActualEllipticCanonicalRelator_eq_fillingRelationClass :
    letI := A.orderFourActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    A.orderFourActualEllipticCanonicalRelator =
      fundamentalGroupElementOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.fillingRelation) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let hp := A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
  let D := A.orderFourActualEllipticBoundaryDeckData
  let hb := A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
  have hcomm : Commute D.meridian (Additive.toMul (D.translation D.twist)) := by
    rw [commute_iff_eq]
    have h := D.conjugate D.twist
    rw [D.twist_fixed] at h
    exact eq_mul_of_mul_inv_eq h
  unfold orderFourActualEllipticCanonicalRelator
  rw [A.orderFourActualEllipticCanonicalChosenCover_meridian_eq_ofDeck]
  simp only [fundamentalGroupAddHomOfBaseEq_apply, toMul_ofMul]
  rw [A.orderFourActualEllipticCanonicalChosenCover_translation_eq_ofDeck]
  change fundamentalGroupElementOfBaseEq hb
          (ofDeck hp A.orderFourActualEllipticBoundaryBase D.meridian) ^ 4 *
        (fundamentalGroupElementOfBaseEq hb
          (ofDeck hp A.orderFourActualEllipticBoundaryBase
            (Additive.toMul (D.translation D.twist))))⁻¹ =
      fundamentalGroupElementOfBaseEq hb
        (ofDeck hp A.orderFourActualEllipticBoundaryBase D.fillingRelation)
  simp only [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation,
    ofDeck_mul, ofDeck_pow, ofDeck_inv]
  have hloop := ofDeck_mul_comm hp A.orderFourActualEllipticBoundaryBase
    (hcomm.pow_left 4).inv_right.eq
  have hloop' :
      ofDeck hp A.orderFourActualEllipticBoundaryBase D.meridian ^ 4 *
          (ofDeck hp A.orderFourActualEllipticBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹ =
        (ofDeck hp A.orderFourActualEllipticBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹ *
          ofDeck hp A.orderFourActualEllipticBoundaryBase D.meridian ^ 4 := by
    simpa only [ofDeck_pow, ofDeck_inv] using hloop
  calc
    _ = fundamentalGroupElementOfBaseEq hb
        (ofDeck hp A.orderFourActualEllipticBoundaryBase D.meridian ^ 4 *
          (ofDeck hp A.orderFourActualEllipticBoundaryBase
            (Additive.toMul (D.translation D.twist)))⁻¹) := by
      exact fundamentalGroupElementOfBaseEq_pow_mul_inv hb _ _ 4
    _ = _ := congrArg
      (fundamentalGroupElementOfBaseEq hb) hloop'

/-- Equivalently, the order-three relator is represented by the straight complete-relation
deck loop. -/
public theorem orderThreeActualEllipticCanonicalRelator_eq_fillingRelationStraightLoop :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    A.orderThreeActualEllipticCanonicalRelator =
      fundamentalGroupElementOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
        (Path.Homotopic.Quotient.mk
          (A.orderThreeActualEllipticBoundaryDeckStraightLoop
            A.orderThreeActualEllipticBoundaryDeckData.fillingRelation)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  calc
    A.orderThreeActualEllipticCanonicalRelator =
        fundamentalGroupElementOfBaseEq
          A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase
            A.orderThreeActualEllipticBoundaryDeckData.fillingRelation) :=
      A.orderThreeActualEllipticCanonicalRelator_eq_fillingRelationClass
    _ = _ := congrArg
      (fundamentalGroupElementOfBaseEq
        A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq)
      (A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck
        A.orderThreeActualEllipticBoundaryDeckData.fillingRelation).symm

/-- Equivalently, the order-four relator is represented by the straight complete-relation
deck loop. -/
public theorem orderFourActualEllipticCanonicalRelator_eq_fillingRelationStraightLoop :
    letI := A.orderFourActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    A.orderFourActualEllipticCanonicalRelator =
      fundamentalGroupElementOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
        (Path.Homotopic.Quotient.mk
          (A.orderFourActualEllipticBoundaryDeckStraightLoop
            A.orderFourActualEllipticBoundaryDeckData.fillingRelation)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  calc
    A.orderFourActualEllipticCanonicalRelator =
        fundamentalGroupElementOfBaseEq
          A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
          (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderFourActualEllipticBoundaryBase
            A.orderFourActualEllipticBoundaryDeckData.fillingRelation) :=
      A.orderFourActualEllipticCanonicalRelator_eq_fillingRelationClass
    _ = _ := congrArg
      (fundamentalGroupElementOfBaseEq
        A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq)
      (A.orderFourActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck
        A.orderFourActualEllipticBoundaryDeckData.fillingRelation).symm

/-- The canonical order-three physical relator, viewed at the literal central overlap base. -/
public noncomputable def orderThreeActualCanonicalRelatorInCentral :
    FundamentalGroup A.CentralFamily A.orderThreeActualOverlapCentralBase :=
  fundamentalGroupElementOfBaseEq (by rfl)
    (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
      A.orderThreeActualEllipticCanonicalRelator)

/-- The canonical order-four physical relator, viewed at the literal central overlap base. -/
public noncomputable def orderFourActualCanonicalRelatorInCentral :
    FundamentalGroup A.CentralFamily A.orderFourActualOverlapCentralBase :=
  fundamentalGroupElementOfBaseEq (by rfl)
    (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
      A.orderFourActualEllipticCanonicalRelator)

/-- Pointwise description of the order-three central relator as the mapped straight complete
filling-relation loop. -/
public theorem orderThreeActualCanonicalRelatorInCentral_eq_fillingRelationStraightLoop :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    A.orderThreeActualCanonicalRelatorInCentral =
      fundamentalGroupElementOfBaseEq (by rfl)
        (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
          (fundamentalGroupElementOfBaseEq
            A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
            (Path.Homotopic.Quotient.mk
              (A.orderThreeActualEllipticBoundaryDeckStraightLoop
                A.orderThreeActualEllipticBoundaryDeckData.fillingRelation)))) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  unfold orderThreeActualCanonicalRelatorInCentral
  rw [A.orderThreeActualEllipticCanonicalRelator_eq_fillingRelationStraightLoop]

/-- Pointwise description of the order-four central relator as the mapped straight complete
filling-relation loop. -/
public theorem orderFourActualCanonicalRelatorInCentral_eq_fillingRelationStraightLoop :
    letI := A.orderFourActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    A.orderFourActualCanonicalRelatorInCentral =
      fundamentalGroupElementOfBaseEq (by rfl)
        (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
          (fundamentalGroupElementOfBaseEq
            A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
            (Path.Homotopic.Quotient.mk
              (A.orderFourActualEllipticBoundaryDeckStraightLoop
                A.orderFourActualEllipticBoundaryDeckData.fillingRelation)))) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  unfold orderFourActualCanonicalRelatorInCentral
  rw [A.orderFourActualEllipticCanonicalRelator_eq_fillingRelationStraightLoop]

/-- The remaining order-three geometry, with connector choice existentially quantified: one
complete physical filling-relation loop is the transported expected affine relator. -/
public def OrderThreeWholeFillingRelatorChartIdentity : Prop :=
  ∃ β : Path A.centralAffineBase A.orderThreeActualOverlapCentralBase,
    A.orderThreeActualCanonicalRelatorInCentral =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β A.orderThreeCentralExpectedRelator

/-- The remaining order-four geometry, with connector choice existentially quantified: one
complete physical filling-relation loop is the transported expected affine relator. -/
public def OrderFourWholeFillingRelatorChartIdentity : Prop :=
  ∃ β : Path A.centralAffineBase A.orderFourActualOverlapCentralBase,
    A.orderFourActualCanonicalRelatorInCentral =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β A.orderFourCentralExpectedRelator

public theorem orderThreeActualCanonicalRelatorInCentral_toCore :
    A.orderThreeActualCentralToCoreEquiv A.orderThreeActualCanonicalRelatorInCentral =
      A.actualEllipticThreeOverlapToCore A.orderThreeActualEllipticCanonicalRelator := by
  rw [A.actualEllipticThreeOverlapToCore_eq_central]
  rfl

public theorem orderFourActualCanonicalRelatorInCentral_toCore :
    A.orderFourActualCentralToCoreEquiv A.orderFourActualCanonicalRelatorInCentral =
      A.actualEllipticFourOverlapToCore A.orderFourActualEllipticCanonicalRelator := by
  rw [A.actualEllipticFourOverlapToCore_eq_central]
  rfl

public theorem actualCuspCentralNaturality_centralToCore_orderThreeCentralExpectedRelator :
    A.actualCuspCentralNaturality.centralToCore A.orderThreeCentralExpectedRelator =
      A.orderThreeCentralRelatorToCore A.actualCuspCentralNaturality := by
  rw [orderThreeCentralExpectedRelator, orderThreeCentralRelatorToCore]
  simp only [map_mul, map_pow, map_inv]
  rfl

public theorem actualCuspCentralNaturality_centralToCore_orderFourCentralExpectedRelator :
    A.actualCuspCentralNaturality.centralToCore A.orderFourCentralExpectedRelator =
      A.orderFourCentralRelatorToCore A.actualCuspCentralNaturality := by
  rw [orderFourCentralExpectedRelator, orderFourCentralRelatorToCore]
  simp only [map_mul, map_pow, map_inv]
  rfl

/-- The one order-three whole-loop identity gives a conjugacy in the actual core. -/
public theorem OrderThreeWholeFillingRelatorChartIdentity.core_conjugacy
    (h : A.OrderThreeWholeFillingRelatorChartIdentity) :
    ∃ c : FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩,
      A.orderThreeCentralRelatorToCore A.actualCuspCentralNaturality =
        c * A.actualEllipticThreeOverlapToCore
          A.orderThreeActualEllipticCanonicalRelator * c⁻¹ := by
  obtain ⟨β, hβ⟩ := h
  let source := A.orderThreeCentralBaseWhisker.cast rfl
    A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase.symm
  have htransport :=
    A.actualCuspCentralNaturalityPair_simultaneouslyConjugate_orderThree
      A.orderThreeCentralExpectedRelator 1
  change SimultaneouslyConjugate
    (A.actualCuspCentralNaturality.centralToCore A.orderThreeCentralExpectedRelator,
      A.actualCuspCentralNaturality.centralToCore 1)
    (A.orderThreeActualCentralToCoreEquiv
        (FundamentalGroup.fundamentalGroupMulEquivOfPath source
          A.orderThreeCentralExpectedRelator),
      A.orderThreeActualCentralToCoreEquiv
        (FundamentalGroup.fundamentalGroupMulEquivOfPath source 1)) at htransport
  have hpaths := fundamentalGroupPair_simultaneouslyConjugate_of_paths
    source β A.orderThreeCentralExpectedRelator 1
  have hpathsCore := hpaths.map A.orderThreeActualCentralToCoreEquiv.toMonoidHom
  have htotal := htransport.trans hpathsCore
  obtain ⟨c, hrelator, _⟩ := htotal
  change A.actualCuspCentralNaturality.centralToCore A.orderThreeCentralExpectedRelator =
    c * A.orderThreeActualCentralToCoreEquiv
      (FundamentalGroup.fundamentalGroupMulEquivOfPath β
        A.orderThreeCentralExpectedRelator) * c⁻¹ at hrelator
  refine ⟨c, ?_⟩
  rw [← A.actualCuspCentralNaturality_centralToCore_orderThreeCentralExpectedRelator]
  rw [hrelator]
  congr 2
  rw [← hβ]
  exact A.orderThreeActualCanonicalRelatorInCentral_toCore

/-- The one order-four whole-loop identity gives a conjugacy in the actual core. -/
public theorem OrderFourWholeFillingRelatorChartIdentity.core_conjugacy
    (h : A.OrderFourWholeFillingRelatorChartIdentity) :
    ∃ c : FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩,
      A.orderFourCentralRelatorToCore A.actualCuspCentralNaturality =
        c * A.actualEllipticFourOverlapToCore
          A.orderFourActualEllipticCanonicalRelator * c⁻¹ := by
  obtain ⟨β, hβ⟩ := h
  let source := A.orderFourCentralBaseWhisker.cast rfl
    A.orderFourActualEllipticCentralBase_eq_overlapCentralBase.symm
  have htransport :=
    A.actualCuspCentralNaturalityPair_simultaneouslyConjugate_orderFour
      A.orderFourCentralExpectedRelator 1
  change SimultaneouslyConjugate
    (A.actualCuspCentralNaturality.centralToCore A.orderFourCentralExpectedRelator,
      A.actualCuspCentralNaturality.centralToCore 1)
    (A.orderFourActualCentralToCoreEquiv
        (FundamentalGroup.fundamentalGroupMulEquivOfPath source
          A.orderFourCentralExpectedRelator),
      A.orderFourActualCentralToCoreEquiv
        (FundamentalGroup.fundamentalGroupMulEquivOfPath source 1)) at htransport
  have hpaths := fundamentalGroupPair_simultaneouslyConjugate_of_paths
    source β A.orderFourCentralExpectedRelator 1
  have hpathsCore := hpaths.map A.orderFourActualCentralToCoreEquiv.toMonoidHom
  have htotal := htransport.trans hpathsCore
  obtain ⟨c, hrelator, _⟩ := htotal
  change A.actualCuspCentralNaturality.centralToCore A.orderFourCentralExpectedRelator =
    c * A.orderFourActualCentralToCoreEquiv
      (FundamentalGroup.fundamentalGroupMulEquivOfPath β
        A.orderFourCentralExpectedRelator) * c⁻¹ at hrelator
  refine ⟨c, ?_⟩
  rw [← A.actualCuspCentralNaturality_centralToCore_orderFourCentralExpectedRelator]
  rw [hrelator]
  congr 2
  rw [← hβ]
  exact A.orderFourActualCanonicalRelatorInCentral_toCore

/-- The order-three whole-loop identity supplies exactly the order-three field of the residual. -/
public theorem OrderThreeWholeFillingRelatorChartIdentity.relator_mem_normalClosure
    (h : A.OrderThreeWholeFillingRelatorChartIdentity) :
    (A.coreDataOf A.actualCuspCentralNaturality).rhoOne ^ 3 *
        (Additive.toMul
          ((A.coreDataOf A.actualCuspCentralNaturality).translation (-epsilon)))⁻¹ ∈
      Subgroup.normalClosure
        {A.actualEllipticThreeOverlapToCore
          A.orderThreeActualEllipticCanonicalRelator} := by
  obtain ⟨c, hc⟩ := h.core_conjugacy A
  change A.orderThreeCentralRelatorToCore A.actualCuspCentralNaturality ∈ _
  rw [hc]
  exact conjugate_mem_normalClosure_singleton c
    (A.actualEllipticThreeOverlapToCore A.orderThreeActualEllipticCanonicalRelator)

/-- The order-four whole-loop identity supplies exactly the order-four field of the residual. -/
public theorem OrderFourWholeFillingRelatorChartIdentity.relator_mem_normalClosure
    (h : A.OrderFourWholeFillingRelatorChartIdentity) :
    (A.coreDataOf A.actualCuspCentralNaturality).rhoTwo ^ 4 *
        (Additive.toMul
          ((A.coreDataOf A.actualCuspCentralNaturality).translation epsilon'))⁻¹ ∈
      Subgroup.normalClosure
        {A.actualEllipticFourOverlapToCore
          A.orderFourActualEllipticCanonicalRelator} := by
  obtain ⟨c, hc⟩ := h.core_conjugacy A
  change A.orderFourCentralRelatorToCore A.actualCuspCentralNaturality ∈ _
  rw [hc]
  exact conjugate_mem_normalClosure_singleton c
    (A.actualEllipticFourOverlapToCore A.orderFourActualEllipticCanonicalRelator)

/-- The residual is reduced to exactly one whole-loop chart identity for each elliptic collar. -/
public theorem actualEllipticRelatorNormalClosureResidual_of_wholeFillingRelatorChartIdentities
    (hThree : A.OrderThreeWholeFillingRelatorChartIdentity)
    (hFour : A.OrderFourWholeFillingRelatorChartIdentity) :
    A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality where
  orderThree := hThree.relator_mem_normalClosure A
  orderFour := hFour.relator_mem_normalClosure A

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
