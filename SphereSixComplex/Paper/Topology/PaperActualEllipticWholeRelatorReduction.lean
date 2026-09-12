module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticStraightLoopGeometricConnectorReduction

/-!
# Whole-relator reduction for the actual elliptic collars

Normal closure does not require separate normalizations of the meridian and translation
generators.  This file reduces each field of the remaining elliptic residual to one loop-class
identity for the complete local filling relation.
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

public theorem cuspCentralNaturality_centralToCore_orderThreeCentralExpectedRelator :
    A.cuspCentralNaturality.centralToCore A.orderThreeCentralExpectedRelator =
      A.orderThreeCentralRelatorToCore A.cuspCentralNaturality := by
  rw [orderThreeCentralExpectedRelator, orderThreeCentralRelatorToCore]
  simp only [map_mul, map_pow, map_inv]
  rfl

public theorem cuspCentralNaturality_centralToCore_orderFourCentralExpectedRelator :
    A.cuspCentralNaturality.centralToCore A.orderFourCentralExpectedRelator =
      A.orderFourCentralRelatorToCore A.cuspCentralNaturality := by
  rw [orderFourCentralExpectedRelator, orderFourCentralRelatorToCore]
  simp only [map_mul, map_pow, map_inv]
  rfl

/-- The one order-three whole-loop identity gives a conjugacy in the actual core. -/
public theorem ellipticThree_core_conjugacy_of_relator_eq
    (h : (∃ β : Path A.centralAffineBase A.ellipticThreeOverlapCentralBase,
    A.ellipticThreeCanonicalRelatorInCentral =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β A.orderThreeCentralExpectedRelator)) :
    ∃ c : FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩,
      A.orderThreeCentralRelatorToCore A.cuspCentralNaturality =
        c * A.ellipticThreeOverlapToCore
          A.ellipticThreeCanonicalRelator * c⁻¹ := by
  obtain ⟨β, hβ⟩ := h
  let source := A.orderThreeCentralBaseWhisker.cast rfl
    A.ellipticThreeCentralBase_eq_overlapCentralBase.symm
  have htransport :=
    A.cuspCentralNaturalityPair_simultaneouslyConjugate_orderThree
      A.orderThreeCentralExpectedRelator 1
  change SimultaneouslyConjugate
    (A.cuspCentralNaturality.centralToCore A.orderThreeCentralExpectedRelator,
      A.cuspCentralNaturality.centralToCore 1)
    (A.ellipticThreeCentralToCoreEquiv
        (FundamentalGroup.fundamentalGroupMulEquivOfPath source
          A.orderThreeCentralExpectedRelator),
      A.ellipticThreeCentralToCoreEquiv
        (FundamentalGroup.fundamentalGroupMulEquivOfPath source 1)) at htransport
  have hpaths := fundamentalGroupPair_simultaneouslyConjugate_of_paths
    source β A.orderThreeCentralExpectedRelator 1
  have hpathsCore := hpaths.map A.ellipticThreeCentralToCoreEquiv.toMonoidHom
  have htotal := htransport.trans hpathsCore
  obtain ⟨c, hrelator, _⟩ := htotal
  change A.cuspCentralNaturality.centralToCore A.orderThreeCentralExpectedRelator =
    c * A.ellipticThreeCentralToCoreEquiv
      (FundamentalGroup.fundamentalGroupMulEquivOfPath β
        A.orderThreeCentralExpectedRelator) * c⁻¹ at hrelator
  refine ⟨c, ?_⟩
  rw [← A.cuspCentralNaturality_centralToCore_orderThreeCentralExpectedRelator]
  rw [hrelator]
  congr 2
  rw [← hβ]
  exact A.ellipticThreeCanonicalRelatorInCentral_toCore

/-- The one order-four whole-loop identity gives a conjugacy in the actual core. -/
public theorem ellipticFour_core_conjugacy_of_relator_eq
    (h : (∃ β : Path A.centralAffineBase A.ellipticFourOverlapCentralBase,
    A.ellipticFourCanonicalRelatorInCentral =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β A.orderFourCentralExpectedRelator)) :
    ∃ c : FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩,
      A.orderFourCentralRelatorToCore A.cuspCentralNaturality =
        c * A.ellipticFourOverlapToCore
          A.ellipticFourCanonicalRelator * c⁻¹ := by
  obtain ⟨β, hβ⟩ := h
  let source := A.orderFourCentralBaseWhisker.cast rfl
    A.ellipticFourCentralBase_eq_overlapCentralBase.symm
  have htransport :=
    A.cuspCentralNaturalityPair_simultaneouslyConjugate_orderFour
      A.orderFourCentralExpectedRelator 1
  change SimultaneouslyConjugate
    (A.cuspCentralNaturality.centralToCore A.orderFourCentralExpectedRelator,
      A.cuspCentralNaturality.centralToCore 1)
    (A.ellipticFourCentralToCoreEquiv
        (FundamentalGroup.fundamentalGroupMulEquivOfPath source
          A.orderFourCentralExpectedRelator),
      A.ellipticFourCentralToCoreEquiv
        (FundamentalGroup.fundamentalGroupMulEquivOfPath source 1)) at htransport
  have hpaths := fundamentalGroupPair_simultaneouslyConjugate_of_paths
    source β A.orderFourCentralExpectedRelator 1
  have hpathsCore := hpaths.map A.ellipticFourCentralToCoreEquiv.toMonoidHom
  have htotal := htransport.trans hpathsCore
  obtain ⟨c, hrelator, _⟩ := htotal
  change A.cuspCentralNaturality.centralToCore A.orderFourCentralExpectedRelator =
    c * A.ellipticFourCentralToCoreEquiv
      (FundamentalGroup.fundamentalGroupMulEquivOfPath β
        A.orderFourCentralExpectedRelator) * c⁻¹ at hrelator
  refine ⟨c, ?_⟩
  rw [← A.cuspCentralNaturality_centralToCore_orderFourCentralExpectedRelator]
  rw [hrelator]
  congr 2
  rw [← hβ]
  exact A.ellipticFourCanonicalRelatorInCentral_toCore

/-- The order-three whole-loop identity supplies exactly the order-three field of the residual. -/
public theorem ellipticThree_relator_mem_normalClosure_of_relator_eq
    (h : (∃ β : Path A.centralAffineBase A.ellipticThreeOverlapCentralBase,
    A.ellipticThreeCanonicalRelatorInCentral =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β A.orderThreeCentralExpectedRelator)) :
    (A.coreDataOf A.cuspCentralNaturality).rhoOne ^ 3 *
        (Additive.toMul
          ((A.coreDataOf A.cuspCentralNaturality).translation (-epsilon)))⁻¹ ∈
      Subgroup.normalClosure
        {A.ellipticThreeOverlapToCore
          A.ellipticThreeCanonicalRelator} := by
  obtain ⟨c, hc⟩ := A.ellipticThree_core_conjugacy_of_relator_eq h
  change A.orderThreeCentralRelatorToCore A.cuspCentralNaturality ∈ _
  rw [hc]
  exact conjugate_mem_normalClosure_singleton c
    (A.ellipticThreeOverlapToCore A.ellipticThreeCanonicalRelator)

/-- The order-four whole-loop identity supplies exactly the order-four field of the residual. -/
public theorem ellipticFour_relator_mem_normalClosure_of_relator_eq
    (h : (∃ β : Path A.centralAffineBase A.ellipticFourOverlapCentralBase,
    A.ellipticFourCanonicalRelatorInCentral =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β A.orderFourCentralExpectedRelator)) :
    (A.coreDataOf A.cuspCentralNaturality).rhoTwo ^ 4 *
        (Additive.toMul
          ((A.coreDataOf A.cuspCentralNaturality).translation epsilon'))⁻¹ ∈
      Subgroup.normalClosure
        {A.ellipticFourOverlapToCore
          A.ellipticFourCanonicalRelator} := by
  obtain ⟨c, hc⟩ := A.ellipticFour_core_conjugacy_of_relator_eq h
  change A.orderFourCentralRelatorToCore A.cuspCentralNaturality ∈ _
  rw [hc]
  exact conjugate_mem_normalClosure_singleton c
    (A.ellipticFourOverlapToCore A.ellipticFourCanonicalRelator)


end SphereSixComplex.Geometry.AnalyticData

end

end
