module

public import SphereSixComplex.Topology.PaperOrderThreeBasedChartLoopIdentities
public import SphereSixComplex.Topology.PaperActualEllipticOrderFourCentralConnectorCoherence

/-!
# Local marked-loop inputs for the actual elliptic collars
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology

public theorem fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path y z) (h : x = y) (a : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p
        (fundamentalGroupElementOfBaseEq h a) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.cast h rfl) a := by
  subst y
  unfold fundamentalGroupElementOfBaseEq
  simp

public theorem mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (a : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq f h a =
      fundamentalGroupElementOfBaseEq h
        (FundamentalGroup.mapOfEq f rfl a) := by
  subst y
  rfl

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

public theorem orderThreeCentralAffineBasedMarkingCoherence :
    A.OrderThreeCentralAffineBasedMarkingCoherence := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let C := A.orderThreeActualCentralCoverComparison
  let β := A.orderThreeCentralBaseWhisker.cast
    A.centralAffineBase_eq_actualCuspCentralBase.symm rfl
  refine ⟨β, ?_, ?_⟩
  · have hinner : A.orderThreeCentralMeridianAtOverlap =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (paperPuncturedGlobalFamilyAffinePresentation A
            (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)) := by
      simpa [orderThreeCentralMeridianAtOverlap, centralAffineCorePiOneData_rhoOne,
        paperPuncturedGlobalFamilyAffinePresentation, actualCuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq] using
        fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left
          A.orderThreeCentralBaseWhisker
          A.centralAffineBase_eq_actualCuspCentralBase.symm A.geometricCentralRhoOne
    exact congrArg
      (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)) hinner

  · have hinner : A.orderThreeCentralTranslationAtOverlap =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (paperPuncturedGlobalFamilyAffinePresentation A
            (Additive.toMul
              (freeAffineTranslation (M := paperCentralFreeMonodromy) (-epsilon)))) := by
      simpa [orderThreeCentralTranslationAtOverlap,
        centralAffineCorePiOneData_translation,
        paperPuncturedGlobalFamilyAffinePresentation, actualCuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq] using
        fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left
          A.orderThreeCentralBaseWhisker
          A.centralAffineBase_eq_actualCuspCentralBase.symm
          (Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon)))
    exact congrArg
      (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)) hinner

public theorem OrderThreeCentralBoundaryStraightLoopIdentities.toMarkedLoopCompatibility
    (H : A.OrderThreeCentralBoundaryStraightLoopIdentities) :
    A.OrderThreeCentralMarkedLoopCompatibility := by
  have hcover := (H.toBasedChartIdentities A).toCoverComparison A
  exact A.orderThreeCentralAffineBasedMarkingCoherence.toMarkedLoopCompatibility A hcover

public def OrderThreeCentralBoundaryMarkedStraightLoopIdentities : Prop :=
  letI := A.orderThreeActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
      (Path.Homotopic.Quotient.mk
        (A.orderThreeActualEllipticBoundaryDeckStraightLoop
          A.orderThreeActualEllipticBoundaryDeckData.meridian)) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderThreeCentralBaseWhisker A.centralAffineCorePiOneData.rhoOne ∧
    FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
      (Path.Homotopic.Quotient.mk
        (A.orderThreeActualEllipticBoundaryDeckStraightLoop
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderThreeCentralBaseWhisker
        (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))

public theorem OrderThreeCentralBoundaryMarkedStraightLoopIdentities.toMarkedLoopCompatibility
    (H : A.OrderThreeCentralBoundaryMarkedStraightLoopIdentities) :
    A.OrderThreeCentralMarkedLoopCompatibility := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let C := A.orderThreeActualCentralCoverComparison
  change _ ∧ _ at H
  change SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        A.orderThreeCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral
        (C.commutes A.orderThreeActualEllipticBoundaryBase)
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))))
  refine ⟨1, ?_, ?_⟩ <;> simp only [one_mul, inv_one, mul_one]
  · rw [← A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
    symm
    calc
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
            (Path.Homotopic.Quotient.mk
              (A.orderThreeActualEllipticBoundaryDeckStraightLoop
                A.orderThreeActualEllipticBoundaryDeckData.meridian))) :=
        mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderThreeCentralBaseWhisker A.centralAffineCorePiOneData.rhoOne) :=
        congrArg _ H.1
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          A.orderThreeCentralMeridianAtOverlap := by rfl
  · rw [← A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
    symm
    calc
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
            (Path.Homotopic.Quotient.mk
              (A.orderThreeActualEllipticBoundaryDeckStraightLoop
                (Additive.toMul
                  (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))))) :=
        mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderThreeCentralBaseWhisker
            (Additive.toMul
              (A.centralAffineCorePiOneData.translation (-epsilon)))) :=
        congrArg _ H.2
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderThreeActualEllipticBoundaryBase)
          A.orderThreeCentralTranslationAtOverlap := by rfl

public noncomputable def orderFourActualEllipticBoundaryDeckStraightLift
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    Path A.orderFourActualEllipticBoundaryBase
      (g • A.orderFourActualEllipticBoundaryBase) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.orderFourActualEllipticBoundaryAction
  let b := A.orderFourActualEllipticBoundaryBase
  exact {
    toFun := fun t ↦ (b.1, Path.segment b.2 (g • b.2) t)
    continuous_toFun :=
      continuous_const.prodMk (Path.segment b.2 (g • b.2)).continuous
    source' := by rw [(Path.segment b.2 (g • b.2)).source]
    target' := by
      rw [(Path.segment b.2 (g • b.2)).target]
      rfl
  }

public noncomputable def orderFourActualEllipticBoundaryDeckStraightLoop
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    Path
      (A.orderFourActualEllipticBoundaryProjection A.orderFourActualEllipticBoundaryBase)
      (A.orderFourActualEllipticBoundaryProjection A.orderFourActualEllipticBoundaryBase) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.orderFourActualEllipticBoundaryAction
  let hp := A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
  exact ((A.orderFourActualEllipticBoundaryDeckStraightLift g).map
      A.orderFourActualEllipticBoundaryProjection.continuous).cast rfl
        (hp.map_smul g).symm

public theorem orderFourActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    Path.Homotopic.Quotient.mk (A.orderFourActualEllipticBoundaryDeckStraightLoop g) =
      ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase g := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let hp := A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
  let e : A.orderFourActualEllipticBoundaryProjection ⁻¹'
      {A.orderFourActualEllipticBoundaryProjection A.orderFourActualEllipticBoundaryBase} :=
    ⟨A.orderFourActualEllipticBoundaryBase, rfl⟩
  apply (hp.fundamentalGroupEquiv e).injective
  rw [fundamentalGroupEquiv_ofDeck]
  apply (hp.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  let e' : A.orderFourActualEllipticBoundaryProjection ⁻¹'
      {A.orderFourActualEllipticBoundaryProjection A.orderFourActualEllipticBoundaryBase} :=
    ⟨g • A.orderFourActualEllipticBoundaryBase, hp.map_smul g⟩
  let Γ : Path.Homotopic.Quotient A.orderFourActualEllipticBoundaryBase
      (g • A.orderFourActualEllipticBoundaryBase) :=
    Path.Homotopic.Quotient.mk (A.orderFourActualEllipticBoundaryDeckStraightLift g)
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq (ex := e) (ey := e') Γ (by
    dsimp [e, e']
    change (Path.Homotopic.Quotient.mk
        (A.orderFourActualEllipticBoundaryDeckStraightLift g)).map
          A.orderFourActualEllipticBoundaryProjection =
      (Path.Homotopic.Quotient.mk
        (A.orderFourActualEllipticBoundaryDeckStraightLoop g)).cast _ _
    rw [← Path.Homotopic.Quotient.mk_map]
    unfold orderFourActualEllipticBoundaryDeckStraightLoop
    rw [Path.Homotopic.Quotient.mk_cast]
    exact eq_of_heq
      ((Path.Homotopic.Quotient.cast_heq _ _).trans
        (Path.Homotopic.Quotient.cast_heq _ _)).symm)
  simpa using congrArg Subtype.val hm.symm

public def OrderFourCentralBoundaryStraightLoopIdentities : Prop :=
  letI := A.orderFourActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
      (Path.Homotopic.Quotient.mk
        (A.orderFourActualEllipticBoundaryDeckStraightLoop
          A.orderFourActualEllipticBoundaryDeckData.meridian)) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderFourCentralBaseWhisker A.centralAffineCorePiOneData.rhoTwo ∧
    FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
      (Path.Homotopic.Quotient.mk
        (A.orderFourActualEllipticBoundaryDeckStraightLoop
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon')))) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderFourCentralBaseWhisker
        (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))

public theorem OrderFourCentralBoundaryStraightLoopIdentities.toMarkedLoopCompatibility
    (H : A.OrderFourCentralBoundaryStraightLoopIdentities) :
    A.OrderFourCentralMarkedLoopCompatibility := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let C := A.orderFourActualCentralCoverComparison
  change _ ∧ _ at H
  change SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        A.orderFourCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        A.orderFourCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral
        (C.commutes A.orderFourActualEllipticBoundaryBase)
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))))
  refine ⟨1, ?_, ?_⟩ <;> simp only [one_mul, inv_one, mul_one]
  · rw [← A.orderFourActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
    symm
    calc
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
            (Path.Homotopic.Quotient.mk
              (A.orderFourActualEllipticBoundaryDeckStraightLoop
                A.orderFourActualEllipticBoundaryDeckData.meridian))) :=
        mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderFourCentralBaseWhisker A.centralAffineCorePiOneData.rhoTwo) :=
        congrArg _ H.1
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          A.orderFourCentralMeridianAtOverlap := by rfl
  · rw [← A.orderFourActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
    symm
    calc
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
            (Path.Homotopic.Quotient.mk
              (A.orderFourActualEllipticBoundaryDeckStraightLoop
                (Additive.toMul
                  (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))))) :=
        mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderFourCentralBaseWhisker
            (Additive.toMul
              (A.centralAffineCorePiOneData.translation epsilon'))) :=
        congrArg _ H.2
      _ = fundamentalGroupElementOfBaseEq
          (C.commutes A.orderFourActualEllipticBoundaryBase)
          A.orderFourCentralTranslationAtOverlap := by rfl

public theorem actualEllipticRelatorNormalClosureResidual_of_straightLoopIdentities
    (H3 : A.OrderThreeCentralBoundaryStraightLoopIdentities)
    (H4 : A.OrderFourCentralBoundaryStraightLoopIdentities) :
    A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality :=
  A.actualEllipticRelatorNormalClosureResidual_of_markedLoopCompatibilities
    (H3.toMarkedLoopCompatibility A) (H4.toMarkedLoopCompatibility A)

public theorem actualEllipticRelatorNormalClosureResidual_of_markedStraightLoopIdentities
    (H3 : A.OrderThreeCentralBoundaryMarkedStraightLoopIdentities)
    (H4 : A.OrderFourCentralBoundaryStraightLoopIdentities) :
    A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality :=
  A.actualEllipticRelatorNormalClosureResidual_of_markedLoopCompatibilities
    (H3.toMarkedLoopCompatibility A) (H4.toMarkedLoopCompatibility A)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
