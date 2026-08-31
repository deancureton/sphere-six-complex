module

public import SphereSixComplex.Topology.PaperActualEllipticLocalMarkedLoopCompatibilityProof

/-!
# Connector-sound straight-loop identities for the actual elliptic collars

The literal chart calculation must select one common connector for each pair.  Requiring exact
transport along the unrelated `PathConnectedSpace.somePath` used by the production marking is
not invariant under changing that choice.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

public def OrderThreeCentralBoundaryExistentialStraightLoopIdentities : Prop :=
  letI := A.orderThreeActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  ∃ β : Path A.centralAffineBase A.orderThreeActualEllipticCentralBase,
    FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.orderThreeActualEllipticBoundaryDeckStraightLoop
            A.orderThreeActualEllipticBoundaryDeckData.meridian)) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          A.centralAffineCorePiOneData.rhoOne ∧
      FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.orderThreeActualEllipticBoundaryDeckStraightLoop
            (Additive.toMul
              (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))

public def OrderFourCentralBoundaryExistentialStraightLoopIdentities : Prop :=
  letI := A.orderFourActualEllipticBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  ∃ β : Path A.centralAffineBase A.orderFourActualEllipticCentralBase,
    FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.orderFourActualEllipticBoundaryDeckStraightLoop
            A.orderFourActualEllipticBoundaryDeckData.meridian)) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          A.centralAffineCorePiOneData.rhoTwo ∧
      FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.orderFourActualEllipticBoundaryDeckStraightLoop
            (Additive.toMul
              (A.orderFourActualEllipticBoundaryDeckData.translation epsilon')))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))

public theorem OrderThreeCentralBoundaryExistentialStraightLoopIdentities.toMarkedLoopCompatibility
    (H : A.OrderThreeCentralBoundaryExistentialStraightLoopIdentities) :
    A.OrderThreeCentralMarkedLoopCompatibility := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let C := A.orderThreeActualCentralCoverComparison
  change ∃ β : Path A.centralAffineBase A.orderThreeActualEllipticCentralBase,
      _ ∧ _ at H
  obtain ⟨β, hmeridian, htranslation⟩ := H
  have hpaths := fundamentalGroupPair_simultaneouslyConjugate_of_paths
    A.orderThreeCentralBaseWhisker β A.centralAffineCorePiOneData.rhoOne
      (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))
  rw [← hmeridian, ← htranslation] at hpaths
  let hbase := C.commutes A.orderThreeActualEllipticBoundaryBase
  have h := hpaths.map (fundamentalGroupMulEquivOfEq hbase).toMonoidHom
  change SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq hbase A.orderThreeCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq hbase A.orderThreeCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral hbase
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral hbase
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))))
  rw [← A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck,
    ← A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
  convert h using 1
  · apply Prod.ext
    · change fundamentalGroupElementOfBaseEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderThreeCentralBaseWhisker A.centralAffineCorePiOneData.rhoOne) =
        fundamentalGroupMulEquivOfEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderThreeCentralBaseWhisker A.centralAffineCorePiOneData.rhoOne)
      exact (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm
    · change fundamentalGroupElementOfBaseEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderThreeCentralBaseWhisker
            (Additive.toMul
              (A.centralAffineCorePiOneData.translation (-epsilon)))) =
        fundamentalGroupMulEquivOfEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderThreeCentralBaseWhisker
            (Additive.toMul
              (A.centralAffineCorePiOneData.translation (-epsilon))))
      exact (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm
  · apply Prod.ext
    · change FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral hbase _ =
          fundamentalGroupMulEquivOfEq hbase
            (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl _)
      calc
        _ = fundamentalGroupElementOfBaseEq hbase
            (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
              (Path.Homotopic.Quotient.mk
                (A.orderThreeActualEllipticBoundaryDeckStraightLoop
                  A.orderThreeActualEllipticBoundaryDeckData.meridian))) :=
          mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
        _ = _ := (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm
    · change FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral hbase _ =
          fundamentalGroupMulEquivOfEq hbase
            (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl _)
      calc
        _ = fundamentalGroupElementOfBaseEq hbase
            (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
              (Path.Homotopic.Quotient.mk
                (A.orderThreeActualEllipticBoundaryDeckStraightLoop
                  (Additive.toMul
                    (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))))) :=
          mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
        _ = _ := (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm

public theorem OrderFourCentralBoundaryExistentialStraightLoopIdentities.toMarkedLoopCompatibility
    (H : A.OrderFourCentralBoundaryExistentialStraightLoopIdentities) :
    A.OrderFourCentralMarkedLoopCompatibility := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let C := A.orderFourActualCentralCoverComparison
  change ∃ β : Path A.centralAffineBase A.orderFourActualEllipticCentralBase,
      _ ∧ _ at H
  obtain ⟨β, hmeridian, htranslation⟩ := H
  have hpaths := fundamentalGroupPair_simultaneouslyConjugate_of_paths
    A.orderFourCentralBaseWhisker β A.centralAffineCorePiOneData.rhoTwo
      (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))
  rw [← hmeridian, ← htranslation] at hpaths
  let hbase := C.commutes A.orderFourActualEllipticBoundaryBase
  have h := hpaths.map (fundamentalGroupMulEquivOfEq hbase).toMonoidHom
  change SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq hbase A.orderFourCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq hbase A.orderFourCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral hbase
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral hbase
        (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))))
  rw [← A.orderFourActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck,
    ← A.orderFourActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
  convert h using 1
  · apply Prod.ext
    · change fundamentalGroupElementOfBaseEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderFourCentralBaseWhisker A.centralAffineCorePiOneData.rhoTwo) =
        fundamentalGroupMulEquivOfEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderFourCentralBaseWhisker A.centralAffineCorePiOneData.rhoTwo)
      exact (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm
    · change fundamentalGroupElementOfBaseEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderFourCentralBaseWhisker
            (Additive.toMul
              (A.centralAffineCorePiOneData.translation epsilon'))) =
        fundamentalGroupMulEquivOfEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderFourCentralBaseWhisker
            (Additive.toMul
              (A.centralAffineCorePiOneData.translation epsilon')))
      exact (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm
  · apply Prod.ext
    · change FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral hbase _ =
          fundamentalGroupMulEquivOfEq hbase
            (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl _)
      calc
        _ = fundamentalGroupElementOfBaseEq hbase
            (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
              (Path.Homotopic.Quotient.mk
                (A.orderFourActualEllipticBoundaryDeckStraightLoop
                  A.orderFourActualEllipticBoundaryDeckData.meridian))) :=
          mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
        _ = _ := (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm
    · change FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral hbase _ =
          fundamentalGroupMulEquivOfEq hbase
            (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl _)
      calc
        _ = fundamentalGroupElementOfBaseEq hbase
            (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
              (Path.Homotopic.Quotient.mk
                (A.orderFourActualEllipticBoundaryDeckStraightLoop
                  (Additive.toMul
                    (A.orderFourActualEllipticBoundaryDeckData.translation epsilon'))))) :=
          mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
        _ = _ := (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm

public theorem actualEllipticRelatorNormalClosureResidual_of_existentialStraightLoopIdentities
    (H3 : A.OrderThreeCentralBoundaryExistentialStraightLoopIdentities)
    (H4 : A.OrderFourCentralBoundaryExistentialStraightLoopIdentities) :
    A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality :=
  A.actualEllipticRelatorNormalClosureResidual_of_markedLoopCompatibilities
    (H3.toMarkedLoopCompatibility A) (H4.toMarkedLoopCompatibility A)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
