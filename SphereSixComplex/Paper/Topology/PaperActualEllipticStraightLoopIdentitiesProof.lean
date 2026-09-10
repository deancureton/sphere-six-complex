module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticLocalMarkedLoopCompatibilityProof

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
  letI := A.ellipticThreeBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  ∃ β : Path A.centralAffineBase A.ellipticThreeCentralBase,
    FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.ellipticThreeBoundaryDeckStraightLoop
            A.ellipticThreeBoundaryDeckData.meridian)) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          A.centralAffineCorePiOneData.rhoOne ∧
      FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.ellipticThreeBoundaryDeckStraightLoop
            (Additive.toMul
              (A.ellipticThreeBoundaryDeckData.translation (-epsilon))))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))

public def OrderFourCentralBoundaryExistentialStraightLoopIdentities : Prop :=
  letI := A.ellipticFourBoundaryAction
  letI : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  ∃ β : Path A.centralAffineBase A.ellipticFourCentralBase,
    FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.ellipticFourBoundaryDeckStraightLoop
            A.ellipticFourBoundaryDeckData.meridian)) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          A.centralAffineCorePiOneData.rhoTwo ∧
      FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
        (Path.Homotopic.Quotient.mk
          (A.ellipticFourBoundaryDeckStraightLoop
            (Additive.toMul
              (A.ellipticFourBoundaryDeckData.translation epsilon')))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))

public theorem OrderThreeCentralBoundaryExistentialStraightLoopIdentities.toMarkedLoopCompatibility
    (H : A.OrderThreeCentralBoundaryExistentialStraightLoopIdentities) :
    A.OrderThreeCentralMarkedLoopCompatibility := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let C := A.ellipticThreeCentralCoverComparison
  change ∃ β : Path A.centralAffineBase A.ellipticThreeCentralBase,
      _ ∧ _ at H
  obtain ⟨β, hmeridian, htranslation⟩ := H
  have hpaths := fundamentalGroupPair_simultaneouslyConjugate_of_paths
    A.orderThreeCentralBaseWhisker β A.centralAffineCorePiOneData.rhoOne
      (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))
  rw [← hmeridian, ← htranslation] at hpaths
  let hbase := C.commutes A.ellipticThreeBoundaryBase
  have h := hpaths.map (fundamentalGroupMulEquivOfEq hbase).toMonoidHom
  change SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq hbase A.orderThreeCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq hbase A.orderThreeCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral hbase
        (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
          A.ellipticThreeBoundaryBase
          A.ellipticThreeBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral hbase
        (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
          A.ellipticThreeBoundaryBase
          (Additive.toMul
            (A.ellipticThreeBoundaryDeckData.translation (-epsilon)))))
  rw [← A.ellipticThreeBoundaryDeckStraightLoop_class_eq_ofDeck,
    ← A.ellipticThreeBoundaryDeckStraightLoop_class_eq_ofDeck]
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
    · change FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral hbase _ =
          fundamentalGroupMulEquivOfEq hbase
            (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl _)
      calc
        _ = fundamentalGroupElementOfBaseEq hbase
            (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
              (Path.Homotopic.Quotient.mk
                (A.ellipticThreeBoundaryDeckStraightLoop
                  A.ellipticThreeBoundaryDeckData.meridian))) :=
          mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
        _ = _ := (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm
    · change FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral hbase _ =
          fundamentalGroupMulEquivOfEq hbase
            (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl _)
      calc
        _ = fundamentalGroupElementOfBaseEq hbase
            (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
              (Path.Homotopic.Quotient.mk
                (A.ellipticThreeBoundaryDeckStraightLoop
                  (Additive.toMul
                    (A.ellipticThreeBoundaryDeckData.translation (-epsilon)))))) :=
          mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
        _ = _ := (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm

public theorem OrderFourCentralBoundaryExistentialStraightLoopIdentities.toMarkedLoopCompatibility
    (H : A.OrderFourCentralBoundaryExistentialStraightLoopIdentities) :
    A.OrderFourCentralMarkedLoopCompatibility := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let C := A.ellipticFourCentralCoverComparison
  change ∃ β : Path A.centralAffineBase A.ellipticFourCentralBase,
      _ ∧ _ at H
  obtain ⟨β, hmeridian, htranslation⟩ := H
  have hpaths := fundamentalGroupPair_simultaneouslyConjugate_of_paths
    A.orderFourCentralBaseWhisker β A.centralAffineCorePiOneData.rhoTwo
      (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))
  rw [← hmeridian, ← htranslation] at hpaths
  let hbase := C.commutes A.ellipticFourBoundaryBase
  have h := hpaths.map (fundamentalGroupMulEquivOfEq hbase).toMonoidHom
  change SimultaneouslyConjugate
    (fundamentalGroupElementOfBaseEq hbase A.orderFourCentralMeridianAtOverlap,
      fundamentalGroupElementOfBaseEq hbase A.orderFourCentralTranslationAtOverlap)
    (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral hbase
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          A.ellipticFourBoundaryDeckData.meridian),
      FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral hbase
        (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
          (Additive.toMul
            (A.ellipticFourBoundaryDeckData.translation epsilon'))))
  rw [← A.ellipticFourBoundaryDeckStraightLoop_class_eq_ofDeck,
    ← A.ellipticFourBoundaryDeckStraightLoop_class_eq_ofDeck]
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
    · change FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral hbase _ =
          fundamentalGroupMulEquivOfEq hbase
            (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl _)
      calc
        _ = fundamentalGroupElementOfBaseEq hbase
            (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
              (Path.Homotopic.Quotient.mk
                (A.ellipticFourBoundaryDeckStraightLoop
                  A.ellipticFourBoundaryDeckData.meridian))) :=
          mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
        _ = _ := (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm
    · change FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral hbase _ =
          fundamentalGroupMulEquivOfEq hbase
            (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl _)
      calc
        _ = fundamentalGroupElementOfBaseEq hbase
            (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
              (Path.Homotopic.Quotient.mk
                (A.ellipticFourBoundaryDeckStraightLoop
                  (Additive.toMul
                    (A.ellipticFourBoundaryDeckData.translation epsilon'))))) :=
          mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl _ _ _
        _ = _ := (fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq hbase _).symm

public theorem ellipticRelatorMembership_of_existentialStraightLoopIdentities
    (H3 : A.OrderThreeCentralBoundaryExistentialStraightLoopIdentities)
    (H4 : A.OrderFourCentralBoundaryExistentialStraightLoopIdentities) :
    A.EllipticRelatorMembership A.cuspCentralNaturality :=
  A.ellipticRelatorMembership_of_markedLoopCompatibilities
    (H3.toMarkedLoopCompatibility A) (H4.toMarkedLoopCompatibility A)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
