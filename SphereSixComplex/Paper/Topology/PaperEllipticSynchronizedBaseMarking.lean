module
public import SphereSixComplex.Paper.Topology.PaperEllipticBoundaryBaseMarking
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeBaseFactorHomotopyProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourLocalGlobalFactorHomotopyReduction

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent

variable (A : AnalyticData)

public theorem orderFourPuncturedProductCentralRealization_coordinate_fiber_independent
    (z : A.OrderFourCayleyPuncturedDisc) (v w : A.OrderFourTorus) :
    letI := A.ellipticFourBoundaryAction
    A.centralFamilyCoordinate (A.orderFourPuncturedProductCentralRealizationMap (z, v)) =
      A.centralFamilyCoordinate (A.orderFourPuncturedProductCentralRealizationMap (z, w)) := by
  let _ := A.ellipticFourBoundaryAction
  apply Subtype.ext
  change (A.centralFamilyCoordinate
    (A.centralQuotientProjection (A.orderFourPuncturedProductRegularRealizationMap (z, v)))).1 =
    (A.centralFamilyCoordinate
    (A.centralQuotientProjection (A.orderFourPuncturedProductRegularRealizationMap (z, w)))).1
  rw [A.centralFamilyCoordinate_centralQuotientProjection,
    A.centralFamilyCoordinate_centralQuotientProjection]
  apply congrArg A.modular.sourceCoordinate.coordinate
  apply orderFourCayleyHomeomorph.injective
  have hv := congrArg Prod.fst
    (A.orderFourPuncturedProductToRegularMap_productCoordinate (z, v))
  have hw := congrArg Prod.fst
    (A.orderFourPuncturedProductToRegularMap_productCoordinate (z, w))
  rw [orderFourRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at hv hw
  exact hv.trans hw.symm

public theorem orderFourCentralBaseFactor_basePath_eq_filling :
    letI := A.ellipticFourBoundaryAction
    A.orderFourCentralBaseFactor.map A.centralFamilyCoordinate_continuous =
      (A.ellipticFourBoundaryDeckStraightCentralLoop
        A.ellipticFourBoundaryDeckData.fillingRelation).map
          A.centralFamilyCoordinate_continuous := by
  let _ := A.ellipticFourBoundaryAction
  apply Path.ext
  funext t
  change A.centralFamilyCoordinate (A.orderFourCentralBaseFactor t) =
    A.centralFamilyCoordinate (A.ellipticFourBoundaryDeckStraightCentralLoop
      A.ellipticFourBoundaryDeckData.fillingRelation t)
  unfold orderFourCentralBaseFactor
  simp only [Path.cast_coe, Path.map_coe, Path.prod_coe, Path.refl_apply, Function.comp_apply]
  rw [A.orderFourDeckStraightCentralLoop_projects_representative]
  change _ = A.centralFamilyCoordinate
    (A.centralQuotientProjection (A.orderFourFillingRelationRegularLoop t))
  rw [← A.orderFourRegularLoop_eq_puncturedProductRealization]
  exact A.orderFourPuncturedProductCentralRealization_coordinate_fiber_independent _ _ _

public theorem twicePuncturedFundamentalGroup_pow_injective
    (x : TwicePuncturedComplex) (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (fun g : FundamentalGroup TwicePuncturedComplex x ↦ g ^ n) := by
  let _ : PathConnectedSpace TwicePuncturedComplex := TwicePuncturedComplex.ambient_pathConnected
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath
    (PathConnectedSpace.somePath x twicePuncturedComplexBasepoint)
  let F := (TwicePuncturedComplex.markedMeridianMulEquiv
    TwicePuncturedComplex.markedMeridianHom_injective).symm
  intro a b hab
  apply E.injective
  apply F.injective
  apply pow_left_injective hn
  simpa only [← map_pow] using congrArg (fun y ↦ F (E y)) hab

public theorem orderFourCentralAffineZeroSectionQuadruplePath_class :
    Path.Homotopic.Quotient.mk A.orderFourCentralAffineZeroSectionQuadruplePath =
      (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoTwo) ^ 4 := by
  unfold orderFourCentralAffineZeroSectionQuadruplePath
  rw [Path.Homotopic.Quotient.mk_cast,
    A.ellipticFourCuspZeroSectionQuadruplePath_class]
  rw [← map_pow]
  unfold cuspToCentralAffineBaseEquiv
  rw [fundamentalGroupMulEquivOfEq_apply]

public theorem orderFourCentralBaseComparisonTrace_first_power
    (H : ContinuousMap.Homotopy A.orderFourCentralBaseFactor.toContinuousMap
      A.orderFourCentralAffineZeroSectionQuadruplePath.toContinuousMap)
    (hH : ∀ s : unitInterval, H (s, 0) = H (s, 1)) :
    letI := A.ellipticFourBoundaryAction
    letI := A.ellipticFourBoundaryCover_simplyConnected
    let f : C(A.CentralFamily, TwicePuncturedComplex) :=
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
    FundamentalGroup.map f A.centralAffineBase
      (FundamentalGroup.fundamentalGroupMulEquivOfPath
        (A.orderFourCentralBaseComparisonTracePath H)
        (Path.Homotopic.Quotient.mk (A.ellipticFourBoundaryDeckStraightCentralLoop
          A.ellipticFourBoundaryDeckData.meridian))) =
      FundamentalGroup.map f A.centralAffineBase
        (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoTwo) := by
  let _ := A.ellipticFourBoundaryAction
  let _ := A.ellipticFourBoundaryCover_simplyConnected
  let f : C(A.CentralFamily, TwicePuncturedComplex) :=
    ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
  let W := A.orderFourCentralBaseComparisonTracePath H
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  have ht : (H.evalAt 0).cast A.orderFourCentralBaseFactor.source.symm
      A.orderFourCentralAffineZeroSectionQuadruplePath.source.symm =
      (H.evalAt 1).cast A.orderFourCentralBaseFactor.target.symm
      A.orderFourCentralAffineZeroSectionQuadruplePath.target.symm := by
    apply Path.ext
    funext t
    exact hH t
  have hf := SphereSixComplex.loopClass_eq_whiskered_of_freeHomotopy
    A.orderFourCentralBaseFactor A.orderFourCentralAffineZeroSectionQuadruplePath H ht
  have hE : E (Path.Homotopic.Quotient.mk A.orderFourCentralBaseFactor) =
      Path.Homotopic.Quotient.mk A.orderFourCentralAffineZeroSectionQuadruplePath := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    change _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm
      (pathLoopClass A.orderFourCentralAffineZeroSectionQuadruplePath)
    rw [fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass]
    exact hf
  apply twicePuncturedFundamentalGroup_pow_injective _ 4 (by decide)
  change (FundamentalGroup.map f A.centralAffineBase
    (E (Path.Homotopic.Quotient.mk (A.ellipticFourBoundaryDeckStraightCentralLoop
      A.ellipticFourBoundaryDeckData.meridian)))) ^ 4 =
    (FundamentalGroup.map f A.centralAffineBase
      (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoTwo)) ^ 4
  rw [← map_pow, ← map_pow, ← map_pow,
    ← A.orderFourCentralAffineZeroSectionQuadruplePath_class, ← hE]
  dsimp only [E]
  rw [CoveringSpace.map_fundamentalGroupMulEquivOfPath,
    CoveringSpace.map_fundamentalGroupMulEquivOfPath]
  apply (FundamentalGroup.fundamentalGroupMulEquivOfPath (W.map f.continuous)).injective.eq_iff.mpr
  simp only [map_pow, FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  rw [A.orderFourCentralBaseFactor_basePath_eq_filling]
  rw [← A.orderFourBoundaryBaseHom_ofDeck,
    ← A.orderFourBoundaryBaseHom_fillingRelation, A.orderFourBoundaryBaseHom_ofDeck]

public theorem orderThreePuncturedProductCentralRealization_coordinate_fiber_independent
    (z : A.OrderThreeCayleyPuncturedDisc) (v w : A.OrderThreeTorus) :
    letI := A.ellipticThreeBoundaryAction
    A.centralFamilyCoordinate (A.orderThreePuncturedProductToCentralMap (z, v)) =
      A.centralFamilyCoordinate (A.orderThreePuncturedProductToCentralMap (z, w)) := by
  let _ := A.ellipticThreeBoundaryAction
  apply Subtype.ext
  change (A.centralFamilyCoordinate
    (A.centralQuotientProjection (A.orderThreePuncturedProductToRegularMap (A.orderThreePuncturedProductCarrierMap (z, v))))).1 =
    (A.centralFamilyCoordinate
    (A.centralQuotientProjection (A.orderThreePuncturedProductToRegularMap (A.orderThreePuncturedProductCarrierMap (z, w))))).1
  rw [A.centralFamilyCoordinate_centralQuotientProjection,
    A.centralFamilyCoordinate_centralQuotientProjection]
  apply congrArg A.modular.sourceCoordinate.coordinate
  apply orderThreeCayleyHomeomorph.injective
  have hv := congrArg Prod.fst
    (A.orderThreePuncturedProductToRegularMap_productCoordinate (z, v))
  have hw := congrArg Prod.fst
    (A.orderThreePuncturedProductToRegularMap_productCoordinate (z, w))
  rw [orderThreeRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at hv hw
  exact hv.trans hw.symm

public theorem orderThreeLocalOffsetBaseCentralPath_basePath_eq_filling :
    letI := A.ellipticThreeBoundaryAction
    A.orderThreeLocalOffsetBaseCentralPath.map A.centralFamilyCoordinate_continuous =
      (A.ellipticThreeBoundaryDeckStraightCentralLoop
        A.ellipticThreeBoundaryDeckData.fillingRelation).map
          A.centralFamilyCoordinate_continuous := by
  let _ := A.ellipticThreeBoundaryAction
  apply Path.ext
  funext t
  change A.centralFamilyCoordinate (A.orderThreeLocalOffsetBaseCentralPath t) =
    A.centralFamilyCoordinate (A.ellipticThreeBoundaryDeckStraightCentralLoop
      A.ellipticThreeBoundaryDeckData.fillingRelation t)
  unfold orderThreeLocalOffsetBaseCentralPath
  simp only [Path.cast_coe, Path.map_coe, Path.prod_coe, Path.refl_apply, Function.comp_apply]
  rw [A.orderThreeDeckStraightCentralLoop_projects_representative]
  change _ = A.centralFamilyCoordinate
    (A.centralQuotientProjection (A.orderThreeFillingRelationRegularLoop t))
  rw [← A.orderThreeRegularLoop_eq_puncturedProductRealization]
  exact A.orderThreePuncturedProductCentralRealization_coordinate_fiber_independent _ _ _


public def orderThreeCentralBaseComparisonTracePath
    (H : ContinuousMap.Homotopy A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap) :
    Path A.ellipticThreeCentralBase A.centralAffineBase :=
  (H.evalAt 0).cast A.orderThreeLocalOffsetBaseCentralPath.source.symm
    A.orderThreeCentralAffineZeroSectionTriplePath.source.symm

public theorem orderThreeCentralAffineZeroSectionTriplePath_class :
    Path.Homotopic.Quotient.mk A.orderThreeCentralAffineZeroSectionTriplePath =
      (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoOne) ^ 3 := by
  unfold orderThreeCentralAffineZeroSectionTriplePath
  rw [Path.Homotopic.Quotient.mk_cast,
    A.ellipticThreeCuspZeroSectionTriplePath_class]
  rw [← map_pow]
  unfold cuspToCentralAffineBaseEquiv
  rw [fundamentalGroupMulEquivOfEq_apply]

public theorem orderThreeCentralBaseComparisonTrace_first_power
    (H : ContinuousMap.Homotopy A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap)
    (hH : ∀ s : unitInterval, H (s, 0) = H (s, 1)) :
    letI := A.ellipticThreeBoundaryAction
    letI := A.ellipticThreeBoundaryCover_simplyConnected
    let f : C(A.CentralFamily, TwicePuncturedComplex) :=
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
    FundamentalGroup.map f A.centralAffineBase
      (FundamentalGroup.fundamentalGroupMulEquivOfPath
        (A.orderThreeCentralBaseComparisonTracePath H)
        (Path.Homotopic.Quotient.mk (A.ellipticThreeBoundaryDeckStraightCentralLoop
          A.ellipticThreeBoundaryDeckData.meridian))) =
      FundamentalGroup.map f A.centralAffineBase
        (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoOne) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ := A.ellipticThreeBoundaryCover_simplyConnected
  let f : C(A.CentralFamily, TwicePuncturedComplex) :=
    ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
  let W := A.orderThreeCentralBaseComparisonTracePath H
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  have ht : (H.evalAt 0).cast A.orderThreeLocalOffsetBaseCentralPath.source.symm
      A.orderThreeCentralAffineZeroSectionTriplePath.source.symm =
      (H.evalAt 1).cast A.orderThreeLocalOffsetBaseCentralPath.target.symm
      A.orderThreeCentralAffineZeroSectionTriplePath.target.symm := by
    apply Path.ext
    funext t
    exact hH t
  have hf := SphereSixComplex.loopClass_eq_whiskered_of_freeHomotopy
    A.orderThreeLocalOffsetBaseCentralPath A.orderThreeCentralAffineZeroSectionTriplePath H ht
  have hE : E (Path.Homotopic.Quotient.mk A.orderThreeLocalOffsetBaseCentralPath) =
      Path.Homotopic.Quotient.mk A.orderThreeCentralAffineZeroSectionTriplePath := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    change _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm
      (pathLoopClass A.orderThreeCentralAffineZeroSectionTriplePath)
    rw [fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass]
    exact hf
  apply twicePuncturedFundamentalGroup_pow_injective _ 3 (by decide)
  change (FundamentalGroup.map f A.centralAffineBase
    (E (Path.Homotopic.Quotient.mk (A.ellipticThreeBoundaryDeckStraightCentralLoop
      A.ellipticThreeBoundaryDeckData.meridian)))) ^ 3 =
    (FundamentalGroup.map f A.centralAffineBase
      (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoOne)) ^ 3
  rw [← map_pow, ← map_pow, ← map_pow,
    ← A.orderThreeCentralAffineZeroSectionTriplePath_class, ← hE]
  dsimp only [E]
  rw [CoveringSpace.map_fundamentalGroupMulEquivOfPath,
    CoveringSpace.map_fundamentalGroupMulEquivOfPath]
  apply (FundamentalGroup.fundamentalGroupMulEquivOfPath (W.map f.continuous)).injective.eq_iff.mpr
  simp only [map_pow, FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  rw [A.orderThreeLocalOffsetBaseCentralPath_basePath_eq_filling]
  rw [← A.orderThreeBoundaryBaseHom_ofDeck,
    ← A.orderThreeBoundaryBaseHom_fillingRelation, A.orderThreeBoundaryBaseHom_ofDeck]

end SphereSixComplex.Geometry.AnalyticData
