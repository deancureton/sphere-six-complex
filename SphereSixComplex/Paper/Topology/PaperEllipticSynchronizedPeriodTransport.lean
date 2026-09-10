module
public import SphereSixComplex.Paper.Topology.PaperEllipticActualStraightPeriod
public import SphereSixComplex.Paper.Topology.PaperOrderFourCentralBoundaryDeckEvaluation
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeFibreComparisonProof

@[expose] public section
noncomputable section
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.LatticeData
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology
variable (A : PaperAnalyticData)

public theorem orderFour_correctedPeriodTransportIdentity :
    A.OrderFourCorrectedPeriodTransportIdentity := by
  let _ := A.ellipticFourBoundaryAction
  let _ := regularFamilyDeckAction A.periods
  obtain ⟨H, hH⟩ := A.orderFourCentralBaseFactor_homotopy_globalZeroSectionQuadruple
  obtain ⟨g, hg, hmeridian⟩ := A.orderFourBaseComparisonTrace_enteringSheet H hH
  refine ⟨H, hH, ?_⟩
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let ex : (regularFamilyQuotientMap A.periods) ⁻¹' {A.ellipticFourCentralBase} :=
    ⟨A.orderFourCollarRegularRepresentativeMap A.ellipticFourBoundaryBase,
      A.orderFourCollarRegularBase_projects⟩
  let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.centralAffineBase} :=
    ⟨A.cuspRegularRepresentative,
      A.cuspRegularRepresentative_projects.trans A.centralAffineBase_eq_actualCuspCentralBase.symm⟩
  let W := A.orderFourCentralBaseComparisonTracePath H
  obtain ⟨Q, hQ⟩ := SphereSixComplex.IsCoveringMap.exists_path_lift_of_monodromy_eq
    hp.isCoveringMap W ex (hp.toPermFiber A.centralAffineBase g ey) hg
  let p₀ := A.ellipticFourStraightCoverPoint
  let p₁ := regularDeckMap A.periods g A.cuspRegularCoverPoint
  have hp₀ : regularFamilyCoverProjection A.periods p₀ = ex.val :=
    A.ellipticFourStraightCoverPoint_projects
  have hp₁ : regularFamilyCoverProjection A.periods p₁ =
      (hp.toPermFiber A.centralAffineBase g ey).val :=
    regularFamilyCoverProjection_regularDeckMap A.periods g A.cuspRegularCoverPoint
  let Q' : Path (regularFamilyCoverProjection A.periods p₀)
      (regularFamilyCoverProjection A.periods p₁) := Q.cast hp₀ hp₁
  let h₀ := (congrArg (regularFamilyQuotientMap A.periods) hp₀).trans ex.property
  let h₁ := (congrArg (regularFamilyQuotientMap A.periods) hp₁).trans
    (hp.toPermFiber A.centralAffineBase g ey).property
  have hQmap : (Q'.map (regularFamilyQuotientMap A.periods).continuous).cast
      h₀.symm h₁.symm = W := by
    apply Path.ext
    funext t
    exact congrArg (fun P : Path _ _ ↦ P t) hQ
  let L₀ := (regularFamilyPeriodLoop A.periods p₀ (-epsilon')).map
    (regularFamilyQuotientMap A.periods).continuous
  let L₁ := (regularFamilyPeriodLoop A.periods p₁ (-epsilon')).map
    (regularFamilyQuotientMap A.periods).continuous
  have hL₀ : L₀.cast h₀.symm h₀.symm = A.orderFourCentralActualBasedStraightFiberPath := by
    apply Path.ext
    funext t
    exact congrArg (fun f : C(unitInterval, A.CentralFamily) ↦ f t)
      A.orderFourMappedActualStraightPeriod_eq_actualBasedStraightFiber
  have hcoeff : rhoLambda g⁻¹ (-epsilon') =
      rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) (-epsilon') := by
    simp only [map_neg, A.orderFour_enteringSheet_inverse_transports_epsilon' g hmeridian]
  have hdeck := regularFamilyPeriodLoop_deck A.periods g A.cuspRegularCoverPoint
    (rhoLambda g⁻¹ (-epsilon'))
  have hcancel : rhoLambda g (rhoLambda g⁻¹ (-epsilon')) = -epsilon' := by simp
  rw [hcancel] at hdeck
  have hL₁ : L₁.cast h₁.symm h₁.symm =
      A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath := by
    apply Path.ext
    funext t
    have ht := congrArg (fun P : Path _ _ ↦ P t) hdeck
    change L₁ t = _ at ht
    change L₁ t = _
    rw [ht]
    change regularFamilyQuotientMap A.periods
        (regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint
          (rhoLambda g⁻¹ (-epsilon')) t) = _
    rw [hcoeff]
    rfl
  have htransport := regularFamilyPeriodLoop_transport_map_of_path A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    Q' (-epsilon') (regularFamilyQuotientMap A.periods)
  have hlocal : Path.Homotopic.Quotient.mk A.orderFourCentralActualBasedStraightFiberPath =
      whiskeredLoopClass W A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath := by
    rw [← hL₀, ← hL₁, ← hQmap]
    have h := congrArg (fun P ↦ Path.Homotopic.Quotient.cast P h₀.symm h₀.symm) htransport
    exact h
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  have hfinal : E (Path.Homotopic.Quotient.mk A.orderFourCentralActualBasedStraightFiberPath) =
      Path.Homotopic.Quotient.mk A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    change _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm
      (pathLoopClass A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath)
    rw [fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass]
    exact hlocal
  exact hfinal

public def orderThreeCentralTraceTransportedStraightPeriodPath
    (H : ContinuousMap.Homotopy A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap) :
    Path A.centralAffineBase A.centralAffineBase :=
  let w := A.orderThreeCentralBaseComparisonTracePath H
  w.symm.trans (A.orderThreeCentralActualBasedStraightFiberPath.trans w)

public def OrderThreeCorrectedPeriodTransportIdentity : Prop :=
  let _ := A.ellipticThreeBoundaryAction
  ∃ H : ContinuousMap.Homotopy A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap,
    (∀ s : unitInterval, H (s, 0) = H (s, 1)) ∧
    Path.Homotopic.Quotient.mk (A.orderThreeCentralTraceTransportedStraightPeriodPath H) =
      Path.Homotopic.Quotient.mk A.orderThreeCentralAffineCorrectedEpsilonPeriodPath

public theorem orderThree_correctedPeriodTransportIdentity :
    A.OrderThreeCorrectedPeriodTransportIdentity := by
  let _ := A.ellipticThreeBoundaryAction
  let _ := regularFamilyDeckAction A.periods
  obtain ⟨H, hH⟩ := A.orderThreeLocalOffsetBaseCentralPath_homotopy_globalZeroSectionTriple
  obtain ⟨g, hg, hmeridian⟩ := A.orderThreeBaseComparisonTrace_enteringSheet H hH
  refine ⟨H, hH, ?_⟩
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let ex : (regularFamilyQuotientMap A.periods) ⁻¹' {A.ellipticThreeCentralBase} :=
    ⟨A.orderThreeCollarRegularRepresentativeMap A.ellipticThreeBoundaryBase,
      A.orderThreeCollarRegularBase_projects⟩
  let ey : (regularFamilyQuotientMap A.periods) ⁻¹' {A.centralAffineBase} :=
    ⟨A.cuspRegularRepresentative,
      A.cuspRegularRepresentative_projects.trans A.centralAffineBase_eq_actualCuspCentralBase.symm⟩
  let W := A.orderThreeCentralBaseComparisonTracePath H
  obtain ⟨Q, hQ⟩ := SphereSixComplex.IsCoveringMap.exists_path_lift_of_monodromy_eq
    hp.isCoveringMap W ex (hp.toPermFiber A.centralAffineBase g ey) hg
  let p₀ := A.ellipticThreeStraightCoverPoint
  let p₁ := regularDeckMap A.periods g A.cuspRegularCoverPoint
  have hp₀ : regularFamilyCoverProjection A.periods p₀ = ex.val :=
    A.ellipticThreeStraightCoverPoint_projects
  have hp₁ : regularFamilyCoverProjection A.periods p₁ =
      (hp.toPermFiber A.centralAffineBase g ey).val :=
    regularFamilyCoverProjection_regularDeckMap A.periods g A.cuspRegularCoverPoint
  let Q' : Path (regularFamilyCoverProjection A.periods p₀)
      (regularFamilyCoverProjection A.periods p₁) := Q.cast hp₀ hp₁
  let h₀ := (congrArg (regularFamilyQuotientMap A.periods) hp₀).trans ex.property
  let h₁ := (congrArg (regularFamilyQuotientMap A.periods) hp₁).trans
    (hp.toPermFiber A.centralAffineBase g ey).property
  have hQmap : (Q'.map (regularFamilyQuotientMap A.periods).continuous).cast
      h₀.symm h₁.symm = W := by
    apply Path.ext
    funext t
    exact congrArg (fun P : Path _ _ ↦ P t) hQ
  let L₀ := (regularFamilyPeriodLoop A.periods p₀ epsilon).map
    (regularFamilyQuotientMap A.periods).continuous
  let L₁ := (regularFamilyPeriodLoop A.periods p₁ epsilon).map
    (regularFamilyQuotientMap A.periods).continuous
  have hL₀ : L₀.cast h₀.symm h₀.symm = A.orderThreeCentralActualBasedStraightFiberPath := by
    apply Path.ext
    funext t
    exact congrArg (fun f : C(unitInterval, A.CentralFamily) ↦ f t)
      A.orderThreeMappedActualStraightPeriod_eq_actualBasedStraightFiber
  have hcoeff : rhoLambda g⁻¹ epsilon =
      rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon := by
    simp only [A.orderThree_enteringSheet_inverse_transports_epsilon g hmeridian]
  have hdeck := regularFamilyPeriodLoop_deck A.periods g A.cuspRegularCoverPoint
    (rhoLambda g⁻¹ epsilon)
  have hcancel : rhoLambda g (rhoLambda g⁻¹ epsilon) = epsilon := by simp
  rw [hcancel] at hdeck
  have hL₁ : L₁.cast h₁.symm h₁.symm =
      A.orderThreeCentralAffineCorrectedEpsilonPeriodPath := by
    apply Path.ext
    funext t
    have ht := congrArg (fun P : Path _ _ ↦ P t) hdeck
    change L₁ t = _ at ht
    change L₁ t = _
    rw [ht]
    change regularFamilyQuotientMap A.periods
        (regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint
          (rhoLambda g⁻¹ epsilon) t) = _
    rw [hcoeff]
    rfl
  have htransport := regularFamilyPeriodLoop_transport_map_of_path A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    Q' epsilon (regularFamilyQuotientMap A.periods)
  have hlocal : Path.Homotopic.Quotient.mk A.orderThreeCentralActualBasedStraightFiberPath =
      whiskeredLoopClass W A.orderThreeCentralAffineCorrectedEpsilonPeriodPath := by
    rw [← hL₀, ← hL₁, ← hQmap]
    have h := congrArg (fun P ↦ Path.Homotopic.Quotient.cast P h₀.symm h₀.symm) htransport
    exact h
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  have hfinal : E (Path.Homotopic.Quotient.mk A.orderThreeCentralActualBasedStraightFiberPath) =
      Path.Homotopic.Quotient.mk A.orderThreeCentralAffineCorrectedEpsilonPeriodPath := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    change _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm
      (pathLoopClass A.orderThreeCentralAffineCorrectedEpsilonPeriodPath)
    rw [fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass]
    exact hlocal
  exact hfinal

public theorem OrderThreeCorrectedPeriodTransportIdentity.toLocalGlobalFactorPointSetComparison
    (h : A.OrderThreeCorrectedPeriodTransportIdentity) :
    A.OrderThreeLocalGlobalFactorPointSetComparison := by
  let _ := A.ellipticThreeBoundaryAction
  rcases h with ⟨Hbase, hbaseTrace, hperiod⟩
  rcases A.orderThreeLocalOffsetFiberCentralPath_homotopic_actualBasedStraight with ⟨HlocalPath⟩
  let p := A.orderThreeCentralActualBasedStraightFiberPath
  let w := A.orderThreeCentralBaseComparisonTracePath Hbase
  let transported := A.orderThreeCentralTraceTransportedStraightPeriodPath Hbase
  have hpad : Nonempty (Path.Homotopy p
      ((Path.refl A.ellipticThreeCentralBase).trans
        (p.trans (Path.refl A.ellipticThreeCentralBase)))) := by
    apply Path.Homotopic.Quotient.exact
    simp
  rcases hpad with ⟨HpadPath⟩
  have hglobal : Path.Homotopic transported
      A.orderThreeCentralAffineCorrectedEpsilonPeriodPath :=
    Quotient.exact hperiod
  rcases hglobal with ⟨HglobalPath⟩
  let F₀ := pathHomotopyToFreeHomotopy HlocalPath
  let F₁ := pathHomotopyToFreeHomotopy HpadPath
  let F₂ := freeLoopWhiskerPrefixHomotopy p w
  let F₃ := pathHomotopyToFreeHomotopy HglobalPath
  let G₀ := ContinuousMap.Homotopy.refl A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
  let G₁ := ContinuousMap.Homotopy.refl A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
  let G₂ := Hbase
  let G₃ := ContinuousMap.Homotopy.refl
    A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap
  have h₀join (s : unitInterval) : F₀ (s, 1) = G₀ (s, 0) := by
    change HlocalPath (s, 1) = A.orderThreeLocalOffsetBaseCentralPath 0
    exact (HlocalPath.target s).trans A.orderThreeLocalOffsetBaseCentralPath.source.symm
  have h₀trace (s : unitInterval) : F₀ (s, 0) = G₀ (s, 1) := by
    change HlocalPath (s, 0) = A.orderThreeLocalOffsetBaseCentralPath 1
    exact (HlocalPath.source s).trans A.orderThreeLocalOffsetBaseCentralPath.target.symm
  have h₁join (s : unitInterval) : F₁ (s, 1) = G₁ (s, 0) := by
    change HpadPath (s, 1) = A.orderThreeLocalOffsetBaseCentralPath 0
    exact (HpadPath.target s).trans A.orderThreeLocalOffsetBaseCentralPath.source.symm
  have h₁trace (s : unitInterval) : F₁ (s, 0) = G₁ (s, 1) := by
    change HpadPath (s, 0) = A.orderThreeLocalOffsetBaseCentralPath 1
    exact (HpadPath.source s).trans A.orderThreeLocalOffsetBaseCentralPath.target.symm
  have h₂left (s : unitInterval) : F₂ (s, 0) = Hbase (s, 0) := by
    change freeLoopWhiskerPrefixHomotopy p w (s, 0) = Hbase (s, 0)
    change ((pathInitialSegment w s).symm.trans
      (p.trans (pathInitialSegment w s))) 0 = Hbase (s, 0)
    exact ((pathInitialSegment w s).symm.trans
      (p.trans (pathInitialSegment w s))).source
  have h₂join (s : unitInterval) : F₂ (s, 1) = G₂ (s, 0) := by
    change freeLoopWhiskerPrefixHomotopy p w (s, 1) = Hbase (s, 0)
    change ((pathInitialSegment w s).symm.trans
      (p.trans (pathInitialSegment w s))) 1 = Hbase (s, 0)
    exact ((pathInitialSegment w s).symm.trans
      (p.trans (pathInitialSegment w s))).target
  have h₂trace (s : unitInterval) : F₂ (s, 0) = G₂ (s, 1) :=
    (h₂left s).trans (hbaseTrace s)
  have h₃join (s : unitInterval) : F₃ (s, 1) = G₃ (s, 0) := by
    change HglobalPath (s, 1) = A.orderThreeCentralAffineZeroSectionTriplePath 0
    exact (HglobalPath.target s).trans
      A.orderThreeCentralAffineZeroSectionTriplePath.source.symm
  have h₃trace (s : unitInterval) : F₃ (s, 0) = G₃ (s, 1) := by
    change HglobalPath (s, 0) = A.orderThreeCentralAffineZeroSectionTriplePath 1
    exact (HglobalPath.source s).trans
      A.orderThreeCentralAffineZeroSectionTriplePath.target.symm
  let F := ((F₀.trans F₁).trans F₂).trans F₃
  let G := ((G₀.trans G₁).trans G₂).trans G₃
  refine ⟨F, G, ?_, ?_⟩
  · intro s
    exact freeLoopHomotopyTrans_pointwise_eq
      ((F₀.trans F₁).trans F₂) F₃ ((G₀.trans G₁).trans G₂) G₃ 1 0
      (fun r ↦ freeLoopHomotopyTrans_pointwise_eq
        (F₀.trans F₁) F₂ (G₀.trans G₁) G₂ 1 0
        (fun q ↦ freeLoopHomotopyTrans_pointwise_eq F₀ F₁ G₀ G₁ 1 0
          h₀join h₁join q)
        h₂join r)
      h₃join s
  · intro s
    exact freeLoopHomotopyTrans_pointwise_eq
      ((F₀.trans F₁).trans F₂) F₃ ((G₀.trans G₁).trans G₂) G₃ 0 1
      (fun r ↦ freeLoopHomotopyTrans_pointwise_eq
        (F₀.trans F₁) F₂ (G₀.trans G₁) G₂ 0 1
        (fun q ↦ freeLoopHomotopyTrans_pointwise_eq F₀ F₁ G₀ G₁ 0 1
          h₀trace h₁trace q)
        h₂trace r)
      h₃trace s

public theorem OrderThreeLocalGlobalFactorPointSetComparison.toRegularLoopChartIdentity
    (h : A.OrderThreeLocalGlobalFactorPointSetComparison) :
    A.OrderThreeActualEllipticRegularLoopChartIdentity := by
  let _ := A.ellipticThreeBoundaryAction
  rcases A.orderThreeProjectedRegularLoop_freeHomotopy_localFiberThenBase_trace with
    ⟨Hsplit, hsplitTrace⟩
  rcases h.assemble A with ⟨Hglobal, hglobalTrace⟩
  let H := Hsplit.trans Hglobal
  apply A.ellipticThreeRegularLoopChartIdentity_of_freeHomotopy
    A.orderThreeCentralAffineCorrectedGeometricRelatorPath
    A.orderThreeCentralAffineCorrectedGeometricRelatorPath_class H
  apply Path.ext
  funext s
  apply freeLoopHomotopyTrans_trace
  · intro r
    exact congrArg (fun p : Path _ _ ↦ p r) hsplitTrace
  · exact hglobalTrace

public theorem ellipticRelatorMembership_proved :
    Nonempty (A.EllipticRelatorMembership A.cuspCentralNaturality) := by
  constructor
  constructor
  · exact (A.orderThree_correctedPeriodTransportIdentity.toLocalGlobalFactorPointSetComparison A
      |>.toRegularLoopChartIdentity A |>.toWholeFillingRelatorChartIdentity A
      |>.relator_mem_normalClosure A)
  · exact A.orderFour_correctedPeriodTransportIdentity.relator_mem_normalClosure A

end SphereSixComplex.Geometry.PaperAnalyticData
