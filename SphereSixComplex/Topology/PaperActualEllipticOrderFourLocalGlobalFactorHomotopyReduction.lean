module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourFibreComparisonProof
public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeLocalGlobalFactorHomotopyReduction
public import SphereSixComplex.Topology.PaperActualEllipticRelatorFreeHomotopyReduction

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology

/-- Vertical composition preserves any pointwise equality between two synchronized homotopies. -/
public theorem freeLoopHomotopyTrans_pointwise_eq
    {X : Type*} [TopologicalSpace X]
    {f₀ f₁ f₂ g₀ g₁ g₂ : C(unitInterval, X)}
    (F₀ : ContinuousMap.Homotopy f₀ f₁)
    (F₁ : ContinuousMap.Homotopy f₁ f₂)
    (G₀ : ContinuousMap.Homotopy g₀ g₁)
    (G₁ : ContinuousMap.Homotopy g₁ g₂)
    (x y : unitInterval)
    (h₀ : ∀ s : unitInterval, F₀ (s, x) = G₀ (s, y))
    (h₁ : ∀ s : unitInterval, F₁ (s, x) = G₁ (s, y))
    (s : unitInterval) :
    F₀.trans F₁ (s, x) = G₀.trans G₁ (s, y) := by
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact h₀ _
  · exact h₁ _

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

public theorem orderFourActualEllipticCentralBase_eq_offsetGaugeRealization :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourActualEllipticCentralBase =
      A.orderFourPuncturedProductCentralRealizationMap
        (A.orderFourCayleyPuncturedBasepoint,
          A.orderFourFillingRelationPrincipalGaugeLoop 0 +
            Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let x := A.orderFourCayleyPuncturedBasepoint
  let y := A.orderFourFillingRelationPrincipalGaugeLoop 0 +
    Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2
  have hregular : A.orderFourCollarRegularRepresentativeMap
      A.orderFourActualEllipticBoundaryBase =
        A.orderFourPuncturedProductRegularRealizationMap (x, y) := by
    exact A.orderFourFillingRelationRegularLoop.source.symm |>.trans
      ((A.orderFourRegularLoop_eq_puncturedProductRealization 0).symm.trans
        (congrArg A.orderFourPuncturedProductRegularRealizationMap
          (Prod.ext A.orderFourFillingRelationCayleyPuncturedLoop.source
            A.orderFourPrincipalGaugeWithOffsetPath.source)))
  exact A.orderFourCollarRegularRepresentative_base_projects.symm.trans
    (congrArg A.centralQuotientProjection hregular)

/-- The classified straight period, translated by the collar offset so that it remains based
at the actual elliptic point. -/
public noncomputable def orderFourCentralActualBasedStraightFiberPath :
    letI := A.orderFourActualEllipticBoundaryAction
    Path A.orderFourActualEllipticCentralBase A.orderFourActualEllipticCentralBase := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let x := A.orderFourCayleyPuncturedBasepoint
  let offset : A.orderFourTorus := Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2
  let g : C(A.orderFourTorus, A.CentralFamily) :=
    { toFun := fun q ↦ A.orderFourPuncturedProductCentralRealizationMap (x, q + offset)
      continuous_toFun := A.orderFourPuncturedProductCentralRealizationMap.continuous.comp
        (continuous_const.prodMk (continuous_id.add continuous_const)) }
  let qbase := torusProjection
    (SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo).1
    (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
  have hqbase : qbase = A.orderFourFillingRelationPrincipalGaugeLoop 0 := by
    rfl
  have hbase : A.orderFourActualEllipticCentralBase =
      g qbase :=
    (orderFourActualEllipticCentralBase_eq_offsetGaugeRealization A).trans
      (congrArg g hqbase).symm
  exact (A.orderFourPrincipalGaugeStraightLoop.map g.continuous).cast hbase hbase

/-- Straightening can be performed after translating by the fixed collar offset, hence with
the actual elliptic basepoint fixed throughout. -/
public theorem orderFourCentralFiberFactor_homotopic_actualBasedStraight :
    letI := A.orderFourActualEllipticBoundaryAction
    Nonempty (Path.Homotopy A.orderFourCentralFiberFactor
      A.orderFourCentralActualBasedStraightFiberPath) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  have hclass := A.orderFourFillingRelationPrincipalGaugeLoop_class_eq_straight
  change Path.Homotopic.Quotient.mk A.orderFourFillingRelationPrincipalGaugeLoop =
    Path.Homotopic.Quotient.mk A.orderFourPrincipalGaugeStraightLoop at hclass
  rcases (Quotient.exact hclass : Path.Homotopic
    A.orderFourFillingRelationPrincipalGaugeLoop
      A.orderFourPrincipalGaugeStraightLoop) with ⟨Htorus⟩
  let x := A.orderFourCayleyPuncturedBasepoint
  let offset : A.orderFourTorus := Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2
  let g : C(A.orderFourTorus, A.CentralFamily) :=
    { toFun := fun q ↦ A.orderFourPuncturedProductCentralRealizationMap (x, q + offset)
      continuous_toFun := A.orderFourPuncturedProductCentralRealizationMap.continuous.comp
        (continuous_const.prodMk (continuous_id.add continuous_const)) }
  have hbase : A.orderFourActualEllipticCentralBase =
      g (A.orderFourFillingRelationPrincipalGaugeLoop 0) :=
    orderFourActualEllipticCentralBase_eq_offsetGaugeRealization A
  let Hmapped := (Htorus.map g).pathCast hbase hbase
  have hsource :
      (A.orderFourFillingRelationPrincipalGaugeLoop.map g.continuous).cast hbase hbase =
        A.orderFourCentralFiberFactor := by
    apply Path.ext
    funext t
    rfl
  have htarget :
      (A.orderFourPrincipalGaugeStraightLoop.map g.continuous).cast hbase hbase =
        A.orderFourCentralActualBasedStraightFiberPath := by
    apply Path.ext
    funext t
    rfl
  exact ⟨Hmapped.cast hsource htarget⟩

/-- The literal cusp period carrying the corrected negative-epsilon-prime label. -/
public noncomputable def orderFourActualCuspCorrectedNegEpsilonPrimePeriodPath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.actualCuspCentralPeriodLoop
    (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) (-epsilon'))

public theorem orderFourActualCuspCorrectedNegEpsilonPrimePeriodPath_class :
    Path.Homotopic.Quotient.mk A.orderFourActualCuspCorrectedNegEpsilonPrimePeriodPath =
      Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon')) := by
  unfold orderFourActualCuspCorrectedNegEpsilonPrimePeriodPath
    correctedActualCuspCentralTranslation
  rw [← A.actualCuspCentralTranslation_eq_periodLoop]
  rfl

/-- The corrected order-four period displayed at the final affine basepoint. -/
public noncomputable def orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.orderFourActualCuspCorrectedNegEpsilonPrimePeriodPath.cast
    A.centralAffineBase_eq_actualCuspCentralBase
    A.centralAffineBase_eq_actualCuspCentralBase

public theorem orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath_class :
    Path.Homotopic.Quotient.mk
        A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath =
      Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon')) := by
  unfold orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath
  rw [Path.Homotopic.Quotient.mk_cast]
  rw [A.orderFourActualCuspCorrectedNegEpsilonPrimePeriodPath_class]
  rw [A.centralAffineCorePiOneData_translation]
  unfold actualCuspToCentralAffineBaseEquiv
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]

/-- A concrete corrected representative of the complete order-four relator at the cusp. -/
public noncomputable def orderFourActualCuspCorrectedGeometricRelatorPath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.orderFourActualCuspCorrectedNegEpsilonPrimePeriodPath.trans
    A.orderFourActualCuspZeroSectionQuadruplePath

public theorem orderFourActualCuspCorrectedGeometricRelatorPath_class :
    A.actualCuspToCentralAffineBaseEquiv
        (Path.Homotopic.Quotient.mk A.orderFourActualCuspCorrectedGeometricRelatorPath) =
      A.orderFourCentralExpectedRelator := by
  rw [orderFourActualCuspCorrectedGeometricRelatorPath,
    Path.Homotopic.Quotient.mk_trans,
    A.orderFourActualCuspCorrectedNegEpsilonPrimePeriodPath_class,
    A.orderFourActualCuspZeroSectionQuadruplePath_class]
  change A.actualCuspToCentralAffineBaseEquiv
      (A.geometricCentralRhoTwo ^ 4 *
        Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon'))) = _
  unfold orderFourCentralExpectedRelator
  rw [map_mul, map_pow, ← A.centralAffineCorePiOneData_rhoTwo]
  have ht := A.centralAffineCorePiOneData_translation epsilon'
  congr 1
  calc
    A.actualCuspToCentralAffineBaseEquiv
          (Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon'))) =
        (A.actualCuspToCentralAffineBaseEquiv
          (Additive.toMul (A.correctedActualCuspCentralTranslation epsilon')))⁻¹ := by
            rw [map_neg, toMul_neg, map_inv]
    _ = (Additive.toMul
          (A.centralAffineCorePiOneData.translation epsilon'))⁻¹ :=
      congrArg Inv.inv ht |>.symm

/-- The corrected order-four relator displayed at the final affine basepoint. -/
public noncomputable def orderFourCentralAffineCorrectedGeometricRelatorPath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.orderFourActualCuspCorrectedGeometricRelatorPath.cast
    A.centralAffineBase_eq_actualCuspCentralBase
    A.centralAffineBase_eq_actualCuspCentralBase

public theorem orderFourCentralAffineCorrectedGeometricRelatorPath_eq_trans :
    A.orderFourCentralAffineCorrectedGeometricRelatorPath =
      A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath.trans
        A.orderFourCentralAffineZeroSectionQuadruplePath := by
  unfold orderFourCentralAffineCorrectedGeometricRelatorPath
    orderFourActualCuspCorrectedGeometricRelatorPath
    orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath
    orderFourCentralAffineZeroSectionQuadruplePath
  rw [Path.cast_trans]

public theorem orderFourCentralAffineCorrectedGeometricRelatorPath_class :
    Path.Homotopic.Quotient.mk A.orderFourCentralAffineCorrectedGeometricRelatorPath =
      A.orderFourCentralExpectedRelator := by
  unfold orderFourCentralAffineCorrectedGeometricRelatorPath
  rw [Path.Homotopic.Quotient.mk_cast]
  rw [← A.orderFourActualCuspCorrectedGeometricRelatorPath_class]
  unfold actualCuspToCentralAffineBaseEquiv
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]

/-- The path traced by the source endpoint of the completed base-factor homotopy. -/
public def orderFourCentralBaseComparisonTracePath
    (Hbase : ContinuousMap.Homotopy
      A.orderFourCentralBaseFactor.toContinuousMap
      A.orderFourCentralAffineZeroSectionQuadruplePath.toContinuousMap) :
    Path A.orderFourActualEllipticCentralBase A.centralAffineBase :=
  (Hbase.evalAt 0).cast A.orderFourCentralBaseFactor.source.symm
    A.orderFourCentralAffineZeroSectionQuadruplePath.source.symm

/-- Transport the actual-based straight period along the base comparison's own trace. -/
public def orderFourCentralTraceTransportedStraightPeriodPath
    (Hbase : ContinuousMap.Homotopy
      A.orderFourCentralBaseFactor.toContinuousMap
      A.orderFourCentralAffineZeroSectionQuadruplePath.toContinuousMap) :
    Path A.centralAffineBase A.centralAffineBase :=
  let w := A.orderFourCentralBaseComparisonTracePath Hbase
  w.symm.trans (A.orderFourCentralActualBasedStraightFiberPath.trans w)

/-- The one remaining geometric identity: transport of the classified local straight period
along the already constructed base trace has the corrected global period class. -/
public def OrderFourCorrectedPeriodTransportIdentity : Prop :=
  let _ := A.orderFourActualEllipticBoundaryAction
  ∃ Hbase : ContinuousMap.Homotopy
      A.orderFourCentralBaseFactor.toContinuousMap
      A.orderFourCentralAffineZeroSectionQuadruplePath.toContinuousMap,
    (∀ s : unitInterval, Hbase (s, 0) = Hbase (s, 1)) ∧
      Path.Homotopic.Quotient.mk
          (A.orderFourCentralTraceTransportedStraightPeriodPath Hbase) =
        Path.Homotopic.Quotient.mk
          A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath

/-- The remaining point-set requirement is a global fibre comparison synchronized with the
already constructed base comparison. -/
public def OrderFourLocalGlobalFactorPointSetComparison : Prop :=
  let _ := A.orderFourActualEllipticBoundaryAction
  ∃ Hfiber : ContinuousMap.Homotopy
      A.orderFourCentralFiberFactor.toContinuousMap
      A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath.toContinuousMap,
    ∃ Hbase : ContinuousMap.Homotopy
      A.orderFourCentralBaseFactor.toContinuousMap
      A.orderFourCentralAffineZeroSectionQuadruplePath.toContinuousMap,
      (∀ s : unitInterval, Hfiber (s, 1) = Hbase (s, 0)) ∧
      (∀ s : unitInterval, Hfiber (s, 0) = Hbase (s, 1))

/-- The single transported-period class identity produces synchronized factor homotopies. -/
public theorem OrderFourCorrectedPeriodTransportIdentity.toLocalGlobalFactorPointSetComparison
    (h : A.OrderFourCorrectedPeriodTransportIdentity) :
    A.OrderFourLocalGlobalFactorPointSetComparison := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rcases h with ⟨Hbase, hbaseTrace, hperiod⟩
  rcases A.orderFourCentralFiberFactor_homotopic_actualBasedStraight with ⟨HlocalPath⟩
  let p := A.orderFourCentralActualBasedStraightFiberPath
  let w := A.orderFourCentralBaseComparisonTracePath Hbase
  let transported := A.orderFourCentralTraceTransportedStraightPeriodPath Hbase
  have hpad : Nonempty (Path.Homotopy p
      ((Path.refl A.orderFourActualEllipticCentralBase).trans
        (p.trans (Path.refl A.orderFourActualEllipticCentralBase)))) := by
    apply Path.Homotopic.Quotient.exact
    simp
  rcases hpad with ⟨HpadPath⟩
  have hglobal : Path.Homotopic transported
      A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath :=
    Quotient.exact hperiod
  rcases hglobal with ⟨HglobalPath⟩
  let F₀ := pathHomotopyToFreeHomotopy HlocalPath
  let F₁ := pathHomotopyToFreeHomotopy HpadPath
  let F₂ := freeLoopWhiskerPrefixHomotopy p w
  let F₃ := pathHomotopyToFreeHomotopy HglobalPath
  let G₀ := ContinuousMap.Homotopy.refl A.orderFourCentralBaseFactor.toContinuousMap
  let G₁ := ContinuousMap.Homotopy.refl A.orderFourCentralBaseFactor.toContinuousMap
  let G₂ := Hbase
  let G₃ := ContinuousMap.Homotopy.refl
    A.orderFourCentralAffineZeroSectionQuadruplePath.toContinuousMap
  have h₀join (s : unitInterval) : F₀ (s, 1) = G₀ (s, 0) := by
    change HlocalPath (s, 1) = A.orderFourCentralBaseFactor 0
    exact (HlocalPath.target s).trans A.orderFourCentralBaseFactor.source.symm
  have h₀trace (s : unitInterval) : F₀ (s, 0) = G₀ (s, 1) := by
    change HlocalPath (s, 0) = A.orderFourCentralBaseFactor 1
    exact (HlocalPath.source s).trans A.orderFourCentralBaseFactor.target.symm
  have h₁join (s : unitInterval) : F₁ (s, 1) = G₁ (s, 0) := by
    change HpadPath (s, 1) = A.orderFourCentralBaseFactor 0
    exact (HpadPath.target s).trans A.orderFourCentralBaseFactor.source.symm
  have h₁trace (s : unitInterval) : F₁ (s, 0) = G₁ (s, 1) := by
    change HpadPath (s, 0) = A.orderFourCentralBaseFactor 1
    exact (HpadPath.source s).trans A.orderFourCentralBaseFactor.target.symm
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
    change HglobalPath (s, 1) = A.orderFourCentralAffineZeroSectionQuadruplePath 0
    exact (HglobalPath.target s).trans
      A.orderFourCentralAffineZeroSectionQuadruplePath.source.symm
  have h₃trace (s : unitInterval) : F₃ (s, 0) = G₃ (s, 1) := by
    change HglobalPath (s, 0) = A.orderFourCentralAffineZeroSectionQuadruplePath 1
    exact (HglobalPath.source s).trans
      A.orderFourCentralAffineZeroSectionQuadruplePath.target.symm
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

public theorem OrderFourLocalGlobalFactorPointSetComparison.assemble
    (h : A.OrderFourLocalGlobalFactorPointSetComparison) :
    letI := A.orderFourActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy
        A.orderFourCentralFiberThenBaseLoop.toContinuousMap
        A.orderFourCentralAffineCorrectedGeometricRelatorPath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rcases h with ⟨Hfiber, Hbase, hjoin, htrace⟩
  let Hfactors := freeLoopHomotopyHcomp Hfiber Hbase hjoin
  have hsource :
      (A.orderFourCentralFiberFactor.trans
        A.orderFourCentralBaseFactor).toContinuousMap =
      A.orderFourCentralFiberThenBaseLoop.toContinuousMap :=
    congrArg Path.toContinuousMap A.orderFourCentralFiberThenBaseLoop_eq_factors.symm
  have htarget :
      (A.orderFourCentralAffineCorrectedNegEpsilonPrimePeriodPath.trans
        A.orderFourCentralAffineZeroSectionQuadruplePath).toContinuousMap =
      A.orderFourCentralAffineCorrectedGeometricRelatorPath.toContinuousMap :=
    congrArg Path.toContinuousMap
      A.orderFourCentralAffineCorrectedGeometricRelatorPath_eq_trans.symm
  let H := Hfactors.cast hsource htarget
  refine ⟨H, fun s ↦ ?_⟩
  change Hfactors (s, 0) = Hfactors (s, 1)
  exact freeLoopHomotopyHcomp_trace Hfiber Hbase hjoin htrace s

/-- Synchronized factor homotopies supply the order-four chart identity required by the
normal-closure reduction. -/
public theorem OrderFourLocalGlobalFactorPointSetComparison.toRegularLoopChartIdentity
    (h : A.OrderFourLocalGlobalFactorPointSetComparison) :
    A.OrderFourActualEllipticRegularLoopChartIdentity := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rcases A.orderFourProjectedRegularLoop_freeHomotopy_fiberThenBase_with_trace with
    ⟨Hsplit, hsplitTrace⟩
  rcases h.assemble A with ⟨Hglobal, hglobalTrace⟩
  let H := Hsplit.trans Hglobal
  apply A.orderFourActualEllipticRegularLoopChartIdentity_of_freeHomotopy
    A.orderFourCentralAffineCorrectedGeometricRelatorPath
    A.orderFourCentralAffineCorrectedGeometricRelatorPath_class H
  apply Path.ext
  funext s
  apply freeLoopHomotopyTrans_trace
  · intro r
    exact congrArg (fun p : Path _ _ ↦ p r) hsplitTrace
  · exact hglobalTrace

/-- The synchronized factor comparison supplies exactly the order-four field of the final
normal-closure residual. -/
public theorem OrderFourLocalGlobalFactorPointSetComparison.relator_mem_normalClosure
    (h : A.OrderFourLocalGlobalFactorPointSetComparison) :
    (A.coreDataOf A.actualCuspCentralNaturality).rhoTwo ^ 4 *
        (Additive.toMul
          ((A.coreDataOf A.actualCuspCentralNaturality).translation epsilon'))⁻¹ ∈
      Subgroup.normalClosure
        {A.actualEllipticFourOverlapToCore
          A.orderFourActualEllipticCanonicalRelator} := by
  exact (h.toRegularLoopChartIdentity A).toWholeFillingRelatorChartIdentity A
    |>.relator_mem_normalClosure A

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
