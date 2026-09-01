module

public import SphereSixComplex.Topology.PaperActualEllipticRelatorChartIdentityProof
public import SphereSixComplex.Topology.PaperActualCuspCentralLoopRelation

/-!
# Free-loop reduction of the actual elliptic relators

A free homotopy need not preserve the chosen basepoint.  Its basepoint trace supplies exactly
the connector needed to compare the two fundamental-group classes.  Consequently the elliptic
normal-closure statements require no equality involving any preselected connector.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

/-- A free homotopy from the explicit order-three regular loop to a representative of the
expected affine relator supplies the required chart identity.  The connector is the reverse of
the moving-basepoint trace, rather than any independently selected path. -/
public theorem orderThreeActualEllipticRegularLoopChartIdentity_of_freeHomotopy
    (gamma : Path A.centralAffineBase A.centralAffineBase)
    (hgamma :
      Path.Homotopic.Quotient.mk gamma =
        A.orderThreeCentralExpectedRelator.toPath)
    (H : ContinuousMap.Homotopy
      ((A.orderThreeFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderThreeCollarRegularRepresentative_base_projects.symm
          A.orderThreeCollarRegularRepresentative_base_projects.symm).toContinuousMap
      gamma.toContinuousMap)
    (htrace :
      (H.evalAt 0).cast
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm).source.symm
          gamma.source.symm =
        (H.evalAt 1).cast
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm).target.symm
          gamma.target.symm) :
    A.OrderThreeActualEllipticRegularLoopChartIdentity := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let L :=
    (A.orderThreeFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderThreeCollarRegularRepresentative_base_projects.symm
        A.orderThreeCollarRegularRepresentative_base_projects.symm
  let w : Path A.orderThreeActualEllipticCentralBase A.centralAffineBase :=
    (H.evalAt 0).cast L.source.symm gamma.source.symm
  let hover := A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase
  refine ⟨w.symm.cast rfl hover.symm, ?_⟩
  have hfree := SphereSixComplex.loopClass_eq_whiskered_of_freeHomotopy
    L gamma H htrace
  have hat :
      Path.Homotopic.Quotient.mk L =
        FundamentalGroup.fundamentalGroupMulEquivOfPath w.symm
          A.orderThreeCentralExpectedRelator := by
    rw [hfree]
    simp only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm]
    rw [hgamma]
    unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
    simp only [CategoryTheory.Iso.conj_apply]
    change (Path.Homotopic.Quotient.mk w).trans
        (A.orderThreeCentralExpectedRelator.toPath.trans
          (Path.Homotopic.Quotient.mk w).symm) =
      (Path.Homotopic.Quotient.mk w.symm).symm.trans
        (A.orderThreeCentralExpectedRelator.toPath.trans
          (Path.Homotopic.Quotient.mk w.symm))
    simp only [← Path.Homotopic.Quotient.mk_symm]
    rw [Path.symm_symm]
  change fundamentalGroupElementOfBaseEq hover
      (Path.Homotopic.Quotient.mk L) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      (w.symm.cast rfl hover.symm) A.orderThreeCentralExpectedRelator
  rw [hat]
  exact (fundamentalGroupMulEquivOfPath_cast_right
    w.symm hover.symm A.orderThreeCentralExpectedRelator).symm

/-- Order-four analogue of the free-loop reduction. -/
public theorem orderFourActualEllipticRegularLoopChartIdentity_of_freeHomotopy
    (gamma : Path A.centralAffineBase A.centralAffineBase)
    (hgamma :
      Path.Homotopic.Quotient.mk gamma =
        A.orderFourCentralExpectedRelator.toPath)
    (H : ContinuousMap.Homotopy
      ((A.orderFourFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderFourCollarRegularRepresentative_base_projects.symm
          A.orderFourCollarRegularRepresentative_base_projects.symm).toContinuousMap
      gamma.toContinuousMap)
    (htrace :
      (H.evalAt 0).cast
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm).source.symm
          gamma.source.symm =
        (H.evalAt 1).cast
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm).target.symm
          gamma.target.symm) :
    A.OrderFourActualEllipticRegularLoopChartIdentity := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let L :=
    (A.orderFourFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm
  let w : Path A.orderFourActualEllipticCentralBase A.centralAffineBase :=
    (H.evalAt 0).cast L.source.symm gamma.source.symm
  let hover := A.orderFourActualEllipticCentralBase_eq_overlapCentralBase
  refine ⟨w.symm.cast rfl hover.symm, ?_⟩
  have hfree := SphereSixComplex.loopClass_eq_whiskered_of_freeHomotopy
    L gamma H htrace
  have hat :
      Path.Homotopic.Quotient.mk L =
        FundamentalGroup.fundamentalGroupMulEquivOfPath w.symm
          A.orderFourCentralExpectedRelator := by
    rw [hfree]
    simp only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm]
    rw [hgamma]
    unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
    simp only [CategoryTheory.Iso.conj_apply]
    change (Path.Homotopic.Quotient.mk w).trans
        (A.orderFourCentralExpectedRelator.toPath.trans
          (Path.Homotopic.Quotient.mk w).symm) =
      (Path.Homotopic.Quotient.mk w.symm).symm.trans
        (A.orderFourCentralExpectedRelator.toPath.trans
          (Path.Homotopic.Quotient.mk w.symm))
    simp only [← Path.Homotopic.Quotient.mk_symm]
    rw [Path.symm_symm]
  change fundamentalGroupElementOfBaseEq hover
      (Path.Homotopic.Quotient.mk L) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      (w.symm.cast rfl hover.symm) A.orderFourCentralExpectedRelator
  rw [hat]
  exact (fundamentalGroupMulEquivOfPath_cast_right
    w.symm hover.symm A.orderFourCentralExpectedRelator).symm

/-- Free homotopies of the two complete local filling loops give both normal-closure
memberships.  No relation between their moving-basepoint traces and the van Kampen connectors
is required. -/
public theorem actualEllipticRelatorNormalClosureResidual_of_regularLoopFreeHomotopies
    (gammaThree : Path A.centralAffineBase A.centralAffineBase)
    (hgammaThree :
      Path.Homotopic.Quotient.mk gammaThree =
        A.orderThreeCentralExpectedRelator.toPath)
    (HThree : ContinuousMap.Homotopy
      ((A.orderThreeFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderThreeCollarRegularRepresentative_base_projects.symm
          A.orderThreeCollarRegularRepresentative_base_projects.symm).toContinuousMap
      gammaThree.toContinuousMap)
    (htraceThree :
      (HThree.evalAt 0).cast
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm).source.symm
          gammaThree.source.symm =
        (HThree.evalAt 1).cast
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm).target.symm
          gammaThree.target.symm)
    (gammaFour : Path A.centralAffineBase A.centralAffineBase)
    (hgammaFour :
      Path.Homotopic.Quotient.mk gammaFour =
        A.orderFourCentralExpectedRelator.toPath)
    (HFour : ContinuousMap.Homotopy
      ((A.orderFourFillingRelationRegularLoop.map
        A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
          A.orderFourCollarRegularRepresentative_base_projects.symm
          A.orderFourCollarRegularRepresentative_base_projects.symm).toContinuousMap
      gammaFour.toContinuousMap)
    (htraceFour :
      (HFour.evalAt 0).cast
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm).source.symm
          gammaFour.source.symm =
        (HFour.evalAt 1).cast
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm).target.symm
          gammaFour.target.symm) :
    A.ActualEllipticRelatorNormalClosureResidual
      A.actualCuspCentralNaturality :=
  A.actualEllipticRelatorNormalClosureResidual_of_regularLoopChartIdentities
    (A.orderThreeActualEllipticRegularLoopChartIdentity_of_freeHomotopy
      gammaThree hgammaThree HThree htraceThree)
    (A.orderFourActualEllipticRegularLoopChartIdentity_of_freeHomotopy
      gammaFour hgammaFour HFour htraceFour)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
