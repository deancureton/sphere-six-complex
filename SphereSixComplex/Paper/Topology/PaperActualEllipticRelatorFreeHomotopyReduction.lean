module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorChartIdentityProof

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
public theorem ellipticThreeRegularLoopChartIdentity_of_freeHomotopy
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
    (let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  ∃ β : Path A.centralAffineBase A.ellipticThreeOverlapCentralBase,
    fundamentalGroupElementOfBaseEq
        A.ellipticThreeCentralBase_eq_overlapCentralBase
        (Path.Homotopic.Quotient.mk
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm)) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        A.orderThreeCentralExpectedRelator) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let L :=
    (A.orderThreeFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderThreeCollarRegularRepresentative_base_projects.symm
        A.orderThreeCollarRegularRepresentative_base_projects.symm
  let w : Path A.ellipticThreeCentralBase A.centralAffineBase :=
    (H.evalAt 0).cast L.source.symm gamma.source.symm
  let hover := A.ellipticThreeCentralBase_eq_overlapCentralBase
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
public theorem ellipticFourRegularLoopChartIdentity_of_freeHomotopy
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
    (let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  ∃ β : Path A.centralAffineBase A.ellipticFourOverlapCentralBase,
    fundamentalGroupElementOfBaseEq
        A.ellipticFourCentralBase_eq_overlapCentralBase
        (Path.Homotopic.Quotient.mk
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm)) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        A.orderFourCentralExpectedRelator) := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let L :=
    (A.orderFourFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm
  let w : Path A.ellipticFourCentralBase A.centralAffineBase :=
    (H.evalAt 0).cast L.source.symm gamma.source.symm
  let hover := A.ellipticFourCentralBase_eq_overlapCentralBase
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
public theorem ellipticRelatorMembership_of_regularLoopFreeHomotopies
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
    A.EllipticRelatorMembership
      A.cuspCentralNaturality :=
  A.ellipticRelatorMembership_of_regularLoopChartIdentities
    (A.ellipticThreeRegularLoopChartIdentity_of_freeHomotopy
      gammaThree hgammaThree HThree htraceThree)
    (A.ellipticFourRegularLoopChartIdentity_of_freeHomotopy
      gammaFour hgammaFour HFour htraceFour)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
