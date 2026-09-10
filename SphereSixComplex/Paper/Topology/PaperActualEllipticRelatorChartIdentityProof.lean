module

public import SphereSixComplex.Paper.Topology.PaperEllipticCollarLoopClassProof

/-!
# Exact chart identities for the actual elliptic relators

The collar calculations already construct the complete filling-relation loops in the regular
family and identify their projections with the canonical physical relators.  Thus the remaining
local-to-global input is exactly that each projected regular loop represents the corresponding
classified affine relator, up to change of basepoint in the central family.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-- The exact order-three local-to-global chart identity, stated for the explicitly constructed
regular-family filling loop. -/
public def OrderThreeActualEllipticRegularLoopChartIdentity : Prop :=
  let _ := A.ellipticThreeBoundaryAction
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
        A.orderThreeCentralExpectedRelator

/-- The exact order-four local-to-global chart identity, stated for the explicitly constructed
regular-family filling loop. -/
public def OrderFourActualEllipticRegularLoopChartIdentity : Prop :=
  let _ := A.ellipticFourBoundaryAction
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
        A.orderFourCentralExpectedRelator

public theorem OrderThreeActualEllipticRegularLoopChartIdentity.toWholeFillingRelatorChartIdentity
    (H : A.OrderThreeActualEllipticRegularLoopChartIdentity) :
    A.OrderThreeWholeFillingRelatorChartIdentity := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  obtain ⟨β, hβ⟩ := H
  refine ⟨β, ?_⟩
  rw [A.ellipticThreeCanonicalRelatorInCentral_eq_regularLoopProjection]
  exact hβ

public theorem OrderThreeWholeFillingRelatorChartIdentity.toRegularLoopChartIdentity
    (H : A.OrderThreeWholeFillingRelatorChartIdentity) :
    A.OrderThreeActualEllipticRegularLoopChartIdentity := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  obtain ⟨β, hβ⟩ := H
  refine ⟨β, ?_⟩
  rw [← A.ellipticThreeCanonicalRelatorInCentral_eq_regularLoopProjection]
  exact hβ

public theorem ellipticThreeRegularLoopChartIdentity_iff_wholeFillingRelatorChartIdentity :
    A.OrderThreeActualEllipticRegularLoopChartIdentity ↔
      A.OrderThreeWholeFillingRelatorChartIdentity :=
  ⟨fun H ↦ H.toWholeFillingRelatorChartIdentity A,
    fun H ↦ H.toRegularLoopChartIdentity A⟩

public theorem OrderFourActualEllipticRegularLoopChartIdentity.toWholeFillingRelatorChartIdentity
    (H : A.OrderFourActualEllipticRegularLoopChartIdentity) :
    A.OrderFourWholeFillingRelatorChartIdentity := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  obtain ⟨β, hβ⟩ := H
  refine ⟨β, ?_⟩
  rw [A.ellipticFourCanonicalRelatorInCentral_eq_regularLoopProjection]
  exact hβ

public theorem OrderFourWholeFillingRelatorChartIdentity.toRegularLoopChartIdentity
    (H : A.OrderFourWholeFillingRelatorChartIdentity) :
    A.OrderFourActualEllipticRegularLoopChartIdentity := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  obtain ⟨β, hβ⟩ := H
  refine ⟨β, ?_⟩
  rw [← A.ellipticFourCanonicalRelatorInCentral_eq_regularLoopProjection]
  exact hβ

public theorem ellipticFourRegularLoopChartIdentity_iff_wholeFillingRelatorChartIdentity :
    A.OrderFourActualEllipticRegularLoopChartIdentity ↔
      A.OrderFourWholeFillingRelatorChartIdentity :=
  ⟨fun H ↦ H.toWholeFillingRelatorChartIdentity A,
    fun H ↦ H.toRegularLoopChartIdentity A⟩

public theorem ellipticRelatorMembership_of_regularLoopChartIdentities
    (H3 : A.OrderThreeActualEllipticRegularLoopChartIdentity)
    (H4 : A.OrderFourActualEllipticRegularLoopChartIdentity) :
    A.EllipticRelatorMembership A.cuspCentralNaturality :=
  A.ellipticRelatorMembership_of_wholeFillingRelatorChartIdentities
    (H3.toWholeFillingRelatorChartIdentity A)
    (H4.toWholeFillingRelatorChartIdentity A)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
