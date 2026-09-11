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



public theorem ellipticThree_exists_relator_eq_of_regularLoop_eq
    (H : (let _ := A.ellipticThreeBoundaryAction
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
        A.orderThreeCentralExpectedRelator)) :
    (∃ β : Path A.centralAffineBase A.ellipticThreeOverlapCentralBase,
    A.ellipticThreeCanonicalRelatorInCentral =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β A.orderThreeCentralExpectedRelator) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  obtain ⟨β, hβ⟩ := H
  refine ⟨β, ?_⟩
  rw [A.ellipticThreeCanonicalRelatorInCentral_eq_regularLoopProjection]
  exact hβ



public theorem ellipticFour_exists_relator_eq_of_regularLoop_eq
    (H : (let _ := A.ellipticFourBoundaryAction
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
        A.orderFourCentralExpectedRelator)) :
    (∃ β : Path A.centralAffineBase A.ellipticFourOverlapCentralBase,
    A.ellipticFourCanonicalRelatorInCentral =
      FundamentalGroup.fundamentalGroupMulEquivOfPath β A.orderFourCentralExpectedRelator) := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  obtain ⟨β, hβ⟩ := H
  refine ⟨β, ?_⟩
  rw [A.ellipticFourCanonicalRelatorInCentral_eq_regularLoopProjection]
  exact hβ




end SphereSixComplex.Geometry.PaperAnalyticData

end

end
