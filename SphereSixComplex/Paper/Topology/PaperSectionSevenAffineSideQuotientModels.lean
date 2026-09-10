module

public import SphereSixComplex.Prerequisites.Topology.EquivariantRadialDomainDescent
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineSideHomotopyEquivalence

/-!
# Monodromy-preserving quotient models for the affine sides

The punctured affine regions in Section 7 carry torus monodromy.  Accordingly, the overlap and
central region are modeled here as diagonal orbit quotients, not as global products.  Equivariant
radial normalization on the lifted base proves the overlap equivalence, and Dold's theorem then
proves the filling-to-side equivalence.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry.EquivariantQuotientHomeomorph OpenUnionHomotopy

/-- The underlying set inclusion from a punctured disc to a containing left half-plane. -/
public theorem puncturedComplexDisc_subset_leftHalfPlane {r c : ℝ} (hrc : r ≤ c) :
    puncturedComplexDisc r ⊆ puncturedComplexLeftHalfPlane c :=
  fun z hz ↦ ⟨hz.1, (Complex.re_le_norm z).trans_lt (hz.2.trans_le hrc)⟩

universe u v

namespace Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

/-- Honest quotient-bundle coordinates for the order-three overlap and central region.  The
actions on the lifted radial domains and on the fibre remain explicit, so the quotient retains
all finite monodromy. -/
public structure AffineOrderThreeSideQuotientInput
    (G : Type u) [Group G] (fiber : Type v) [TopologicalSpace fiber] where
  normalizationRadius : ℝ
  affineDiscRadius : ℝ
  normalizationRadius_pos : 0 < normalizationRadius
  normalizationRadius_lt_disc : normalizationRadius < affineDiscRadius
  affineDiscRadius_le_halfPlane : affineDiscRadius ≤ 2 / 3
  radialData : EquivariantRadialDomainInclusionData G
    (puncturedComplexDisc_radial normalizationRadius_pos normalizationRadius_lt_disc)
    (puncturedComplexLeftHalfPlane_radial normalizationRadius_pos
      (normalizationRadius_lt_disc.trans_le affineDiscRadius_le_halfPlane))
    (puncturedComplexDisc_subset_leftHalfPlane affineDiscRadius_le_halfPlane)
  fiberAction : MulAction G fiber
  smallAction_continuous :
    letI := radialData.smallAction
    ContinuousConstSMul G (puncturedComplexDisc affineDiscRadius)
  bigAction_continuous :
    letI := radialData.bigAction
    ContinuousConstSMul G (puncturedComplexLeftHalfPlane (2 / 3))
  fiberAction_continuous :
    letI := fiberAction
    ContinuousConstSMul G fiber
  overlapModel :
    ↥(A.orderThreeFillingImage ∩ A.affineOrderThreeCentralRegion) ≃ₜ
      Quotient (orbitRelOf
        (explicitProductAction radialData.smallAction fiberAction))
  centralModel :
    A.affineOrderThreeCentralRegion ≃ₜ
      Quotient (orbitRelOf
        (explicitProductAction radialData.bigAction fiberAction))
  commutes : centralModel ∘
      (interToRight A.orderThreeFillingImage
        A.affineOrderThreeCentralRegion).hom =
    (radialData.toEquivariantHomotopyEquivData.prodRightId
      fiberAction).quotientToFun ∘ overlapModel

namespace AffineOrderThreeSideQuotientInput

variable {G : Type u} [Group G] {fiber : Type v} [TopologicalSpace fiber]

/-- Equivariant radial descent proves the literal order-three overlap map is a homotopy
equivalence without globally trivializing its torus monodromy. -/
public theorem overlapIsHomotopyEquivalence
    (Q : A.AffineOrderThreeSideQuotientInput G fiber) :
    IsHomotopyEquivalence
      (interToRight A.orderThreeFillingImage
        A.affineOrderThreeCentralRegion).hom := by
  let E := Q.radialData.toEquivariantHomotopyEquivData.prodRightId Q.fiberAction
  apply E.isHomotopyEquivalence_of_quotient_models _ Q.overlapModel Q.centralModel Q.commutes
  · exact explicitProductAction_continuous Q.radialData.smallAction Q.fiberAction
      Q.smallAction_continuous Q.fiberAction_continuous
  · exact explicitProductAction_continuous Q.radialData.bigAction Q.fiberAction
      Q.bigAction_continuous Q.fiberAction_continuous

/-- Dold's open-union theorem upgrades the quotient-radial overlap equivalence to the actual
order-three filling-to-side equivalence. -/
public theorem homotopyEquivalenceInclusion
    (Q : A.AffineOrderThreeSideQuotientInput G fiber)
    [NormalSpace ↥(A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion)]
    [ParacompactSpace ↥(A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion)] :
    IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderThreeFillingSubspace := by
  change IsHomotopyEquivalenceInclusion
    (Subtype.val ⁻¹' A.orderThreeFillingImage :
      Set ↥(A.orderThreeFillingImage ∪
        A.affineOrderThreeCentralRegion))
  exact isHomotopyEquivalenceInclusion_of_leftToUnion _ _
    (leftToUnion_isHomotopyEquivalence_of_normal_paracompact _ _
      A.orderThreeFillingImage_isOpen
      A.actualAffineHeightSplit.centralHeightLowerRegion_isOpen
      Q.overlapIsHomotopyEquivalence)

end AffineOrderThreeSideQuotientInput

/-- Honest quotient-bundle coordinates for the order-four overlap and central region, written
after reflection about `1 / 2`.  This converts the puncture at one to the radial puncture at zero
while preserving the diagonal quotient model. -/
public structure AffineOrderFourSideQuotientInput
    (G : Type u) [Group G] (fiber : Type v) [TopologicalSpace fiber] where
  normalizationRadius : ℝ
  affineDiscRadius : ℝ
  normalizationRadius_pos : 0 < normalizationRadius
  normalizationRadius_lt_disc : normalizationRadius < affineDiscRadius
  affineDiscRadius_le_halfPlane : affineDiscRadius ≤ 1 - 1 / 3
  radialData : EquivariantRadialDomainInclusionData G
    (puncturedComplexDisc_radial normalizationRadius_pos normalizationRadius_lt_disc)
    (puncturedComplexLeftHalfPlane_radial normalizationRadius_pos
      (normalizationRadius_lt_disc.trans_le affineDiscRadius_le_halfPlane))
    (puncturedComplexDisc_subset_leftHalfPlane affineDiscRadius_le_halfPlane)
  fiberAction : MulAction G fiber
  smallAction_continuous :
    letI := radialData.smallAction
    ContinuousConstSMul G (puncturedComplexDisc affineDiscRadius)
  bigAction_continuous :
    letI := radialData.bigAction
    ContinuousConstSMul G (puncturedComplexLeftHalfPlane (1 - 1 / 3))
  fiberAction_continuous :
    letI := fiberAction
    ContinuousConstSMul G fiber
  overlapModel :
    ↥(A.orderFourFillingImage ∩ A.affineOrderFourCentralRegion) ≃ₜ
      Quotient (orbitRelOf
        (explicitProductAction radialData.smallAction fiberAction))
  centralModel :
    A.affineOrderFourCentralRegion ≃ₜ
      Quotient (orbitRelOf
        (explicitProductAction radialData.bigAction fiberAction))
  commutes : centralModel ∘
      (interToRight A.orderFourFillingImage
        A.affineOrderFourCentralRegion).hom =
    (radialData.toEquivariantHomotopyEquivData.prodRightId
      fiberAction).quotientToFun ∘ overlapModel

namespace AffineOrderFourSideQuotientInput

variable {G : Type u} [Group G] {fiber : Type v} [TopologicalSpace fiber]

/-- Equivariant radial descent proves the literal order-four overlap map is a homotopy
equivalence without globally trivializing its torus monodromy. -/
public theorem overlapIsHomotopyEquivalence
    (Q : A.AffineOrderFourSideQuotientInput G fiber) :
    IsHomotopyEquivalence
      (interToRight A.orderFourFillingImage
        A.affineOrderFourCentralRegion).hom := by
  let E := Q.radialData.toEquivariantHomotopyEquivData.prodRightId Q.fiberAction
  apply E.isHomotopyEquivalence_of_quotient_models _ Q.overlapModel Q.centralModel Q.commutes
  · exact explicitProductAction_continuous Q.radialData.smallAction Q.fiberAction
      Q.smallAction_continuous Q.fiberAction_continuous
  · exact explicitProductAction_continuous Q.radialData.bigAction Q.fiberAction
      Q.bigAction_continuous Q.fiberAction_continuous

/-- Dold's open-union theorem upgrades the quotient-radial overlap equivalence to the actual
order-four filling-to-side equivalence. -/
public theorem homotopyEquivalenceInclusion
    (Q : A.AffineOrderFourSideQuotientInput G fiber)
    [NormalSpace ↥(A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion)]
    [ParacompactSpace ↥(A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion)] :
    IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderFourFillingSubspace := by
  change IsHomotopyEquivalenceInclusion
    (Subtype.val ⁻¹' A.orderFourFillingImage :
      Set ↥(A.orderFourFillingImage ∪
        A.affineOrderFourCentralRegion))
  exact isHomotopyEquivalenceInclusion_of_leftToUnion _ _
    (leftToUnion_isHomotopyEquivalence_of_normal_paracompact _ _
      A.orderFourFillingImage_isOpen
      A.actualAffineHeightSplit.centralHeightUpperRegion_isOpen
      Q.overlapIsHomotopyEquivalence)

end AffineOrderFourSideQuotientInput

end Geometry.PaperAnalyticData

end SphereSixComplex
