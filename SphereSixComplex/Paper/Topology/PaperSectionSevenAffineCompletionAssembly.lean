module

public import SphereSixComplex.Paper.Geometry.PaperStarHausdorff
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineSideHomotopyEquivalence

/-!
# Assembly of the affine Section 7 completion

The actual affine sides are open subspaces of the finite-dimensional complex manifold obtained
from the paper's four-piece star.  This supplies the normality and paracompactness needed by the
open-union argument.  Product coordinates then construct both side homotopy equivalences, leaving
only their compatibility with the two fixed central-fibre covering projections.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap ContDiff Manifold

namespace SphereSixComplex.Geometry.PaperAnalyticData

open BiholomorphicStarGluing
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

variable (A : PaperAnalyticData)

/-- The space obtained by gluing the four analytic pieces is locally compact. -/
public theorem starUnion_locallyCompact :
    LocallyCompactSpace A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := by
  let S := A.openEmbeddingStarData.toFourPieceStarGluingData
  let B := A.biholomorphicFourPieceStarData
  let _ := S.nonemptyPieceOfCollars A.fourPieceStarGluingData_nonemptyCentralCollar
  let _ := B.complexCharts
  let _ : ∀ i, IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (S.glueData.U i) :=
    B.isManifold_piece A.fourPieceStarGluingData_nonemptyCentralCollar
  let _ : ChartedSpace ComplexModel (GluedSpace S.glueData) := gluedChartedSpace S.glueData
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (GluedSpace S.glueData) :=
    isManifold_gluedChartedSpace S.glueData
      (BiholomorphicFourPieceStarData.gluing_atlas_compatible S
        A.fourPieceStarGluingData_nonemptyCentralCollar B)
  exact Manifold.locallyCompact_of_finiteDimensional
    (modelWithCornersSelf ℂ ComplexModel)

/-- The concrete four-piece gluing is second countable. -/
public theorem starUnion_secondCountable :
    SecondCountableTopology A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := by
  let D := A.openEmbeddingStarData.toFourPieceStarGluingData.glueData
  let _ : Countable D.J := by
    change Countable (Option (Fin 3))
    infer_instance
  let _ (i : D.J) : SecondCountableTopology (D.U i) := A.starPiece_secondCountable i
  exact secondCountableTopology_gluedSpace D

/-- The elliptic interior is locally compact. -/
public theorem ellipticInterior_locallyCompact :
    LocallyCompactSpace A.ellipticInterior := by
  let _ : LocallyCompactSpace
      A.openEmbeddingStarData.SectionSevenMayerVietorisSpace :=
    A.starUnion_locallyCompact
  exact A.starCover.isOpen_stage (2 : Fin 4) |>.locallyCompactSpace

/-- The elliptic interior is paracompact. -/
public theorem ellipticInterior_paracompact :
    ParacompactSpace A.ellipticInterior := by
  let _ : LocallyCompactSpace A.ellipticInterior :=
    A.ellipticInterior_locallyCompact
  let _ : T2Space A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := A.starGluedT2
  let _ : SecondCountableTopology
      A.openEmbeddingStarData.SectionSevenMayerVietorisSpace :=
    A.starUnion_secondCountable
  infer_instance

/-- Every open subspace of the elliptic interior is paracompact. -/
public theorem ellipticInteriorOpenSubspace_paracompact
    (U : Set A.ellipticInterior) (hU : IsOpen U) :
    ParacompactSpace U := by
  let _ : LocallyCompactSpace A.ellipticInterior :=
    A.ellipticInterior_locallyCompact
  let _ : LocallyCompactSpace U := hU.locallyCompactSpace
  let _ : SecondCountableTopology
      A.openEmbeddingStarData.SectionSevenMayerVietorisSpace :=
    A.starUnion_secondCountable
  let _ : T2Space A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := A.starGluedT2
  infer_instance

/-- Every open subspace of the elliptic interior is normal. -/
public theorem ellipticInteriorOpenSubspace_normal
    (U : Set A.ellipticInterior) (hU : IsOpen U) :
    NormalSpace U := by
  let _ : ParacompactSpace U := A.ellipticInteriorOpenSubspace_paracompact U hU
  let _ : T2Space A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := A.starGluedT2
  infer_instance

variable {A : PaperAnalyticData}

namespace AffineOrderThreeSideProductInput

variable {fiber : Type*} [TopologicalSpace fiber]

/-- The order-three product coordinates construct the required side contraction with all
separation-space instances discharged from the analytic star. -/
public theorem actualHomotopyEquivalenceInclusion
    (P : A.AffineOrderThreeSideProductInput fiber) :
    IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderThreeFillingSubspace := by
  have hopen : IsOpen (A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion) :=
    A.orderThreeFillingImage_isOpen.union
      A.actualAffineHeightSplit.centralHeightLowerRegion_isOpen
  let _ : ParacompactSpace ↑(A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion) :=
    A.ellipticInteriorOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.orderThreeFillingImage ∪
      A.affineOrderThreeCentralRegion) :=
    A.ellipticInteriorOpenSubspace_normal _ hopen
  exact P.homotopyEquivalenceInclusion

end AffineOrderThreeSideProductInput

namespace AffineOrderFourSideProductInput

variable {fiber : Type*} [TopologicalSpace fiber]

/-- The order-four product coordinates construct the required side contraction with all
separation-space instances discharged from the analytic star. -/
public theorem actualHomotopyEquivalenceInclusion
    (P : A.AffineOrderFourSideProductInput fiber) :
    IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderFourFillingSubspace := by
  have hopen : IsOpen (A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion) :=
    A.orderFourFillingImage_isOpen.union
      A.actualAffineHeightSplit.centralHeightUpperRegion_isOpen
  let _ : ParacompactSpace ↑(A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion) :=
    A.ellipticInteriorOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.orderFourFillingImage ∪
      A.affineOrderFourCentralRegion) :=
    A.ellipticInteriorOpenSubspace_normal _ hopen
  exact P.homotopyEquivalenceInclusion

end AffineOrderFourSideProductInput

/-- The map from the affine band to the reduced order-three fibre obtained from the side
contraction constructed by the open-union argument. -/
public noncomputable def AffineOrderThreeSideProductInput.bandToReducedFiber
    {fiber : Type*} [TopologicalSpace fiber]
    (P : A.AffineOrderThreeSideProductInput fiber) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      orderThreeReducedCentralFiber A.periods) :=
  (A.orderThreeFillingImageHomotopyEquiv.toFun.comp
    (P.actualHomotopyEquivalenceInclusion.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderThreeSide
        A.orderThreeFillingImage
        A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToLeft
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide)

/-- The fixed order-three covering projection on the affine band. -/
public noncomputable def affineBandOrderThreeCoverMap (A : PaperAnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      orderThreeReducedCentralFiber A.periods) :=
  (RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
      A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩ |>.comp
        (A.actualAffineHeightSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
          (A.affineCentralBandHomotopyEquiv
            A.affineCentralSeparation)).toFun

/-- The map from the affine band to the reduced order-four fibre obtained from the side
contraction constructed by the open-union argument. -/
public noncomputable def AffineOrderFourSideProductInput.bandToReducedFiber
    {fiber : Type*} [TopologicalSpace fiber]
    (P : A.AffineOrderFourSideProductInput fiber) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      orderFourReducedCentralFiber A.periods) :=
  (A.orderFourFillingImageHomotopyEquiv.toFun.comp
    (P.actualHomotopyEquivalenceInclusion.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderFourSide
        A.orderFourFillingImage
        A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToRight
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide)

/-- The fixed order-four covering projection on the affine band. -/
public noncomputable def affineBandOrderFourCoverMap (A : PaperAnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      orderFourReducedCentralFiber A.periods) :=
  (RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩ |>.comp
        (A.actualAffineHeightSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
          (A.affineCentralBandHomotopyEquiv
            A.affineCentralSeparation)).toFun

/-- The smallest exact affine completion package after the point-set topology and radial base
equivalences have been discharged.  Its only proof fields are the two geometric compatibility
homotopies between the constructed side contractions and the fixed finite-cover projections. -/
public structure AffineSideCompletionInput
    (orderThreeFiber orderFourFiber : Type*)
    [TopologicalSpace orderThreeFiber] [TopologicalSpace orderFourFiber] where
  orderThreeProduct : A.AffineOrderThreeSideProductInput orderThreeFiber
  orderFourProduct : A.AffineOrderFourSideProductInput orderFourFiber
  orderThreeCompatibility : orderThreeProduct.bandToReducedFiber.Homotopic
    (affineBandOrderThreeCoverMap A)
  orderFourCompatibility : orderFourProduct.bandToReducedFiber.Homotopic
    (affineBandOrderFourCoverMap A)

namespace AffineSideCompletionInput

variable {orderThreeFiber orderFourFiber : Type*}
variable [TopologicalSpace orderThreeFiber] [TopologicalSpace orderFourFiber]

/-- Assemble the original four-field affine radial input from product coordinates and the two
remaining band compatibility homotopies. -/
public theorem toRadialCompletion
    (P : A.AffineSideCompletionInput orderThreeFiber orderFourFiber) :
    A.AffineRadialCompletionInput where
  orderThreeHomotopyEquivalence := P.orderThreeProduct.actualHomotopyEquivalenceInclusion
  orderFourHomotopyEquivalence := P.orderFourProduct.actualHomotopyEquivalenceInclusion
  orderThree_inclusion_compatibility := P.orderThreeCompatibility
  orderFour_inclusion_compatibility := P.orderFourCompatibility

end AffineSideCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData

end
