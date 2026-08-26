module

public import SphereSixComplex.Geometry.PaperBiholomorphicStar
public import SphereSixComplex.Geometry.PaperOpenEmbeddingStarNonempty
public import SphereSixComplex.Geometry.PaperStarHausdorff
public import SphereSixComplex.Geometry.PaperStarPieceTopology
public import SphereSixComplex.Topology.PaperSectionSevenAffineSideHomotopyEquivalence

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

open SphereSixComplex.Geometry.EstablishedBiholomorphicStarGluing
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

variable (A : PaperAnalyticData)

/-- The space obtained by gluing the four analytic pieces is locally compact. -/
public theorem sectionSevenMayerVietorisSpace_locallyCompact :
    LocallyCompactSpace A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := by
  let S := A.openEmbeddingStarData.toFourPieceStarGluingData
  let B := A.biholomorphicFourPieceStarData
  let _ := S.nonemptyPieceOfCollars A.fourPieceStarGluingData_nonemptyCentralCollar
  let _ := B.complexCharts
  let _ : ∀ i, IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (S.glueData.U i) :=
    B.pieceManifold A.fourPieceStarGluingData_nonemptyCentralCollar
  let _ : ChartedSpace ComplexModel (GluedSpace S.glueData) := gluedChartedSpace S.glueData
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (GluedSpace S.glueData) :=
    isManifold_gluedChartedSpace S.glueData
      (establishedFourPieceBiholomorphicGluingAtlasCompatible S
        A.fourPieceStarGluingData_nonemptyCentralCollar B)
  exact Manifold.locallyCompact_of_finiteDimensional
    (modelWithCornersSelf ℂ ComplexModel)

/-- The concrete four-piece gluing is second countable. -/
public theorem sectionSevenMayerVietorisSpace_secondCountable :
    SecondCountableTopology A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := by
  let D := A.openEmbeddingStarData.toFourPieceStarGluingData.glueData
  let _ : Countable D.J := by
    change Countable (Option (Fin 3))
    infer_instance
  let _ (i : D.J) : SecondCountableTopology (D.U i) := A.starPiece_secondCountable i
  exact secondCountableTopology_gluedSpace D

/-- The elliptic interior is locally compact. -/
public theorem sectionSevenEllipticInterior_locallyCompact :
    LocallyCompactSpace A.SectionSevenEllipticInterior := by
  let _ : LocallyCompactSpace
      A.openEmbeddingStarData.SectionSevenMayerVietorisSpace :=
    A.sectionSevenMayerVietorisSpace_locallyCompact
  exact A.SectionSevenEllipticCover.isOpen_stage (2 : Fin 4) |>.locallyCompactSpace

/-- The elliptic interior is paracompact. -/
public theorem sectionSevenEllipticInterior_paracompact :
    ParacompactSpace A.SectionSevenEllipticInterior := by
  let _ : LocallyCompactSpace A.SectionSevenEllipticInterior :=
    A.sectionSevenEllipticInterior_locallyCompact
  let _ : T2Space A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := A.starGluedT2
  let _ : SecondCountableTopology
      A.openEmbeddingStarData.SectionSevenMayerVietorisSpace :=
    A.sectionSevenMayerVietorisSpace_secondCountable
  infer_instance

/-- Every open subspace of the elliptic interior is paracompact. -/
public theorem sectionSevenOpenSubspace_paracompact
    (U : Set A.SectionSevenEllipticInterior) (hU : IsOpen U) :
    ParacompactSpace U := by
  let _ : LocallyCompactSpace A.SectionSevenEllipticInterior :=
    A.sectionSevenEllipticInterior_locallyCompact
  let _ : LocallyCompactSpace U := hU.locallyCompactSpace
  let _ : SecondCountableTopology
      A.openEmbeddingStarData.SectionSevenMayerVietorisSpace :=
    A.sectionSevenMayerVietorisSpace_secondCountable
  let _ : T2Space A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := A.starGluedT2
  infer_instance

/-- Every open subspace of the elliptic interior is normal. -/
public theorem sectionSevenOpenSubspace_normal
    (U : Set A.SectionSevenEllipticInterior) (hU : IsOpen U) :
    NormalSpace U := by
  let _ : ParacompactSpace U := A.sectionSevenOpenSubspace_paracompact U hU
  let _ : T2Space A.openEmbeddingStarData.SectionSevenMayerVietorisSpace := A.starGluedT2
  infer_instance

variable {A : PaperAnalyticData}

namespace SectionSevenAffineOrderThreeSideProductInput

variable {fiber : Type*} [TopologicalSpace fiber]

/-- The order-three product coordinates construct the required side contraction with all
separation-space instances discharged from the analytic star. -/
public theorem actualHomotopyEquivalenceInclusion
    (P : A.SectionSevenAffineOrderThreeSideProductInput fiber) :
    IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderThreeFillingSubspace := by
  have hopen : IsOpen (A.sectionSevenOrderThreeFillingImage ∪
      A.sectionSevenAffineOrderThreeCentralRegion) :=
    A.sectionSevenOrderThreeFillingImage_isOpen.union
      A.sectionSevenActualAffineSplit.centralHeightLowerRegion_isOpen
  let _ : ParacompactSpace ↑(A.sectionSevenOrderThreeFillingImage ∪
      A.sectionSevenAffineOrderThreeCentralRegion) :=
    A.sectionSevenOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.sectionSevenOrderThreeFillingImage ∪
      A.sectionSevenAffineOrderThreeCentralRegion) :=
    A.sectionSevenOpenSubspace_normal _ hopen
  exact P.homotopyEquivalenceInclusion

end SectionSevenAffineOrderThreeSideProductInput

namespace SectionSevenAffineOrderFourSideProductInput

variable {fiber : Type*} [TopologicalSpace fiber]

/-- The order-four product coordinates construct the required side contraction with all
separation-space instances discharged from the analytic star. -/
public theorem actualHomotopyEquivalenceInclusion
    (P : A.SectionSevenAffineOrderFourSideProductInput fiber) :
    IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderFourFillingSubspace := by
  have hopen : IsOpen (A.sectionSevenOrderFourFillingImage ∪
      A.sectionSevenAffineOrderFourCentralRegion) :=
    A.sectionSevenOrderFourFillingImage_isOpen.union
      A.sectionSevenActualAffineSplit.centralHeightUpperRegion_isOpen
  let _ : ParacompactSpace ↑(A.sectionSevenOrderFourFillingImage ∪
      A.sectionSevenAffineOrderFourCentralRegion) :=
    A.sectionSevenOpenSubspace_paracompact _ hopen
  let _ : NormalSpace ↑(A.sectionSevenOrderFourFillingImage ∪
      A.sectionSevenAffineOrderFourCentralRegion) :=
    A.sectionSevenOpenSubspace_normal _ hopen
  exact P.homotopyEquivalenceInclusion

end SectionSevenAffineOrderFourSideProductInput

/-- The map from the affine band to the reduced order-three fibre obtained from the side
contraction constructed by the open-union argument. -/
public noncomputable def SectionSevenAffineOrderThreeSideProductInput.bandToReducedFiber
    {fiber : Type*} [TopologicalSpace fiber]
    (P : A.SectionSevenAffineOrderThreeSideProductInput fiber) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderThreeReducedCentralFiber A.periods) :=
  (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
    (P.actualHomotopyEquivalenceInclusion.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenOrderThreeFillingImage
        A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToLeft
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide)

/-- The fixed order-three covering projection on the affine band. -/
public noncomputable def sectionSevenAffineBandOrderThreeCoverMap (A : PaperAnalyticData) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderThreeReducedCentralFiber A.periods) :=
  (RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
      A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩ |>.comp
        (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
          (A.sectionSevenAffineCentralBandHomotopyEquiv
            A.sectionSevenAffineCentralSeparation)).toFun

/-- The map from the affine band to the reduced order-four fibre obtained from the side
contraction constructed by the open-union argument. -/
public noncomputable def SectionSevenAffineOrderFourSideProductInput.bandToReducedFiber
    {fiber : Type*} [TopologicalSpace fiber]
    (P : A.SectionSevenAffineOrderFourSideProductInput fiber) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderFourReducedCentralFiber A.periods) :=
  (A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
    (P.actualHomotopyEquivalenceInclusion.toHomotopyEquiv.trans
      (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderFourSide
        A.sectionSevenOrderFourFillingImage
        A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToRight
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide)

/-- The fixed order-four covering projection on the affine band. -/
public noncomputable def sectionSevenAffineBandOrderFourCoverMap (A : PaperAnalyticData) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      OrderFourReducedCentralFiber A.periods) :=
  (RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩ |>.comp
        (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
          (A.sectionSevenAffineCentralBandHomotopyEquiv
            A.sectionSevenAffineCentralSeparation)).toFun

/-- The smallest exact affine completion package after the point-set topology and radial base
equivalences have been discharged.  Its only proof fields are the two geometric compatibility
homotopies between the constructed side contractions and the fixed finite-cover projections. -/
public structure SectionSevenAffineSideCompletionInput
    (orderThreeFiber orderFourFiber : Type*)
    [TopologicalSpace orderThreeFiber] [TopologicalSpace orderFourFiber] where
  orderThreeProduct : A.SectionSevenAffineOrderThreeSideProductInput orderThreeFiber
  orderFourProduct : A.SectionSevenAffineOrderFourSideProductInput orderFourFiber
  orderThreeCompatibility : orderThreeProduct.bandToReducedFiber.Homotopic
    (sectionSevenAffineBandOrderThreeCoverMap A)
  orderFourCompatibility : orderFourProduct.bandToReducedFiber.Homotopic
    (sectionSevenAffineBandOrderFourCoverMap A)

namespace SectionSevenAffineSideCompletionInput

variable {orderThreeFiber orderFourFiber : Type*}
variable [TopologicalSpace orderThreeFiber] [TopologicalSpace orderFourFiber]

/-- Assemble the original four-field affine radial input from product coordinates and the two
remaining band compatibility homotopies. -/
public theorem toRadialCompletion
    (P : A.SectionSevenAffineSideCompletionInput orderThreeFiber orderFourFiber) :
    A.SectionSevenAffineRadialCompletionInput where
  orderThreeHomotopyEquivalence := P.orderThreeProduct.actualHomotopyEquivalenceInclusion
  orderFourHomotopyEquivalence := P.orderFourProduct.actualHomotopyEquivalenceInclusion
  orderThree_inclusion_compatibility := P.orderThreeCompatibility
  orderFour_inclusion_compatibility := P.orderFourCompatibility

end SectionSevenAffineSideCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData

end
