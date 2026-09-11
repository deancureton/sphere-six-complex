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


end SphereSixComplex.Geometry.PaperAnalyticData

end
