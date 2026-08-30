module

public import SphereSixComplex.Topology.EstablishedAffineStarBridge
public import SphereSixComplex.Topology.EstablishedChosenAffineFillings
public import SphereSixComplex.Topology.PaperActualAffineCoreData
public import SphereSixComplex.Topology.PaperActualAffineFillingCoverModelsDefs
public import SphereSixComplex.Topology.PaperActualAffineFillingCoverModelsProof
public import SphereSixComplex.Topology.PaperActualVanKampenCover
public import SphereSixComplex.Topology.PaperActualVanKampenNiceness
public import SphereSixComplex.Topology.PaperVanKampenAlgebraAdapter

/-!
# Actual affine filling-cover models for the paper star

The three regular cover squares are based on the actual overlaps and filling pieces of the
four-piece star. Their deck kernels feed the source-independent based van Kampen bridge; the
paper's final affine relations and generation are then proved consequences.

The bundled structure itself now lives in `PaperActualAffineFillingCoverModelsDefs` and its
inhabitant is constructed in `PaperActualAffineFillingCoverModelsProof`, so that this module can
import that construction. Every declaration keeps its original name, namespace and signature.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover

variable (A : PaperAnalyticData)

/-- Universal-cover classification for the actual affine torus collars and their cyclic and toric
fillings.

This chooses the three regular cover squares, identifies their induced maps with the actual
overlap inclusions, and records based naturality and the exact local vanishing statements. The
final filling relations and `HasVanKampenData` are derived from this package.

It is no longer a boundary. The cusp square, the whole cusp half of the affine bridge, the two
elliptic based gluing squares and the two transported cyclic filling relations are proved; the
remaining geometry is isolated in `establishedActualStarPeripheralNaturality`, which bundles the
marked peripheral naturality of all three collars with the two elliptic regular-cover models.
-/
public theorem establishedActualAffineFillingCoverSquares :
    Nonempty A.ActualAffineFillingCoverSquares :=
  A.nonempty_actualAffineFillingCoverSquares

/-- A coherent production choice of all three actual filling-cover squares. -/
public noncomputable def actualAffineFillingCoverSquares :
    A.ActualAffineFillingCoverSquares :=
  Classical.choice A.establishedActualAffineFillingCoverSquares

namespace ActualAffineFillingCoverSquares

variable {A : PaperAnalyticData}

/-- The actual order-three collar inclusion is onto on fundamental groups. -/
public theorem orderThreeFundamentalGroupMap_surjective
    (S : A.ActualAffineFillingCoverSquares) :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap :=
  S.bridge.oneSurjective

/-- The actual order-four collar inclusion is onto on fundamental groups. -/
public theorem orderFourFundamentalGroupMap_surjective
    (S : A.ActualAffineFillingCoverSquares) :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap :=
  S.bridge.twoSurjective

/-- The actual cusp collar inclusion is onto on fundamental groups. -/
public theorem cuspFundamentalGroupMap_surjective
    (S : A.ActualAffineFillingCoverSquares) :
    Function.Surjective A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap :=
  S.bridge.cuspSurjective

/-- The actual cover squares give a surjective core map and the exact filling relations. -/
public theorem relationsAndCoreSurjective
    (S : A.ActualAffineFillingCoverSquares) :
    ∃ hcore : Function.Surjective
        A.actualVanKampenFourPieceCover.coreFundamentalGroupMap,
      AffineTorusStarFillingRelations
        (S.coreData.mapSurjective
          A.actualVanKampenFourPieceCover.coreFundamentalGroupMap hcore)
        3 4 (-epsilon) epsilon' 0 paperToricSubgroup := by
  let _ := A.vanKampenCharts
  have _ : StronglyLocallyContractibleSpace A.VanKampenSpace := A.vanKampen_locallyNice
  have _ : PathConnectedSpace A.VanKampenSpace := A.vanKampen_pathConnected
  have _ : TauCeti.SemilocallySimplyConnectedSpace A.VanKampenSpace :=
    A.vanKampen_semilocallySimplyConnected
  exact S.bridge.relationsAndCoreSurjective

/-- The actual three cover squares give the verified van Kampen contract for the glued star. -/
public theorem hasVanKampenData
    (S : A.ActualAffineFillingCoverSquares) :
    HasVanKampenData A.VanKampenSpace 0 1 (-1) := by
  obtain ⟨hcore, relations⟩ := S.relationsAndCoreSurjective
  exact hasVanKampenData_of_correctedAffineData _
    (S.coreData.mapSurjective
      A.actualVanKampenFourPieceCover.coreFundamentalGroupMap hcore)
    relations

end ActualAffineFillingCoverSquares

/-- The established analytic choices give a complete van Kampen witness for their actual star. -/
public theorem actualStarHasVanKampenData :
    Topology.HasVanKampenData A.VanKampenSpace 0 1 (-1) :=
  A.actualAffineFillingCoverSquares.hasVanKampenData

end SphereSixComplex.Geometry.PaperAnalyticData

namespace SphereSixComplex.Geometry

/-- The production analytic package has the required actual-star van Kampen presentation. -/
public theorem establishedPaperStarHasVanKampenData :
    Topology.HasVanKampenData establishedPaperAnalyticData.VanKampenSpace 0 1 (-1) :=
  establishedPaperAnalyticData.actualStarHasVanKampenData

end SphereSixComplex.Geometry

end
