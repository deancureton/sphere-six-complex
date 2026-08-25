module

public import SphereSixComplex.Topology.EstablishedAffineStarBridge
public import SphereSixComplex.Topology.EstablishedChosenAffineFillings
public import SphereSixComplex.Topology.PaperActualAffineCoreData
public import SphereSixComplex.Topology.PaperActualVanKampenCover
public import SphereSixComplex.Topology.PaperActualVanKampenNiceness
public import SphereSixComplex.Topology.PaperVanKampenAlgebraAdapter

/-!
# Actual affine filling-cover models for the paper star

The three regular cover squares below are based on the actual overlaps and filling pieces of the
four-piece star. Their deck kernels feed the source-independent based van Kampen bridge; the
paper's final affine relations and generation are then proved consequences.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover

variable (A : PaperAnalyticData)

/-- The exact regular-cover classifications of the three actual collar-to-filling maps.

The `HEq` fields identify the maps carried by the chosen cover models with the actual based
overlap maps despite their propositionally equal chosen base points. The bridge retains only the
resulting local kernels and based gluing squares, not the final relations. -/
public structure ActualAffineFillingCoverSquares where
  coreData : AffineTorusCorePiOneData
    (FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨_, A.actualVanKampenFourPieceCover.base_mem_core⟩)
    Lattice paperMonodromyOne paperMonodromyTwo
  centralToCore : FundamentalGroup A.CentralFamily A.centralAffineBase ≃*
    FundamentalGroup A.actualVanKampenFourPieceCover.core
      ⟨_, A.actualVanKampenFourPieceCover.base_mem_core⟩
  coreData_eq : coreData = A.centralAffineCorePiOneData.mapSurjective
    centralToCore.toMonoidHom centralToCore.surjective
  orderThreeCover : ChosenCyclicAffineFillingCoverModel 3 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticThree
  orderThreeBoundaryBase_eq : orderThreeCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩
  orderThreeFillingBase_eq : orderThreeCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩
  orderThreeMap_eq : fundamentalGroupHomOfBaseEq
    orderThreeBoundaryBase_eq orderThreeFillingBase_eq
    orderThreeCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
  orderFourCover : ChosenCyclicAffineFillingCoverModel 4 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticFour
  orderFourBoundaryBase_eq : orderFourCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩
  orderFourFillingBase_eq : orderFourCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩
  orderFourMap_eq : fundamentalGroupHomOfBaseEq
    orderFourBoundaryBase_eq orderFourFillingBase_eq
    orderFourCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
  cuspCover : ChosenToricFillingCoverModel Lattice paperToricSubgroup
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.cusp : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.cusp
  cuspBoundaryBase_eq : cuspCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.cuspPoint,
      A.actualVanKampenFourPieceCover.cuspPoint_mem⟩
  cuspFillingBase_eq : cuspCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.cuspPoint,
      A.actualVanKampenFourPieceCover.cuspPoint_mem.2⟩
  cuspMap_eq : fundamentalGroupHomOfBaseEq cuspBoundaryBase_eq cuspFillingBase_eq
    cuspCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.cuspOverlapFundamentalGroupMap
  bridge : AffineTorusStarFillingBridge A.actualVanKampenFourPieceCover coreData
    3 4 epsilon (-epsilon') 0 paperToricSubgroup
  orderThreeTwist_eq : orderThreeCover.twist = epsilon
  orderThreeTranslation_eq : fundamentalGroupAddHomOfBaseEq
    orderThreeBoundaryBase_eq orderThreeCover.translation = bridge.oneTranslation
  orderThreeMeridian_eq : fundamentalGroupElementOfBaseEq
    orderThreeBoundaryBase_eq orderThreeCover.meridian = bridge.oneMeridian
  orderFourTwist_eq : orderFourCover.twist = -epsilon'
  orderFourTranslation_eq : fundamentalGroupAddHomOfBaseEq
    orderFourBoundaryBase_eq orderFourCover.translation = bridge.twoTranslation
  orderFourMeridian_eq : fundamentalGroupElementOfBaseEq
    orderFourBoundaryBase_eq orderFourCover.meridian = bridge.twoMeridian
  cuspTranslation_eq : fundamentalGroupAddHomOfBaseEq
    cuspBoundaryBase_eq cuspCover.translation = bridge.cuspTranslation
  cuspMeridian_eq : fundamentalGroupElementOfBaseEq
    cuspBoundaryBase_eq cuspCover.meridian = bridge.cuspMeridian
  cuspVanishing_onto : ∀ a ∈ paperToricSubgroup,
    ∃ k, cuspCover.vanishing k = a

/-- Universal-cover classification for the actual affine torus collars and their cyclic and toric
fillings.

This established boundary is geometric: it chooses the three regular cover squares, identifies
their induced maps with the actual overlap inclusions, and records based naturality with the
central universal cover. It asserts neither the final filling relations nor `HasVanKampenData`.
-/
public axiom establishedActualAffineFillingCoverSquares :
    Nonempty A.ActualAffineFillingCoverSquares

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
        3 4 epsilon (-epsilon') 0 paperToricSubgroup := by
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
  exact hasVanKampenData_of_affineData _
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
