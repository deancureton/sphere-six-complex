module

public import SphereSixComplex.Topology.EstablishedAffineStarBridge
public import SphereSixComplex.Topology.EstablishedChosenAffineFillings
public import SphereSixComplex.Topology.PaperActualAffineCoreData
public import SphereSixComplex.Topology.PaperActualVanKampenCover
public import SphereSixComplex.Topology.PaperActualVanKampenNiceness
public import SphereSixComplex.Topology.PaperVanKampenAlgebraAdapter

/-!
# Actual affine filling-cover models for the paper star: definitions

The three regular cover squares below are based on the actual overlaps and filling pieces of the
four-piece star. Their deck kernels feed the source-independent based van Kampen bridge; the
paper's final affine relations and generation are then proved consequences.

This module carries only the bundled structure. It is separated from
`PaperActualAffineFillingCoverModels` so that the proof module
`PaperActualAffineFillingCoverModelsProof`, which constructs an inhabitant of that structure from
the elliptic peripheral-naturality input, can be imported by the original module without an import
cycle. Every declaration keeps its original name and namespace.
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
overlap maps despite their propositionally equal chosen base points. The bridge records the
resulting local kernels, based gluing squares, and the local vanishing statements from which the
final relations are derived. -/
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

end SphereSixComplex.Geometry.PaperAnalyticData

end
