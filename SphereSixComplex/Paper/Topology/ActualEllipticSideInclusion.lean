module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.AnalyticData
open EllipticFilling
variable {A : AnalyticData}

public theorem orderThreeSide_inverse_inclusion (R : A.AffineRadialCompletionInput)
    (x : orderThreeReducedCentralFiber A.periods) :
    (R.twoDiscCover.orderThreeSideHomotopyEquiv.invFun x).val.val =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some (1 : Fin 3)) ((orderThreeSelectedFillingHomotopyEquivCentralFiber A).invFun x) := by
  change (R.orderThreeHomotopyEquivalence.toHomotopyEquiv.invFun _).val.val = _
  rw [IsHomotopyEquivalenceInclusion.toHomotopyEquiv_invFun]
  rfl

public theorem orderFourSide_inverse_inclusion (R : A.AffineRadialCompletionInput)
    (x : orderFourReducedCentralFiber A.periods) :
    (R.twoDiscCover.orderFourSideHomotopyEquiv.invFun x).val.val =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some (2 : Fin 3)) ((orderFourSelectedFillingHomotopyEquivCentralFiber A).invFun x) := by
  change (R.orderFourHomotopyEquivalence.toHomotopyEquiv.invFun _).val.val = _
  rw [IsHomotopyEquivalenceInclusion.toHomotopyEquiv_invFun]
  rfl

end SphereSixComplex.Geometry.AnalyticData
