module
public import SphereSixComplex.Paper.Topology.ActualEllipticSideInclusion
public import SphereSixComplex.Paper.Topology.StarFourthTranslation
@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.AnalyticData
open EllipticFilling
variable {A : AnalyticData}

public theorem orderThreeSelectedFilling_inverse (x : orderThreeReducedCentralFiber A.periods) :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).invFun x =
      A.orderThreeFourthFillingHomeomorph.symm x.val := rfl

public theorem orderFourSelectedFilling_inverse (x : orderFourReducedCentralFiber A.periods) :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).invFun x =
      A.orderFourFourthFillingHomeomorph.symm x.val := rfl

public theorem ellipticFourthTranslation_three (z : UnitAddCircle)
    (q : A.openEmbeddingStarData.filling 1) :
    A.ellipticFourthTranslation (z, A.fourthTranslationThreeInclusion q) =
      A.fourthTranslationThreeInclusion (A.actualOrderThreeFourthTranslation (z,q)) := by
  have h := ContinuousMap.liftCover_coe
    (S := A.fourthTranslationPatchSet) (φ := A.fourthTranslationPatch)
    (hφ := A.fourthTranslationPatch_compatible) (hS := A.fourthTranslationPatchSet_nhds)
    (i := 1) ⟨(z,A.fourthTranslationThreeInclusion q),
      (A.fourthTranslationThreeChart.symm q).property⟩
  change A.ellipticFourthTranslation (z,A.fourthTranslationThreeInclusion q) =
    A.fourthTranslationThreeInclusion (A.actualOrderThreeFourthTranslation
      (z,A.fourthTranslationThreeChart (A.fourthTranslationThreeChart.symm q))) at h
  simpa only [Homeomorph.apply_symm_apply] using h

public theorem ellipticFourthTranslation_four (z : UnitAddCircle)
    (q : A.openEmbeddingStarData.filling 2) :
    A.ellipticFourthTranslation (z, A.fourthTranslationFourInclusion q) =
      A.fourthTranslationFourInclusion (A.actualOrderFourFourthTranslation (z,q)) := by
  have h := ContinuousMap.liftCover_coe
    (S := A.fourthTranslationPatchSet) (φ := A.fourthTranslationPatch)
    (hφ := A.fourthTranslationPatch_compatible) (hS := A.fourthTranslationPatchSet_nhds)
    (i := 2) ⟨(z,A.fourthTranslationFourInclusion q),
      (A.fourthTranslationFourChart.symm q).property⟩
  change A.ellipticFourthTranslation (z,A.fourthTranslationFourInclusion q) =
    A.fourthTranslationFourInclusion (A.actualOrderFourFourthTranslation
      (z,A.fourthTranslationFourChart (A.fourthTranslationFourChart.symm q))) at h
  simpa only [Homeomorph.apply_symm_apply] using h

public theorem orderThreeSide_fourthTranslation (R : A.AffineRadialCompletionInput)
    (z : UnitAddCircle) (x y : orderThreeReducedCentralFiber A.periods)
    (hy : y.val = orderThreeFourthCircleTranslation A.periods (z,x.val)) :
    A.starFourthTranslation (z,(R.twoDiscCover.orderThreeSideHomotopyEquiv.invFun x).val.val) =
      (R.twoDiscCover.orderThreeSideHomotopyEquiv.invFun y).val.val := by
  rw [orderThreeSide_inverse_inclusion, orderThreeSide_inverse_inclusion]
  change A.starFourthTranslation
      (z,(A.fourthTranslationThreeInclusion
        ((orderThreeSelectedFillingHomotopyEquivCentralFiber A).invFun x)).val) =
    (A.fourthTranslationThreeInclusion
      ((orderThreeSelectedFillingHomotopyEquivCentralFiber A).invFun y)).val
  rw [A.starFourthTranslation_elliptic]
  erw [ellipticFourthTranslation_three]
  apply congrArg (fun q ↦ (A.fourthTranslationThreeInclusion q).val)
  rw [orderThreeSelectedFilling_inverse, orderThreeSelectedFilling_inverse]
  change A.orderThreeFourthFillingHomeomorph.symm
    (orderThreeFourthCircleTranslation A.periods
      (z,A.orderThreeFourthFillingHomeomorph (A.orderThreeFourthFillingHomeomorph.symm x.val))) =
    A.orderThreeFourthFillingHomeomorph.symm y.val
  rw [Homeomorph.apply_symm_apply, hy]

public theorem orderFourSide_fourthTranslation (R : A.AffineRadialCompletionInput)
    (z : UnitAddCircle) (x y : orderFourReducedCentralFiber A.periods)
    (hy : y.val = orderFourFourthCircleTranslation A.periods (z,x.val)) :
    A.starFourthTranslation (z,(R.twoDiscCover.orderFourSideHomotopyEquiv.invFun x).val.val) =
      (R.twoDiscCover.orderFourSideHomotopyEquiv.invFun y).val.val := by
  rw [orderFourSide_inverse_inclusion, orderFourSide_inverse_inclusion]
  change A.starFourthTranslation
      (z,(A.fourthTranslationFourInclusion
        ((orderFourSelectedFillingHomotopyEquivCentralFiber A).invFun x)).val) =
    (A.fourthTranslationFourInclusion
      ((orderFourSelectedFillingHomotopyEquivCentralFiber A).invFun y)).val
  rw [A.starFourthTranslation_elliptic]
  erw [ellipticFourthTranslation_four]
  apply congrArg (fun q ↦ (A.fourthTranslationFourInclusion q).val)
  rw [orderFourSelectedFilling_inverse, orderFourSelectedFilling_inverse]
  change A.orderFourFourthFillingHomeomorph.symm
    (orderFourFourthCircleTranslation A.periods
      (z,A.orderFourFourthFillingHomeomorph (A.orderFourFourthFillingHomeomorph.symm x.val))) =
    A.orderFourFourthFillingHomeomorph.symm y.val
  rw [Homeomorph.apply_symm_apply, hy]

end SphereSixComplex.Geometry.AnalyticData
