module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.CentralFiber.CellularModel

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric
open CategoryTheory

namespace SphereSixComplex.Geometry.InfiniteA2Toric.CentralFiber.CellAtlas

public theorem coordinateBoundary_single_eq_attachingDegree
    {X : Type} [TopologicalSpace X] [T2Space X]
    (A : CentralFiber.CellAtlas X) (n : ℕ)
    [DecidableEq (CentralFiber.Cell (n + 1))]
    (i : CentralFiber.Cell (n + 1)) (j : CentralFiber.Cell n) :
    let _ := A.cwComplex
    CentralFiber.CWModel.coordinateBoundary A.toCWModel n (Pi.single i 1) j =
      CellularHomology.integralComparison.normalized.attachingDegree X n i j := by
  classical
  let _ := A.cwComplex
  let _ := CentralFiber.finite_cell (n + 1)
  simp only [CentralFiber.CWModel.coordinateBoundary,
    CentralFiber.CWModel.integralCellularChainModel,
    CellularHomology.normalizedModel,
    CellularHomology.IntegralComparison.objectwiseModel, integralCWSkeletalChainComplex,
    Nat.succ_eq_add_one, ChainComplex.of_d]
  change ((CellularHomology.integralComparison.normalized.cellBasis X n).symm
    (ConcreteCategory.hom (integralCWRelativeBoundary X n)
      (CellularHomology.integralComparison.normalized.cellBasis X (n + 1)
        (Finsupp.addEquivFunOnFinite.symm (Pi.single i 1))))) j = _
  have h : (Finsupp.addEquivFunOnFinite.symm (Pi.single i (1 : ℤ))) = Finsupp.single i 1 := by
    ext k
    change (Pi.single i 1 : CentralFiber.Cell (n + 1) → ℤ) k = (Finsupp.single i 1) k
    simp [Pi.single_apply, Finsupp.single_apply, eq_comm]
  rw [h]
  rfl

end SphereSixComplex.Geometry.InfiniteA2Toric.CentralFiber.CellAtlas
