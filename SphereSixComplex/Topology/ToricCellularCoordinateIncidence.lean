module

public import SphereSixComplex.Topology.PaperCuspCentralFiberCWTypes

@[expose] public section
noncomputable section
open CategoryTheory

namespace SphereSixComplex.StandardA2ToricCentralFiberCellAtlas

public theorem coordinateBoundary_single_eq_attachingDegree
    {X : Type} [TopologicalSpace X] [T2Space X]
    (A : StandardA2ToricCentralFiberCellAtlas X) (n : ℕ)
    [DecidableEq (cuspWCellIndex (n + 1))]
    (i : cuspWCellIndex (n + 1)) (j : cuspWCellIndex n) :
    let _ := A.cwComplex
    standardA2ToricCellularCoordinateBoundary A.toCWDecomposition n (Pi.single i 1) j =
      integralCWCellularHomologyFoundation.normalized.attachingDegree X n i j := by
  classical
  let _ := A.cwComplex
  let _ := cuspWCellIndex_finite (n + 1)
  simp only [standardA2ToricCellularCoordinateBoundary,
    StandardA2ToricCentralFiberCWDecomposition.integralCellularChainModel,
    EstablishedCellularHomology.integralCWCellularHomologyModel,
    IntegralCWCellularHomologyFoundation.objectwiseModel, integralCWSkeletalChainComplex,
    Nat.succ_eq_add_one, ChainComplex.of_d]
  change ((integralCWCellularHomologyFoundation.normalized.cellBasis X n).symm
    (ConcreteCategory.hom (integralCWRelativeBoundary X n)
      (integralCWCellularHomologyFoundation.normalized.cellBasis X (n + 1)
        (Finsupp.addEquivFunOnFinite.symm (Pi.single i 1))))) j = _
  have h : (Finsupp.addEquivFunOnFinite.symm (Pi.single i (1 : ℤ))) = Finsupp.single i 1 := by
    ext k
    change (Pi.single i 1 : cuspWCellIndex (n + 1) → ℤ) k = (Finsupp.single i 1) k
    simp [Pi.single_apply, Finsupp.single_apply, eq_comm]
  rw [h]
  rfl

end SphereSixComplex.StandardA2ToricCentralFiberCellAtlas
