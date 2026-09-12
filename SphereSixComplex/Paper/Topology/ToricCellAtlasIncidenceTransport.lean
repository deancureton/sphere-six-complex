module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.CentralFiber.CellularModel
public import SphereSixComplex.Prerequisites.Topology.CellularCharacteristicNaturality
public import SphereSixComplex.Paper.Topology.ToricCellularCoordinateIncidence

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric

namespace SphereSixComplex.Geometry.InfiniteA2Toric.CentralFiber.CellAtlas

public theorem transport_attachingDegree
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (A : CentralFiber.CellAtlas X) (e : X ≃ₜ Y)
    (T : CellularHomology.IntegralComparison) (n : ℕ)
    (i : CentralFiber.Cell (n + 1)) (j : CentralFiber.Cell n) :
    let _ := A.cwComplex
    let _ := (A.transport e).cwComplex
    T.attachingDegree X n i j = T.attachingDegree Y n i j := by
  let _ := A.cwComplex
  let _ := (A.transport e).cwComplex
  have h : ∀ n (i : CentralFiber.Cell n) (x : Fin n → ℝ),
      x ∈ Metric.closedBall 0 1 →
      e (Topology.CWComplex.map (C := (Set.univ : Set X)) n i x) =
        (Topology.CWComplex.map (C := (Set.univ : Set Y)) n i x) := by
    intro n i x hx
    rfl
  exact T.attachingDegree_natural ⟨e, e.continuous⟩
    (isIntegralCWCellularMap_of_characteristic ⟨e, e.continuous⟩ (fun _ ↦ id) h)
    (fun _ ↦ id) h n Function.injective_id i j

public theorem transport_coordinateBoundary_single
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (A : CentralFiber.CellAtlas X) (e : X ≃ₜ Y) (n : ℕ)
    [DecidableEq (CentralFiber.Cell (n + 1))]
    (i : CentralFiber.Cell (n + 1)) (j : CentralFiber.Cell n) :
    CentralFiber.CWModel.coordinateBoundary A.toCWModel n (Pi.single i 1) j =
      CentralFiber.CWModel.coordinateBoundary (A.transport e).toCWModel n
        (Pi.single i 1) j := by
  rw [A.coordinateBoundary_single_eq_attachingDegree,
    (A.transport e).coordinateBoundary_single_eq_attachingDegree]
  exact A.transport_attachingDegree e CellularHomology.integralComparison.normalized n i j

end SphereSixComplex.Geometry.InfiniteA2Toric.CentralFiber.CellAtlas
