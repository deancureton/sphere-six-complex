module

public import SphereSixComplex.Topology.PaperCuspCentralFiberCWTypes
public import SphereSixComplex.Topology.CellularCharacteristicNaturality

@[expose] public section
noncomputable section

namespace SphereSixComplex.StandardA2ToricCentralFiberCellAtlas

public theorem transport_attachingDegree
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (A : StandardA2ToricCentralFiberCellAtlas X) (e : X ≃ₜ Y)
    (T : IntegralCWCellularHomologyFoundation) (n : ℕ)
    (i : cuspWCellIndex (n + 1)) (j : cuspWCellIndex n) :
    let _ := A.cwComplex
    let _ := (A.transport e).cwComplex
    T.attachingDegree X n i j = T.attachingDegree Y n i j := by
  let _ := A.cwComplex
  let _ := (A.transport e).cwComplex
  have h : ∀ n (i : cuspWCellIndex n) (x : Fin n → ℝ),
      x ∈ Metric.closedBall 0 1 →
      e (Topology.CWComplex.map (C := (Set.univ : Set X)) n i x) =
        (Topology.CWComplex.map (C := (Set.univ : Set Y)) n i x) := by
    intro n i x hx
    rfl
  exact T.attachingDegree_natural ⟨e, e.continuous⟩
    (isIntegralCWCellularMap_of_characteristic ⟨e, e.continuous⟩ (fun _ ↦ id) h)
    (fun _ ↦ id) h n Function.injective_id i j

end SphereSixComplex.StandardA2ToricCentralFiberCellAtlas
