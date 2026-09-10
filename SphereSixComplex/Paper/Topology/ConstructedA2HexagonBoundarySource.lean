module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveBoundaryCellular
public import SphereSixComplex.Prerequisites.Topology.CellularSquareOrientation

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex

public theorem constructedA2HexagonSide_gauge (i : Fin 6) (t : unitInterval) :
    constructedA2HexagonGauge (constructedA2HexagonSide i t).1 = 2 / 3 := by
  have hu := (show constructedA2CorrectedPlaneCell 0 ⊆ constructedA2CorrectedClosedHexagon 0 by
    rw [constructedA2CorrectedClosedHexagon_eq_planeCell]) (constructedA2HexagonSide i t).property
  change constructedA2HexagonGauge
    ((constructedA2HexagonSide i t).1 - constructedA2CorrectedPlaneCenter 0) ≤ 2 / 3 at hu
  have hc : constructedA2CorrectedPlaneCenter 0 = 0 := by
    ext j
    fin_cases j <;> norm_num [constructedA2CorrectedPlaneCenter]
  rw [hc, sub_zero] at hu
  apply le_antisymm hu
  have h₀ := (norm_le_pi_norm (constructedA2HexagonSide i t).1 0).trans
    (norm_le_constructedA2HexagonGauge _)
  have h₁ := (norm_le_pi_norm (constructedA2HexagonSide i t).1 1).trans
    (norm_le_constructedA2HexagonGauge _)
  have h₂ : |(constructedA2HexagonSide i t).1 0 - (constructedA2HexagonSide i t).1 1| ≤
      constructedA2HexagonGauge (constructedA2HexagonSide i t).1 := le_max_right _ _
  rw [constructedA2HexagonSide_val] at h₀ h₁ h₂ ⊢
  fin_cases i <;>
    simp [constructedA2PlaneVertexOffset, constructedA2PlaneNextVertexOffset,
      Pi.add_apply, smul_eq_mul] at h₀ h₁ h₂ ⊢ <;>
    ring_nf at h₀ h₁ h₂ ⊢ <;> norm_num at h₀ h₁ h₂ ⊢ <;> assumption

public abbrev ConstructedA2HexagonBoundary :=
  {x : Fin 2 → ℝ // constructedA2HexagonGauge x = 2 / 3}

public def constructedA2SquareBoundaryHexagonHomeomorph :
    CWCharacteristicBoundarySphere 2 ≃ₜ ConstructedA2HexagonBoundary :=
  (constructedA2CorrectedHexagonHomeomorph 0).subtype (fun x ↦ by
    change x ∈ Metric.sphere 0 1 ↔
      constructedA2HexagonGauge
        (constructedA2CorrectedPlaneCenter 0 + constructedA2SquareToHexagonRadial x) = 2 / 3
    have hc : constructedA2CorrectedPlaneCenter 0 = 0 := by
      ext j
      fin_cases j <;> norm_num [constructedA2CorrectedPlaneCenter]
    rw [hc, zero_add, constructedA2HexagonGauge_squareToHexagonRadial,
      Metric.mem_sphere, dist_zero_right]
    constructor <;> intro h <;> nlinarith)

public def constructedA2HexagonBoundaryVertex (i : Fin 6) : ConstructedA2HexagonBoundary :=
  ⟨constructedA2PlaneVertexOffset i, by
    have h := constructedA2HexagonSide_gauge i 0
    simpa [constructedA2HexagonSide_val] using h⟩

public def constructedA2HexagonBoundarySidePath (i : Fin 6) :
    Path (constructedA2HexagonBoundaryVertex i)
      (constructedA2HexagonBoundaryVertex (constructedA2CellNextIndex i)) where
  toFun t := ⟨(constructedA2HexagonSide i t).1, constructedA2HexagonSide_gauge i t⟩
  continuous_toFun := (continuous_subtype_val.comp
    (constructedA2HexagonSide_continuous i)).subtype_mk _
  source' := by
    apply Subtype.ext
    simp [constructedA2HexagonSide_val, constructedA2HexagonBoundaryVertex]
  target' := by
    apply Subtype.ext
    simp [constructedA2HexagonSide_val, constructedA2HexagonBoundaryVertex,
      constructedA2PlaneNextVertexOffset]

public def constructedA2HexagonBoundaryLoop :
    Path (constructedA2HexagonBoundaryVertex 0) (constructedA2HexagonBoundaryVertex 0) :=
  (((((constructedA2HexagonBoundarySidePath 0).trans
    (constructedA2HexagonBoundarySidePath 1)).trans
    (constructedA2HexagonBoundarySidePath 2)).trans
    (constructedA2HexagonBoundarySidePath 3)).trans
    (constructedA2HexagonBoundarySidePath 4)).trans
    (constructedA2HexagonBoundarySidePath 5)

end SphereSixComplex.Geometry.InfiniteA2Toric
