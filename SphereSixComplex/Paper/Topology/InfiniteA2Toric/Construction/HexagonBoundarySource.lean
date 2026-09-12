module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveBoundaryCellular

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex

public theorem hexagonSide_gauge (i : Fin 6) (t : unitInterval) :
    hexagonGauge (hexagonSide i t).1 = 2 / 3 := by
  have hu := (show correctedPlaneCell 0 ⊆ correctedClosedHexagon 0 by
    rw [correctedClosedHexagon_eq_planeCell]) (hexagonSide i t).property
  change hexagonGauge
    ((hexagonSide i t).1 - correctedPlaneCenter 0) ≤ 2 / 3 at hu
  have hc : correctedPlaneCenter 0 = 0 := by
    ext j
    fin_cases j <;> norm_num [correctedPlaneCenter]
  rw [hc, sub_zero] at hu
  apply le_antisymm hu
  have h₀ := (norm_le_pi_norm (hexagonSide i t).1 0).trans
    (norm_le_hexagonGauge _)
  have h₁ := (norm_le_pi_norm (hexagonSide i t).1 1).trans
    (norm_le_hexagonGauge _)
  have h₂ : |(hexagonSide i t).1 0 - (hexagonSide i t).1 1| ≤
      hexagonGauge (hexagonSide i t).1 := le_max_right _ _
  rw [hexagonSide_val] at h₀ h₁ h₂ ⊢
  fin_cases i <;>
    simp [planeVertexOffset, planeNextVertexOffset,
      Pi.add_apply, smul_eq_mul] at h₀ h₁ h₂ ⊢ <;>
    ring_nf at h₀ h₁ h₂ ⊢ <;> norm_num at h₀ h₁ h₂ ⊢ <;> assumption

public abbrev HexagonBoundary :=
  {x : Fin 2 → ℝ // hexagonGauge x = 2 / 3}

public def squareBoundaryHexagonHomeomorph :
    CWCharacteristicBoundarySphere 2 ≃ₜ HexagonBoundary :=
  (correctedHexagonHomeomorph 0).subtype (fun x ↦ by
    change x ∈ Metric.sphere 0 1 ↔
      hexagonGauge
        (correctedPlaneCenter 0 + squareToHexagonRadial x) = 2 / 3
    have hc : correctedPlaneCenter 0 = 0 := by
      ext j
      fin_cases j <;> norm_num [correctedPlaneCenter]
    rw [hc, zero_add, hexagonGauge_squareToHexagonRadial,
      Metric.mem_sphere, dist_zero_right]
    constructor <;> intro h <;> nlinarith)

public def hexagonBoundaryVertex (i : Fin 6) : HexagonBoundary :=
  ⟨planeVertexOffset i, by
    have h := hexagonSide_gauge i 0
    simpa [hexagonSide_val] using h⟩

public def hexagonBoundarySidePath (i : Fin 6) :
    Path (hexagonBoundaryVertex i)
      (hexagonBoundaryVertex (cellNextIndex i)) where
  toFun t := ⟨(hexagonSide i t).1, hexagonSide_gauge i t⟩
  continuous_toFun := (continuous_subtype_val.comp
    (continuous_hexagonSide i)).subtype_mk _
  source' := by
    apply Subtype.ext
    simp [hexagonSide_val, hexagonBoundaryVertex]
  target' := by
    apply Subtype.ext
    simp [hexagonSide_val, hexagonBoundaryVertex,
      planeNextVertexOffset]

public def hexagonBoundaryLoop :
    Path (hexagonBoundaryVertex 0) (hexagonBoundaryVertex 0) :=
  (((((hexagonBoundarySidePath 0).trans
    (hexagonBoundarySidePath 1)).trans
    (hexagonBoundarySidePath 2)).trans
    (hexagonBoundarySidePath 3)).trans
    (hexagonBoundarySidePath 4)).trans
    (hexagonBoundarySidePath 5)

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
