module

public import SphereSixComplex.Paper.Topology.ConstructedA2HexagonPuncturedHomotopy

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex

public theorem puncturedPlane_normalize_mem_sphere (x : PuncturedRealPlane) :
    ‖x.1‖⁻¹ • x.1 ∈ Metric.sphere 0 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul]
  simp [norm_ne_zero_iff.mpr x.2]

public def puncturedPlaneToSquareBoundary : ContinuousMap PuncturedRealPlane
    (CWCharacteristicBoundarySphere 2) :=
  ⟨fun x ↦ ⟨‖x.1‖⁻¹ • x.1, puncturedPlane_normalize_mem_sphere x⟩,
    (((continuous_norm.comp continuous_subtype_val).inv₀
      (fun x ↦ norm_ne_zero_iff.mpr x.2)).smul continuous_subtype_val).subtype_mk
        puncturedPlane_normalize_mem_sphere⟩

namespace Geometry.InfiniteA2Toric

public theorem constructedA2Hexagon_radial_to_square (z : ConstructedA2HexagonBoundary) :
    puncturedPlaneToSquareBoundary (constructedA2HexagonBoundaryToPunctured z) =
      constructedA2SquareBoundaryHexagonHomeomorph.symm z := by
  apply Subtype.ext
  change ‖z.1‖⁻¹ • z.1 =
    constructedA2HexagonToSquareRadial (z.1 - constructedA2CorrectedPlaneCenter 0)
  have hc : constructedA2CorrectedPlaneCenter 0 = 0 := by
    ext j
    fin_cases j <;> norm_num [constructedA2CorrectedPlaneCenter]
  rw [hc, sub_zero, constructedA2HexagonToSquareRadial, z.2]
  congr 1
  field_simp

public theorem constructedA2Hexagon_radial_to_square_map :
    puncturedPlaneToSquareBoundary.comp constructedA2HexagonBoundaryToPunctured =
      (⟨constructedA2SquareBoundaryHexagonHomeomorph.symm,
        constructedA2SquareBoundaryHexagonHomeomorph.symm.continuous⟩ : ContinuousMap _ _) := by
  apply ContinuousMap.ext
  intro z
  exact constructedA2Hexagon_radial_to_square z

end Geometry.InfiniteA2Toric
end SphereSixComplex
