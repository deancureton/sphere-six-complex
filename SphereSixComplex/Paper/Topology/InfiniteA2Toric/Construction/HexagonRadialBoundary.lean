module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HexagonPuncturedHomotopy

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
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
namespace Construction


public theorem hexagon_radial_to_square (z : HexagonBoundary) :
    puncturedPlaneToSquareBoundary (hexagonBoundaryToPunctured z) =
      squareBoundaryHexagonHomeomorph.symm z := by
  apply Subtype.ext
  change ‖z.1‖⁻¹ • z.1 =
    hexagonToSquareRadial (z.1 - correctedPlaneCenter 0)
  have hc : correctedPlaneCenter 0 = 0 := by
    ext j
    fin_cases j <;> norm_num [correctedPlaneCenter]
  rw [hc, sub_zero, hexagonToSquareRadial, z.2]
  congr 1
  field_simp


end Construction

end Geometry.InfiniteA2Toric
end SphereSixComplex
