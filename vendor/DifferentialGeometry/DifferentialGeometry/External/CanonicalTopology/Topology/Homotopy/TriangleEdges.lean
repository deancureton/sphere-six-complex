module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.PlaneTriangle
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-! # The actual three edges of the original planar triangle -/

noncomputable section

open Set Function
open scoped Topology

namespace DifferentialGeometry.Topology

/-- A point in the triangle is on its frontier precisely when one of its
three affine defining inequalities is an equality. -/
theorem planeTriangle_mem_frontier_iff (z : ℂ) :
    z ∈ frontier planeTriangle ↔ z ∈ planeTriangle ∧
      (z.re = 0 ∨ z.im = 0 ∨ z.re + z.im = 1) := by
  constructor
  · intro hz
    exact ⟨isClosed_planeTriangle.frontier_subset hz, planeTriangle_frontier_edges hz⟩
  · rintro ⟨hz, he⟩
    rw [frontier, isClosed_planeTriangle.closure_eq]
    refine ⟨hz, ?_⟩
    intro hi
    rcases he with hr | hi0 | hsum
    · have ho : IsOpenMap Complex.re := Complex.reLm.isOpenMap_of_finiteDimensional
        (fun r => ⟨(r : ℂ), by simp⟩)
      have hm : z ∈ interior (Complex.re ⁻¹' Ici 0) := interior_mono (fun _ h => h.1) hi
      have hc := ho.interior_preimage_subset_preimage_interior hm
      simp only [mem_preimage, interior_Ici, mem_Ioi, hr, lt_self_iff_false] at hc
    · have ho : IsOpenMap Complex.im := Complex.imLm.isOpenMap_of_finiteDimensional
        (fun r => ⟨(r : ℂ) * Complex.I, by simp⟩)
      have hm : z ∈ interior (Complex.im ⁻¹' Ici 0) := interior_mono (fun _ h => h.2.1) hi
      have hc := ho.interior_preimage_subset_preimage_interior hm
      simp only [mem_preimage, interior_Ici, mem_Ioi, hi0, lt_self_iff_false] at hc
    · have ho : IsOpenMap (fun z : ℂ => z.re + z.im) :=
        (Complex.reLm + Complex.imLm).isOpenMap_of_finiteDimensional
          (fun r => ⟨(r : ℂ), by simp⟩)
      have hm : z ∈ interior ((fun z : ℂ => z.re + z.im) ⁻¹' Iic 1) :=
        interior_mono (fun _ h => h.2.2) hi
      have hc := ho.interior_preimage_subset_preimage_interior hm
      simp only [mem_preimage, interior_Iic, mem_Iio, hsum, lt_self_iff_false] at hc

/-- The edge coordinates are ordered by their missing barycentric vertex:
edge 12, edge 02, and edge 01. -/
def planeTriangleEdgeValue (i : Fin 3) (s : unitInterval) : ℂ :=
  ![((1 - s.val : ℝ) : ℂ) + (s.val : ℂ) * Complex.I,
    (s.val : ℂ) * Complex.I, (s.val : ℂ)] i

/-- Each original edge parametrization lies on the same actual frontier. -/
theorem planeTriangleEdgeValue_mem (i : Fin 3) (s : unitInterval) :
    planeTriangleEdgeValue i s ∈ frontier planeTriangle := by
  rw [planeTriangle_mem_frontier_iff]
  fin_cases i
  · simpa [planeTriangleEdgeValue, planeTriangle] using And.intro s.property.2 s.property.1
  · simpa [planeTriangleEdgeValue, planeTriangle] using And.intro s.property.1 s.property.2
  · simpa [planeTriangleEdgeValue, planeTriangle] using And.intro s.property.1 s.property.2

/-- The actual closed-interval parametrizations of the three edges. -/
def planeTriangleEdge (i : Fin 3) : C(unitInterval, frontier planeTriangle) :=
  ⟨fun s => ⟨planeTriangleEdgeValue i s, planeTriangleEdgeValue_mem i s⟩, by
    apply Continuous.subtype_mk
    fin_cases i
    · exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_subtype_val)).add
        ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
    · exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const
    · exact Complex.continuous_ofReal.comp continuous_subtype_val⟩

end DifferentialGeometry.Topology
