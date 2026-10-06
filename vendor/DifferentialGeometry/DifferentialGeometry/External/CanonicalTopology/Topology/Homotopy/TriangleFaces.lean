module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.TriangleEdges

import all Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

@[expose] public section

/-! # Exact ordered barycentric faces of the original planar triangle -/

noncomputable section

open Set Function
open scoped Topology

namespace DifferentialGeometry.Topology

/-- The ordered face maps have the same interval parameter as the original
three planar edges, including all their endpoints. -/
theorem simplexTriangleHomeomorph_face (i : Fin 3) (t : Convexity.StdSimplex ℝ (Fin 2)) :
    (simplexTriangleHomeomorph (Convexity.StdSimplex.map i.succAbove t)).val =
      planeTriangleEdgeValue i (Convexity.StdSimplex.homeomorphI t) := by
  have ht := t.total_fin_two
  change (⟨(t.weights.mapDomain i.succAbove) 1,
    (t.weights.mapDomain i.succAbove) 2⟩ : ℂ) =
      planeTriangleEdgeValue i ⟨t.weights 1, _⟩
  simp only [Finsupp.mapDomain_fintype, Fin.sum_univ_two,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  fin_cases i <;> apply Complex.ext <;>
    simp [planeTriangleEdgeValue, Fin.succAbove]
  linarith

end DifferentialGeometry.Topology
