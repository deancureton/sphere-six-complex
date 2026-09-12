module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HexagonBoundarySource
public import SphereSixComplex.Prerequisites.Topology.QuarterCirclePathComparison

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex

private theorem path_trans_forall {X : Type*} [TopologicalSpace X] {x y z : X}
    {P : X → Prop} (p : Path x y) (q : Path y z)
    (hp : ∀ t, P (p t)) (hq : ∀ t, P (q t)) (t : unitInterval) : P ((p.trans q) t) := by
  have h : (p.trans q) t ∈ Set.range p ∪ Set.range q := by
    rw [← Path.trans_range]
    exact Set.mem_range_self t
  rcases h with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact hu ▸ hp u
  · exact hu ▸ hq u

namespace Construction

public def hexagonSideQuadrant : Fin 6 → Fin 4 := ![0, 0, 1, 2, 2, 3]
public def hexagonQuadrantVertex : Fin 4 → Fin 6 := ![0, 2, 3, 5]
public def nextQuadrant : Fin 4 → Fin 4 := ![1, 2, 3, 0]

public theorem hexagonSide_mem_quadrant (i : Fin 6) (t : unitInterval) :
    0 < quadrantFunctional (hexagonSideQuadrant i) (hexagonSide i t).1 := by
  rw [hexagonSide_val]
  fin_cases i <;>
    simp [hexagonSideQuadrant, quadrantFunctional,
      planeVertexOffset, planeNextVertexOffset] <;>
    nlinarith [t.property.1, t.property.2]

public def hexagonBoundaryQuarterPath (i : Fin 4) :
    Path (hexagonBoundaryVertex (hexagonQuadrantVertex i))
      (hexagonBoundaryVertex
        (hexagonQuadrantVertex (nextQuadrant i))) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j ↦ Fin.elim0 j)))) i
  · exact (hexagonBoundarySidePath 0).trans (hexagonBoundarySidePath 1)
  · exact hexagonBoundarySidePath 2
  · exact (hexagonBoundarySidePath 3).trans (hexagonBoundarySidePath 4)
  · exact hexagonBoundarySidePath 5

public theorem hexagonBoundaryQuarterPath_mem_quadrant (i : Fin 4) (t : unitInterval) :
    0 < quadrantFunctional i (hexagonBoundaryQuarterPath i t).1 := by
  fin_cases i
  · exact path_trans_forall (P := fun z : HexagonBoundary ↦ 0 < quadrantFunctional 0 z.1)
      (hexagonBoundarySidePath 0)
      (hexagonBoundarySidePath 1)
      (hexagonSide_mem_quadrant 0) (hexagonSide_mem_quadrant 1) t
  · exact hexagonSide_mem_quadrant 2 t
  · exact path_trans_forall (P := fun z : HexagonBoundary ↦ 0 < quadrantFunctional 2 z.1)
      (hexagonBoundarySidePath 3)
      (hexagonBoundarySidePath 4)
      (hexagonSide_mem_quadrant 3) (hexagonSide_mem_quadrant 4) t
  · exact hexagonSide_mem_quadrant 5 t

public theorem planeCirclePoint_quarter_start (i : Fin 4) :
    planeCirclePoint (2 / 3) ((i : ℝ) / 4) =
      planeVertexOffset (hexagonQuadrantVertex i) := by
  have h := planeCirclePoint_quarter (2 / 3) i.castSucc
  fin_cases i <;> norm_num [hexagonQuadrantVertex, planeVertexOffset] at h ⊢ <;> exact h

public theorem planeCirclePoint_quarter_end (i : Fin 4) :
    planeCirclePoint (2 / 3) (((i : ℝ) + 1) / 4) =
      planeVertexOffset
        (hexagonQuadrantVertex (nextQuadrant i)) := by
  have h := planeCirclePoint_quarter (2 / 3) i.succ
  fin_cases i <;> norm_num [hexagonQuadrantVertex, nextQuadrant,
    planeVertexOffset] at h ⊢ <;> exact h

public def hexagonPlaneQuarterPath (i : Fin 4) :
    Path (planeCirclePoint (2 / 3) ((i : ℝ) / 4))
      (planeCirclePoint (2 / 3) (((i : ℝ) + 1) / 4)) :=
  ((hexagonBoundaryQuarterPath i).map continuous_subtype_val).cast
    (planeCirclePoint_quarter_start i) (planeCirclePoint_quarter_end i)

public theorem hexagonPlaneQuarterPath_mem_quadrant (i : Fin 4) (t : unitInterval) :
    0 < quadrantFunctional i (hexagonPlaneQuarterPath i t) :=
  hexagonBoundaryQuarterPath_mem_quadrant i t

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric
