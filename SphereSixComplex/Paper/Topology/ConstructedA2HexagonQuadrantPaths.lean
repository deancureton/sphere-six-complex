module

public import SphereSixComplex.Paper.Topology.ConstructedA2HexagonBoundarySource
public import SphereSixComplex.Prerequisites.Topology.QuarterCirclePathComparison

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
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

public def constructedA2HexagonSideQuadrant : Fin 6 → Fin 4 := ![0, 0, 1, 2, 2, 3]
public def constructedA2HexagonQuadrantVertex : Fin 4 → Fin 6 := ![0, 2, 3, 5]
public def constructedA2NextQuadrant : Fin 4 → Fin 4 := ![1, 2, 3, 0]

public theorem constructedA2HexagonSide_mem_quadrant (i : Fin 6) (t : unitInterval) :
    0 < quadrantFunctional (constructedA2HexagonSideQuadrant i) (constructedA2HexagonSide i t).1 := by
  rw [constructedA2HexagonSide_val]
  fin_cases i <;>
    simp [constructedA2HexagonSideQuadrant, quadrantFunctional,
      constructedA2PlaneVertexOffset, constructedA2PlaneNextVertexOffset] <;>
    nlinarith [t.property.1, t.property.2]

public def constructedA2HexagonBoundaryQuarterPath (i : Fin 4) :
    Path (constructedA2HexagonBoundaryVertex (constructedA2HexagonQuadrantVertex i))
      (constructedA2HexagonBoundaryVertex
        (constructedA2HexagonQuadrantVertex (constructedA2NextQuadrant i))) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j ↦ Fin.elim0 j)))) i
  · exact (constructedA2HexagonBoundarySidePath 0).trans (constructedA2HexagonBoundarySidePath 1)
  · exact constructedA2HexagonBoundarySidePath 2
  · exact (constructedA2HexagonBoundarySidePath 3).trans (constructedA2HexagonBoundarySidePath 4)
  · exact constructedA2HexagonBoundarySidePath 5

public theorem constructedA2HexagonBoundaryQuarterPath_mem_quadrant (i : Fin 4) (t : unitInterval) :
    0 < quadrantFunctional i (constructedA2HexagonBoundaryQuarterPath i t).1 := by
  fin_cases i
  · exact path_trans_forall (P := fun z : ConstructedA2HexagonBoundary ↦ 0 < quadrantFunctional 0 z.1)
      (constructedA2HexagonBoundarySidePath 0)
      (constructedA2HexagonBoundarySidePath 1)
      (constructedA2HexagonSide_mem_quadrant 0) (constructedA2HexagonSide_mem_quadrant 1) t
  · exact constructedA2HexagonSide_mem_quadrant 2 t
  · exact path_trans_forall (P := fun z : ConstructedA2HexagonBoundary ↦ 0 < quadrantFunctional 2 z.1)
      (constructedA2HexagonBoundarySidePath 3)
      (constructedA2HexagonBoundarySidePath 4)
      (constructedA2HexagonSide_mem_quadrant 3) (constructedA2HexagonSide_mem_quadrant 4) t
  · exact constructedA2HexagonSide_mem_quadrant 5 t

public theorem constructedA2PlaneCirclePoint_quarter_start (i : Fin 4) :
    planeCirclePoint (2 / 3) ((i : ℝ) / 4) =
      constructedA2PlaneVertexOffset (constructedA2HexagonQuadrantVertex i) := by
  have h := planeCirclePoint_quarter (2 / 3) i.castSucc
  fin_cases i <;> norm_num [constructedA2HexagonQuadrantVertex, constructedA2PlaneVertexOffset] at h ⊢ <;> exact h

public theorem constructedA2PlaneCirclePoint_quarter_end (i : Fin 4) :
    planeCirclePoint (2 / 3) (((i : ℝ) + 1) / 4) =
      constructedA2PlaneVertexOffset
        (constructedA2HexagonQuadrantVertex (constructedA2NextQuadrant i)) := by
  have h := planeCirclePoint_quarter (2 / 3) i.succ
  fin_cases i <;> norm_num [constructedA2HexagonQuadrantVertex, constructedA2NextQuadrant,
    constructedA2PlaneVertexOffset] at h ⊢ <;> exact h

public def constructedA2HexagonPlaneQuarterPath (i : Fin 4) :
    Path (planeCirclePoint (2 / 3) ((i : ℝ) / 4))
      (planeCirclePoint (2 / 3) (((i : ℝ) + 1) / 4)) :=
  ((constructedA2HexagonBoundaryQuarterPath i).map continuous_subtype_val).cast
    (constructedA2PlaneCirclePoint_quarter_start i) (constructedA2PlaneCirclePoint_quarter_end i)

public theorem constructedA2HexagonPlaneQuarterPath_mem_quadrant (i : Fin 4) (t : unitInterval) :
    0 < quadrantFunctional i (constructedA2HexagonPlaneQuarterPath i t) :=
  constructedA2HexagonBoundaryQuarterPath_mem_quadrant i t

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
