module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexMaps
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

/-! # Actual affine singular simplices and their original faces -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual barycentric affine simplex with the specified ordered vertices. -/
def affineSimplexMap {ι : Type*} [Fintype ι] (v : ι → E) : C(Convexity.StdSimplex ℝ ι, E) :=
  ⟨fun t => ∑ i, t.weights i • v i,
    continuous_finsetSum _ (fun i _ =>
      (Convexity.StdSimplex.continuous_weights_apply ℝ i).smul continuous_const)⟩

/-- Its original barycentric vertex evaluates to the specified vertex. -/
theorem affineSimplexMap_vertex {ι : Type*} [Fintype ι]
    (v : ι → E) (i : ι) : affineSimplexMap v (Convexity.StdSimplex.single i) = v i := by
  classical
  change ∑ j, (Finsupp.single i (1 : ℝ)) j • v j = v i
  simp [Finsupp.single_apply]

/-- Every point of the actual affine simplex lies in the convex hull of
its original vertices. -/
theorem affineSimplexMap_mem_convexHull {ι : Type*} [Fintype ι] (v : ι → E)
    (t : Convexity.StdSimplex ℝ ι) : affineSimplexMap v t ∈ convexHull ℝ (range v) :=
  (convex_convexHull ℝ (range v)).sum_mem (fun i _ => t.weights_nonneg i) t.total_of_fintype
    (fun i _ => subset_convexHull ℝ (range v) ⟨i, rfl⟩)

/-- The affine simplex respects the original barycentric pushforward for
every map of its finite vertex sets. -/
theorem affineSimplexMap_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (v : κ → E) (t : Convexity.StdSimplex ℝ ι) :
    affineSimplexMap v (Convexity.StdSimplex.map f t) = affineSimplexMap (v ∘ f) t := by
  classical
  change (∑ j, (t.weights.mapDomain f) j • v j) = ∑ i, t.weights i • v (f i)
  calc
    (∑ j, (t.weights.mapDomain f) j • v j) =
        (t.weights.mapDomain f).sum (fun j r => r • v j) :=
      (Finsupp.sum_fintype (t.weights.mapDomain f) (fun j r => r • v j)
        (fun _ => zero_smul ℝ _)).symm
    _ = t.weights.sum (fun i r => r • v (f i)) :=
      Finsupp.sum_mapDomain_index (fun _ => zero_smul ℝ _) (fun _ _ _ => add_smul _ _ _)
    _ = ∑ i, t.weights i • v (f i) := Finsupp.sum_fintype _ _ (by simp)

/-- The same affine map as an original singular simplex. -/
def affineSingularSimplex (n : ℕ) (v : Fin (n + 1) → E) : integralSingularSimplex n E :=
  (integralSingularSimplexEquiv n E).symm (affineSimplexMap v)

/-- Its original ordered face deletes exactly that same vertex. -/
theorem affineSingularSimplex_face (n : ℕ) (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of E)).δ i (affineSingularSimplex (n + 1) v) =
      affineSingularSimplex n (v ∘ i.succAbove) := by
  apply (integralSingularSimplexEquiv n E).injective
  apply ContinuousMap.ext
  intro t
  change (TopCat.of E).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of E)).δ i
    (affineSingularSimplex (n + 1) v)) t = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv (n + 1) E
    ((integralSingularSimplexEquiv (n + 1) E).symm (affineSimplexMap v))
      (Convexity.StdSimplex.map i.succAbove t) =
    integralSingularSimplexEquiv n E ((integralSingularSimplexEquiv n E).symm
      (affineSimplexMap (v ∘ i.succAbove))) t
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact affineSimplexMap_map i.succAbove v t

end DifferentialGeometry.Topology
