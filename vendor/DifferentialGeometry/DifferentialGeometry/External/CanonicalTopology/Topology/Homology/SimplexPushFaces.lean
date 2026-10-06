module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexEvaluation
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LiftedFaces

@[expose] public section

/-! # Exact ordered-face compatibility for original simplex chain evaluation -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Evaluation of an original face is evaluation of the same original
simplex after its actual ordered barycentric face inclusion. -/
theorem singularSimplexEvaluation_face (n : ℕ) (σ : integralSingularSimplex (n + 1) X)
    (i : Fin (n + 2)) :
    singularSimplexEvaluation n ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      (singularSimplexEvaluation (n + 1) σ).comp (liftedSimplexBodyMap n (n + 1) i.succAbove) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := (liftedSimplexHomeomorph.{u} n).surjective z
  simp only [ContinuousMap.comp_apply, liftedSimplexBodyMap_apply]
  change integralSingularSimplexEquiv n X _
      ((liftedSimplexHomeomorph.{u} n).symm (liftedSimplexHomeomorph.{u} n t)) =
    integralSingularSimplexEquiv (n + 1) X σ
      ((liftedSimplexHomeomorph.{u} (n + 1)).symm
        (liftedSimplexHomeomorph.{u} (n + 1) (Convexity.StdSimplex.map i.succAbove t)))
  simp only [Homeomorph.symm_apply_apply]
  exact TopCat.toSSetObjEquiv_δ_apply σ i t

/-- Pushing through an original face equals pushing its original carrier
image through the same simplex, in every chain degree. -/
theorem singularSimplexChainPush_face (n k : ℕ) (σ : integralSingularSimplex (n + 1) X)
    (i : Fin (n + 2)) (c : integralSingularChainsIn k (liftedSimplexBody.{u} n)) :
    singularSimplexChainPush (n + 1) k σ
      (singularCarrierMap k ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
        (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
          (liftedSimplexLinearMap_body n (n + 1) i.succAbove) c) =
      singularSimplexChainPush n k ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) c := by
  unfold singularSimplexChainPush
  rw [LinearMap.comp_apply, integralSingularChainRestriction_map, LinearMap.comp_apply]
  have hmap : integralSingularChainMap
      (singularSimplexEvaluation n ((TopCat.toSSet.obj (TopCat.of X)).δ i σ)) =
        integralSingularChainMap (liftedSimplexBodyMap n (n + 1) i.succAbove) ≫
          integralSingularChainMap (singularSimplexEvaluation (n + 1) σ) := by
    rw [singularSimplexEvaluation_face, integralSingularChainMap_comp]
  exact (congrArg (fun h : integralSingularChains (liftedSimplexBody.{u} n) ⟶ integralSingularChains X =>
    h.f k (integralSingularChainRestriction k (liftedSimplexBody n) c)) hmap).symm

end DifferentialGeometry.Topology
