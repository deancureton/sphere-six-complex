module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineNaturality
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

@[expose] public section

/-! # The actual standard simplex in the singular chain universe -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

/-- The standard finite coordinate space, lifted only to the target universe. -/
abbrev liftedSimplexSpace (n : ℕ) := ULift.{u} (Fin (n + 1) → ℝ)

/-- The actual barycentric simplex as a convex subset of that lifted space. -/
def liftedSimplexBody (n : ℕ) : Set (liftedSimplexSpace.{u} n) :=
  range (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
    ULift.up.{u} (t.weights : Fin (n + 1) → ℝ))

/-- Its original ordered vertices, with only the universe lift added. -/
def liftedSimplexVertex (n : ℕ) (i : Fin (n + 1)) : liftedSimplexSpace.{u} n :=
  ULift.up (Pi.single i 1)

/-- The lifted body is convex for the original real scalar action. -/
theorem convex_liftedSimplexBody (n : ℕ) : Convex ℝ (liftedSimplexBody.{u} n) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ a b ha hb hab
  refine ⟨Convexity.convexCombPair a b ha hb hab s t, ?_⟩
  apply ULift.ext
  change (⇑(Convexity.convexCombPair a b ha hb hab s t).weights) =
    a • (⇑s.weights) + b • (⇑t.weights)
  simp only [Convexity.StdSimplex.weights_convexCombPair, Finsupp.coe_add, Finsupp.coe_smul]

/-- Each lifted original vertex belongs to the same lifted body. -/
theorem liftedSimplexVertex_mem (n : ℕ) (i : Fin (n + 1)) :
    liftedSimplexVertex.{u} n i ∈ liftedSimplexBody n := by
  refine ⟨Convexity.StdSimplex.single i, ?_⟩
  apply ULift.ext
  exact Finsupp.single_eq_pi_single i (1 : ℝ)

/-- The actual original standard simplex and this body have exactly the
same points, parameters and topology, modulo the universe lift. -/
def liftedSimplexHomeomorph (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ liftedSimplexBody.{u} n :=
  ((Homeomorph.ulift : liftedSimplexSpace.{u} n ≃ₜ (Fin (n + 1) → ℝ)).symm.isEmbedding.comp
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1)))).toHomeomorph

/-- The original affine simplex on these vertices is exactly the lifted
identity parametrization of the same standard simplex. -/
theorem affineSimplexMap_liftedSimplexVertex (n : ℕ) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    affineSimplexMap (liftedSimplexVertex.{u} n) t = ULift.up t.weights := by
  apply (ULift.moduleEquiv : liftedSimplexSpace.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ)).injective
  change (ULift.moduleEquiv : liftedSimplexSpace.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
    (∑ i, t.weights i • liftedSimplexVertex n i) = t.weights
  rw [map_sum]
  simp only [map_smul]
  funext j
  simp [Finset.sum_apply, liftedSimplexVertex, Pi.single_apply]

/-- The original universal affine simplex chain lies in that same body. -/
theorem liftedSimplexChain_mem (n : ℕ) :
    affineSingularChain n (liftedSimplexVertex.{u} n) ∈ affineSingularChainsIn n (liftedSimplexBody n) :=
  affineSingularChain_mem n _ _ (liftedSimplexVertex_mem n)

end DifferentialGeometry.Topology
