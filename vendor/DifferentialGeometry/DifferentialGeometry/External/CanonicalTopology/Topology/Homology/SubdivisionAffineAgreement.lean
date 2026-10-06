module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionCarriers
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.MeshIteration

@[expose] public section

/-! # The full subdivision agrees with the geometrically shrinking affine one -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original barycentric affine parametrization extends linearly to
the lifted coordinate space; this extension retains every original vertex. -/
def liftedAffineSimplexLinearMap (n : ℕ) (v : Fin (n + 1) → E) :
    liftedSimplexSpace.{u} n →L[ℝ] E where
  toFun x := ∑ i, x.down i • v i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]
  cont := continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp Homeomorph.ulift.continuous).smul continuous_const)

/-- The same linear extension takes each original vertex to its prescribed value. -/
theorem liftedAffineSimplexLinearMap_vertex (n : ℕ) (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    liftedAffineSimplexLinearMap n v (liftedSimplexVertex n i) = v i := by
  change ∑ j, (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) j • v j = v i
  simp [Pi.single_apply]

/-- On the original body, this extension is exactly evaluation through
the SAME original affine singular simplex. -/
theorem singularSimplexEvaluation_affine (n : ℕ) (v : Fin (n + 1) → E) :
    singularSimplexEvaluation n (affineSingularSimplex n v) =
      (⟨liftedAffineSimplexLinearMap n v, (liftedAffineSimplexLinearMap n v).continuous⟩ :
        C(liftedSimplexSpace n, E)).comp (singularSubspaceInclusion (liftedSimplexBody n)) := by
  unfold singularSimplexEvaluation affineSingularSimplex
  rw [Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := (liftedSimplexHomeomorph.{u} n).surjective z
  change affineSimplexMap v
      ((liftedSimplexHomeomorph.{u} n).symm (liftedSimplexHomeomorph.{u} n t)) =
    affineSimplexMap v t
  rw [Homeomorph.symm_apply_apply]

/-- Pushing any original carrier chain through that affine simplex is
the original ambient chain map of its same linear extension. -/
theorem singularSimplexChainPush_affine (n k : ℕ) (v : Fin (n + 1) → E)
    (c : integralSingularChainsIn k (liftedSimplexBody.{u} n)) :
    singularSimplexChainPush n k (affineSingularSimplex n v) c =
      (integralSingularChainMap ⟨liftedAffineSimplexLinearMap n v,
        (liftedAffineSimplexLinearMap n v).continuous⟩).f k c.val := by
  unfold singularSimplexChainPush
  rw [singularSimplexEvaluation_affine, integralSingularChainMap_comp]
  change (integralSingularChainMap _).f k
    ((integralSingularChainMap (singularSubspaceInclusion (liftedSimplexBody n))).f k
      (integralSingularChainRestriction k (liftedSimplexBody n) c)) = _
  rw [integralSingularChainRestriction_inclusion]

/-- Full singular subdivision agrees with the original geometric affine
subdivision on every original affine simplex, including degenerate ones. -/
theorem integralSingularSubdivision_affine_simplex (n : ℕ) (v : Fin (n + 1) → E) :
    integralSingularSubdivision n (affineSingularChain n v) =
      affineSingularSubdivision n (affineSingularChain n v) := by
  change integralSingularSubdivision n (integralSimplexChain n (affineSingularSimplex n v)) = _
  rw [integralSingularSubdivision_simplex, singularSimplexChainPush_affine]
  change (integralSingularChainMap _).f n
    (affineSingularSubdivision n (affineSingularChain n (liftedSimplexVertex n))) = _
  rw [affineSingularSubdivision_linear n _ (convex_liftedSimplexBody n) (liftedSimplexChain_mem n),
    affineSingularChain_linear]
  have hv : liftedAffineSimplexLinearMap n v ∘ liftedSimplexVertex n = v :=
    funext (liftedAffineSimplexLinearMap_vertex n v)
  rw [hv]

/-- The two actual operators coincide on every original affine carrier chain. -/
theorem integralSingularSubdivision_affine (n : ℕ) (A : Set E)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    integralSingularSubdivision n c = affineSingularSubdivision n c := by
  have h : affineSingularChainsIn n A ≤
      LinearMap.ker (integralSingularSubdivision n - affineSingularSubdivision n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, _, rfl⟩
    exact sub_eq_zero.mpr (integralSingularSubdivision_affine_simplex n v)
  exact sub_eq_zero.mp (h hc)

end DifferentialGeometry.Topology
