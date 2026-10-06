module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.UniversalSubdivisionFaces

@[expose] public section

/-! # The same universal homotopy with its exact original boundary -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

/-- The exact identity-minus-subdivision formula for the original universal
homotopy, including its original signed face corrections in the SAME carrier. -/
theorem universalSimplexHomotopy_boundary (n : ℕ) :
    (⟨(integralSingularChains (liftedSimplexSpace.{u} (n + 1))).d (n + 2) (n + 1)
        (universalSimplexHomotopy (n + 1)).val,
      integralSingularChainsIn_boundary (n + 1) _ (universalSimplexHomotopy (n + 1)).property⟩ :
        integralSingularChainsIn (n + 1) (liftedSimplexBody (n + 1))) =
      ⟨affineSingularChain (n + 1) (liftedSimplexVertex (n + 1)),
        affineSingularChainsIn_le (n + 1) (convex_liftedSimplexBody (n + 1)) (liftedSimplexChain_mem (n + 1))⟩ -
      universalSimplexSubdivision (n + 1) -
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        singularCarrierMap (n + 1) ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
          (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
            (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexHomotopy n) := by
  apply Subtype.ext
  change (integralSingularChains (liftedSimplexSpace.{u} (n + 1))).d (n + 2) (n + 1)
      (affineSubdivisionHomotopy (n + 1) (affineSingularChain (n + 1) (liftedSimplexVertex (n + 1)))) =
    (integralSingularChainsIn (n + 1) (liftedSimplexBody (n + 1))).subtype
      (⟨affineSingularChain (n + 1) (liftedSimplexVertex (n + 1)), _⟩ -
        universalSimplexSubdivision (n + 1) - ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          singularCarrierMap (n + 1)
            ⟨liftedSimplexLinearMap n (n + 1) i.succAbove, (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
              (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexHomotopy n))
  simp only [map_sub, map_sum, map_zsmul]
  rw [affineSubdivisionHomotopy_boundary n (convex_liftedSimplexBody (n + 1)) (liftedSimplexChain_mem (n + 1))]
  change affineSingularChain (n + 1) (liftedSimplexVertex (n + 1)) -
    affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) (liftedSimplexVertex (n + 1))) -
      affineSubdivisionHomotopy n ((integralSingularChains (liftedSimplexSpace (n + 1))).d (n + 1) n
        (affineSingularChain (n + 1) (liftedSimplexVertex (n + 1)))) =
      affineSingularChain (n + 1) (liftedSimplexVertex (n + 1)) -
        affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) (liftedSimplexVertex (n + 1))) - _
  congr 1
  rw [affineSingularChain_boundary, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, universalSimplexHomotopy_face]
  rfl

end DifferentialGeometry.Topology
