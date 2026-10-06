module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SpherePuncture
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractibleCoverOne

@[expose] public section

/-! # Dimension shift for the original singular homology of a sphere -/

noncomputable section

open CategoryTheory ContinuousMap Set Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual intersection of the two pole complements is homotopy
 equivalent to the unit sphere in the pole's orthogonal hyperplane. -/
def spherePoleIntersectionHomotopyEquiv (v : sphere (0 : E) 1) :
    subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ ≃ₕ
      sphere (0 : (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ) 1 :=
  (sphereDoublePunctureHomeomorph v).toHomotopyEquiv.trans
    (puncturedSpaceSphereHomotopyEquiv _)

/-- Original sphere homology shifts down one degree to the same original
lower-dimensional sphere. The map uses the actual relative connecting
homomorphism, excision, stereographic projection and radial normalization. -/
def integralSphereHomologyShiftEquiv (n : ℕ) (v : sphere (0 : E) 1) :
    integralSingularHomology (n + 2) (sphere (0 : E) 1) ≃ₗ[ℤ]
      integralSingularHomology (n + 1) (sphere (0 : (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ) 1) := by
  letI := spherePuncture_contractible v
  letI := spherePuncture_contractible (-v)
  exact (integralHomologyContractibleCoverEquiv n {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)).trans
      (integralSingularHomologyHomotopyEquiv (n + 1) (spherePoleIntersectionHomotopyEquiv v))

/-- Degree one is the actual kernel of the inclusion on H0 of the same
intersection, with no generator or homology computation assumed. -/
def integralSphereHomologyOneKernelEquiv [PathConnectedSpace (sphere (0 : E) 1)]
    (v : sphere (0 : E) 1) :
    integralSingularHomology 1 (sphere (0 : E) 1) ≃ₗ[ℤ]
      LinearMap.ker (integralSingularHomologyMap 0
        (singularSubspaceInclusion (subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ))) := by
  letI := spherePuncture_contractible v
  letI := spherePuncture_contractible (-v)
  exact integralHomologyOneContractibleCoverEquiv {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)

end DifferentialGeometry.Topology
