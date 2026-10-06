module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyShift
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ReducedZero
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

/-! # The degree-one sphere computation uses actual reduced H0 -/

noncomputable section

open ContinuousMap Set Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Original H1 of the sphere is original reduced H0 of the lower sphere,
using the same pole charts and the normalized original augmentation. -/
def integralSphereHomologyOneReducedEquiv [PathConnectedSpace (sphere (0 : E) 1)]
    (v : sphere (0 : E) 1) :
    integralSingularHomology 1 (sphere (0 : E) 1) ≃ₗ[ℤ]
      integralReducedHomologyZero (sphere (0 : (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ) 1) := by
  letI := spherePuncture_contractible (-v)
  exact ((integralSphereHomologyOneKernelEquiv v).trans
    (integralZeroMapKernelReducedEquiv (singularSubspaceInclusion
      (subspaceIntersection ({v}ᶜ : Set (sphere (0 : E) 1)) {-v}ᶜ)))).trans
        (integralReducedZeroHomotopyEquiv (spherePoleIntersectionHomotopyEquiv v))

/-- The required path-connectedness is proved from actual vector-space
rank, rather than included as a sphere-homology hypothesis. -/
theorem unitSphere_pathConnected_of_rank (h : 1 < Module.rank ℝ E) :
    PathConnectedSpace (sphere (0 : E) 1) :=
  isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere h 0 (by norm_num))

end DifferentialGeometry.Topology
