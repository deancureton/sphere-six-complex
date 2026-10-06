module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereRank

@[expose] public section

/-! # Original top-dimensional integral sphere homology -/

noncomputable section

open Metric Module

universe u

namespace DifferentialGeometry.Topology

/-- The original integral homology in the dimension of a positive-dimensional
sphere is Z. This is proved by the actual excision dimension shift, terminating
at the computed normalized two-point augmentation kernel. No sphere homology
value or fundamental class is an input. -/
def integralSphereTopHomologyEquiv (n : ℕ) (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : finrank ℝ E = n + 2) :
    integralSingularHomology (n + 1) (sphere (0 : E) 1) ≃ₗ[ℤ] ℤ := by
  induction n generalizing E with
  | zero =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      letI := unitSphere_pathConnected_of_finrank (E := E) (by omega)
      exact (integralSphereHomologyOneReducedEquiv v).trans
        (integralZeroSphereReducedEquiv (unitSpherePoleHyperplane_finrank 1 hd (-v)))
  | succ n ih =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      exact (integralSphereHomologyShiftEquiv n v).trans
        (ih (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ
          (unitSpherePoleHyperplane_finrank (n + 2) (by omega) (-v)))

end DifferentialGeometry.Topology
