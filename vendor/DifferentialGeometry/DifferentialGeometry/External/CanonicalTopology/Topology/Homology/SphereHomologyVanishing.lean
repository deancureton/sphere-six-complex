module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology

@[expose] public section

/-! # Original sphere homology vanishes outside its dimension -/

noncomputable section

open Metric Module

universe u

namespace DifferentialGeometry.Topology

/-- In every positive degree different from the sphere dimension, the
ORIGINAL integral singular homology vanishes. The proof reduces the actual
two-chart pair sequence to the lower sphere, with the computed reduced-H0
base and totally disconnected zero-sphere termination. -/
theorem integralSphereHomology_subsingleton (n k : ℕ) (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : finrank ℝ E = n + 1) (hk : k ≠ 0) (hkn : k ≠ n) :
    Subsingleton (integralSingularHomology k (sphere (0 : E) 1)) := by
  induction n generalizing E k with
  | zero =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      let := oneDimUnitSphere_finite hd v
      exact integralSingularHomology_subsingleton_of_totallyDisconnected k hk _
  | succ n ih =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      have hp := unitSpherePoleHyperplane_finrank (n + 1) hd (-v)
      cases k with
      | zero => exact (hk rfl).elim
      | succ k =>
          cases k with
          | zero =>
              let := unitSphere_pathConnected_of_finrank (E := E) (by omega)
              let := unitSphere_pathConnected_of_finrank
                (E := (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ) (by omega)
              let := integralReducedZero_subsingleton
                (X := sphere (0 : (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ) 1)
              exact ⟨fun a b => (integralSphereHomologyOneReducedEquiv v).injective
                (Subsingleton.elim _ _)⟩
          | succ k =>
              let := ih (k + 1) (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ hp (by omega) (by omega)
              exact ⟨fun a b => (integralSphereHomologyShiftEquiv k v).injective
                (Subsingleton.elim _ _)⟩

end DifferentialGeometry.Topology
