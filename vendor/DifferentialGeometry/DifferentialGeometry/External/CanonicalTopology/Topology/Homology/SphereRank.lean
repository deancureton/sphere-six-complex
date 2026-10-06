module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OneDimensionalSphere
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyOne
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoPointReducedZero

@[expose] public section

/-! # Finite-dimensional sphere prerequisites on the actual vector spaces -/

noncomputable section

open Set Metric Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E]

/-- Positive actual dimension supplies an actual unit vector. -/
def unitSpherePointOfFinrankPos (h : 0 < finrank ℝ E) : sphere (0 : E) 1 := by
  letI := Module.nontrivial_of_finrank_pos h
  exact ⟨(NormedSpace.sphere_nonempty (E := E) (x := 0)).mpr (by norm_num) |>.choose,
    (NormedSpace.sphere_nonempty (E := E) (x := 0)).mpr (by norm_num) |>.choose_spec⟩

/-- The actual reduced H0 of a zero-sphere is Z, with a proved two-point
model and the normalized original augmentation. -/
def integralZeroSphereReducedEquiv (hd : finrank ℝ E = 1) :
    integralReducedHomologyZero (sphere (0 : E) 1) ≃ₗ[ℤ] ℤ := by
  let v := unitSpherePointOfFinrankPos (E := E) (by omega)
  letI := oneDimUnitSphere_finite hd v
  exact integralTwoPointReducedZeroEquiv (oneDimUnitSphereEquivBool hd v)

end

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Passing to the actual pole hyperplane lowers dimension by exactly one. -/
theorem unitSpherePoleHyperplane_finrank (n : ℕ) (hd : finrank ℝ E = n + 1)
    (v : sphere (0 : E) 1) : finrank ℝ (ℝ ∙ (v : E))ᗮ = n := by
  let : Fact (finrank ℝ E = n + 1) := ⟨hd⟩
  apply Submodule.finrank_orthogonal_span_singleton
  intro h
  have hn := norm_eq_of_mem_sphere v
  rw [h, norm_zero] at hn
  norm_num at hn

/-- Dimension at least two supplies actual sphere path-connectedness. -/
theorem unitSphere_pathConnected_of_finrank (hd : 1 < finrank ℝ E) :
    PathConnectedSpace (sphere (0 : E) 1) := by
  apply unitSphere_pathConnected_of_rank
  rw [← finrank_eq_rank ℝ E]
  exact_mod_cast hd

end DifferentialGeometry.Topology
