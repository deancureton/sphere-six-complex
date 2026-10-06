module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SpherePuncture
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-! # The actual unit sphere of a one-dimensional real inner product space -/

noncomputable section

open Set Metric Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In dimension one, the actual unit sphere consists precisely of the
specified unit vector and its antipode. -/
theorem oneDimUnitSphere_eq_or_antipode (hd : finrank ℝ E = 1)
    (v x : sphere (0 : E) 1) : x = v ∨ x = -v := by
  let : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hd
  have hv : (v : E) ≠ 0 := by
    intro h
    have hn := norm_eq_of_mem_sphere v
    rw [h, norm_zero] at hn
    norm_num at hn
  have hspan : ℝ ∙ (v : E) = ⊤ := Submodule.eq_top_of_finrank_eq
    ((finrank_span_singleton hv).trans hd.symm)
  have hx : (x : E) ∈ ℝ ∙ (v : E) := hspan.symm ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
  have hn : |r| = 1 := by
    have h := congrArg norm hr
    simpa [norm_smul, norm_eq_of_mem_sphere v, norm_eq_of_mem_sphere x, Real.norm_eq_abs] using h
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hn with h | h
  · left
    apply Subtype.ext
    simpa [h] using hr.symm
  · right
    apply Subtype.ext
    simpa [h] using hr.symm

/-- A concrete two-point parametrization of that original sphere. -/
def oneDimUnitSphereEquivBool (hd : finrank ℝ E = 1) (v : sphere (0 : E) 1) :
    sphere (0 : E) 1 ≃ Bool := (Equiv.ofBijective (fun b : Bool => if b then -v else v) (by
  constructor
  · intro a b h
    cases a <;> cases b <;> simp_all [unitSphere_ne_antipode v, (unitSphere_ne_antipode v).symm]
  · intro x
    rcases oneDimUnitSphere_eq_or_antipode hd v x with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩)).symm

/-- This actual sphere is finite; its inherited Hausdorff topology is therefore discrete. -/
theorem oneDimUnitSphere_finite (hd : finrank ℝ E = 1) (v : sphere (0 : E) 1) :
    Finite (sphere (0 : E) 1) := Finite.of_equiv Bool (oneDimUnitSphereEquivBool hd v).symm

end DifferentialGeometry.Topology
