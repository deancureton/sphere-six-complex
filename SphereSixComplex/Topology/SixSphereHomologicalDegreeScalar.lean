module

public import SphereSixComplex.Topology.SixSphereDegreeHomology

/-!
# Scalar actions and homological degree on the six-sphere

This file records that a degree calculation made with one additive orientation determines the
entire endomorphism of top homology, and hence gives the same degree for every orientation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology ContinuousMap

namespace SphereSixComplex

/-- On an infinite-cyclic top homology group, degree `z` with respect to one orientation forces
the induced endomorphism to be scalar multiplication by `z`. -/
public theorem sixSphereTopIntegralHomologyMap_eq_zsmul_id_of_degree
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ)
    (f : C(SixSphere, SixSphere)) (z : ℤ)
    (hdegree : sixSphereHomologicalDegree orientation f = z) :
    sixSphereTopIntegralHomologyMap f =
      z • AddMonoidHom.id (IntegralSingularHomology 6 SixSphere) := by
  let H := IntegralSingularHomology 6 SixSphere
  let fH : H →+ H := sixSphereTopIntegralHomologyMap f
  let fZ : ℤ →+ ℤ := orientation.toAddMonoidHom.comp
    (fH.comp orientation.symm.toAddMonoidHom)
  have hf (a : ℤ) : orientation (fH (orientation.symm a)) = a * z := by
    change fZ a = a * z
    rw [intAddHom_apply_eq_mul_apply_one]
    change a * sixSphereHomologicalDegree orientation f = a * z
    rw [hdegree]
  apply AddMonoidHom.ext
  intro x
  apply orientation.injective
  have hx := hf (orientation x)
  rw [orientation.symm_apply_apply] at hx
  simpa [mul_comm] using hx

/-- A degree computed using one additive orientation has the same value for every other additive
orientation of top homology. -/
public theorem sixSphereHomologicalDegree_allOrientations_of_one
    (orientation₀ : IntegralSingularHomology 6 SixSphere ≃+ ℤ)
    (f : C(SixSphere, SixSphere)) (z : ℤ)
    (h₀ : sixSphereHomologicalDegree orientation₀ f = z)
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ) :
    sixSphereHomologicalDegree orientation f = z := by
  rw [sixSphereHomologicalDegree,
    sixSphereTopIntegralHomologyMap_eq_zsmul_id_of_degree orientation₀ f z h₀]
  simp

end SphereSixComplex
