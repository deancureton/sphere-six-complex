module

public import SphereSixComplex.Topology.SixSphereAntipodalReflectionHomotopy
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The coordinate reflection as an orthogonal linear reflection

This identifies the concrete reflection used in the antipodal homotopy with reflection in the
codimension-one coordinate hyperplane and computes its ambient determinant.
-/

@[expose] public section

noncomputable section

open Module Submodule

namespace SphereSixComplex

/-- The first standard unit vector in seven-dimensional Euclidean space. -/
public noncomputable def sixSphereFirstCoordinateVector :
    EuclideanSpace ℝ (Fin 7) :=
  EuclideanSpace.single 0 1

/-- The hyperplane perpendicular to the first standard unit vector. -/
public noncomputable def sixSphereCoordinateReflectionHyperplane :
    Submodule ℝ (EuclideanSpace ℝ (Fin 7)) :=
  (ℝ ∙ sixSphereFirstCoordinateVector)ᗮ

/-- Orthogonal reflection in the first-coordinate hyperplane. -/
public noncomputable def sixSphereCoordinateReflectionLinearIsometry :
    EuclideanSpace ℝ (Fin 7) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 7) :=
  sixSphereCoordinateReflectionHyperplane.reflection

public theorem sixSphereFirstCoordinateVector_norm :
    ‖sixSphereFirstCoordinateVector‖ = 1 := by
  simp [sixSphereFirstCoordinateVector]

public theorem sixSphereFirstCoordinateVector_ne_zero :
    sixSphereFirstCoordinateVector ≠ 0 := by
  intro h
  have := congrArg (fun x : EuclideanSpace ℝ (Fin 7) ↦ x 0) h
  simpa [sixSphereFirstCoordinateVector] using this

/-- The abstract orthogonal reflection agrees coordinatewise with the concrete map. -/
public theorem sixSphereCoordinateReflectionLinearIsometry_apply
    (x : EuclideanSpace ℝ (Fin 7)) :
    sixSphereCoordinateReflectionLinearIsometry x =
      sixSphereCoordinateReflectionAmbient x := by
  change ((ℝ ∙ sixSphereFirstCoordinateVector)ᗮ).reflection x =
    sixSphereCoordinateReflectionAmbient x
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply,
    sixSphereFirstCoordinateVector_norm]
  apply (EuclideanSpace.equiv (Fin 7) ℝ).injective
  funext i
  fin_cases i <;> simp [sixSphereFirstCoordinateVector,
    sixSphereCoordinateReflectionAmbient, EuclideanSpace.inner_single_left] <;> ring

/-- The ambient linear reflection has determinant `-1`. -/
public theorem sixSphereCoordinateReflectionLinearIsometry_det :
    sixSphereCoordinateReflectionLinearIsometry.toLinearEquiv.det = -1 := by
  rw [sixSphereCoordinateReflectionLinearIsometry,
    Submodule.linearEquiv_det_reflection]
  have hclosure : (ℝ ∙ sixSphereFirstCoordinateVector :
      Submodule ℝ (EuclideanSpace ℝ (Fin 7))).topologicalClosure =
        ℝ ∙ sixSphereFirstCoordinateVector := by
    exact (ℝ ∙ sixSphereFirstCoordinateVector :
      Submodule ℝ (EuclideanSpace ℝ (Fin 7))).closed_of_finiteDimensional
        |>.submodule_topologicalClosure_eq
  rw [sixSphereCoordinateReflectionHyperplane,
    Submodule.orthogonal_orthogonal_eq_closure, hclosure,
    finrank_span_singleton sixSphereFirstCoordinateVector_ne_zero]
  norm_num

end SphereSixComplex
