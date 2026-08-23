module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Complex Structures on the Six-Sphere

The final theorem is stated as the existence of a complex atlas on the standard topological
six-sphere. This is stronger than the existence of an almost-complex tangent endomorphism.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The standard unit six-sphere in seven-dimensional Euclidean space. -/
public abbrev SixSphere : Type := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1)

/-- The complex vector space used as the local model for a complex threefold. -/
public abbrev ComplexModel : Type := EuclideanSpace ℂ (Fin 3)

/-- A topological space admits a complex structure when it has a complex-differentiable atlas. -/
public def AdmitsComplexStructure (M : Type*) [TopologicalSpace M] : Prop :=
  ∃ c : ChartedSpace ComplexModel M,
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel inferInstance
      𝓘(ℂ, ComplexModel) 1 M inferInstance c

/-- The standard six-sphere admits an integrable complex structure. -/
public theorem sphere_six_admits_complex_structure : AdmitsComplexStructure SixSphere := by
  sorry

end SphereSixComplex
