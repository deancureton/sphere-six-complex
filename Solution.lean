module

public import SphereSixComplex.Final

open scoped ContDiff Manifold

open SphereSixComplex

/-- Comparator wrapper around the completed project theorem. -/
public theorem sphere_six_admits_complex_structure : AdmitsComplexStructure SixSphere := by
  exact SphereSixComplex.sphere_six_admits_complex_structure

/-- The unit `n`-sphere, defined as `Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin (n + 1))`. -/
public abbrev unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) := Metric.sphere 0 1

/--
Does the 6-sphere admit a complex structure, i.e. an atlas of holomorphically compatible charts
relating it to `EuclideanSpace ℂ (Fin 3)`?

The project theorem is stronger in two ways: its atlas is smooth to all orders, and it is
compatible with the standard smooth structure. Forgetting both gives the statement below.
-/
public theorem mathoverflow_1973 :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6) := by
  obtain ⟨c, hc, -⟩ := SphereSixComplex.sphere_six_admits_complex_structure
  refine ⟨c, ?_⟩
  have hinf : IsManifold 𝓘(ℂ, ComplexModel) ∞ SixSphere := hc
  infer_instance
