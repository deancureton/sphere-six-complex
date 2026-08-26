module

public import SphereSixComplex.Final
public import ChallengeAxioms

open scoped ContDiff Manifold

open SphereSixComplex

/-- Comparator wrapper around the completed project theorem. -/
public theorem sphere_six_admits_complex_structure : AdmitsComplexStructure SixSphere := by
  exact SphereSixComplex.sphere_six_admits_complex_structure

/--
Does the 6-sphere admit a complex structure, i.e. an atlas of holomorphically compatible charts
relating it to `EuclideanSpace ℂ (Fin 3)`?

The project theorem is stronger in two ways: its atlas is smooth to all orders, and it is
compatible with the standard smooth structure. Forgetting both gives the statement below.
-/
public theorem mathoverflow_1973 :
    ∃ atlas : ChartedSpace ComplexModel (unitSphere 6),
      @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance
        ComplexModel inferInstance 𝓘(ℂ, ComplexModel) 1
        (unitSphere 6) inferInstance atlas := by
  obtain ⟨c, hc, -⟩ := SphereSixComplex.sphere_six_admits_complex_structure
  refine ⟨c, ?_⟩
  letI : ChartedSpace ComplexModel (unitSphere 6) := c
  letI : IsManifold 𝓘(ℂ, ComplexModel) ∞ (unitSphere 6) := hc
  infer_instance
