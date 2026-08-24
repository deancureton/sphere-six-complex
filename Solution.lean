module

public import SphereSixComplex.Topology.NormalizedComplexStructure

open SphereSixComplex

/-- Comparator wrapper around the completed project theorem. -/
public theorem sphere_six_admits_complex_structure : AdmitsComplexStructure SixSphere := by
  obtain ⟨c⟩ := SphereSixComplex.sixSphere_has_normalizedComplexStructure
  exact c.toAdmitsComplexStructure
