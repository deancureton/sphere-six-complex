module

public import SphereSixComplex.Final

open SphereSixComplex

/-- Comparator wrapper around the completed project theorem. -/
public theorem sphere_six_admits_complex_structure : AdmitsComplexStructure SixSphere := by
  exact SphereSixComplex.sphere_six_admits_complex_structure
