module

public import SphereSixComplex.Paper.Final
public import SphereSixComplex.Prerequisites.Geometry.NormalizedComplexStructure

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The complex atlas on standard S⁶ can be chosen with identity real comparison. -/
public theorem sixSphere_has_normalizedComplexStructure :
    Nonempty (NormalizedComplexStructure SixSphere) := by
  obtain ⟨X, ⟨d⟩⟩ := exists_complex_threefold_diffeomorphic_sixSphere
  exact normalizedComplexStructure_of_diffeomorph d

end SphereSixComplex
