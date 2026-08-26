module

public import ChallengeDefs
public import ChallengeAxioms

/-!
# The Comparator challenge statement

This module is the trusted statement boundary. Every definition the final theorem mentions is
declared in `ChallengeDefs`. The established results permitted by Comparator are imported through
`ChallengeAxioms`, so Challenge and Solution share the exact same declarations.

The final theorem is stated as the existence of a complex atlas compatible with the standard smooth
structure on the six-sphere. This is stronger than the existence of an almost-complex tangent
endomorphism.

Nothing else in the repository may import this module: `Solution` reaches the same definitions
through `ChallengeDefs`, and if it also saw this file the theorem name would resolve to the sorried
statement below rather than to the proved one.
-/

open scoped ContDiff Manifold

open SphereSixComplex

/-- Trusted statement used by Comparator. -/
public theorem sphere_six_admits_complex_structure : AdmitsComplexStructure SixSphere := by
  sorry

/--
Does the 6-sphere admit a complex structure, i.e. an atlas of holomorphically compatible charts
relating it to `EuclideanSpace ℂ (Fin 3)`?
-/
public theorem mathoverflow_1973 :
    ∃ atlas : ChartedSpace ComplexModel (unitSphere 6),
      @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance
        ComplexModel inferInstance 𝓘(ℂ, ComplexModel) 1
        (unitSphere 6) inferInstance atlas := by
  sorry
