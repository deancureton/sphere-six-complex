module

public import ChallengeDefs

/-!
# The Comparator challenge statement

This module is the trusted statement boundary. Every definition the final theorem mentions is
declared in `ChallengeDefs`, which depends only on Mathlib, so the challenge can be read and
audited in full without opening any file in `SphereSixComplex/`.

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

/-- The unit `n`-sphere, defined as `Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin (n + 1))`. -/
public abbrev unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) := Metric.sphere 0 1

/--
Does the 6-sphere admit a complex structure, i.e. an atlas of holomorphically compatible charts
relating it to `EuclideanSpace ℂ (Fin 3)`?
-/
public theorem mathoverflow_1973 :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6) := by
  sorry
