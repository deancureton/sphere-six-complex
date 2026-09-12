module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCompletion
public import SphereSixComplex.Prerequisites.Topology.EstablishedRecognition

/-!
# A complex structure on the standard six-sphere

The four-piece construction produces a simply connected compact complex threefold whose
integral homology agrees degreewise with that of the six-sphere. Smooth sphere recognition
then gives a diffeomorphism, along which the complex atlas is transported.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The glued threefold is simply connected and has the integral homology of the six-sphere. -/
public theorem exists_complexThreefold_simplyConnected_homologyEquiv_sixSphere :
    ∃ X : ComplexThreefold, SimplyConnectedSpace X.Carrier ∧
      ∀ k : ℕ, Nonempty
        (IntegralSingularHomology k X.Carrier ≃+ IntegralSingularHomology k SixSphere) := by
  let P := Geometry.analyticData
  exact ⟨P.compactComplexStar.toComplexThreefold,
    P.star_simplyConnectedSpace, P.star_nonempty_homologyEquiv_sixSphere⟩

/-- There exists a compact complex threefold whose underlying real manifold is diffeomorphic
to S⁶. -/
public theorem exists_complexThreefold_nonempty_diffeomorph_sixSphere :
    ∃ X : ComplexThreefold,
      Nonempty (Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X.Carrier SixSphere ∞) := by
  obtain ⟨X, hπ, hH⟩ := exists_complexThreefold_simplyConnected_homologyEquiv_sixSphere
  let := hπ
  exact ⟨X, SmoothSixSphere.nonempty_diffeomorph hH⟩


/-- A threefold satisfying the construction contract gives the standard six-sphere a complex
structure. -/
public theorem sphere_six_admits_complex_structure : AdmitsComplexStructure SixSphere := by
  obtain ⟨X, ⟨d⟩⟩ := exists_complexThreefold_nonempty_diffeomorph_sixSphere
  let _ : TopologicalSpace X.Carrier := X.topology
  exact admitsComplexStructure_of_diffeomorph X.charts X.manifold X.realManifold d

end SphereSixComplex
