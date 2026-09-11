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
public theorem exists_simplyConnected_complexThreefold :
    ∃ X : ComplexThreefold, SimplyConnectedSpace X.Carrier ∧
      ∀ k : ℕ, Nonempty
        (IntegralSingularHomology k X.Carrier ≃+ IntegralSingularHomology k SixSphere) := by
  let P := Geometry.chosenPaperAnalyticData
  exact ⟨P.compactComplexStar.toComplexThreefold,
    P.star_simplyConnectedSpace, P.star_nonempty_homologyEquiv_sixSphere⟩

/-- The underlying real manifold of a compact complex threefold is diffeomorphic to standard S⁶. -/
public theorem exists_complex_threefold_diffeomorphic_sixSphere :
    ∃ X : ComplexThreefold,
      Nonempty (Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X.Carrier SixSphere ∞) := by
  obtain ⟨X, hπ, hH⟩ := exists_simplyConnected_complexThreefold
  let := hπ
  exact ⟨X, SmoothSixSphere.nonempty_diffeomorph hH⟩

/-- The construction already yields a complex atlas on the topological six-sphere. -/
public theorem sixSphere_admits_topological_complex_structure :
    AdmitsTopologicalComplexStructure SixSphere := by
  obtain ⟨X, ⟨d⟩⟩ := exists_complex_threefold_diffeomorphic_sixSphere
  let _ : TopologicalSpace X.Carrier := X.topology
  let _ : ChartedSpace ComplexModel X.Carrier := X.charts
  let _ : IsManifold 𝓘(ℂ, ComplexModel) ∞ X.Carrier := X.manifold
  let _ : ChartedSpace RealModel X.Carrier := underlyingRealChartedSpace X.charts
  exact admitsTopologicalComplexStructure_of_homeomorph d.toHomeomorph

/-- A threefold satisfying the construction contract gives the standard six-sphere a complex
structure. -/
public theorem sphere_six_admits_complex_structure : AdmitsComplexStructure SixSphere := by
  obtain ⟨X, ⟨d⟩⟩ := exists_complex_threefold_diffeomorphic_sixSphere
  let _ : TopologicalSpace X.Carrier := X.topology
  exact admitsComplexStructure_of_diffeomorph X.charts X.manifold X.realManifold d

end SphereSixComplex
