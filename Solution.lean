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

Transporting the constructed complex atlas along a homeomorphism proves this statement
without the smooth Poincare theorem needed for compatibility with the standard real atlas.
-/
public theorem mathoverflow_1973 :
    ∃ atlas : ChartedSpace ComplexModel (unitSphere 6),
      @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance
        ComplexModel inferInstance 𝓘(ℂ, ComplexModel) 1
        (unitSphere 6) inferInstance atlas := by
  obtain ⟨X, hπ, hH⟩ := exists_complexThreefold_simplyConnected_homologyEquiv_sixSphere
  have hX : SmoothSimplyConnectedIntegralHomologySixSphere X.Carrier :=
    { isManifold := inferInstance
      compact := inferInstance
      connected := inferInstance
      integralHomology := hH
      simplyConnected := hπ }
  obtain ⟨e⟩ := hX.nonempty_homeomorph
  refine ⟨transportChartedSpace (H := ComplexModel) e, ?_⟩
  exact isManifold_transportChartedSpace (I := 𝓘(ℂ, ComplexModel)) (n := 1) e
