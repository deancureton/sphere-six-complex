module

public import SphereSixComplex.Geometry.PaperGluingData
public import SphereSixComplex.Topology.EstablishedRecognition

/-!
# Final construction and recognition

The paper-specific gluing is assembled before the two established smooth-recognition inputs are
applied. Keeping this module downstream of `PaperAssembly` allows the existence proof to use the
actual geometric and topological construction data.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The paper-specific construction target: the explicit torus family, three fillings, and their
overlap maps provide the exact finite gluing data consumed by the assembly theorem. -/
public theorem exists_paperGluingData : Nonempty PaperGluingData := by
  sorry

/-- The verified assembly map turns the paper's gluing data into a completed threefold. -/
public theorem exists_completedPaperThreefold : Nonempty CompletedPaperThreefold :=
  exists_completedPaperThreefold_of_paperGluingData exists_paperGluingData

/-- The dimension-six smooth recognition step required for the completed paper threefold. -/
public theorem completedPaperThreefold_smoothRecognition (C : CompletedPaperThreefold) :
    letI := C.X.topology
    letI := underlyingRealChartedSpace C.X.charts
    SmoothSixSphereRecognitionObligation C.X.Carrier := by
  let _ : TopologicalSpace C.X.Carrier := C.X.topology
  let _ : ChartedSpace RealModel C.X.Carrier :=
    underlyingRealChartedSpace C.X.charts
  let _ : T2Space C.X.Carrier := C.X.t2
  let _ : SecondCountableTopology C.X.Carrier := C.X.secondCountable
  exact establishedSmoothSixSphereRecognition

/-- The minimal construction-and-recognition theorem extracted from the source's two-page summary. -/
public theorem exists_complex_threefold_diffeomorphic_sixSphere :
    ∃ X : ComplexThreefold, DiffeomorphicToSixSphere X := by
  obtain ⟨C⟩ := exists_completedPaperThreefold
  refine ⟨C.X, ?_⟩
  let _ : TopologicalSpace C.X.Carrier := C.X.topology
  let _ : ChartedSpace RealModel C.X.Carrier := underlyingRealChartedSpace C.X.charts
  exact completedPaperThreefold_smoothRecognition C C.smoothRecognitionInput

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
