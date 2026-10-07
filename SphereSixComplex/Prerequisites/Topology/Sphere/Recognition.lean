module

public import SphereSixComplex.Prerequisites.Topology.Sphere.SmoothRecognition
public import Wikipedia.NoExoticSixSphere.Classification
public import SphereSixComplex.Prerequisites.Topology.Sphere.HomologyRecognition
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.ModuleComparison
public import SphereSixComplex.Prerequisites.Topology.Sphere.Homology
public import SphereSixComplex.Prerequisites.Topology.Sphere.LoopContraction

/-!
# Smooth homology six-sphere recognition

The h-cobordism theorem identifies a simply connected integral homology six-sphere
with the topological sphere. Smooth six-sphere classification then supplies a
diffeomorphism for the specified smooth atlas.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- A simply connected smooth integral homology six-sphere is homeomorphic to the sphere. -/
public theorem SmoothSimplyConnectedIntegralHomologySixSphere.nonempty_homeomorph
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] (hX : SmoothSimplyConnectedIntegralHomologySixSphere X) :
    Nonempty (X ≃ₜ SixSphere) := by
  let _ : SimplyConnectedSpace X := hX.simplyConnected
  let _ : IsManifold 𝓘(ℝ, RealModel) ∞ X := hX.isManifold
  let _ : CompactSpace X := hX.compact
  obtain ⟨e⟩ := DifferentialGeometry.Topology.nonempty_homeomorph_sphere_of_homology
    (n := 6) (by omega) (M := X) (fun k hk6 hk0 ↦ by
      obtain ⟨eH⟩ := hX.integralHomology k
      have := sixSpherePositiveHomologyInputs.otherDegrees k hk0 hk6
      have : Subsingleton (IntegralSingularHomology k X) := eH.injective.subsingleton
      apply ModuleCat.isZero_iff_subsingleton.mpr
      exact (IntegralSingularComparison.homologyIso X k).addCommGroupIsoToAddEquiv.injective
        |>.subsingleton)
  exact ⟨e⟩

/-- A compact simply connected smooth six-manifold with the integral homology of the sphere
is diffeomorphic to the standard six-sphere. -/
public theorem SmoothSixSphere.nonempty_diffeomorph
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] [IsManifold 𝓘(ℝ, RealModel) ∞ X]
    [CompactSpace X] [SimplyConnectedSpace X]
    (hhomology : ∀ k, Nonempty
      (IntegralSingularHomology k X ≃+ IntegralSingularHomology k SixSphere)) :
    Nonempty (Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X SixSphere ∞) := by
  have hX : SmoothSimplyConnectedIntegralHomologySixSphere X :=
    { isManifold := inferInstance
      compact := inferInstance
      connected := inferInstance
      integralHomology := hhomology
      simplyConnected := inferInstance }
  exact NoExoticSixSphere.noExoticSixSpheres X inferInstance inferInstance inferInstance
    hX.nonempty_homeomorph

end SphereSixComplex
