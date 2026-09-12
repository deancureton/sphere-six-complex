module

public import SphereSixComplex.Prerequisites.Topology.HomologySphereRecognition
public import SphereSixComplex.Prerequisites.Topology.HomologyToHomotopySixSphereProof
public import SphereSixComplex.Prerequisites.Topology.SphereLoopContraction

/-!
# Smooth homology six-sphere recognition

Higher Hurewicz, compact-manifold CW type and homological Whitehead identify a simply connected
integral homology six-sphere with the homotopy type of the sphere. The retained smooth Poincare
theorem then supplies a diffeomorphism for the specified smooth atlas.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- A simply connected smooth integral homology six-sphere is a homotopy sphere. -/
public theorem SmoothSimplyConnectedIntegralHomologySixSphere.nonempty_homotopyEquiv
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    HomologyToHomotopySixSphereObligation X := by
  intro hX
  let _ : SimplyConnectedSpace X := hX.simplyConnected
  have hGenerator : HasTopDimensionalSphericalGenerator X := by
    exact SixSphere.has_spherical_generator_of_homology X
      (fun n hn₀ hn₆ ↦ hX.integralHomologyVanishing n
        (Nat.ne_of_gt hn₀) (Nat.ne_of_lt hn₆))
      hX.integralHomologyDegreeSix
  let _ : IsManifold 𝓘(ℝ, RealModel) ∞ X := hX.isManifold
  let _ : CompactSpace X := hX.compact
  have hCWX : HasCWType X :=
    SmoothSixManifold.hasCWType X
  have hWhitehead : CWType.HomologicalWhiteheadProperty SixSphere X := by
    let _ : SimplyConnectedSpace SixSphere := sixSphere_simplyConnected
    exact CWType.homological_whitehead_property SixSphere X
  exact homotopyEquivSixSphere_of_sphericalGenerator_of_classicalCWWhitehead
    sixSpherePositiveHomologyInputs hX.integralHomology hGenerator hCWX hWhitehead


/-- The standard-model consequence recovers smooth Poincare in dimension six. -/
public theorem SmoothHomotopySixSphere.isDiffeomorphic
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    SmoothHomotopySixSphere X → SmoothSixSphere.IsDiffeomorphic X := by
  intro hX
  let _ : CompactSpace X := hX.compact
  let _ : IsManifold 𝓘(ℝ, RealModel) ∞ X := hX.isManifold
  exact SmoothSixSphere.poincare X hX.homotopyEquiv

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
  exact SmoothHomotopySixSphere.isDiffeomorphic
    { toCompactConnectedSmoothSixManifold := hX.toCompactConnectedSmoothSixManifold
      homotopyEquiv := SmoothSimplyConnectedIntegralHomologySixSphere.nonempty_homotopyEquiv hX }

end SphereSixComplex
