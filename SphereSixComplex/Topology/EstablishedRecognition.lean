module

public import SphereSixComplex.Topology.EstablishedClassicalRecognitionFoundations
public import SphereSixComplex.Topology.HomologyToHomotopySixSphereProof
public import SphereSixComplex.Topology.SphereLoopContraction

/-!
# Established six-sphere recognition inputs

This module derives recognition of a smooth integral homology six-sphere from the four exact
classical inputs isolated in `EstablishedClassicalRecognitionFoundations`: higher Hurewicz,
compact-manifold CW type, simply connected homological Whitehead, and smooth Poincare in dimension
six. No paper-specific construction claim is assumed here.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- A simply connected smooth integral homology six-sphere is a homotopy sphere. -/
public theorem establishedHomologyToHomotopySixSphere
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    HomologyToHomotopySixSphereObligation X := by
  intro hX
  let _ : SimplyConnectedSpace X := hX.simplyConnected
  have hGenerator : HasTopDimensionalSphericalGenerator X := by
    exact establishedHigherHurewiczSixGenerator X
      (fun n hn₀ hn₆ ↦ hX.integralHomologyVanishing n
        (Nat.ne_of_gt hn₀) (Nat.ne_of_lt hn₆))
      hX.integralHomologyDegreeSix
  let _ : IsManifold 𝓘(ℝ, RealModel) ∞ X := hX.isManifold
  let _ : CompactSpace X := hX.compact
  have hCWX : HasClassicalCWType X :=
    establishedCompactSmoothSixManifoldClassicalCWType X
  have hWhitehead : ClassicalCWIntegralHomologyWhiteheadProperty SixSphere X := by
    let _ : SimplyConnectedSpace SixSphere := sixSphere_simplyConnected
    exact establishedSimplyConnectedClassicalCWIntegralHomologyWhitehead SixSphere X
  exact homotopyEquivSixSphere_of_sphericalGenerator_of_classicalCWWhitehead
    establishedSixSpherePositiveHomologyInputs hX.integralHomology hGenerator hCWX hWhitehead

/-- **Smooth recognition of integral homology six-spheres.** Every smooth, closed, connected,
simply connected integral homology six-sphere is diffeomorphic to the standard six-sphere. -/
public theorem establishedSmoothIntegralHomologySixSphereRecognition
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    SmoothSixSphereRecognitionObligation X := by
  intro hX
  let _ : IsManifold 𝓘(ℝ, RealModel) ∞ X := hX.isManifold
  let _ : CompactSpace X := hX.compact
  exact establishedSmoothPoincareSixStandardModel X
    (establishedHomologyToHomotopySixSphere hX)

/-- Smale's generalized topological Poincare theorem in dimension six. -/
public theorem establishedGeneralizedTopologicalPoincareSix :
    GeneralizedTopologicalPoincareSix :=
  generalizedTopologicalPoincareSix_of_smoothPoincareSixStandardModel
    establishedSmoothPoincareSixStandardModel

/-- The h-cobordism theorem and the Kervaire--Milnor computation `Theta_6 = 0`, stated as their
exact consequence for unoriented smooth structures on a topological six-sphere. -/
public theorem establishedMarkedSmoothSixSphereClassesTrivial :
    MarkedSmoothSixSphere.DiffeomorphismClassesTrivial :=
  markedSmoothSixSphereClassesTrivial_of_smoothPoincareSixStandardModel
    establishedSmoothPoincareSixStandardModel

/-- The standard-model consequence recovers smooth Poincare in dimension six. -/
public theorem establishedSmoothPoincareSix
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    SmoothHomotopySixSphere X → SmoothDiffeomorphicToSixSphere X := by
  intro hX
  let _ : CompactSpace X := hX.compact
  let _ : IsManifold 𝓘(ℝ, RealModel) ∞ X := hX.isManifold
  exact smoothPoincareSixStandardModel_of_classicalStages
    establishedGeneralizedTopologicalPoincareSix
    establishedMarkedSmoothSixSphereClassesTrivial X hX.homotopyEquiv

/-- The combined established theorem gives the exact smooth-recognition obligation used by the
construction through the two legacy interfaces. -/
public theorem establishedSmoothSixSphereRecognition
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    SmoothSixSphereRecognitionObligation X := by
  intro hX
  exact establishedSmoothPoincareSix
    { toCompactConnectedSmoothSixManifold := hX.toCompactConnectedSmoothSixManifold
      homotopyEquiv := establishedHomologyToHomotopySixSphere hX }

end SphereSixComplex
