module

public import SphereSixComplex.Topology.SmoothRecognition
public import SphereSixComplex.Topology.SmoothSixSphereClassification
public import SphereSixComplex.Topology.SphereLoopContraction

/-!
# Established six-sphere recognition inputs

This module isolates the classical external theorem used to recognize a smooth integral homology
six-sphere. It is an explicit axiom because its proof is not yet available in Mathlib. The two
formerly separate Hurewicz--Whitehead and smooth Poincare interfaces are derived from the single
standard recognition theorem; no paper-specific construction claim is assumed here.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

private theorem recognition_pathConnectedSpace_of_homotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) : PathConnectedSpace X where
  nonempty := ⟨e.symm (Classical.choice (inferInstance : Nonempty Y))⟩
  joined x y := ⟨(e.left_inv.some.evalAt x).symm.trans
    ((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous) |>.trans
      (e.left_inv.some.evalAt y)⟩

/-- **Smooth recognition of integral homology six-spheres.** Every smooth, closed, connected,
simply connected integral homology six-sphere is diffeomorphic to the standard six-sphere.

This combines the finite-CW/Hurewicz/Whitehead argument, Smale's generalized Poincare theorem,
smooth h-cobordism, and the Kervaire--Milnor computation `Theta_6 = 0`. -/
public axiom establishedSmoothIntegralHomologySixSphereRecognition
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    SmoothSixSphereRecognitionObligation X

/-- A simply connected smooth integral homology six-sphere is a homotopy sphere. -/
public theorem establishedHomologyToHomotopySixSphere
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    HomologyToHomotopySixSphereObligation X := by
  intro hX
  obtain ⟨d⟩ := establishedSmoothIntegralHomologySixSphereRecognition hX
  exact ⟨d.toHomeomorph.toHomotopyEquiv⟩

/-- The standard-model smooth Poincare theorem in dimension six. -/
public theorem establishedSmoothPoincareSixStandardModel :
    SmoothPoincareSixStandardModel := by
  intro M _ _ _ _ _ _ hHomotopy
  obtain ⟨e⟩ := hHomotopy
  let _ : PathConnectedSpace SixSphere := sixSphere_pathConnectedSpace
  let _ : PathConnectedSpace M := recognition_pathConnectedSpace_of_homotopyEquiv e
  let hM : SmoothHomotopySixSphere M :=
    { isManifold := inferInstance
      compact := inferInstance
      connected := inferInstance
      homotopyEquiv := ⟨e⟩ }
  let _ : SimplyConnectedSpace SixSphere := sixSphere_simplyConnected
  let _ : SimplyConnectedSpace M := hM.simplyConnected
  exact establishedSmoothIntegralHomologySixSphereRecognition
    { toSmoothIntegralHomologySixSphere := hM.toSmoothIntegralHomologySixSphere
      simplyConnected := inferInstance }

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
