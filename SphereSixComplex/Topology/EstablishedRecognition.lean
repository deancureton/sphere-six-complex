module

public import SphereSixComplex.Topology.SmoothRecognition
public import SphereSixComplex.Topology.SmoothSixSphereClassification

/-!
# Established six-sphere recognition inputs

This module isolates the classical external theorems used to recognize a smooth integral homology
six-sphere. They are explicit axioms because their proofs are not yet available in Mathlib. The
smooth Poincare step is decomposed into generalized topological Poincare and the classification
of smooth structures on a topological six-sphere; no paper-specific construction claim is
assumed here.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- A simply connected smooth integral homology six-sphere is a homotopy sphere. This is the
standard finite-CW-type, Hurewicz, and Whitehead argument for smooth manifolds. -/
public axiom establishedHomologyToHomotopySixSphere
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    HomologyToHomotopySixSphereObligation X

/-- The standard-model smooth Poincare theorem in dimension six. -/
public axiom establishedSmoothPoincareSixStandardModel :
    SmoothPoincareSixStandardModel

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

/-- The three classical stages imply smooth Poincare in dimension six. -/
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

/-- The two established external inputs give the exact smooth-recognition obligation used by the
construction. -/
public theorem establishedSmoothSixSphereRecognition
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    SmoothSixSphereRecognitionObligation X := by
  intro hX
  exact establishedSmoothPoincareSix
    { toCompactConnectedSmoothSixManifold := hX.toCompactConnectedSmoothSixManifold
      homotopyEquiv := establishedHomologyToHomotopySixSphere hX }

end SphereSixComplex
