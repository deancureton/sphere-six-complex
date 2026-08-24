module

public import SphereSixComplex.Topology.SmoothRecognition

/-!
# Established six-sphere recognition inputs

This module isolates the two classical external theorems used to recognize a smooth integral
homology six-sphere. They are explicit axioms because their proofs are not yet available in
Mathlib. No paper-specific construction claim is assumed here.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- A simply connected smooth integral homology six-sphere is a homotopy sphere. This is the
standard finite-CW-type, Hurewicz, and Whitehead argument for smooth manifolds. -/
public axiom establishedHomologyToHomotopySixSphere
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    HomologyToHomotopySixSphereObligation X

/-- The smooth Poincare theorem in dimension six for classical smooth manifolds: every compact,
connected, Hausdorff, second-countable smooth homotopy six-sphere is diffeomorphic to the standard
sphere. This combines the h-cobordism theorem with the computation `Theta_6 = 0`. -/
public axiom establishedSmoothPoincareSix
    {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X] :
    SmoothHomotopySixSphere X → SmoothDiffeomorphicToSixSphere X

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
