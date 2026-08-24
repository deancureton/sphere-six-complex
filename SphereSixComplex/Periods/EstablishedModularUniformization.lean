module

public import SphereSixComplex.Periods.FuchsianModularParameterExistence
public import SphereSixComplex.Periods.Uniformization.EstablishedExactFuchsianOrbifoldCoordinate
public import SphereSixComplex.Periods.Uniformization.EstablishedExactNormalizedModularJUniformization
public import SphereSixComplex.Periods.Uniformization.NormalizedModularJLiftingExistence

/-!
# Established modular uniformization

This file assembles the exact source orbifold uniformization, exact target modular-`j`
uniformization, and normalized branched-lifting theorem used for the modular parameter in
Theorem 3.4(i).  The three formerly axiomatized inputs are now kernel-checked theorems, and all
consequences below are proved from them.

No additive period function, torus family, filling, gluing, or sphere-recognition statement is
assumed here.
-/

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- Classical uniformization of the explicit `(3, 4, ∞)` source orbifold, including its exact
orbit fibres, elliptic ramification, and completed cusp. -/
public theorem establishedExactFuchsianOrbifoldCoordinate :
    Nonempty ExactFuchsianOrbifoldCoordinate :=
  establishedExactFuchsianOrbifoldCoordinate_proved

/-- Classical level-one modular uniformization by the normalized modular invariant, including its
exact orbit fibres, elliptic ramification, special values, and completed cusp. -/
public theorem establishedExactNormalizedModularJUniformization :
    Nonempty ExactNormalizedModularJUniformization :=
  establishedExactNormalizedModularJUniformization_proved

/-- Classical normalized branched-lifting theorem from an exact `(3, 4, ∞)` quotient coordinate
through the exact level-one modular quotient. -/
public theorem establishedNormalizedFuchsianModularJLifting :
    NormalizedFuchsianModularJLiftingExistence :=
  NormalizedModularJLiftingExistence.normalizedFuchsianModularJLiftingExistence

/-- A normalized modular parameter together with the exact source quotient coordinate it lifts. -/
public structure EstablishedFuchsianModularParameter where
  /-- The exact source orbifold quotient coordinate. -/
  sourceCoordinate : ExactFuchsianOrbifoldCoordinate
  /-- The resulting holomorphic equivariant modular parameter. -/
  modularParameter : FuchsianModularParameter
  /-- Normalization at the order-three source elliptic point. -/
  tau_at_one :
    modularParameter.tau fuchsianOneFixedPoint = ellipticThreeParameter
  /-- Normalization at the order-four source elliptic point. -/
  tau_at_two :
    modularParameter.tau fuchsianTwoFixedPoint = UpperHalfPlane.I
  /-- The modular invariant of the lift is the prescribed source quotient coordinate. -/
  induced_coordinate : ∀ z,
    modularParameter.coordinate z = sourceCoordinate.coordinate z

/-- The three classical uniformization inputs produce the normalized Fuchsian modular parameter
and its exact source quotient coordinate. -/
public theorem exists_establishedFuchsianModularParameter :
    Nonempty EstablishedFuchsianModularParameter := by
  obtain ⟨C⟩ := establishedExactFuchsianOrbifoldCoordinate
  obtain ⟨J⟩ := establishedExactNormalizedModularJUniformization
  obtain ⟨P, hOne, hTwo, hCoordinate⟩ :=
    exists_fuchsianModularParameter_of_normalizedLiftingExistence
      establishedNormalizedFuchsianModularJLifting J C
  exact ⟨⟨C, P, hOne, hTwo, hCoordinate⟩⟩

end SphereSixComplex.Periods
