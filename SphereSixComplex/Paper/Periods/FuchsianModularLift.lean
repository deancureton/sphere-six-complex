module

public import SphereSixComplex.Prerequisites.Periods.FuchsianModularParameterExistence
public import SphereSixComplex.Prerequisites.Periods.Uniformization.EstablishedExactFuchsianOrbifoldCoordinate
public import SphereSixComplex.Prerequisites.Periods.Uniformization.EstablishedExactNormalizedModularJUniformization
public import SphereSixComplex.Prerequisites.Periods.Uniformization.NormalizedModularJLiftingExistence

/-!
# Normalized Fuchsian modular lift

This file assembles the exact source orbifold uniformization, exact target modular-`j`
uniformization, and normalized branched-lifting theorem used for the modular parameter in
Theorem 3.4(i).

No additive period function, torus family, filling, gluing, or sphere-recognition statement is
assumed here.
-/

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- Classical uniformization of the explicit `(3, 4, ∞)` source orbifold, including its exact
orbit fibres, elliptic ramification, and completed cusp. -/
public theorem ExactFuchsianOrbifoldCoordinate.nonempty :
    Nonempty ExactFuchsianOrbifoldCoordinate :=
  nonempty_exactFuchsianOrbifoldCoordinate

/-- Classical level-one modular uniformization by the normalized modular invariant, including its
exact orbit fibres, elliptic ramification, special values, and completed cusp. -/
public theorem ExactNormalizedModularJUniformization.nonempty :
    Nonempty ExactNormalizedModularJUniformization :=
  nonempty_exactNormalizedModularJUniformization

/-- Classical normalized branched-lifting theorem from an exact `(3, 4, ∞)` quotient coordinate
through the exact level-one modular quotient. -/
public theorem normalizedFuchsianModularJLiftingExistence :
    NormalizedFuchsianModularJLiftingExistence :=
  NormalizedModularJLiftingExistence.normalizedFuchsianModularJLiftingExistence

/-- A normalized modular parameter together with the exact source quotient coordinate it lifts. -/
public structure FuchsianModularLift where
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
public theorem nonempty_fuchsianModularLift :
    Nonempty FuchsianModularLift := by
  obtain ⟨C⟩ := ExactFuchsianOrbifoldCoordinate.nonempty
  obtain ⟨J⟩ := ExactNormalizedModularJUniformization.nonempty
  obtain ⟨P, hOne, hTwo, hCoordinate⟩ :=
    exists_fuchsianModularParameter_of_normalizedLiftingExistence
      normalizedFuchsianModularJLiftingExistence J C
  exact ⟨⟨C, P, hOne, hTwo, hCoordinate⟩⟩

end SphereSixComplex.Periods
