module

public import SphereSixComplex.Periods.Uniformization.SourceFundamentalPairingClassification
import all SphereSixComplex.Periods.Uniformization.SourceFundamentalPairingClassification
public import SphereSixComplex.Periods.Uniformization.OrbitScalarEllipticCorners
import all SphereSixComplex.Periods.Uniformization.OrbitScalarEllipticCorners

@[expose] public section

/-!
# Exact source orbifold uniformization

This is the final assembly replacing
`SphereSixComplex.Periods.establishedExactFuchsianOrbifoldCoordinate`.

Tau Ceti is used transitively by the Carathéodory seed and scalar-continuation construction
imported above. This file makes no additional direct Tau Ceti import or theorem call.
-/

noncomputable section

namespace SphereSixComplex.Periods

open SourceChamberTopology

/-- The exact `(3, 4, ∞)` Fuchsian orbifold coordinate exists, with no classical-analysis
axiom. -/
theorem establishedExactFuchsianOrbifoldCoordinate_proved :
    Nonempty ExactFuchsianOrbifoldCoordinate := by
  obtain ⟨S⟩ := exists_sourceChamberCaratheodorySeed
  exact
    nonempty_exactFuchsianOrbifoldCoordinate_of_fundamentalScalarConsistent S
      (sourceFundamentalScalarConsistent S)


end SphereSixComplex.Periods
