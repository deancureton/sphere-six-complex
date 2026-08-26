module

public import SphereSixComplex.Periods.EstablishedFuchsianTorsorDescent
public import SphereSixComplex.Periods.FuchsianCuspNormalization
public import SphereSixComplex.Topology.CuspPhaseSpreadingData

/-!
# Established phase spreading for the standard infinite `A₂` toric model

This boundary records only the standard toric orbit, deck, and stabilizer compatibility package.
It contains no quotient retraction, homology, Euler-characteristic, or global paper conclusion.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction

/-- The standard polar-honeycomb model can be chosen compatibly with compact phase orbits, the
frozen deck action, and the stabilizers of the positive-part cellular homotopy. -/
public axiom polarHoneycombPhaseSpreadingPackage
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) (hr : 0 < r) :
    Nonempty (Σ P : PolarHoneycombData M r,
      FrozenLocalCuspPhaseSpreadingData N M r P)

/-- Forgetting the phase-spreading compatibility gives the underlying polar-honeycomb model. -/
public theorem polarHoneycombData (M : Model) (r : ℝ) (hr : 0 < r) :
    Nonempty (PolarHoneycombData M r) := by
  obtain ⟨E⟩ := exists_establishedFuchsianModularParameter
  obtain ⟨F⟩ := establishedExactLiftedModularNegOneFrame E
  let D := establishedFuchsianPeriodLocalData E F
  obtain ⟨N⟩ := FuchsianCuspNormalization.exists_normalizedFuchsianCuspCoordinate E D
  exact Nonempty.map (fun package ↦ package.1)
    (polarHoneycombPhaseSpreadingPackage N M r hr)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
