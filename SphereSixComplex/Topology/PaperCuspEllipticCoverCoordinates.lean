module

public import SphereSixComplex.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Geometry.CuspRealPeriodDeckCoordinates
public import SphereSixComplex.Topology.PaperCuspBoundaryUniversalCover

/-!
# Normalized cover coordinates for the cusp-to-elliptic map

The local cusp quotient enters the regular elliptic family through the same normalized modular
coordinate used by the central affine cover.  Together with the real-period deck calculation,
this gives the exact base and fibre equalities required before constructing a comparison of the
Wang and Mayer--Vietoris chain sequences.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollarPairProperness
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- On the normalized additive universal cover, the actual local-to-global cusp map has exactly
the modular base coordinate used to define the affine central split. -/
public theorem centralCuspCoordinate_puncturedLocalCuspQuotientMap
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    centralCuspCoordinate
        (puncturedLocalCuspQuotientMap W (additiveCuspBoundaryProjection W p)) =
      normalizedModularJCoordinate
        ((assembledFuchsianPeriodFunctions E D).tau (N.lift p.1.2)) := by
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection]
  exact centralCuspCoordinate_additiveCover W p

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

