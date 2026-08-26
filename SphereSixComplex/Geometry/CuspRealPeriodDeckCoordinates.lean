module

public import SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
public import SphereSixComplex.Geometry.GlobalDeckSmoothness

/-!
# Cusp deck transport in real-period coordinates

The real-period product chart conjugates the parabolic deck transformation to the integral
matrix `M₀`.  These equalities are the cover-level compatibility needed to identify the cusp
mapping-torus marking with the marking inherited from the regular elliptic family.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization

open Matrix
open SphereSixComplex.Geometry SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.LatticeData

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- In fixed real-period coordinates, the cusp deck transformation acts through the canonical
real extension of its integral period representation. -/
public theorem movingToFixedCover_deckMap_gZero
    (z₀ : UpperHalfPlane) (p : UpperHalfPlane × ComplexTwoSpace) :
    movingToFixedCover F z₀ (deckMap F g₀ p) =
      (U.sourceAction g₀ • p.1,
        (fullRankDomain (parameterMap F z₀)).realEquiv
          (rhoLambdaReal g₀ (periodCoordinates (parameterMap F p.1) p.2))) := by
  apply Prod.ext
  · rfl
  · change (fullRankDomain (parameterMap F z₀)).realEquiv
        (periodCoordinates (parameterMap F (U.sourceAction g₀ • p.1))
          (periodTransport g₀ (parameterMap F p.1) p.2)) = _
    rw [parameterMap_equivariant, periodCoordinates_transport]

/-- On the integral period lattice, the preceding real-coordinate formula is exactly `M₀`.
This pins down both the cusp generator and the fibre marking before any homology choices. -/
public theorem movingToFixedCover_deckMap_gZero_periodVector
    (z₀ z : UpperHalfPlane) (n : IntegerPeriods) :
    movingToFixedCover F z₀
        (deckMap F g₀ (z, periodVector (parameterMap F z).1 n)) =
      (U.sourceAction g₀ • z,
        periodVector (parameterMap F z₀).1 (M₀ *ᵥ n)) := by
  rw [show deckMap F g₀ (z, periodVector (parameterMap F z).1 n) =
      (U.sourceAction g₀ • z,
        periodVector (parameterMap F (U.sourceAction g₀ • z)).1 (M₀ *ᵥ n)) by
    apply Prod.ext
    · rfl
    · change periodTransport g₀ (parameterMap F z)
          (periodVector (parameterMap F z).1 n) =
        periodVector (parameterMap F (U.sourceAction g₀ • z)).1 (M₀ *ᵥ n)
      rw [parameterMap_equivariant, periodTransport_periodVector, rhoLambda_g₀_apply]]
  apply Prod.ext
  · rfl
  · change (fullRankDomain (parameterMap F z₀)).realEquiv
      (periodCoordinates (parameterMap F (U.sourceAction g₀ • z))
        (periodVector (parameterMap F (U.sourceAction g₀ • z)).1 (M₀ *ᵥ n))) =
      periodVector (parameterMap F z₀).1 (M₀ *ᵥ n)
    rw [periodCoordinates_periodVector, (fullRankDomain (parameterMap F z₀)).map_integer]

end SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization

