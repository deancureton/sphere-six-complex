module

public import SphereSixComplex.Paper.Topology.EstablishedA2PhaseSpreading

/-!
# Reduction of normalized polar-honeycomb phase geometry

The abstract quotient argument already constructs an equivariant strong deformation retraction
of the positive part onto its central honeycomb.  This file isolates the two point-set geometric
facts needed to show that this retraction spreads across compact phase orbits: the modulus is
phase-invariant, and the retraction does not shrink compact-torus stabilizers.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction

/-- The polar modulus is constant on compact-phase orbits. -/
public def CompactPhaseInvariantModulus
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r) : Prop :=
  ∀ k p, Q.modulus (compactPhaseOrbit M r Q.positivePart (k, p)) = Q.modulus p

/-- A homotopy of the positive part does not shrink the stabilizer of any point under the
compact-torus action. -/
public def CompactPhaseStabilizerMonotone
    {M : Model} {r : ℝ} (P : PolarHoneycombData M r) :
    letI := P.positiveDeckAction
    EquivariantStrongDeformationRetraction
        (Multiplicative ParameterLattice) P.positivePart P.central → Prop := by
  let _ := P.positiveDeckAction
  exact fun R ↦ ∀ s k l p,
    compactPhaseOrbit M r P.positivePart (k, p) =
        compactPhaseOrbit M r P.positivePart (l, p) →
      compactPhaseOrbit M r P.positivePart (k, R.homotopy (s, p)) =
        compactPhaseOrbit M r P.positivePart (l, R.homotopy (s, p))

/-- Every compact-phase orbit has at most one representative in the positive part. -/
public def CompactPhaseFundamentalDomain
    {M : Model} {r : ℝ} (P : PolarHoneycombData M r) : Prop :=
  ∀ k p l q,
    compactPhaseOrbit M r P.positivePart (k, p) =
        compactPhaseOrbit M r P.positivePart (l, q) →
      p = q

/-- A phase-invariant modulus makes the positive part a section of the compact-phase orbit
map. -/
public theorem compactPhaseOrbit_modulus
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r)
    (hmodulus : CompactPhaseInvariantModulus Q) (k : CompactTorus)
    (p : Q.positivePart) :
    Q.modulus (compactPhaseOrbit M r Q.positivePart (k, p)) = p := by
  rw [hmodulus k p, Q.modulus_fixed p]

/-- Phase invariance of the modulus proves uniqueness of positive orbit representatives. -/
public theorem compactPhaseFundamentalDomain_of_invariantModulus
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r)
    (hmodulus : CompactPhaseInvariantModulus Q) :
    CompactPhaseFundamentalDomain Q.toPolarHoneycombData := by
  intro k p l q hpq
  have h := congrArg Q.modulus hpq
  change Q.modulus (compactPhaseOrbit M r Q.positivePart (k, p)) =
    Q.modulus (compactPhaseOrbit M r Q.positivePart (l, q)) at h
  rw [compactPhaseOrbit_modulus Q hmodulus k p,
    compactPhaseOrbit_modulus Q hmodulus l q] at h
  exact h

/-- For a positive fundamental domain, arbitrary fiber preservation is exactly same-point
stabilizer monotonicity. -/
public theorem compactPhaseOrbit_fiberwise_iff_stabilizerMonotone_of_fundamentalDomain
    {M : Model} {r : ℝ} (P : PolarHoneycombData M r)
    (hfundamental : CompactPhaseFundamentalDomain P) :
    letI := P.positiveDeckAction
    ∀ R : EquivariantStrongDeformationRetraction
        (Multiplicative ParameterLattice) P.positivePart P.central,
      (∀ s k p l q,
        compactPhaseOrbit M r P.positivePart (k, p) =
            compactPhaseOrbit M r P.positivePart (l, q) →
          compactPhaseOrbit M r P.positivePart (k, R.homotopy (s, p)) =
            compactPhaseOrbit M r P.positivePart (l, R.homotopy (s, q))) ↔
        CompactPhaseStabilizerMonotone P R := by
  let _ := P.positiveDeckAction
  intro R
  constructor
  · intro hfiber s k l p hkl
    exact hfiber s k p l p hkl
  · intro hstabilizer s k p l q hpq
    have hpq' : p = q := hfundamental k p l q hpq
    subst q
    exact hstabilizer s k l p hpq



end SphereSixComplex.Geometry.InfiniteA2Toric
