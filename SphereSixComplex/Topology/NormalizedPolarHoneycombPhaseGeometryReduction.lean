module

public import SphereSixComplex.Topology.EstablishedA2PhaseSpreading

/-!
# Reduction of normalized polar-honeycomb phase geometry

The abstract quotient argument already constructs an equivariant strong deformation retraction
of the positive part onto its central honeycomb.  This file isolates the two point-set geometric
facts needed to show that this retraction spreads across compact phase orbits: the modulus is
phase-invariant, and the retraction does not shrink compact-torus stabilizers.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction

/-- The polar modulus is constant on compact-phase orbits. -/
public def CompactPhaseInvariantModulus
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r)
    (hmodulus : CompactPhaseInvariantModulus Q) (k : CompactTorus)
    (p : Q.positivePart) :
    Q.modulus (compactPhaseOrbit M r Q.positivePart (k, p)) = p := by
  rw [hmodulus k p, Q.modulus_fixed p]

/-- Phase invariance of the modulus proves uniqueness of positive orbit representatives. -/
public theorem compactPhaseFundamentalDomain_of_invariantModulus
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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

/-- On a positive fundamental domain, the geometric core is exactly the existence of a
stabilizer-monotone equivariant retraction. -/
public theorem polarPhaseGeometricCore_iff_exists_stabilizerMonotone
    {M : Model} {r : ℝ} (P : PolarHoneycombData M r)
    (hfundamental : CompactPhaseFundamentalDomain P) :
    PolarPhaseGeometricCore M r P ↔
      letI := P.positiveDeckAction
      ∃ R : EquivariantStrongDeformationRetraction
          (Multiplicative ParameterLattice) P.positivePart P.central,
        CompactPhaseStabilizerMonotone P R := by
  let _ := P.positiveDeckAction
  constructor
  · rintro ⟨R, hfiber⟩
    exact ⟨R, (compactPhaseOrbit_fiberwise_iff_stabilizerMonotone_of_fundamentalDomain
      P hfundamental R).mp hfiber⟩
  · rintro ⟨R, hstabilizer⟩
    exact ⟨R, (compactPhaseOrbit_fiberwise_iff_stabilizerMonotone_of_fundamentalDomain
      P hfundamental R).mpr hstabilizer⟩

/-- Once the modulus is phase-invariant, preservation of arbitrary phase-orbit fibers is
equivalent to the same-point stabilizer condition. -/
public theorem compactPhaseOrbit_fiberwise_iff_stabilizerMonotone
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r)
    (hmodulus : CompactPhaseInvariantModulus Q) :
    let P := Q.toPolarHoneycombData
    letI := P.positiveDeckAction
    ∀ R : EquivariantStrongDeformationRetraction
        (Multiplicative ParameterLattice) P.positivePart P.central,
      (∀ s k p l q,
        compactPhaseOrbit M r Q.positivePart (k, p) =
            compactPhaseOrbit M r Q.positivePart (l, q) →
          compactPhaseOrbit M r Q.positivePart (k, R.homotopy (s, p)) =
            compactPhaseOrbit M r Q.positivePart (l, R.homotopy (s, q))) ↔
        CompactPhaseStabilizerMonotone P R := by
  dsimp only
  let _ := Q.toPolarHoneycombData.positiveDeckAction
  intro R
  exact compactPhaseOrbit_fiberwise_iff_stabilizerMonotone_of_fundamentalDomain
    Q.toPolarHoneycombData
    (compactPhaseFundamentalDomain_of_invariantModulus Q hmodulus) R

/-- A positive fundamental domain and stabilizer-monotone retraction imply the full phase
geometric core. -/
public theorem polarPhaseGeometricCore_of_fundamentalDomain
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r)
    (hfundamental : CompactPhaseFundamentalDomain Q.toPolarHoneycombData)
    (hstabilizer :
      let P := Q.toPolarHoneycombData
      letI := P.positiveDeckAction
      CompactPhaseStabilizerMonotone P P.positiveEquivariantStrongDeformationRetraction) :
    PolarPhaseGeometricCore M r Q.toPolarHoneycombData := by
  let P := Q.toPolarHoneycombData
  let _ := P.positiveDeckAction
  let R := P.positiveEquivariantStrongDeformationRetraction
  refine ⟨R, ?_⟩
  exact (compactPhaseOrbit_fiberwise_iff_stabilizerMonotone_of_fundamentalDomain
    P hfundamental R).mpr hstabilizer

/-- Phase invariance of the modulus is a concrete sufficient condition for the fundamental
domain hypothesis. -/
public theorem polarPhaseGeometricCore_of_stabilizerMonotone
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r)
    (hmodulus : CompactPhaseInvariantModulus Q)
    (hstabilizer :
      let P := Q.toPolarHoneycombData
      letI := P.positiveDeckAction
      CompactPhaseStabilizerMonotone P P.positiveEquivariantStrongDeformationRetraction) :
    PolarPhaseGeometricCore M r Q.toPolarHoneycombData :=
  polarPhaseGeometricCore_of_fundamentalDomain Q
    (compactPhaseFundamentalDomain_of_invariantModulus Q hmodulus) hstabilizer

/-- A precise replacement input for the broad normalized phase-geometry axiom.  Its first field
is the already narrowed polar-honeycomb construction; the last two are explicit point-set
properties of the positive section and the canonical lifted retraction. -/
public structure NormalizedPolarHoneycombExplicitPhaseGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) where
  construction : NormalizedPolarHoneycombConstructionData N M r
  positivePart_fundamentalDomain :
    CompactPhaseFundamentalDomain construction.toPolarHoneycombData
  positiveRetraction_stabilizerMonotone :
    let P := construction.toPolarHoneycombData
    letI := P.positiveDeckAction
    CompactPhaseStabilizerMonotone P P.positiveEquivariantStrongDeformationRetraction

/-- A phase-invariant modulus supplies the fundamental-domain field of the explicit residue. -/
public noncomputable def NormalizedPolarHoneycombExplicitPhaseGeometry.ofInvariantModulus
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r)
    (hmodulus : CompactPhaseInvariantModulus Q)
    (hstabilizer :
      let P := Q.toPolarHoneycombData
      letI := P.positiveDeckAction
      CompactPhaseStabilizerMonotone P P.positiveEquivariantStrongDeformationRetraction) :
    NormalizedPolarHoneycombExplicitPhaseGeometry N M r where
  construction := Q
  positivePart_fundamentalDomain :=
    compactPhaseFundamentalDomain_of_invariantModulus Q hmodulus
  positiveRetraction_stabilizerMonotone := hstabilizer

/-- Explicit phase geometry supplies exactly the conclusion formerly taken as a single
paper-specific black box. -/
public noncomputable def NormalizedPolarHoneycombExplicitPhaseGeometry.toPhaseGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
  (G : NormalizedPolarHoneycombExplicitPhaseGeometry N M r) :
    {Q : NormalizedPolarHoneycombConstructionData N M r //
      PolarPhaseGeometricCore M r Q.toPolarHoneycombData} :=
  ⟨G.construction, polarPhaseGeometricCore_of_fundamentalDomain G.construction
    G.positivePart_fundamentalDomain G.positiveRetraction_stabilizerMonotone⟩

/-- Existence of the explicit residue implies the exact normalized phase-geometry statement. -/
public theorem normalizedPolarHoneycombPhaseGeometry_of_explicit
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (h : Nonempty (NormalizedPolarHoneycombExplicitPhaseGeometry N M r)) :
    Nonempty {Q : NormalizedPolarHoneycombConstructionData N M r //
      PolarPhaseGeometricCore M r Q.toPolarHoneycombData} :=
  h.map NormalizedPolarHoneycombExplicitPhaseGeometry.toPhaseGeometry

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
