module

public import SphereSixComplex.Topology.NormalizedPolarHoneycombPhaseGeometryReduction

/-!
# Ambient phase homotopy for a normalized polar honeycomb

The positive retraction currently obtained by abstract covering-space lifting has no formula.
This file gives the minimal explicit replacement: a homotopy of the ambient local carrier whose
restriction is the positive retraction and which commutes with the compact torus.  These two
equations prove phase-fiber preservation without any separate stabilizer calculation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction

/-- The compact-torus action on the full local carrier. -/
public def compactPhaseLocalAction (M : Model) (r : ℝ)
    (k : CompactTorus) (p : LocalCarrier M r) : LocalCarrier M r :=
  ⟨M.torusAction (compactTorusEmbedding k) p, by
    change M.t (M.torusAction (compactTorusEmbedding k) (p : M.Carrier)) ∈
      Metric.ball 0 r
    rw [Metric.mem_ball, dist_zero_right, M.t_torusAction, norm_mul]
    change ‖(k 2 : ℂ)‖ * ‖M.t (p : LocalCarrier M r)‖ < r
    rw [Circle.norm_coe, one_mul]
    simpa only [dist_zero_right] using Metric.mem_ball.mp p.property⟩

/-- The compact-phase orbit map is the restriction of the ambient compact-phase action. -/
@[simp]
public theorem compactPhaseOrbit_eq_compactPhaseLocalAction
    (M : Model) (r : ℝ) (positivePart : Set (LocalCarrier M r))
    (k : CompactTorus) (p : positivePart) :
    compactPhaseOrbit M r positivePart (k, p) =
      compactPhaseLocalAction M r k (p : LocalCarrier M r) :=
  rfl

/-- An explicit radial-coordinate factorization of the polar modulus.  The coordinate target is
left abstract so that the eventual toric construction may use its natural nonnegative
honeycomb coordinates. -/
public structure CompactPhaseRadialFactorization
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r) where
  Coordinates : Type
  radialCoordinates : LocalCarrier M r → Coordinates
  radialCoordinates_phase : ∀ k p,
    radialCoordinates (compactPhaseLocalAction M r k p) = radialCoordinates p
  positiveSection : Coordinates → Q.positivePart
  modulus_eq : ∀ p, Q.modulus p = positiveSection (radialCoordinates p)

namespace CompactPhaseRadialFactorization

/-- A factorization through phase-invariant radial coordinates proves phase invariance of the
polar modulus. -/
public theorem compactPhaseInvariantModulus
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {Q : NormalizedPolarHoneycombConstructionData N M r}
    (F : CompactPhaseRadialFactorization Q) : CompactPhaseInvariantModulus Q := by
  intro k p
  rw [compactPhaseOrbit_eq_compactPhaseLocalAction, F.modulus_eq, F.modulus_eq,
    F.radialCoordinates_phase]

end CompactPhaseRadialFactorization

/-- Explicit data showing that a positive retraction is the restriction of a compact-phase
equivariant ambient homotopy. -/
public structure CompactPhaseEquivariantAmbientRetraction
    {M : Model} {r : ℝ} (P : PolarHoneycombData M r) where
  retraction :
    letI := P.positiveDeckAction
    EquivariantStrongDeformationRetraction
      (Multiplicative ParameterLattice) P.positivePart P.central
  ambientHomotopy : C(unitInterval × LocalCarrier M r, LocalCarrier M r)
  ambientHomotopy_positive :
    letI := P.positiveDeckAction
    ∀ s (p : P.positivePart),
      ambientHomotopy (s, (p : LocalCarrier M r)) =
        (retraction.homotopy (s, p) : P.positivePart)
  ambientHomotopy_phase : ∀ s k p,
    ambientHomotopy (s, compactPhaseLocalAction M r k p) =
      compactPhaseLocalAction M r k (ambientHomotopy (s, p))

namespace CompactPhaseEquivariantAmbientRetraction

/-- The ambient phase equations give the orbit formula for the restricted retraction. -/
public theorem homotopy_compactPhaseOrbit
    {M : Model} {r : ℝ} {P : PolarHoneycombData M r}
    (A : CompactPhaseEquivariantAmbientRetraction P) (s : unitInterval)
    (k : CompactTorus) (p : P.positivePart) :
    letI := P.positiveDeckAction
    compactPhaseOrbit M r P.positivePart (k, A.retraction.homotopy (s, p)) =
      A.ambientHomotopy (s, compactPhaseOrbit M r P.positivePart (k, p)) := by
  let _ := P.positiveDeckAction
  rw [compactPhaseOrbit_eq_compactPhaseLocalAction,
    compactPhaseOrbit_eq_compactPhaseLocalAction, A.ambientHomotopy_phase]
  congr 2
  exact (A.ambientHomotopy_positive s p).symm

/-- An ambient phase-equivariant extension proves arbitrary phase-fiber preservation. -/
public theorem homotopy_fiberwise
    {M : Model} {r : ℝ} {P : PolarHoneycombData M r}
    (A : CompactPhaseEquivariantAmbientRetraction P) :
    letI := P.positiveDeckAction
    ∀ s k p l q,
      compactPhaseOrbit M r P.positivePart (k, p) =
          compactPhaseOrbit M r P.positivePart (l, q) →
        compactPhaseOrbit M r P.positivePart (k, A.retraction.homotopy (s, p)) =
          compactPhaseOrbit M r P.positivePart (l, A.retraction.homotopy (s, q)) := by
  let _ := P.positiveDeckAction
  intro s k p l q hpq
  rw [A.homotopy_compactPhaseOrbit, A.homotopy_compactPhaseOrbit, hpq]

/-- The explicit ambient extension supplies the complete phase-geometric core. -/
public theorem toPolarPhaseGeometricCore
    {M : Model} {r : ℝ} {P : PolarHoneycombData M r}
    (A : CompactPhaseEquivariantAmbientRetraction P) :
    PolarPhaseGeometricCore M r P := by
  let _ := P.positiveDeckAction
  refine ⟨A.retraction, ?_⟩
  exact A.homotopy_fiberwise

/-- In particular, the explicit ambient extension proves stabilizer monotonicity. -/
public theorem stabilizerMonotone
    {M : Model} {r : ℝ} {P : PolarHoneycombData M r}
    (A : CompactPhaseEquivariantAmbientRetraction P) :
    CompactPhaseStabilizerMonotone P A.retraction := by
  let _ := P.positiveDeckAction
  intro s k l p hp
  exact A.homotopy_fiberwise s k p l p hp

end CompactPhaseEquivariantAmbientRetraction

/-- The smallest concrete construction record replacing the abstract normalized phase-geometry
existence claim.  The first field is the underlying polar honeycomb; the second is an explicit
ambient formula for its positive retraction. -/
public structure NormalizedPolarHoneycombAmbientPhaseGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D)
    (M : Model) (r : ℝ) where
  construction : NormalizedPolarHoneycombConstructionData N M r
  radialFactorization : CompactPhaseRadialFactorization construction
  ambientRetraction :
    CompactPhaseEquivariantAmbientRetraction construction.toPolarHoneycombData

namespace NormalizedPolarHoneycombAmbientPhaseGeometry

/-- The explicit radial factorization proves the first remaining phase property. -/
public theorem modulus_phase_invariant
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (G : NormalizedPolarHoneycombAmbientPhaseGeometry N M r) :
    CompactPhaseInvariantModulus G.construction :=
  G.radialFactorization.compactPhaseInvariantModulus

/-- Consequently, the positive part is a compact-phase fundamental domain. -/
public theorem positivePart_fundamentalDomain
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (G : NormalizedPolarHoneycombAmbientPhaseGeometry N M r) :
    CompactPhaseFundamentalDomain G.construction.toPolarHoneycombData :=
  compactPhaseFundamentalDomain_of_invariantModulus G.construction
    G.modulus_phase_invariant

end NormalizedPolarHoneycombAmbientPhaseGeometry

/-- The explicit construction record implies the exact normalized phase-geometry conclusion. -/
public theorem normalizedPolarHoneycombPhaseGeometry_of_ambient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D)
    (M : Model) (r : ℝ)
    (h : Nonempty (NormalizedPolarHoneycombAmbientPhaseGeometry N M r)) :
    Nonempty {Q : NormalizedPolarHoneycombConstructionData N M r //
      PolarPhaseGeometricCore M r Q.toPolarHoneycombData} := by
  exact h.map fun G ↦ ⟨G.construction, G.ambientRetraction.toPolarPhaseGeometricCore⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
