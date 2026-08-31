module

public import SphereSixComplex.Topology.NormalizedPolarHoneycombAmbientPhaseHomotopy

/-!
# Direct ambient reduction of normalized polar-honeycomb phase geometry

The construction and quotient APIs produce an abstract equivariant retraction of the positive
part, but do not expose a formula controlling its compact-torus stabilizers.  A direct ambient
homotopy to the zero fibre is enough: if it preserves the positive part, commutes with its deck
action, fixes the zero fibre, and commutes with compact phase, then its restriction has exactly
the required phase-fibre property.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction

/-- A concrete ambient deformation to the toric zero fibre, with only the preservation and
equivariance properties needed to restrict it to a normalized polar honeycomb. -/
public structure CompactPhaseEquivariantAmbientZeroHomotopy
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r) where
  homotopy : C(unitInterval × LocalCarrier M r, LocalCarrier M r)
  map_zero_left : ∀ p : LocalCarrier M r, homotopy (0, p) = p
  map_one_t : ∀ p : LocalCarrier M r, M.t (homotopy (1, p)) = 0
  fixed_of_t_eq_zero : ∀ s (p : LocalCarrier M r),
    M.t p = 0 → homotopy (s, p) = p
  positive_mem : ∀ s (q : Q.positivePart), homotopy (s, q) ∈ Q.positivePart
  positiveDeck_equivariant :
    letI := normalizedPositiveDeckAction N M Q.positivePart Q.positiveDeck_mem
    ∀ (g : Multiplicative ParameterLattice) s (q : Q.positivePart),
      homotopy (s, ((g • q : Q.positivePart) : LocalCarrier M r)) =
        ((g • ⟨homotopy (s, q), positive_mem s q⟩ : Q.positivePart) :
          LocalCarrier M r)
  compactPhase_equivariant : ∀ s k (p : LocalCarrier M r),
    homotopy (s, compactPhaseLocalAction M r k p) =
      compactPhaseLocalAction M r k (homotopy (s, p))

namespace CompactPhaseEquivariantAmbientZeroHomotopy

/-- Restrict the ambient endpoint to the positive part. -/
public def positiveRetract
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {Q : NormalizedPolarHoneycombConstructionData N M r}
    (H : CompactPhaseEquivariantAmbientZeroHomotopy Q) :
    C(Q.positivePart, Q.positivePart) where
  toFun q := ⟨H.homotopy (1, q), H.positive_mem 1 q⟩
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact H.homotopy.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)

/-- Restrict the ambient deformation to the positive part. -/
public def positiveHomotopy
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {Q : NormalizedPolarHoneycombConstructionData N M r}
    (H : CompactPhaseEquivariantAmbientZeroHomotopy Q) :
    ContinuousMap.Homotopy (ContinuousMap.id Q.positivePart) H.positiveRetract where
  toFun z := ⟨H.homotopy (z.1, z.2), H.positive_mem z.1 z.2⟩
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact H.homotopy.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  map_zero_left q := Subtype.ext (H.map_zero_left q)
  map_one_left _ := rfl

/-- The restricted ambient deformation is the required lattice-equivariant strong deformation
retraction of the positive part onto its central honeycomb. -/
public def positiveEquivariantStrongDeformationRetraction
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {Q : NormalizedPolarHoneycombConstructionData N M r}
    (H : CompactPhaseEquivariantAmbientZeroHomotopy Q) :
    letI := normalizedPositiveDeckAction N M Q.positivePart Q.positiveDeck_mem
    EquivariantStrongDeformationRetraction
      (Multiplicative ParameterLattice) Q.positivePart Q.central := by
  let _ := normalizedPositiveDeckAction N M Q.positivePart Q.positiveDeck_mem
  refine {
    retract := H.positiveRetract
    homotopy := H.positiveHomotopy
    retract_mem := ?_
    retract_fixed := ?_
    homotopy_fixed := ?_
    retract_equivariant := ?_
    homotopy_equivariant := ?_
  }
  · intro q
    exact H.map_one_t q
  · intro q hq
    apply Subtype.ext
    exact H.fixed_of_t_eq_zero 1 q hq
  · intro s q hq
    apply Subtype.ext
    exact H.fixed_of_t_eq_zero s q hq
  · intro g q
    apply Subtype.ext
    exact H.positiveDeck_equivariant g 1 q
  · intro g s q
    apply Subtype.ext
    exact H.positiveDeck_equivariant g s q

/-- The direct ambient formula packages as the earlier ambient-retraction interface. -/
public def toAmbientRetraction
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {Q : NormalizedPolarHoneycombConstructionData N M r}
    (H : CompactPhaseEquivariantAmbientZeroHomotopy Q) :
    CompactPhaseEquivariantAmbientRetraction Q.toPolarHoneycombData where
  retraction := H.positiveEquivariantStrongDeformationRetraction
  ambientHomotopy := H.homotopy
  ambientHomotopy_positive := by
    intro s q
    rfl
  ambientHomotopy_phase := H.compactPhase_equivariant

/-- Hence a single ambient zero-fibre formula gives the exact phase-geometric core, with no
separate modulus factorization or stabilizer calculation. -/
public theorem toPolarPhaseGeometricCore
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {Q : NormalizedPolarHoneycombConstructionData N M r}
    (H : CompactPhaseEquivariantAmbientZeroHomotopy Q) :
    PolarPhaseGeometricCore M r Q.toPolarHoneycombData :=
  H.toAmbientRetraction.toPolarPhaseGeometricCore

end CompactPhaseEquivariantAmbientZeroHomotopy

/-- The remaining normalized construction together with one explicit ambient radial homotopy.
Unlike the established conclusion, this record does not contain a phase-geometric core or a
positive-part retraction. -/
public structure NormalizedPolarHoneycombAmbientZeroGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) where
  construction : NormalizedPolarHoneycombConstructionData N M r
  ambientZeroHomotopy : CompactPhaseEquivariantAmbientZeroHomotopy construction

namespace NormalizedPolarHoneycombAmbientZeroGeometry

/-- Direct ambient geometry produces the exact subtype occurring in the established axiom. -/
public def toPhaseGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (G : NormalizedPolarHoneycombAmbientZeroGeometry N M r) :
    {Q : NormalizedPolarHoneycombConstructionData N M r //
      PolarPhaseGeometricCore M r Q.toPolarHoneycombData} :=
  ⟨G.construction, G.ambientZeroHomotopy.toPolarPhaseGeometricCore⟩

end NormalizedPolarHoneycombAmbientZeroGeometry

/-- A nonempty direct ambient construction implies the exact statement of
`normalizedPolarHoneycombPhaseGeometry`.  The premise is independent construction data; this
proof does not select it from that axiom. -/
public theorem normalizedPolarHoneycombPhaseGeometry_of_ambientZeroGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (_hr : 0 < r)
    (h : Nonempty (NormalizedPolarHoneycombAmbientZeroGeometry N M r)) :
    Nonempty {Q : NormalizedPolarHoneycombConstructionData N M r //
      PolarPhaseGeometricCore M r Q.toPolarHoneycombData} :=
  h.map NormalizedPolarHoneycombAmbientZeroGeometry.toPhaseGeometry

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
