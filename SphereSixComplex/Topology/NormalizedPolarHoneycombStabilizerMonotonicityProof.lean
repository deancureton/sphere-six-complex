module

public import SphereSixComplex.Topology.NormalizedPolarHoneycombPhaseGeometryReduction

/-!
# Stabilizer monotonicity for polar-honeycomb retractions

Compact-torus stabilizers cannot shrink under any strong deformation retraction onto the zero
fibre: away from that fibre the dense-torus action is free, while points on the fibre are fixed
throughout the homotopy.  Thus the normalized phase-geometry residue only needs uniqueness of
the positive representative in each compact-phase orbit.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction

/-- The compact torus acts freely at every point of nonzero height. -/
private theorem compactPhase_eq_of_eq_at_nonzero_height
    {M : Model} {r : ℝ} {positivePart : Set (LocalCarrier M r)}
    {k l : CompactTorus} {p : positivePart}
    (ht : M.t (p : LocalCarrier M r) ≠ 0)
    (h : compactPhaseOrbit M r positivePart (k, p) =
      compactPhaseOrbit M r positivePart (l, p)) :
    k = l := by
  have hpRange : (p : M.Carrier) ∈ Set.range M.torusEmbedding := by
    rw [M.torus_range]
    exact ht
  obtain ⟨x, hx⟩ := hpRange
  have hcarrier := congrArg (fun q : LocalCarrier M r ↦ (q : M.Carrier)) h
  change M.torusAction (compactTorusEmbedding k) (p : M.Carrier) =
    M.torusAction (compactTorusEmbedding l) (p : M.Carrier) at hcarrier
  rw [← hx, M.torusAction_torus, M.torusAction_torus] at hcarrier
  have hmul := M.torus_openEmbedding.injective hcarrier
  have hembedding : compactTorusEmbedding k = compactTorusEmbedding l :=
    mul_right_cancel hmul
  funext i
  apply Circle.coe_injective
  exact congrArg Units.val (congrFun hembedding i)

/-- Stabilizers cannot shrink under any strong deformation retraction onto the central fibre. -/
public theorem compactPhaseStabilizerMonotone_of_retraction
    {M : Model} {r : ℝ} (P : PolarHoneycombData M r) :
    letI := P.positiveDeckAction
    ∀ R : EquivariantStrongDeformationRetraction
        (Multiplicative ParameterLattice) P.positivePart P.central,
      CompactPhaseStabilizerMonotone P R := by
  let _ := P.positiveDeckAction
  intro R s k l p hkl
  by_cases ht : M.t (p : LocalCarrier M r) = 0
  · have hp : p ∈ P.central := by
      rw [P.central_eq]
      exact ht
    simpa only [R.homotopy_fixed s p hp] using hkl
  · have hphase : k = l := compactPhase_eq_of_eq_at_nonzero_height ht hkl
    subst l
    rfl

/-- On a positive compact-phase fundamental domain, no additional stabilizer hypothesis is
needed for the phase-geometric core. -/
public theorem polarPhaseGeometricCore_of_fundamentalDomain_only
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r)
    (hfundamental : CompactPhaseFundamentalDomain Q.toPolarHoneycombData) :
    PolarPhaseGeometricCore M r Q.toPolarHoneycombData := by
  apply polarPhaseGeometricCore_of_fundamentalDomain Q hfundamental
  exact compactPhaseStabilizerMonotone_of_retraction Q.toPolarHoneycombData
    Q.toPolarHoneycombData.positiveEquivariantStrongDeformationRetraction

/-- Phase invariance of the polar modulus is the sole extra phase condition needed after the
normalized polar-honeycomb construction has been supplied. -/
public theorem polarPhaseGeometricCore_of_invariantModulus_only
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r)
    (hmodulus : CompactPhaseInvariantModulus Q) :
    PolarPhaseGeometricCore M r Q.toPolarHoneycombData :=
  polarPhaseGeometricCore_of_fundamentalDomain_only Q
    (compactPhaseFundamentalDomain_of_invariantModulus Q hmodulus)

/-- The normalized phase-geometry axiom is reduced to construction data whose modulus is
compact-phase invariant; stabilizer compatibility is automatic. -/
public theorem normalizedPolarHoneycombPhaseGeometry_of_invariantModulus_only
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (h : Nonempty {Q : NormalizedPolarHoneycombConstructionData N M r //
      CompactPhaseInvariantModulus Q}) :
    Nonempty {Q : NormalizedPolarHoneycombConstructionData N M r //
      PolarPhaseGeometricCore M r Q.toPolarHoneycombData} := by
  exact h.map fun ⟨Q, hQ⟩ ↦
    ⟨Q, polarPhaseGeometricCore_of_invariantModulus_only Q hQ⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
