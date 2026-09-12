module
public import SphereSixComplex.Paper.Topology.NormalizedPolarHoneycombAmbientPhaseHomotopy

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Periods CuspFilling CuspLocalPhaseAction CuspCollar
open CuspPeriodExpansion InfiniteA2Toric
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}

public theorem polarModulus_frozenDeck
    (P : PolarHoneycombData M r) (L : PolarPhaseDeckLift N M r P)
    (hmod : ∀ k p, P.modulus (compactPhaseOrbit M r P.positivePart (k, p)) = p) :
    let _ := P.positiveDeckAction
    let _ := frozenLocalCuspAction N M r
    ∀ (g : Multiplicative ParameterLattice) (x : localCarrier M r),
      P.modulus (g • x) = g • P.modulus x := by
  let _ := P.positiveDeckAction
  let _ := frozenLocalCuspAction N M r
  dsimp only
  intro g x
  obtain ⟨k, hk⟩ := P.polar_surjective x
  have hx : compactPhaseOrbit M r P.positivePart (k, P.modulus x) = x :=
    Subtype.ext hk
  rw [← hx, ← L.deck_orbit g k (P.modulus x), hmod, hmod]

public def frozenPositiveModulusProjection
    (P : PolarHoneycombData M r) (L : PolarPhaseDeckLift N M r P)
    (hmod : ∀ k p, P.modulus (compactPhaseOrbit M r P.positivePart (k, p)) = p) :
    let _ := P.positiveDeckAction
    C(FrozenLocalCuspFilling N M r, PolarHoneycombData.OrbitQuotient P.positivePart) := by
  let _ := P.positiveDeckAction
  let _ := frozenLocalCuspAction N M r
  refine ⟨Quotient.lift (fun x ↦ Quotient.mk _ (P.modulus x)) ?_, ?_⟩
  · intro a b hab
    change MulAction.orbitRel (Multiplicative ParameterLattice) (localCarrier M r) a b at hab
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab
    obtain ⟨g, rfl⟩ := hab
    apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice) P.positivePart
      (P.modulus (g • b)) (P.modulus b)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨g, (polarModulus_frozenDeck P L hmod g b).symm⟩
  · apply Continuous.quotient_lift
    exact continuous_quot_mk.comp P.modulus.continuous


public def actualPositiveModulusProjection
    (W : ActualPuncturedCuspCollarWitness N M)
    (P : PolarHoneycombData M W.localWitness.radius)
    (L : PolarPhaseDeckLift N M W.localWitness.radius P)
    (hmod : ∀ k p, P.modulus (compactPhaseOrbit M W.localWitness.radius P.positivePart (k, p)) = p) :
    let _ := P.positiveDeckAction
    C(ActualLocalCuspFilling W, PolarHoneycombData.OrbitQuotient P.positivePart) := by
  let _ := P.positiveDeckAction
  exact (frozenPositiveModulusProjection P L hmod).comp
    (quotientStraighteningHomeomorph W : C(_, _))


public theorem polarModulus_compactPhase
    (P : PolarHoneycombData M r)
    (hmod : ∀ k p, P.modulus (compactPhaseOrbit M r P.positivePart (k, p)) = p)
    (k : CompactTorus) (x : localCarrier M r) :
    P.modulus (compactPhaseLocalAction M r k x) = P.modulus x := by
  obtain ⟨l, hl⟩ := P.polar_surjective x
  have h : compactPhaseLocalAction M r k x =
      compactPhaseOrbit M r P.positivePart (k * l, P.modulus x) := by
    apply Subtype.ext
    change M.torusAction (compactTorusEmbedding k) x.1 =
      M.torusAction (compactTorusEmbedding (k * l)) (P.modulus x).1.1
    rw [← hl, map_mul, map_mul, Equiv.Perm.mul_apply]
  rw [h, hmod]

public theorem actualPositiveModulusProjection_central_compact
    (W : ActualPuncturedCuspCollarWitness N M)
    (P : PolarHoneycombData M W.localWitness.radius)
    (L : PolarPhaseDeckLift N M W.localWitness.radius P)
    (hmod : ∀ k p, P.modulus (compactPhaseOrbit M W.localWitness.radius P.positivePart (k, p)) = p)
    (k : CompactTorus) (x : localCarrier M W.localWitness.radius) (hx : M.t x.1 = 0) :
    let _ := P.positiveDeckAction
    actualPositiveModulusProjection W P L hmod
      (Quotient.mk _ (compactPhaseLocalAction M W.localWitness.radius k x)) =
      actualPositiveModulusProjection W P L hmod (Quotient.mk _ x) := by
  let _ := P.positiveDeckAction
  change Quotient.mk _ (P.modulus (CuspStraightening.pointStraightening W _)) =
    Quotient.mk _ (P.modulus (CuspStraightening.pointStraightening W x))
  rw [CuspStraightening.pointStraightening_of_t_eq_zero W x hx,
    CuspStraightening.pointStraightening_of_t_eq_zero W _ ?_,
    polarModulus_compactPhase P hmod]
  change M.t (M.torusAction _ x.1) = 0
  rw [M.t_torusAction, hx, mul_zero]

end SphereSixComplex.Geometry.CuspStraighteningRetraction
