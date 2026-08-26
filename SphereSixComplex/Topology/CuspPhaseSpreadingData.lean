module

public import SphereSixComplex.Topology.ActualCuspStraighteningRetraction
public import SphereSixComplex.Topology.StandardInfiniteA2PositiveRetraction

/-!
# Phase-spreading compatibility data

This file defines the orbit, deck-action, and stabilizer compatibility interface shared by the
standard `A₂` existence theorem and the actual cusp retraction.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.CuspStraighteningRetraction

open SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspPeriodExpansion
open StandardInfiniteA2ToricModel

/-- The action of compact phases on the positive part of a local toric carrier. -/
public def compactPhaseOrbit (M : Model) (r : ℝ)
    (positivePart : Set (LocalCarrier M r)) :
    CompactTorus × positivePart → LocalCarrier M r :=
  fun z ↦ ⟨M.torusAction (compactTorusEmbedding z.1) (z.2 : M.Carrier), by
    change M.t (M.torusAction (compactTorusEmbedding z.1) (z.2 : M.Carrier)) ∈
      Metric.ball 0 r
    rw [Metric.mem_ball, dist_zero_right, M.t_torusAction, norm_mul]
    change ‖(z.1 2 : ℂ)‖ * ‖M.t (z.2 : LocalCarrier M r)‖ < r
    rw [Circle.norm_coe, one_mul]
    simpa only [dist_zero_right] using Metric.mem_ball.mp
      (z.2 : LocalCarrier M r).property⟩

public theorem continuous_compactTorusEmbedding : Continuous compactTorusEmbedding := by
  apply continuous_pi
  intro i
  rw [Units.isEmbedding_val₀.isInducing.continuous_iff]
  exact continuous_subtype_val.comp (continuous_apply i)

public theorem continuous_compactPhaseOrbit (M : Model) (r : ℝ)
    (positivePart : Set (LocalCarrier M r)) :
    Continuous (compactPhaseOrbit M r positivePart) := by
  let J := StandardInfiniteA2ToricModel.Established.establishedContinuousTorusAction M
  have hg : Continuous (fun z : CompactTorus × positivePart ↦ compactTorusEmbedding z.1) :=
    continuous_compactTorusEmbedding.comp continuous_fst
  have hp : Continuous (fun z : CompactTorus × positivePart ↦ (z.2 : M.Carrier)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have h := J.variable_action hg hp
  rw [continuous_induced_rng]
  exact h

/-- The exact orbit-stratum and deck-action compatibility still required from the standard
toric cellular contraction. -/
public structure FrozenLocalCuspPhaseSpreadingData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (P : PolarHoneycombData M r) where
  phaseOrbit_isOpenQuotientMap :
    IsOpenQuotientMap (compactPhaseOrbit M r P.positivePart)
  deckPhase : Multiplicative ParameterLattice → CompactTorus → CompactTorus
  deck_orbit :
    letI := P.positiveDeckAction
    letI := frozenLocalCuspAction N M r
    ∀ g k p, compactPhaseOrbit M r P.positivePart (deckPhase g k, g • p) =
      g • compactPhaseOrbit M r P.positivePart (k, p)
  homotopy_fiberwise :
    letI := P.positiveDeckAction
    let R := P.positiveEquivariantStrongDeformationRetraction
    ∀ s k p l q,
      compactPhaseOrbit M r P.positivePart (k, p) =
        compactPhaseOrbit M r P.positivePart (l, q) →
      compactPhaseOrbit M r P.positivePart (k, R.homotopy (s, p)) =
        compactPhaseOrbit M r P.positivePart (l, R.homotopy (s, q))

end SphereSixComplex.Geometry.CuspStraighteningRetraction
