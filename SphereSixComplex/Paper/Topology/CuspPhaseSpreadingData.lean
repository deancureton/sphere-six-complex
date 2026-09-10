module

public import SphereSixComplex.Paper.Topology.ActualCuspStraighteningRetraction
public import SphereSixComplex.Paper.Topology.StandardInfiniteA2PositiveRetraction

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
open InfiniteA2Toric

/-- The action of compact phases on the positive part of a local toric carrier. -/
public def compactPhaseOrbit (M : Model) (r : ℝ)
    (positivePart : Set (localCarrier M r)) :
    CompactTorus × positivePart → localCarrier M r :=
  fun z ↦ ⟨M.torusAction (compactTorusEmbedding z.1) (z.2 : M.Carrier), by
    change M.t (M.torusAction (compactTorusEmbedding z.1) (z.2 : M.Carrier)) ∈
      Metric.ball 0 r
    rw [Metric.mem_ball, dist_zero_right, M.t_torusAction, norm_mul]
    change ‖(z.1 2 : ℂ)‖ * ‖M.t (z.2 : localCarrier M r)‖ < r
    rw [Circle.norm_coe, one_mul]
    simpa only [dist_zero_right] using Metric.mem_ball.mp
      (z.2 : localCarrier M r).property⟩

public theorem continuous_compactTorusEmbedding : Continuous compactTorusEmbedding := by
  apply continuous_pi
  intro i
  rw [Units.isEmbedding_val₀.isInducing.continuous_iff]
  exact continuous_subtype_val.comp (continuous_apply i)

public theorem continuous_compactPhaseOrbit (M : Model) (r : ℝ)
    (positivePart : Set (localCarrier M r)) :
    Continuous (compactPhaseOrbit M r positivePart) := by
  let J := InfiniteA2Toric.continuousTorusAction M
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
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (P : PolarHoneycombData M r) where
  positiveRetraction :
    letI := P.positiveDeckAction
    EquivariantStrongDeformationRetraction
      (Multiplicative ParameterLattice) P.positivePart P.central
  phaseOrbit_prod_isQuotientMap :
    Topology.IsQuotientMap
      (Prod.map (id : unitInterval → unitInterval)
        (compactPhaseOrbit M r P.positivePart))
  deckPhase : Multiplicative ParameterLattice → CompactTorus → CompactTorus
  deck_orbit :
    letI := P.positiveDeckAction
    letI := frozenLocalCuspAction N M r
    ∀ g k p, compactPhaseOrbit M r P.positivePart (deckPhase g k, g • p) =
      g • compactPhaseOrbit M r P.positivePart (k, p)
  homotopy_fiberwise :
    letI := P.positiveDeckAction
    let R := positiveRetraction
    ∀ s k p l q,
      compactPhaseOrbit M r P.positivePart (k, p) =
        compactPhaseOrbit M r P.positivePart (l, q) →
      compactPhaseOrbit M r P.positivePart (k, R.homotopy (s, p)) =
        compactPhaseOrbit M r P.positivePart (l, R.homotopy (s, q))

end SphereSixComplex.Geometry.CuspStraighteningRetraction
