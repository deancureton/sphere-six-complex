module

public import SphereSixComplex.Paper.Topology.NormalizedPolarHoneycombPhaseGeometryReduction

/-!
# Ambient phase homotopy for a normalized polar honeycomb

The positive retraction currently obtained by abstract covering-space lifting has no formula.
This file gives the minimal explicit replacement: a homotopy of the ambient local carrier whose
restriction is the positive retraction and which commutes with the compact torus.  These two
equations prove phase-fiber preservation without any separate stabilizer calculation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction

/-- The compact-torus action on the full local carrier. -/
public def compactPhaseLocalAction (M : Model) (r : ℝ)
    (k : CompactTorus) (p : localCarrier M r) : localCarrier M r :=
  ⟨M.torusAction (compactTorusEmbedding k) p, by
    change M.t (M.torusAction (compactTorusEmbedding k) (p : M.Carrier)) ∈
      Metric.ball 0 r
    rw [Metric.mem_ball, dist_zero_right, M.t_torusAction, norm_mul]
    change ‖(k 2 : ℂ)‖ * ‖M.t (p : localCarrier M r)‖ < r
    rw [Circle.norm_coe, one_mul]
    simpa only [dist_zero_right] using Metric.mem_ball.mp p.property⟩



end SphereSixComplex.Geometry.InfiniteA2Toric
