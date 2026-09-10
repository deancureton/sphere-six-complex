module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveSingletonBall
public import SphereSixComplex.Paper.Topology.StandardA2ToricBoundaryFaceCoverage

@[expose] public section

noncomputable section

open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2ClosedBallPositiveCell_boundary_support_ge_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) (hx : x.1 ∈ Metric.sphere 0 1) :
    2 ≤ (componentSupport constructedModel
      ((constructedA2ClosedBallPositiveCellHomeomorph W x).1.1.1.1 : Carrier)).ncard := by
  let q := constructedA2ClosedBallPositiveCellHomeomorph W x
  let S := componentSupport constructedModel (q.1.1.1.1 : Carrier)
  have hzero : (0 : ToricLattice) ∈ S := q.property
  have hfinite : S.Finite := componentSupport_finite _ _
  have hpos : 0 < S.ncard := (Set.ncard_pos hfinite).mpr ⟨0, hzero⟩
  have hone : S.ncard ≠ 1 := by
    intro hone
    obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp hone
    have hvzero : v = 0 := (Set.mem_singleton_iff.mp (hv ▸ hzero)).symm
    have hs : S = {0} := by simpa [hvzero] using hv
    have hopen := (constructedA2ClosedBallPositiveCellHomeomorph_support_iff W x).mp hs
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hx hopen
  change 2 ≤ S.ncard
  omega

public theorem constructedA2EffectivePhaseBall_boundary_mem_boundaryTwoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) (hx : x.1 ∈ Metric.sphere 0 1)
    (k : Fin 2 → Circle) :
    constructedA2EffectivePhaseCentralOrbit W k
      (constructedA2ClosedBallPositiveCellHomeomorph W x).1 ∈
        constructedCentralBoundaryTwoSkeleton W := by
  apply constructedCentral_support_ge_two_mem_boundaryTwoSkeleton
  rw [constructedA2EffectivePhaseCentralPoint_support]
  exact constructedA2ClosedBallPositiveCell_boundary_support_ge_two W x hx

end SphereSixComplex.Geometry.InfiniteA2Toric

end
