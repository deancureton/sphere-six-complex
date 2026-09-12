module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveSingletonBall
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
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}
namespace Construction


public theorem closedBallPositiveCell_boundary_support_ge_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) (hx : x.1 ∈ Metric.sphere 0 1) :
    2 ≤ (componentSupport constructedModel
      ((closedBallPositiveCellHomeomorph W x).1.1.1.1 : Carrier)).ncard := by
  let q := closedBallPositiveCellHomeomorph W x
  let S := componentSupport constructedModel (q.1.1.1.1 : Carrier)
  have hzero : (0 : ToricLattice) ∈ S := q.property
  have hfinite : S.Finite := componentSupport_finite _ _
  have hpos : 0 < S.ncard := (Set.ncard_pos hfinite).mpr ⟨0, hzero⟩
  have hone : S.ncard ≠ 1 := by
    intro hone
    obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp hone
    have hvzero : v = 0 := (Set.mem_singleton_iff.mp (hv ▸ hzero)).symm
    have hs : S = {0} := by simpa [hvzero] using hv
    have hopen := (closedBallPositiveCellHomeomorph_support_iff W x).mp hs
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hx hopen
  change 2 ≤ S.ncard
  omega

public theorem effectivePhaseBall_boundary_mem_boundaryTwoSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) (hx : x.1 ∈ Metric.sphere 0 1)
    (k : Fin 2 → Circle) :
    effectivePhaseCentralOrbit W k
      (closedBallPositiveCellHomeomorph W x).1 ∈
        constructedCentralBoundaryTwoSkeleton W := by
  apply constructedCentral_support_ge_two_mem_boundaryTwoSkeleton
  rw [effectivePhaseCentralPoint_support]
  exact closedBallPositiveCell_boundary_support_ge_two W x hx

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
