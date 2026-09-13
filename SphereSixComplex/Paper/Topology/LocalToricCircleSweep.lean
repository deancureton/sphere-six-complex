module

public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof
public import SphereSixComplex.Paper.Geometry.EstablishedContinuousTorusAction

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Topology CuspStraightening
open CuspPhaseEstimates CuspLocalPhaseAction

public def localHeightPreservingCircleAction (M : Model) (r : ℝ)
    (g : C(UnitAddCircle, DenseTorus)) (hg : ∀ z, g z 2 = 1) :
    C(UnitAddCircle × localCarrier M r, localCarrier M r) where
  toFun z := ⟨M.torusAction (g z.1) z.2, by
    change M.t (M.torusAction (g z.1) z.2) ∈ Metric.ball 0 r
    rw [M.t_torusAction, hg, Units.val_one, one_mul]
    exact z.2.property⟩
  continuous_toFun := ((continuous_torusAction M).comp
    ((g.continuous.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

end SphereSixComplex.Geometry.InfiniteA2Toric
