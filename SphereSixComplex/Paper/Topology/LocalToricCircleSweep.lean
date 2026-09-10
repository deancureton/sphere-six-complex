module
public import SphereSixComplex.Prerequisites.Topology.SimplyConnectedCircleSweep
public import SphereSixComplex.Paper.Geometry.EstablishedContinuousTorusAction

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Topology CuspStraighteningExtension
open CuspPhaseEstimates CuspLocalPhaseAction

public def localHeightPreservingCircleAction (M : Model) (r : ℝ)
    (g : C(UnitAddCircle, DenseTorus)) (hg : ∀ z, g z 2 = 1) :
    C(UnitAddCircle × LocalCarrier M r, LocalCarrier M r) where
  toFun z := ⟨M.torusAction (g z.1) z.2, by
    change M.t (M.torusAction (g z.1) z.2) ∈ Metric.ball 0 r
    rw [M.t_torusAction, hg, Units.val_one, one_mul]
    exact z.2.property⟩
  continuous_toFun := ((Established.establishedContinuousTorusAction M).variable_action
    (g.continuous.comp continuous_fst) (continuous_subtype_val.comp continuous_snd)).subtype_mk _

public theorem localHeightPreservingCircleSweep_zero (M : Model) (r : ℝ) (hr : 0 < r)
    (g : C(UnitAddCircle, DenseTorus)) (hg : ∀ z, g z 2 = 1)
    (f : C(UnitAddCircle × StandardTorusHomology.StdTorus 1,
      UnitAddCircle × LocalCarrier M r))
    (p : C(StandardTorusHomology.StdTorus 1, LocalCarrier M r))
    (h : C(UnitAddCircle × StandardTorusHomology.StdTorus 1, StandardTorusHomology.StdTorus 1))
    (hf : CircleProductIdentityMappingTorus.productFiberProjection.comp f = p.comp h)
    (x : IntegralSingularHomology 2 (UnitAddCircle × StandardTorusHomology.StdTorus 1)) :
    integralSingularHomologyMap 2 ((localHeightPreservingCircleAction M r g hg).comp f) x = 0 := by
  let : SimplyConnectedSpace (LocalCarrier M r) := M.localCarrierSimplyConnected r hr
  rw [← integralSingularHomologyMap_comp_wang, circleFactor_homologyTwo_zero f p h hf, map_zero]

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
