module

public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
import all SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Topology
open CircleProductIdentityMappingTorus StandardTorusHomology

public theorem firstHomology_subsingleton_of_simplyConnected
    (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X] :
    Subsingleton (IntegralSingularHomology 1 X) := by
  let b : X := Classical.choice inferInstance
  let e := FirstHurewiczProof.firstHurewiczEquiv b
  let : Subsingleton (EstablishedFirstHurewicz.AbelianPi1 X b) := by
    change Subsingleton (Additive (FundamentalGroup X b ⧸ commutator (FundamentalGroup X b)))
    constructor
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg (Quotient.mk _) (Subsingleton.elim x y)
  exact e.symm.injective.subsingleton

public theorem circleFactor_homologyTwo_zero
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (f : C(UnitAddCircle × StdTorus 1, UnitAddCircle × X))
    (g : C(StdTorus 1, X)) (h : C(UnitAddCircle × StdTorus 1, StdTorus 1))
    (hf : productFiberProjection.comp f = g.comp h)
    (x : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1)) :
    integralSingularHomologyMap 2 f x = 0 := by
  let := firstHomology_subsingleton_of_simplyConnected X
  apply circleProductClass_ext 1
  · exact Subsingleton.elim _ _
  · rw [map_zero, integralSingularHomologyMap_comp_wang, hf,
      ← integralSingularHomologyMap_comp_wang]
    let : Subsingleton (IntegralSingularHomology 2 (StdTorus 1)) := by
      constructor
      intro x y
      apply (stdTorusHomologyTwo 1).injective
      funext i
      exact Fin.elim0 i
    rw [Subsingleton.elim (integralSingularHomologyMap 2 h x) 0, map_zero]

end SphereSixComplex.Topology
