module

public import SphereSixComplex.Topology.CircleProductIdentityMappingTorus
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasisProof

/-!
# Positive circle cross-products
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.PositiveCircleCross

open StandardTorusHomology

/-- Product a map with the identity of the oriented circle. -/
public def circleProductMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : C(UnitAddCircle × X, UnitAddCircle × Y) where
  toFun p := (p.1, f p.2)
  continuous_toFun := continuous_fst.prodMk (f.continuous.comp continuous_snd)

/-- The head--tail identification of two standard circles with the standard two-torus. -/
public def circleProdStandardCircleHomeomorph :
    UnitAddCircle × StdTorus 1 ≃ₜ StdTorus 2 where
  toFun p := Fin.cons p.1 p.2
  invFun z := (z 0, Fin.tail z)
  left_inv p := by ext <;> rfl
  right_inv z := Fin.cons_self_tail z
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The positive cross-product generator `[S¹]₊ × [S¹]₊`. -/
public def positiveCircleProductGenerator :
    IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1) :=
  (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).symm
    standardTwoTorusHomologyGenerator

/-- Cross the positive base-circle class with a parametrized circle in the fibre. -/
public def positiveCircleCross {X : Type} [TopologicalSpace X]
    (c : C(StdTorus 1, X)) :
    IntegralSingularHomology 2 (UnitAddCircle × X) :=
  integralSingularHomologyMap 2 (circleProductMap c) positiveCircleProductGenerator

end SphereSixComplex.Topology.PositiveCircleCross

end

end
