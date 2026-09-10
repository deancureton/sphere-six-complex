module

public import SphereSixComplex.Prerequisites.Topology.FiniteCyclicProductMappingTorus
public import SphereSixComplex.Prerequisites.Topology.StandardTorusHomology

/-!
# Degree-two coordinates on circle times the standard three-torus
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.StandardTorusHomology

open CyclicMappingTorus

/-- The standard four-torus basis transported through the head-circle/tail-torus split. -/
public noncomputable def standardCircleProdThreeTorusHomologyTwo :
    IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3) ≃+ (Fin 6 → ℤ) :=
  (integralSingularHomologyEquiv 2 fourTorusSplit.symm).trans
    naturalStdTorusFourHomologyTwo

@[simp]
public theorem standardCircleProdThreeTorusHomologyTwo_apply (x) :
    standardCircleProdThreeTorusHomologyTwo x =
      naturalStdTorusFourHomologyTwo
        (integralSingularHomologyMap 2 fourTorusSplit.symm x) :=
  rfl

end SphereSixComplex.StandardTorusHomology

end

end
