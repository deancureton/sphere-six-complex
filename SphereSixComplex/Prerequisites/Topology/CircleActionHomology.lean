module

public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology
open CircleProductIdentityMappingTorus StandardTorusHomology

public theorem circleAction_torus_homologyTwo_eq_zero
    {X : Type} [TopologicalSpace X] [Subsingleton (IntegralSingularHomology 1 X)]
    (f : C(UnitAddCircle × StdTorus 1, X))
    (g : C(UnitAddCircle × X, X))
    (hf : ∀ t s, f (t, s) = g (s 0, f (t, 0)))
    (x : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 1)) :
    integralSingularHomologyMap 2 f x = 0 := by
  let lift : C(UnitAddCircle × StdTorus 1, UnitAddCircle × X) :=
    ⟨fun p ↦ (p.2 0, f (p.1, 0)), by fun_prop⟩
  have hz : integralSingularHomologyMap 2 lift x = 0 := by
    apply circleProductClass_ext 1
    · exact Subsingleton.elim _ _
    · rw [map_zero, integralSingularHomologyMap_comp_wang]
      let b : C(StdTorus 1, X) := ⟨fun s ↦ f (s 0, 0), by fun_prop⟩
      let h : C(UnitAddCircle × StdTorus 1, StdTorus 1) :=
        ⟨fun p _ ↦ p.1, by fun_prop⟩
      have he : productFiberProjection.comp lift = b.comp h := rfl
      rw [he, ← integralSingularHomologyMap_comp_wang]
      let : Subsingleton (IntegralSingularHomology 2 (StdTorus 1)) := by
        constructor
        intro a b
        apply (stdTorusHomologyTwo 1).injective
        funext i
        exact Fin.elim0 i
      rw [Subsingleton.elim (integralSingularHomologyMap 2 h x) 0, map_zero]
  have he : f = g.comp lift := by
    ext p
    exact hf p.1 p.2
  rw [he, ← integralSingularHomologyMap_comp_wang, hz, map_zero]

end SphereSixComplex.Topology
