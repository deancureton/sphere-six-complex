module

public import SphereSixComplex.Prerequisites.Topology.PositiveCircleCross

/-!
# The positive generator of the canonical product Wang boundary

The explicit torus coordinates identify the canonical product Wang boundary of the selected
positive degree-two generator.  This calculation is independent of any orbit-sweep theorem.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.CanonicalProductWangBoundarySlant

open CircleProductIdentityMappingTorus
open PositiveCircleCross
open StandardTorusHomology
open CyclicAngularFundamentalDomain

private theorem reflMappingTorusHomologySplit_right
    {F : Type} [TopologicalSpace F] (k a m : ℕ)
    (e1 : IntegralSingularHomology (k + 1) F ≃+ (Fin a → ℤ))
    (e0 : IntegralSingularHomology k F ≃+ (Fin m → ℤ))
    (z : IntegralSingularHomology (k + 1)
      (CircleMappingTorus (Homeomorph.refl F))) (j : Fin m) :
    reflMappingTorusHomologySplit k a m e1 e0 z
        (finSumFinEquiv (Sum.inr j)) =
      e0 ((circleMappingTorusWangPresentationOfCover
        (Homeomorph.refl F) k).boundary z) j := by
  classical
  set P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) k
  have hhigh : P.highDifference = 0 :=
    circleMonodromyDifference_refl (F := F) (k + 1)
  have hlow : P.lowDifference = 0 := circleMonodromyDifference_refl (F := F) k
  have hi : Function.Injective P.inclusion := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨c, hc⟩ := (P.exact_highDifference_inclusion b).mp hb
    rw [hhigh] at hc
    simpa using hc.symm
  have hbsurj : Function.Surjective P.boundary := by
    intro y
    exact (P.exact_boundary_lowDifference y).mp (by rw [hlow]; rfl)
  let q : IntegralSingularHomology (k + 1)
      (CircleMappingTorus (Homeomorph.refl F)) →+ (Fin m → ℤ) :=
    e0.toAddMonoidHom.comp P.boundary
  have hq : Function.Surjective q := e0.surjective.comp hbsurj
  have hex : Function.Exact P.inclusion q := by
    intro b
    rw [← P.exact_inclusion_boundary b]
    constructor
    · intro h
      have h' : e0 (P.boundary b) = 0 := h
      exact e0.injective (by rw [h', map_zero])
    · intro h
      show e0 (P.boundary b) = 0
      rw [h, map_zero]
  have hs := splitOfFreeQuotient_snd P.inclusion q hi hq hex z
  unfold reflMappingTorusHomologySplit
  simp only [AddEquiv.trans_apply, finArrowProdAddEquiv, AddEquiv.coe_mk,
    Equiv.coe_fn_mk, Equiv.symm_apply_apply, Sum.elim_inr]
  have ht :
      ((e1.prodCongr (AddEquiv.refl _))
        ((splitOfFreeQuotient P.inclusion q hi hq hex) z)).2 = q z := by
    change (splitOfFreeQuotient P.inclusion q hi hq hex z).2 = q z
    exact hs
  simpa [q] using congrFun ht j

private theorem circleProduct_stdTorus_homeomorph :
    (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1)).trans
        (stdTorusMappingTorusHomeomorph 1) =
      circleProdStandardCircleHomeomorph := by
  ext p k
  change ((stdTorusSplit 1).symm
    (circleProductIdentityMappingTorusHomeomorph.symm
      (circleProductIdentityMappingTorusHomeomorph p))) k = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The canonical product Wang boundary of the selected degree-two generator has winding
coordinate `+1`. -/
public theorem canonicalProductWangBoundary_positiveGenerator_coordinate_core :
    standardCircleCanonicalHomologyOne
        (canonicalProductWangBoundary 1 positiveCircleProductGenerator) =
      Pi.single (0 : Fin 1) 1 := by
  let P := circleMappingTorusWangPresentationOfCover
    (Homeomorph.refl (StdTorus 1)) 1
  let eT := integralSingularHomologyEquiv 2 (stdTorusMappingTorusHomeomorph 1)
  let y := eT.symm standardTwoTorusHomologyGenerator
  have hcomp :
      (stdTorusMappingTorusHomeomorph 1 :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), StdTorus 2)).comp
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1)))) =
        (circleProdStandardCircleHomeomorph :
          C(UnitAddCircle × StdTorus 1, StdTorus 2)) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg (fun e : (UnitAddCircle × StdTorus 1) ≃ₜ StdTorus 2 ↦ e p)
      circleProduct_stdTorus_homeomorph
  have hy :
      integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
          positiveCircleProductGenerator = y := by
    apply eT.injective
    rw [eT.apply_symm_apply]
    change integralSingularHomologyMap 2
        (stdTorusMappingTorusHomeomorph 1 :
          C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), StdTorus 2))
        (integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
          positiveCircleProductGenerator) = standardTwoTorusHomologyGenerator
    rw [integralSingularHomologyMap_comp_wang, hcomp]
    exact (integralSingularHomologyEquiv 2
      circleProdStandardCircleHomeomorph).apply_symm_apply _
  have hcoordinate :
      standardCircleCanonicalHomologyOne (P.boundary y) = Pi.single (0 : Fin 1) 1 := by
    funext j
    fin_cases j
    change standardCircleCanonicalHomologyOne (P.boundary y) 0 = 1
    dsimp [P]
    rw [← reflMappingTorusHomologySplit_right 1 0 1
      (stdTorusHomologyTwo 1) standardCircleCanonicalHomologyOne y 0]
    rw [← eT.symm_apply_apply y]
    change stdTorusHomologyTwo 2 (eT y)
      (finSumFinEquiv (Sum.inr (0 : Fin 1))) = 1
    rw [eT.apply_symm_apply]
    rw [show stdTorusHomologyTwo 2 standardTwoTorusHomologyGenerator =
        Pi.single standardTwoTorusDegreeTwoIndex 1 by
      exact (stdTorusHomologyTwo 2).apply_symm_apply _]
    rw [show finSumFinEquiv (Sum.inr (0 : Fin 1)) =
        standardTwoTorusDegreeTwoIndex by
      apply Fin.ext
      rfl]
    exact Pi.single_eq_same _ _
  change standardCircleCanonicalHomologyOne
      (P.boundary
        (integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
          positiveCircleProductGenerator)) = Pi.single (0 : Fin 1) 1
  rw [hy, hcoordinate]

public theorem canonicalProductWangBoundary_positiveGenerator_core :
    canonicalProductWangBoundary 1 positiveCircleProductGenerator =
      standardCircleHomologyGenerator := by
  apply standardCircleCanonicalHomologyOne.injective
  rw [canonicalProductWangBoundary_positiveGenerator_coordinate_core,
    standardCircleCanonicalHomologyOne_generator]

end SphereSixComplex.Topology.CanonicalProductWangBoundarySlant

end

end
