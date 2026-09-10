module

public import SphereSixComplex.Prerequisites.Topology.CircleProductIdentityMappingTorus
public import SphereSixComplex.Prerequisites.Topology.NormalizedCoverCrossLowOverlapCalculationProof

import all SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof

/-!
Wang exactness and the fibre projection give a unique lift with zero fibre projection.
This constructs additive circle crosses without a choice of homology basis.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.CircleProductIdentityMappingTorus

variable {X : Type} [TopologicalSpace X]

public def productFiberProjection : C(UnitAddCircle × X, X) where
  toFun := Prod.snd
  continuous_toFun := continuous_snd

public theorem productFiberProjection_inclusion (k : ℕ)
    (x : IntegralSingularHomology (k + 1) X) :
    integralSingularHomologyMap (k + 1) productFiberProjection
      (integralSingularHomologyMap (k + 1) productFiberInclusion x) = x := by
  rw [integralSingularHomologyMap_comp_wang]
  change integralSingularHomologyMap (k + 1) (ContinuousMap.id X) x = x
  exact integralSingularHomologyMap_id_wang (k + 1) x

public theorem circleProductClass_ext (k : ℕ)
    {x y : IntegralSingularHomology (k + 1) (UnitAddCircle × X)}
    (hboundary : canonicalProductWangBoundary k x = canonicalProductWangBoundary k y)
    (hprojection : integralSingularHomologyMap (k + 1) productFiberProjection x =
      integralSingularHomologyMap (k + 1) productFiberProjection y) : x = y := by
  have hz : canonicalProductWangBoundary k (x - y) = 0 := by
    rw [map_sub, hboundary, sub_self]
  obtain ⟨a, ha⟩ := (canonicalProductWang_exact k (x - y)).mp hz
  have hp := congrArg (integralSingularHomologyMap (k + 1) productFiberProjection) ha
  rw [productFiberProjection_inclusion, map_sub, hprojection, sub_self] at hp
  rw [hp, map_zero] at ha
  exact sub_eq_zero.mp ha.symm

public theorem exists_normalizedCircleCross (k : ℕ)
    (x : IntegralSingularHomology k X) :
    ∃ y : IntegralSingularHomology (k + 1) (UnitAddCircle × X),
      canonicalProductWangBoundary k y = x ∧
        integralSingularHomologyMap (k + 1) productFiberProjection y = 0 := by
  obtain ⟨y, hy⟩ := canonicalProductWangBoundary_surjective k x
  refine ⟨y - integralSingularHomologyMap (k + 1) productFiberInclusion
    (integralSingularHomologyMap (k + 1) productFiberProjection y), ?_, ?_⟩
  · rw [map_sub, hy, (canonicalProductWang_exact k).apply_apply_eq_zero, sub_zero]
  · rw [map_sub, productFiberProjection_inclusion, sub_self]

public noncomputable def normalizedCircleCross (k : ℕ) :
    IntegralSingularHomology k X →+ IntegralSingularHomology (k + 1) (UnitAddCircle × X) where
  toFun x := Classical.choose (exists_normalizedCircleCross k x)
  map_zero' := by
    apply circleProductClass_ext k
    · rw [(Classical.choose_spec (exists_normalizedCircleCross k 0)).1, map_zero]
    · rw [(Classical.choose_spec (exists_normalizedCircleCross k 0)).2, map_zero]
  map_add' x y := by
    apply circleProductClass_ext k
    · rw [(Classical.choose_spec (exists_normalizedCircleCross k (x + y))).1, map_add,
        (Classical.choose_spec (exists_normalizedCircleCross k x)).1,
        (Classical.choose_spec (exists_normalizedCircleCross k y)).1]
    · rw [(Classical.choose_spec (exists_normalizedCircleCross k (x + y))).2, map_add,
        (Classical.choose_spec (exists_normalizedCircleCross k x)).2,
        (Classical.choose_spec (exists_normalizedCircleCross k y)).2, add_zero]

public theorem normalizedCircleCross_boundary (k : ℕ)
    (x : IntegralSingularHomology k X) :
    canonicalProductWangBoundary k (normalizedCircleCross k x) = x :=
  (Classical.choose_spec (exists_normalizedCircleCross k x)).1

public theorem normalizedCircleCross_projection (k : ℕ)
    (x : IntegralSingularHomology k X) :
    integralSingularHomologyMap (k + 1) productFiberProjection
      (normalizedCircleCross k x) = 0 :=
  (Classical.choose_spec (exists_normalizedCircleCross k x)).2

open StandardTorusHomology PositiveCircleCross

public theorem positiveCircleCross_projection
    (c : C(StdTorus 1, X)) :
    integralSingularHomologyMap 2 productFiberProjection (positiveCircleCross c) = 0 := by
  let : Subsingleton (IntegralSingularHomology 2 (StdTorus 1)) := by
    constructor
    intro x y
    apply (stdTorusHomologyTwo 1).injective
    funext i
    exact Fin.elim0 i
  rw [positiveCircleCross, integralSingularHomologyMap_comp_wang]
  have hc : productFiberProjection.comp (circleProductMap c) =
      c.comp (productFiberProjection (X := StdTorus 1)) := rfl
  rw [hc, ← integralSingularHomologyMap_comp_wang]
  rw [Subsingleton.elim
    (integralSingularHomologyMap 2 productFiberProjection positiveCircleProductGenerator) 0,
    map_zero]

public theorem positiveCircleCross_eq_normalized
    {G : Type} [TopologicalSpace G]
    (c : C(StdTorus 1, G)) :
    positiveCircleCross c = normalizedCircleCross 1
      (integralSingularHomologyMap 1 c standardCircleHomologyGenerator) := by
  apply circleProductClass_ext 1
  · rw [FixedTopologicalCircleWangBoundary.canonicalProductWangBoundary_positiveCircleCross,
      normalizedCircleCross_boundary]
  · rw [positiveCircleCross_projection, normalizedCircleCross_projection]

public theorem positiveCircleCross_add
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G] (c d : C(StdTorus 1, G)) :
    positiveCircleCross (c + d) = positiveCircleCross c + positiveCircleCross d := by
  rw [positiveCircleCross_eq_normalized, positiveCircleCross_eq_normalized,
    positiveCircleCross_eq_normalized,
    NormalizedFiniteOrderAdditiveCircleSweepProof.standardCircleHomologyClass_map_add,
    map_add]

public noncomputable def circleSweepClass
    {Y : Type} [TopologicalSpace Y]
    (sweep : C(UnitAddCircle × X, Y)) {x : X} (p : Path x x) :
    IntegralSingularHomology 2 Y :=
  integralSingularHomologyMap 2 sweep
    (normalizedCircleCross 1 (StandardCircleHomologyLiftDegree.loopHomologyClass p))

public theorem circleSweepClass_trans
    {Y : Type} [TopologicalSpace Y]
    (sweep : C(UnitAddCircle × X, Y)) {x : X} (p q : Path x x) :
    circleSweepClass sweep (p.trans q) = circleSweepClass sweep p + circleSweepClass sweep q := by
  simp only [circleSweepClass, Hurewicz.Chains.loopHomologyClass_trans, map_add]

public theorem circleSweepClass_homotopic
    {Y : Type} [TopologicalSpace Y]
    (sweep : C(UnitAddCircle × X, Y)) {x : X} {p q : Path x x}
    (h : p.Homotopic q) : circleSweepClass sweep p = circleSweepClass sweep q := by
  obtain ⟨H⟩ := h
  rw [circleSweepClass, circleSweepClass, Hurewicz.Chains.loopHomologyClass_homotopic H]

end SphereSixComplex.Topology.CircleProductIdentityMappingTorus

end
end


@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Topology.CircleProductIdentityMappingTorus
open StandardTorusHomology PositiveCircleCross StandardCircleHomologyLiftDegree
variable {X : Type} [TopologicalSpace X]

public noncomputable def pathCircleMap {x : X} (p : Path x x) : C(StdTorus 1, X) where
  toFun z := AddCircle.liftIco (1 : ℝ) 0 p.extend (z 0)
  continuous_toFun := (AddCircle.liftIco_zero_continuous
    (by simp : p.extend 0 = p.extend 1) p.continuous_extend.continuousOn).comp
      (continuous_apply 0)

public theorem pathCircleMap_loop {x : X} (p : Path x x) (t : unitInterval) :
    pathCircleMap p (standardCirclePositiveLoop t) = p t := by
  change AddCircle.liftIco (1 : ℝ) 0 p.extend (((t : ℝ) * ((1 : ℤ) : ℝ) : ℝ) : UnitAddCircle) = p t
  simp only [Int.cast_one, mul_one]
  by_cases ht : (t : ℝ) = 1
  · have ht' : t = 1 := Subtype.ext ht
    subst t
    change AddCircle.liftIco (1 : ℝ) 0 p.extend ((1 : ℝ) : UnitAddCircle) = p 1
    rw [show ((1 : ℝ) : UnitAddCircle) = 0 by exact AddCircle.coe_period 1]
    rw [← show ((0 : ℝ) : UnitAddCircle) = 0 from rfl,
      AddCircle.liftIco_zero_coe_apply ⟨le_refl 0, zero_lt_one⟩]
    simp
  · rw [AddCircle.liftIco_zero_coe_apply ⟨t.2.1, lt_of_le_of_ne t.2.2 ht⟩,
      p.extend_apply t.2]

public theorem pathCircleMap_homology {x : X} (p : Path x x) :
    integralSingularHomologyMap 1 (pathCircleMap p) standardCircleHomologyGenerator =
      loopHomologyClass p := by
  rw [standardCircleHomologyGenerator, integralSingularHomologyMap_loopHomologyClass]
  have hx : pathCircleMap p 0 = x := by
    simpa using pathCircleMap_loop p 0
  have hp : (standardCirclePositiveLoop.map (pathCircleMap p).continuous).cast hx.symm hx.symm = p := by
    ext t
    exact pathCircleMap_loop p t
  rw [← loopHomologyClass_cast _ hx.symm, hp]

public theorem normalizedCircleCross_naturality
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace X]
    (f : C(X, Y)) (x : IntegralSingularHomology 1 X) :
    integralSingularHomologyMap 2 (circleProductMap f) (normalizedCircleCross 1 x) =
      normalizedCircleCross 1 (integralSingularHomologyMap 1 f x) := by
  let b : X := Classical.choice inferInstance
  let H := Hurewicz.Chains.abelianizationComparison X b
  obtain ⟨p, hp⟩ := Hurewicz.loopClass_surjective (H.equiv.symm x)
  have hx : loopHomologyClass p = x := by
    rw [← H.equiv_loopClass, hp, H.equiv.apply_symm_apply]
  rw [← hx, ← pathCircleMap_homology p, ← positiveCircleCross_eq_normalized]
  rw [positiveCircleCross, integralSingularHomologyMap_comp_wang]
  have hcomp : (circleProductMap f).comp (circleProductMap (pathCircleMap p)) =
      circleProductMap (f.comp (pathCircleMap p)) := rfl
  rw [hcomp]
  change positiveCircleCross (f.comp (pathCircleMap p)) = _
  rw [positiveCircleCross_eq_normalized, integralSingularHomologyMap_comp_wang]

end SphereSixComplex.Topology.CircleProductIdentityMappingTorus
end
end
