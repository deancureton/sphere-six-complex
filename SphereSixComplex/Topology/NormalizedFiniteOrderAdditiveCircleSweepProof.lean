module

public import Mathlib.Topology.Homotopy.HSpaces
public import SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality
public import SphereSixComplex.Topology.EstablishedFirstHurewicz
public import SphereSixComplex.Topology.NormalizedFiniteOrderAdditiveCircleSweep

/-!
# The normalized finite-order additive circle sweep

This file develops the point-set and Wang-naturality ingredients for the general orbit-sweep
theorem.  In particular, the fibre square and invariance under one clutching step follow directly
from the normalized affine quotient, independently of a sweep construction.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.NormalizedFiniteOrderAdditiveCircleSweepProof

open CanonicalProductWangBoundaryNaturality
open CircleProductIdentityMappingTorus
open CyclicAngularFundamentalDomain
open FiniteCyclicMappingTorusWangNaturality
open NormalizedAffineMappingTorusCover
open NormalizedFiniteOrderAdditiveCircleSweep
open PaperAffineCyclicReducedFiberMappingTorus
open PositiveCircleCross
open StandardTorusHomology

variable {m : ℕ} [NeZero m]

private def normalizedBaseStep (X : Type) [TopologicalSpace X] :
    C(UnitAddCircle × X, UnitAddCircle × X) where
  toFun p := (p.1 + ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle), p.2)
  continuous_toFun := by fun_prop

private def normalizedBaseStepHomotopy (X : Type) [TopologicalSpace X] :
    ContinuousMap.Homotopy (ContinuousMap.id (UnitAddCircle × X))
      (normalizedBaseStep (m := m) X) where
  toFun p := (p.2.1 + (((((p.1 : ℝ) / (m : ℝ) : ℝ))) : UnitAddCircle), p.2.2)
  continuous_toFun := by fun_prop
  map_zero_left p := by
    apply Prod.ext <;> simp
  map_one_left p := by
    apply Prod.ext <;> simp [normalizedBaseStep]

private theorem normalizedCover_loopAction_square
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (hpow : phi.toHomeomorph ^ m = 1)
    (c : C(StdTorus 1, G)) :
    (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow).comp
        (circleProductMap (loopAction phi c)) =
      (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow).comp
        ((normalizedBaseStep (m := m) G).comp (circleProductMap c)) := by
  ext p
  change (normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph
      phi.toHomeomorph hpow)
        (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
          (p.1, phi (c p.2))) =
    (normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph
      phi.toHomeomorph hpow)
        (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
          (p.1 + ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle), c p.2))
  rw [(normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph
    phi.toHomeomorph hpow).injective.eq_iff]
  change Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
      (p.1, phi (c p.2)) =
    Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
      (p.1 + ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle), c p.2)
  symm
  apply Quotient.sound
  refine ⟨1, ?_⟩
  apply Prod.ext
  · change p.1 =
      p.1 + ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) -
        (((((1 : ℤ) : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle)
    rw [show (((((1 : ℤ) : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) =
        ((((1 : ℝ) / (m : ℝ) : ℝ)) : UnitAddCircle) by norm_num]
    abel
  · change phi (c p.2) = (phi.toHomeomorph ^ (1 : ℤ)) (c p.2)
    rw [zpow_one]
    rfl

/-- The normalized cover identifies the positive cross of a loop with the positive cross of its
clutching translate. -/
public theorem normalizedCover_positiveCircleCross_loopAction
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (hpow : phi.toHomeomorph ^ m = 1)
    (c : C(StdTorus 1, G)) :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (positiveCircleCross (loopAction phi c)) =
      integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (positiveCircleCross c) := by
  rw [positiveCircleCross, positiveCircleCross]
  rw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
  rw [normalizedCover_loopAction_square phi hpow c]
  rw [← integralSingularHomologyMap_comp_wang]
  rw [← integralSingularHomologyMap_comp_wang]
  have hstep := integralSingularHomologyMap_eq_of_homotopy 2
    (normalizedBaseStepHomotopy (m := m) G)
  rw [← hstep]
  rw [integralSingularHomologyMap_id_wang]
  rw [← integralSingularHomologyMap_comp_wang]

/-- Every iterate in the clutching orbit has the same positive-cross image under the normalized
cover. -/
public theorem normalizedCover_positiveCircleCross_loopAction_pow
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (hpow : phi.toHomeomorph ^ m = 1)
    (i : ℕ) (c : C(StdTorus 1, G)) :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (positiveCircleCross (((loopAction phi) ^ i) c)) =
      integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (positiveCircleCross c) := by
  induction i generalizing c with
  | zero => rfl
  | succ i ih =>
      rw [pow_succ]
      change integralSingularHomologyMap 2
          (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
          (positiveCircleCross (((loopAction phi) ^ i) (loopAction phi c))) = _
      rw [ih, normalizedCover_positiveCircleCross_loopAction phi hpow c]

/-- The fibre square required by `SweepData` follows from the literal point-set fibre square. -/
public theorem normalizedFiniteOrderAdditiveCircleSweep_fibreSquare
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (hpow : phi.toHomeomorph ^ m = 1)
    (x : IntegralSingularHomology 2 G) :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (integralSingularHomologyMap 2 (circleProductFiberInclusion (X := G)) x) =
      (circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1).inclusion x := by
  exact normalizedAffineCover_fiber_square phi.toHomeomorph hpow 1 x

/-- The finite-cover boundary formula holds on every class supported in the product fibre. -/
public theorem normalizedFiniteOrderAdditiveCircleSweep_boundarySquare_fibre
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (hpow : phi.toHomeomorph ^ m = 1)
    (x : IntegralSingularHomology 2 G) :
    (circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1).boundary
        (integralSingularHomologyMap 2
          (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
          (integralSingularHomologyMap 2 (circleProductFiberInclusion (X := G)) x)) =
      ∑ i ∈ Finset.range m,
        integralSingularHomologyMap 1
          ((phi.toHomeomorph ^ i : G ≃ₜ G) : C(G, G))
          (canonicalProductWangBoundary 1
            (integralSingularHomologyMap 2
              (circleProductFiberInclusion (X := G)) x)) := by
  rw [normalizedFiniteOrderAdditiveCircleSweep_fibreSquare phi hpow x]
  rw [(circleMappingTorusWangPresentationOfCover
    phi.toHomeomorph 1).boundary_inclusion]
  have hsource : canonicalProductWangBoundary 1
      (integralSingularHomologyMap 2
        (circleProductFiberInclusion (X := G)) x) = 0 :=
    (canonicalProductWang_exact 1).apply_apply_eq_zero x
  rw [hsource]
  simp

private def pathAddRight
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    {a : G} (p : Path a a) (b : G) : Path (a + b) (a + b) :=
  p.add (Path.refl b)

private def pathAddLeft
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (a : G) {b : G} (q : Path b b) : Path (a + b) (a + b) :=
  (Path.refl a).add q

private def pointwiseAddToConcatenationHomotopy
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    {a b : G} (p : Path a a) (q : Path b b) :
    Path.Homotopy
      ((pathAddRight p b).trans (pathAddLeft a q))
      (p.add q) where
  toFun u := Path.delayReflRight u.1 p u.2 + Path.delayReflLeft u.1 q u.2
  continuous_toFun := by
    have hp : Continuous fun t : unitInterval ↦ Path.delayReflRight t p :=
      Path.continuous_delayReflRight.comp (continuous_id.prodMk continuous_const)
    have hq : Continuous fun t : unitInterval ↦ Path.delayReflLeft t q :=
      Path.continuous_delayReflLeft.comp (continuous_id.prodMk continuous_const)
    exact (Path.continuous_uncurry_iff.mpr hp).add
      (Path.continuous_uncurry_iff.mpr hq)
  map_zero_left t := by
    change Path.delayReflRight 0 p t + Path.delayReflLeft 0 q t =
      ((pathAddRight p b).trans (pathAddLeft a q)) t
    rw [Path.delayReflRight_zero, Path.delayReflLeft_zero]
    simp only [pathAddRight, pathAddLeft, Path.add_apply]
    rw [Path.trans_apply, Path.trans_apply, Path.trans_apply]
    split_ifs <;> rfl
  map_one_left t := by
    change Path.delayReflRight 1 p t + Path.delayReflLeft 1 q t = (p.add q) t
    rw [Path.delayReflRight_one, Path.delayReflLeft_one]
    rfl
  prop' u t ht := by
    rcases ht with rfl | ht
    · simp
    · rw [Set.mem_singleton_iff] at ht
      subst t
      simp

private theorem loopHomologyClass_add
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    {a b : G} (p : Path a a) (q : Path b b) :
    StandardCircleHomologyLiftDegree.loopHomologyClass (p.add q) =
      StandardCircleHomologyLiftDegree.loopHomologyClass (pathAddRight p b) +
        StandardCircleHomologyLiftDegree.loopHomologyClass (pathAddLeft a q) := by
  rw [← FirstHurewiczProof.loopHomologyClass_trans]
  exact FirstHurewiczProof.loopHomologyClass_homotopic
    (pointwiseAddToConcatenationHomotopy p q).symm

private def addRightMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (b : G) : C(G, G) where
  toFun x := x + b
  continuous_toFun := continuous_id.add continuous_const

private def addLeftMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (a : G) : C(G, G) where
  toFun x := a + x
  continuous_toFun := continuous_const.add continuous_id

private def addRightMapHomotopy
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G] (b : G) :
    ContinuousMap.Homotopy (addRightMap b) (ContinuousMap.id G) where
  toFun u := u.2 + PathConnectedSpace.somePath b 0 u.1
  continuous_toFun := continuous_snd.add
    ((PathConnectedSpace.somePath b 0).continuous.comp continuous_fst)
  map_zero_left x := by simp [addRightMap]
  map_one_left x := by simp

private def addLeftMapHomotopy
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G] (a : G) :
    ContinuousMap.Homotopy (addLeftMap a) (ContinuousMap.id G) where
  toFun u := PathConnectedSpace.somePath a 0 u.1 + u.2
  continuous_toFun :=
    ((PathConnectedSpace.somePath a 0).continuous.comp continuous_fst).add continuous_snd
  map_zero_left x := by simp [addLeftMap]
  map_one_left x := by simp

private theorem loopHomologyClass_pathAddRight
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G] {a : G} (p : Path a a) (b : G) :
    StandardCircleHomologyLiftDegree.loopHomologyClass (pathAddRight p b) =
      StandardCircleHomologyLiftDegree.loopHomologyClass p := by
  have hpath : pathAddRight p b = p.map (addRightMap b).continuous := by
    ext t
    rfl
  calc
    StandardCircleHomologyLiftDegree.loopHomologyClass (pathAddRight p b) =
        StandardCircleHomologyLiftDegree.loopHomologyClass
          (p.map (addRightMap b).continuous) := congrArg _ hpath
    _ = integralSingularHomologyMap 1 (addRightMap b)
          (StandardCircleHomologyLiftDegree.loopHomologyClass p) :=
      (StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass
        (addRightMap b) p).symm
    _ = integralSingularHomologyMap 1 (ContinuousMap.id G)
          (StandardCircleHomologyLiftDegree.loopHomologyClass p) := by
      rw [integralSingularHomologyMap_eq_of_homotopy 1 (addRightMapHomotopy b)]
    _ = _ := by rw [integralSingularHomologyMap_id_wang]

private theorem loopHomologyClass_pathAddLeft
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G] (a : G) {b : G} (q : Path b b) :
    StandardCircleHomologyLiftDegree.loopHomologyClass (pathAddLeft a q) =
      StandardCircleHomologyLiftDegree.loopHomologyClass q := by
  have hpath : pathAddLeft a q = q.map (addLeftMap a).continuous := by
    ext t
    rfl
  calc
    StandardCircleHomologyLiftDegree.loopHomologyClass (pathAddLeft a q) =
        StandardCircleHomologyLiftDegree.loopHomologyClass
          (q.map (addLeftMap a).continuous) := congrArg _ hpath
    _ = integralSingularHomologyMap 1 (addLeftMap a)
          (StandardCircleHomologyLiftDegree.loopHomologyClass q) :=
      (StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass
        (addLeftMap a) q).symm
    _ = integralSingularHomologyMap 1 (ContinuousMap.id G)
          (StandardCircleHomologyLiftDegree.loopHomologyClass q) := by
      rw [integralSingularHomologyMap_eq_of_homotopy 1 (addLeftMapHomotopy a)]
    _ = _ := by rw [integralSingularHomologyMap_id_wang]

/-- On a path-connected topological additive group, the degree-one class carried by a
parametrized circle is additive under pointwise addition. -/
public theorem standardCircleHomologyClass_map_add
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G] (c d : C(StdTorus 1, G)) :
    integralSingularHomologyMap 1 (c + d) standardCircleHomologyGenerator =
      integralSingularHomologyMap 1 c standardCircleHomologyGenerator +
        integralSingularHomologyMap 1 d standardCircleHomologyGenerator := by
  rw [standardCircleHomologyGenerator]
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  let p := standardCirclePositiveLoop.map c.continuous
  let q := standardCirclePositiveLoop.map d.continuous
  have hsum : standardCirclePositiveLoop.map (c + d).continuous = p.add q := by
    ext t
    rfl
  rw [hsum, loopHomologyClass_add p q,
    loopHomologyClass_pathAddRight p _, loopHomologyClass_pathAddLeft _ q]

public theorem standardCircleHomologyClass_map_zero
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] :
    integralSingularHomologyMap 1 (0 : C(StdTorus 1, G))
        standardCircleHomologyGenerator = 0 := by
  rw [standardCircleHomologyGenerator]
  rw [StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass]
  have hpath : standardCirclePositiveLoop.map
      (0 : C(StdTorus 1, G)).continuous = Path.refl 0 := by
    ext t
    rfl
  rw [hpath]
  exact FirstHurewiczProof.loopHomologyClass_refl 0

/-- The degree-one class represented by a parametrized circle is an additive function of the
parametrization. -/
public noncomputable def standardCircleHomologyClassMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G] :
    C(StdTorus 1, G) →+ IntegralSingularHomology 1 G where
  toFun c := integralSingularHomologyMap 1 c standardCircleHomologyGenerator
  map_zero' := standardCircleHomologyClass_map_zero
  map_add' := standardCircleHomologyClass_map_add

private theorem loopAction_pow_apply'
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (i : ℕ) (c : C(StdTorus 1, G)) :
    ((loopAction phi) ^ i) c =
      (((phi.toHomeomorph ^ i : G ≃ₜ G) : C(G, G)).comp c) := by
  induction i generalizing c with
  | zero =>
      ext x
      rfl
  | succ i ih =>
      rw [pow_succ]
      change ((loopAction phi) ^ i) (loopAction phi c) = _
      rw [ih]
      ext x
      rfl

/-- The circle class of the pointwise orbit norm is the ordinary cyclic norm on first
homology. -/
public theorem standardCircleHomologyClass_orbitNorm
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G]
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (c : C(StdTorus 1, G)) :
    integralSingularHomologyMap 1 (orbitNorm m phi hpow c).1
        standardCircleHomologyGenerator =
      ∑ i ∈ Finset.range m,
        integralSingularHomologyMap 1
          ((phi.toHomeomorph ^ i : G ≃ₜ G) : C(G, G))
          (integralSingularHomologyMap 1 c standardCircleHomologyGenerator) := by
  change standardCircleHomologyClassMap ((orbitNorm m phi hpow c).1) = _
  rw [orbitNorm_value]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [loopAction_pow_apply' phi i c]
  change integralSingularHomologyMap 1
      (((phi.toHomeomorph ^ i : G ≃ₜ G) : C(G, G)).comp c)
      standardCircleHomologyGenerator = _
  rw [integralSingularHomologyMap_comp_wang]

private theorem fixedLoop_apply
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (x : StdTorus 1) :
    phi (c.1 x) = c.1 x := by
  have h := LinearMap.mem_ker.mp c.2
  have hx := DFunLike.congr_fun h x
  apply sub_eq_zero.mp
  simpa [loopAction] using hx

private theorem fixedLoop_zpow_apply
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (k : ℤ) (x : StdTorus 1) :
    (phi.toHomeomorph ^ k) (c.1 x) = c.1 x := by
  refine Int.induction_on (motive := fun n ↦
    (phi.toHomeomorph ^ n) (c.1 x) = c.1 x) k ?_ ?_ ?_
  · rfl
  · intro i hi
    rw [zpow_add_one]
    change (phi.toHomeomorph ^ (i : ℤ)) (phi (c.1 x)) = c.1 x
    rw [fixedLoop_apply phi c x, hi]
  · intro i hi
    rw [zpow_sub_one]
    change (phi.toHomeomorph ^ (-(i : ℤ))) (phi.symm (c.1 x)) = c.1 x
    have hinv : phi.symm (c.1 x) = c.1 x := by
      apply phi.injective
      rw [phi.apply_symm_apply, fixedLoop_apply phi c x]
    rw [hinv, hi]

public def fixedLoopRealPreMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) : C(ℝ × StdTorus 1, ℝ × G) where
  toFun p := (p.1, c.1 p.2)
  continuous_toFun := continuous_fst.prodMk (c.1.continuous.comp continuous_snd)

/-- A pointwise fixed parametrized loop induces a map from the identity mapping torus into the
mapping torus of the clutching map. -/
public noncomputable def fixedLoopRealMappingTorusMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    C(RealMappingTorus (Homeomorph.refl (StdTorus 1)),
      RealMappingTorus phi.toHomeomorph) where
  toFun := Quotient.map (fixedLoopRealPreMap phi c) fun p q hpq ↦ by
    change realMappingTorusSetoid (Homeomorph.refl (StdTorus 1)) p q at hpq
    change realMappingTorusSetoid phi.toHomeomorph
      (fixedLoopRealPreMap phi c p) (fixedLoopRealPreMap phi c q)
    obtain ⟨k, hk⟩ := hpq
    refine ⟨k, ?_⟩
    rw [hk, mappingTorusShift_apply, mappingTorusShift_apply]
    apply Prod.ext
    · rfl
    · change c.1 (((Homeomorph.refl (StdTorus 1)) ^ k) p.2) =
        (phi.toHomeomorph ^ k) (c.1 p.2)
      rw [show Homeomorph.refl (StdTorus 1) = 1 by rfl, one_zpow]
      exact (fixedLoop_zpow_apply phi c k p.2).symm
  continuous_toFun := continuous_quot_lift _
    (continuous_quot_mk.comp (fixedLoopRealPreMap phi c).continuous)

@[simp]
public theorem fixedLoopRealMappingTorusMap_mk
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (t : ℝ) (x : StdTorus 1) :
    fixedLoopRealMappingTorusMap phi c
        (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x)) =
      Quotient.mk (realMappingTorusSetoid phi.toHomeomorph) (t, c.1 x) := by
  rfl

/-- The torus carried by a pointwise fixed parametrized loop in the mapping torus. -/
public noncomputable def fixedLoopMappingTorusMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    C(UnitAddCircle × StdTorus 1, CircleMappingTorus phi.toHomeomorph) :=
  (realMappingTorusHomeomorph phi.toHomeomorph :
      C(RealMappingTorus phi.toHomeomorph, CircleMappingTorus phi.toHomeomorph)).comp
    ((fixedLoopRealMappingTorusMap phi c).comp
      (circleProductRealMappingTorusHomeomorph (X := StdTorus 1) :
        C(UnitAddCircle × StdTorus 1,
          RealMappingTorus (Homeomorph.refl (StdTorus 1)))))

/-- The geometric degree-two class swept out by a pointwise fixed parametrized loop. -/
public noncomputable def fixedLoopSweepClass
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    IntegralSingularHomology 2 (CircleMappingTorus phi.toHomeomorph) :=
  integralSingularHomologyMap 2 (fixedLoopMappingTorusMap phi c)
    positiveCircleProductGenerator

end SphereSixComplex.Topology.NormalizedFiniteOrderAdditiveCircleSweepProof

end

end
