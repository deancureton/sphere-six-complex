module

public import Mathlib.Topology.Homotopy.HSpaces
public import SphereSixComplex.Prerequisites.Topology.CanonicalProductWangBoundaryNaturality
public import SphereSixComplex.Prerequisites.Topology.EstablishedFirstHurewicz
public import SphereSixComplex.Prerequisites.Topology.NormalizedFiniteOrderAdditiveCircleSweep

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

namespace SphereSixComplex.CyclicMappingTorus.CircleSweep

open SphereSixComplex.Topology

open CanonicalProductWangBoundaryNaturality
open CircleProductIdentityMappingTorus
open CyclicAngularFundamentalDomain
open FiniteCyclicMappingTorusWangNaturality
open NormalizedAffineMappingTorusCover
open NormalizedFiniteOrderAdditiveCircleSweep
open CyclicMappingTorus
open PositiveCircleCross
open StandardTorusHomology

variable {m : ℕ} [NeZero m]






/-- The fibre square required by `SweepData` follows from the literal point-set fibre square. -/
public theorem normalizedFiniteOrderAdditiveCircleSweep_fiberSquare
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (hpow : phi.toHomeomorph ^ m = 1)
    (x : IntegralSingularHomology 2 G) :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (integralSingularHomologyMap 2 (circleProductFiberInclusion (X := G)) x) =
      (circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1).inclusion x := by
  exact normalizedAffineCover_fiber_square phi.toHomeomorph hpow 1 x

















private theorem fixedLoop_apply
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : fixedLoops phi) (x : StdTorus 1) :
    phi (c.1 x) = c.1 x := by
  have h := LinearMap.mem_ker.mp c.2
  have hx := DFunLike.congr_fun h x
  apply sub_eq_zero.mp
  simpa [loopAction] using hx

private theorem fixedLoop_zpow_apply
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : fixedLoops phi) (k : ℤ) (x : StdTorus 1) :
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
    (phi : G ≃ₜ+ G) (c : fixedLoops phi) : C(ℝ × StdTorus 1, ℝ × G) where
  toFun p := (p.1, c.1 p.2)
  continuous_toFun := continuous_fst.prodMk (c.1.continuous.comp continuous_snd)

/-- A pointwise fixed parametrized loop induces a map from the identity mapping torus into the
mapping torus of the clutching map. -/
public noncomputable def fixedLoopRealMappingTorusMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : fixedLoops phi) :
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
    (phi : G ≃ₜ+ G) (c : fixedLoops phi) (t : ℝ) (x : StdTorus 1) :
    fixedLoopRealMappingTorusMap phi c
        (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x)) =
      Quotient.mk (realMappingTorusSetoid phi.toHomeomorph) (t, c.1 x) := by
  rfl

/-- The torus carried by a pointwise fixed parametrized loop in the mapping torus. -/
public noncomputable def fixedLoopMappingTorusMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : fixedLoops phi) :
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
    (phi : G ≃ₜ+ G) (c : fixedLoops phi) :
    IntegralSingularHomology 2 (CircleMappingTorus phi.toHomeomorph) :=
  integralSingularHomologyMap 2 (fixedLoopMappingTorusMap phi c)
    positiveCircleProductGenerator

end SphereSixComplex.CyclicMappingTorus.CircleSweep

end

end
