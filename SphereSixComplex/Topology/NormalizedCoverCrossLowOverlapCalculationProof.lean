module

public import SphereSixComplex.Topology.FixedLoopSweepAdditivityReduction

/-!
# The normalized-cover positive-cross calculation

This file proves the normalized-cover overlap calculation whenever multiplication by the cover
order is injective on first homology.  In particular, it applies to the three-torus fibres used
by the elliptic charts.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.NormalizedCoverCrossLowOverlapCalculationProof

open CanonicalProductWangBoundaryNaturality
open CircleProductIdentityMappingTorus
open CyclicAngularFundamentalDomain
open FixedLoopSweepAdditivityReduction
open FixedLoopSweepWangBoundary
open NormalizedAffineMappingTorusCover
open NormalizedFiniteOrderAdditiveCircleSweep
open NormalizedFiniteOrderAdditiveCircleSweepProof
open PaperAffineCyclicReducedFiberMappingTorus
open PositiveCircleCross
open StandardTorusHomology

variable {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [PathConnectedSpace G]

private def baseMultiply (m : ℕ) (X : Type) [TopologicalSpace X] :
    C(UnitAddCircle × X, UnitAddCircle × X) where
  toFun p := (m • p.1, p.2)
  continuous_toFun := by fun_prop

private def baseMultiplyMatrix (m : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(m : ℤ), 0; 0, 1]

private theorem baseMultiply_conjugate_matrix (m : ℕ) :
    (circleProdStandardCircleHomeomorph :
        C(UnitAddCircle × StdTorus 1, StdTorus 2)).comp
        (baseMultiply m (StdTorus 1)) =
      (standardTwoTorusMatrixMap (baseMultiplyMatrix m)).comp
        (circleProdStandardCircleHomeomorph :
          C(UnitAddCircle × StdTorus 1, StdTorus 2)) := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  funext i
  change (@Fin.cons 1 (fun _ : Fin 2 ↦ UnitAddCircle) (m • s) x) i =
    ∑ j, baseMultiplyMatrix m i j •
      (@Fin.cons 1 (fun _ : Fin 2 ↦ UnitAddCircle) s x) j
  fin_cases i <;> simp [baseMultiplyMatrix, Fin.sum_univ_two]

private theorem baseMultiply_positiveCircleProductGenerator_mapped (m : ℕ) :
    integralSingularHomologyMap 2 circleProdStandardCircleHomeomorph
        (integralSingularHomologyMap 2 (baseMultiply m (StdTorus 1))
          positiveCircleProductGenerator) =
      (m : ℤ) • standardTwoTorusHomologyGenerator := by
  calc
    integralSingularHomologyMap 2 circleProdStandardCircleHomeomorph
        (integralSingularHomologyMap 2 (baseMultiply m (StdTorus 1))
          positiveCircleProductGenerator) =
        integralSingularHomologyMap 2
          (standardTwoTorusMatrixMap (baseMultiplyMatrix m))
          standardTwoTorusHomologyGenerator := by
      rw [integralSingularHomologyMap_comp_wang, baseMultiply_conjugate_matrix,
        ← integralSingularHomologyMap_comp_wang]
      rw [show integralSingularHomologyMap 2 circleProdStandardCircleHomeomorph
          positiveCircleProductGenerator = standardTwoTorusHomologyGenerator by
        exact (integralSingularHomologyEquiv 2
          circleProdStandardCircleHomeomorph).apply_symm_apply _]
    _ = (m : ℤ) • standardTwoTorusHomologyGenerator := by
      rw [standardTwoTorusMatrixDeterminantDegree]
      congr 1
      simp [baseMultiplyMatrix, Matrix.det_fin_two]

private theorem baseMultiply_positiveCircleProductGenerator (m : ℕ) :
    integralSingularHomologyMap 2 (baseMultiply m (StdTorus 1))
        positiveCircleProductGenerator =
      (m : ℤ) • positiveCircleProductGenerator := by
  apply (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).injective
  rw [map_zsmul]
  rw [show (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph)
      positiveCircleProductGenerator = standardTwoTorusHomologyGenerator by
    exact (integralSingularHomologyEquiv 2
      circleProdStandardCircleHomeomorph).apply_symm_apply _]
  exact baseMultiply_positiveCircleProductGenerator_mapped m

omit [IsTopologicalAddGroup G] [PathConnectedSpace G] in
private theorem normalizedAffineCover_real
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (t : ℝ) (x : G) :
    normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow
        (((t : ℝ) : UnitAddCircle), x) =
      realMappingTorusHomeomorph phi.toHomeomorph
        (Quotient.mk (realMappingTorusSetoid phi.toHomeomorph) ((m : ℝ) * t, x)) := by
  change normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph
      phi.toHomeomorph hpow
      (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
        (((t : ℝ) : UnitAddCircle), x)) = _
  unfold normalizedAffineCyclicQuotientCircleMappingTorusHomeomorph
  rw [Homeomorph.trans_apply]
  congr 1
  unfold normalizedAffineCyclicQuotientRealMappingTorusHomeomorph
    CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps
  dsimp only
  apply (normalizedAffineQuotientMap_eq_iff phi.toHomeomorph hpow _ _).mp
  calc
    normalizedAffineQuotientMap (m := m) phi.toHomeomorph
        (Function.surjInv (normalizedAffineQuotientMap_surjective phi.toHomeomorph)
          (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
            (((t : ℝ) : UnitAddCircle), x))) =
      Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi.toHomeomorph)
        (((t : ℝ) : UnitAddCircle), x) :=
      Function.surjInv_eq (normalizedAffineQuotientMap_surjective phi.toHomeomorph) _
    _ = normalizedAffineQuotientMap (m := m) phi.toHomeomorph ((m : ℝ) * t, x) := by
      change Quotient.mk _ (((t : ℝ) : UnitAddCircle), x) =
        Quotient.mk _ (((((m : ℝ) * t) / (m : ℝ) : ℝ) : UnitAddCircle), x)
      congr 2
      rw [mul_div_cancel_left₀ t (by exact_mod_cast (NeZero.ne m))]

omit [PathConnectedSpace G] in
private theorem normalizedAffineCover_comp_circleProductMap_fixed
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (d : FixedLoop phi) :
    (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow).comp
        (circleProductMap d.1) =
      (fixedLoopMappingTorusMap phi d).comp (baseMultiply m (StdTorus 1)) := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) s
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
  change normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow
      (((t : ℝ) : UnitAddCircle), d.1 x) =
    fixedLoopMappingTorusMap phi d (m • ((t : ℝ) : UnitAddCircle), x)
  rw [normalizedAffineCover_real]
  unfold fixedLoopMappingTorusMap
  change realMappingTorusHomeomorph phi.toHomeomorph
      (Quotient.mk (realMappingTorusSetoid phi.toHomeomorph) ((m : ℝ) * t, d.1 x)) =
    realMappingTorusHomeomorph phi.toHomeomorph
      (fixedLoopRealMappingTorusMap phi d
        (circleProductRealMappingTorusHomeomorph
          (m • ((t : ℝ) : UnitAddCircle), x)))
  congr 1
  rw [show m • ((t : ℝ) : UnitAddCircle) =
      (((m : ℝ) * t : ℝ) : UnitAddCircle) by
    rw [← AddCircle.coe_nsmul]
    congr 1
    simp [nsmul_eq_mul]]
  rw [← show realToCircleProduct ((m : ℝ) * t, x) =
      ((((m : ℝ) * t : ℝ) : UnitAddCircle), x) by rfl]
  rw [circleProductRealMappingTorusHomeomorph_real,
    fixedLoopRealMappingTorusMap_mk]

omit [PathConnectedSpace G] in
/-- A pointwise-fixed loop crosses the normalized cover with degree exactly `m` in the base. -/
public theorem normalizedAffineCover_positiveCircleCross_fixed
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (d : FixedLoop phi) :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (positiveCircleCross d.1) =
      (m : ℤ) • fixedLoopSweepClass phi d := by
  rw [positiveCircleCross, integralSingularHomologyMap_comp_wang,
    normalizedAffineCover_comp_circleProductMap_fixed m phi hpow d,
    ← integralSingularHomologyMap_comp_wang,
    baseMultiply_positiveCircleProductGenerator, map_zsmul]
  rfl

omit [PathConnectedSpace G] in
private theorem normalizedAffineCover_positiveCircleCross_fixed_boundary
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (d : FixedLoop phi) :
    (FixedLoopPresentation phi).boundary
        (integralSingularHomologyMap 2
          (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
          (positiveCircleCross d.1)) =
      (m : ℤ) •
        integralSingularHomologyMap 1 d.1 standardCircleHomologyGenerator := by
  rw [normalizedAffineCover_positiveCircleCross_fixed, map_zsmul,
    fixedLoopSweepClass_boundary]

private def reflFixedLoop (c : C(StdTorus 1, G)) :
    FixedLoop (ContinuousAddEquiv.refl G) := by
  refine ⟨c, LinearMap.mem_ker.mpr ?_⟩
  change c - c = 0
  exact sub_self c

omit [PathConnectedSpace G] in
private theorem fixedLoopMappingTorusMap_refl (c : C(StdTorus 1, G)) :
    fixedLoopMappingTorusMap (ContinuousAddEquiv.refl G) (reflFixedLoop c) =
      (circleProductIdentityMappingTorusHomeomorph (X := G) :
        C(UnitAddCircle × G, CircleMappingTorus (Homeomorph.refl G))).comp
        (circleProductMap c) := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) s
  change realMappingTorusHomeomorph (Homeomorph.refl G)
      (fixedLoopRealMappingTorusMap (ContinuousAddEquiv.refl G) (reflFixedLoop c)
        (circleProductRealMappingTorusHomeomorph (((t : ℝ) : UnitAddCircle), x))) =
    realMappingTorusHomeomorph (Homeomorph.refl G)
      (circleProductRealMappingTorusHomeomorph (((t : ℝ) : UnitAddCircle), c x))
  rw [← show realToCircleProduct (t, x) = (((t : ℝ) : UnitAddCircle), x) by rfl,
    ← show realToCircleProduct (t, c x) =
      (((t : ℝ) : UnitAddCircle), c x) by rfl,
    circleProductRealMappingTorusHomeomorph_real,
    circleProductRealMappingTorusHomeomorph_real,
    fixedLoopRealMappingTorusMap_mk]
  rfl

omit [PathConnectedSpace G] in
/-- The positive-cross formula for the canonical product boundary, proved from the explicit
fixed-loop cover calculation rather than the finite-order sweep axiom. -/
public theorem canonicalProductWangBoundary_positiveCircleCross
    (c : C(StdTorus 1, G)) :
    canonicalProductWangBoundary 1 (positiveCircleCross c) =
      integralSingularHomologyMap 1 c standardCircleHomologyGenerator := by
  let phi : G ≃ₜ+ G := ContinuousAddEquiv.refl G
  let d : FixedLoop phi := reflFixedLoop c
  change (FixedLoopPresentation phi).boundary
      (integralSingularHomologyMap 2
        (circleProductIdentityMappingTorusHomeomorph (X := G) :
          C(UnitAddCircle × G, CircleMappingTorus (Homeomorph.refl G)))
        (positiveCircleCross c)) = _
  rw [positiveCircleCross, integralSingularHomologyMap_comp_wang,
    ← fixedLoopMappingTorusMap_refl c]
  exact fixedLoopSweepClass_boundary phi d

private theorem positiveCircleCross_add_defect_mem_fibre
    (c d : C(StdTorus 1, G)) :
    positiveCircleCross (c + d) - positiveCircleCross c - positiveCircleCross d ∈
      Set.range (integralSingularHomologyMap 2 (productFiberInclusion (X := G))) := by
  apply (canonicalProductWang_exact (X := G) 1 _).mp
  rw [map_sub, map_sub, canonicalProductWangBoundary_positiveCircleCross,
    canonicalProductWangBoundary_positiveCircleCross,
    canonicalProductWangBoundary_positiveCircleCross,
    standardCircleHomologyClass_map_add]
  abel

private theorem normalizedAffineCover_positiveCircleCross_boundary_add
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (c d : C(StdTorus 1, G)) :
    (FixedLoopPresentation phi).boundary
        (integralSingularHomologyMap 2
          (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
          (positiveCircleCross (c + d))) =
      (FixedLoopPresentation phi).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross c)) +
        (FixedLoopPresentation phi).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross d)) := by
  obtain ⟨x, hx⟩ := positiveCircleCross_add_defect_mem_fibre c d
  have hzero :
      (FixedLoopPresentation phi).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross (c + d) - positiveCircleCross c -
              positiveCircleCross d)) = 0 := by
    rw [← hx]
    have hsquare := normalizedAffineCover_fiber_square phi.toHomeomorph hpow 1 x
    change integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
          (integralSingularHomologyMap 2 (productFiberInclusion (X := G)) x) =
      (FixedLoopPresentation phi).inclusion x at hsquare
    rw [hsquare, (FixedLoopPresentation phi).boundary_inclusion]
  rw [map_sub, map_sub, map_sub, map_sub] at hzero
  calc
    _ = ((FixedLoopPresentation phi).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross (c + d))) -
        (FixedLoopPresentation phi).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross c)) -
        (FixedLoopPresentation phi).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross d))) +
        (FixedLoopPresentation phi).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross c)) +
        (FixedLoopPresentation phi).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross d)) := by abel
    _ = _ := by rw [hzero]; abel

end SphereSixComplex.Topology.NormalizedCoverCrossLowOverlapCalculationProof

end

end
