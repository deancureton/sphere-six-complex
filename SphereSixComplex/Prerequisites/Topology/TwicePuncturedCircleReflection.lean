module

public import SphereSixComplex.Prerequisites.Topology.TwicePuncturedCircleHomology

@[expose] public section
noncomputable section

namespace SphereSixComplex.Topology.TwicePuncturedComplex.Circles

open SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree
open Set

public def punctureReflection : C(TwicePuncturedComplex, TwicePuncturedComplex) where
  toFun z := ⟨1 - z.1, by
    have hz : z.1 ≠ 0 ∧ z.1 ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] using z.property
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · exact sub_ne_zero.mpr (Ne.symm hz.2)
    · intro h
      apply hz.1
      linear_combination -h⟩
  continuous_toFun := by fun_prop

public theorem punctureReflection_zeroMeridian_homology :
    integralSingularHomologyMap 1 punctureReflection
      (hurewiczFunction twicePuncturedComplexBasepoint zeroMeridianClass⁻¹) =
      hurewiczFunction twicePuncturedComplexBasepoint oneMeridianClass⁻¹ := by
  change integralSingularHomologyMap 1 punctureReflection
    (loopHomologyClass twicePuncturedClockwiseZeroMeridian.symm) =
      loopHomologyClass twicePuncturedClockwiseOneMeridian.symm
  rw [integralSingularHomologyMap_loopHomologyClass]
  apply loopHomologyClass_eq_of_toContinuousMap_eq
  ext t
  change 1 - circleMap 0 (2 : ℝ)⁻¹ (-(2 * Real.pi * (unitInterval.symm t : ℝ))) =
    circleMap 1 (-(2 : ℝ)⁻¹) (-(2 * Real.pi * (unitInterval.symm t : ℝ)))
  simp only [circleMap, Complex.ofReal_neg]
  ring

public theorem coefficientCircleOne_homology
    (n : ℕ) (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1)
    {x : TwicePuncturedComplex} (p : Path x x)
    (hp : ∀ t, (p t : ℂ) = 1 + d * Complex.exp
      ((2 * Real.pi * (n : ℝ) * (t : ℝ) : ℂ) * Complex.I)) :
    loopHomologyClass p = n • hurewiczFunction twicePuncturedComplexBasepoint
      oneMeridianClass⁻¹ := by
  have h := coefficientCircle_homology n (-d) (neg_ne_zero.mpr hd)
    (by simpa using hd1) (p.map punctureReflection.continuous) (by
      intro t
      change 1 - (p t : ℂ) = _
      rw [hp]
      ring)
  have hm := congrArg (integralSingularHomologyMap 1 punctureReflection) h
  rw [map_nsmul, punctureReflection_zeroMeridian_homology,
    integralSingularHomologyMap_loopHomologyClass] at hm
  refine (loopHomologyClass_eq_of_toContinuousMap_eq p
    ((p.map punctureReflection.continuous).map punctureReflection.continuous) ?_).trans hm
  ext t
  change (p t : ℂ) = 1 - (1 - (p t : ℂ))
  ring

end SphereSixComplex.Topology.TwicePuncturedComplex.Circles
