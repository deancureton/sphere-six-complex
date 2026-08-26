module

public import SphereSixComplex.Topology.TwicePuncturedComplexHalfPlaneCover
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Marked meridians in the twice-punctured complex plane

This file fixes the two clockwise tangent circles based at `1 / 2`, proves that they stay in the
corresponding members of the half-plane cover, and computes their local winding classes via the
complex exponential covering.
-/

@[expose] public section

noncomputable section

open Set Metric Topology CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex.Topology

/-- A homotopy equivalence induces an equivalence of fundamental groups at corresponding
basepoints. -/
public noncomputable def fundamentalGroupMulEquivOfHomotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)

public theorem fundamentalGroupMulEquivOfHomotopyEquiv_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (p : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfHomotopyEquiv e x p = FundamentalGroup.map e.toFun x p := by
  exact CategoryTheory.Functor.FullyFaithful.mulEquivEnd_apply _ _ _

/-- Equality of basepoints induces the corresponding conjugation equivalence of fundamental
groups. -/
public def fundamentalGroupMulEquivOfEq
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) :
    FundamentalGroup X x ≃* FundamentalGroup X y :=
  (eqToIso (congrArg FundamentalGroupoid.mk h)).conj

public theorem fundamentalGroupMulEquivOfEq_apply
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (p : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfEq h p =
      Path.Homotopic.Quotient.cast p h.symm h.symm := by
  exact FundamentalGroupoid.conj_eqToHom _ _

/-- The common basepoint, regarded as a point of the left cover member. -/
public def twicePuncturedComplexLeftBasepoint : twicePuncturedComplexLeft :=
  ⟨twicePuncturedComplexBasepoint, twicePuncturedComplexBasepoint_mem_left⟩

/-- The common basepoint, regarded as a point of the right cover member. -/
public def twicePuncturedComplexRightBasepoint : twicePuncturedComplexRight :=
  ⟨twicePuncturedComplexBasepoint, twicePuncturedComplexBasepoint_mem_right⟩

public theorem twicePuncturedComplexLeftHomotopyEquiv_basepoint :
    twicePuncturedComplexLeftHomotopyEquivPuncturedComplex
        twicePuncturedComplexLeftBasepoint =
      (⟨(2 : ℂ)⁻¹, by norm_num⟩ : PuncturedComplex) := by
  exact twicePuncturedComplexLeftHomotopyEquivPuncturedComplex_basepoint

public theorem twicePuncturedComplexRightHomotopyEquiv_basepoint :
    twicePuncturedComplexRightHomotopyEquivPuncturedComplex
        twicePuncturedComplexRightBasepoint =
      (⟨(2 : ℂ)⁻¹, by norm_num⟩ : PuncturedComplex) := by
  exact twicePuncturedComplexRightHomotopyEquivPuncturedComplex_basepoint

private theorem circleMap_zero_half_ne_one (θ : ℝ) :
    circleMap 0 (2 : ℝ)⁻¹ θ ≠ (1 : ℂ) := by
  intro h
  have hs := circleMap_mem_sphere 0 (by positivity : 0 ≤ (2 : ℝ)⁻¹) θ
  rw [Metric.mem_sphere, h] at hs
  norm_num [Complex.dist_eq] at hs

private theorem circleMap_one_negHalf_ne_zero (θ : ℝ) :
    circleMap 1 (-(2 : ℝ)⁻¹) θ ≠ (0 : ℂ) := by
  intro h
  have hs := circleMap_mem_sphere' 1 (-(2 : ℝ)⁻¹) θ
  rw [Metric.mem_sphere, h] at hs
  norm_num [Complex.dist_eq] at hs

/-- One clockwise turn about zero, as a point of the twice-punctured plane. -/
public def twicePuncturedClockwiseZeroPoint (t : unitInterval) :
    TwicePuncturedComplex :=
  ⟨circleMap 0 (2 : ℝ)⁻¹ (-(2 * Real.pi * (t : ℝ))), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨circleMap_ne_center (by norm_num),
      circleMap_zero_half_ne_one _⟩⟩

/-- One clockwise turn about one, as a point of the twice-punctured plane. -/
public def twicePuncturedClockwiseOnePoint (t : unitInterval) :
    TwicePuncturedComplex :=
  ⟨circleMap 1 (-(2 : ℝ)⁻¹) (-(2 * Real.pi * (t : ℝ))), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨circleMap_one_negHalf_ne_zero _,
      circleMap_ne_center (by norm_num)⟩⟩

public theorem twicePuncturedClockwiseZeroPoint_zero :
    twicePuncturedClockwiseZeroPoint 0 = twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [twicePuncturedClockwiseZeroPoint, twicePuncturedComplexBasepoint, circleMap]

public theorem twicePuncturedClockwiseZeroPoint_one :
    twicePuncturedClockwiseZeroPoint 1 = twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [twicePuncturedClockwiseZeroPoint, twicePuncturedComplexBasepoint,
    circleMap, Complex.exp_neg, Complex.exp_two_pi_mul_I]

public theorem twicePuncturedClockwiseOnePoint_zero :
    twicePuncturedClockwiseOnePoint 0 = twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [twicePuncturedClockwiseOnePoint, twicePuncturedComplexBasepoint, circleMap]

public theorem twicePuncturedClockwiseOnePoint_one :
    twicePuncturedClockwiseOnePoint 1 = twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [twicePuncturedClockwiseOnePoint, twicePuncturedComplexBasepoint,
    circleMap, Complex.exp_neg, Complex.exp_two_pi_mul_I]

/-- The actual clockwise meridian about zero. -/
public def twicePuncturedClockwiseZeroMeridian :
    Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint where
  toFun := twicePuncturedClockwiseZeroPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := twicePuncturedClockwiseZeroPoint_zero
  target' := twicePuncturedClockwiseZeroPoint_one

/-- The actual clockwise meridian about one. -/
public def twicePuncturedClockwiseOneMeridian :
    Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint where
  toFun := twicePuncturedClockwiseOnePoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := twicePuncturedClockwiseOnePoint_zero
  target' := twicePuncturedClockwiseOnePoint_one

public theorem twicePuncturedClockwiseZeroPoint_mem_left (t : unitInterval) :
    twicePuncturedClockwiseZeroPoint t ∈ twicePuncturedComplexLeft := by
  change (circleMap 0 (2 : ℝ)⁻¹ (-(2 * Real.pi * (t : ℝ)))).re < 2 / 3
  have hre := Complex.re_le_norm
    (circleMap 0 (2 : ℝ)⁻¹ (-(2 * Real.pi * (t : ℝ))))
  have hs : ‖circleMap 0 (2 : ℝ)⁻¹ (-(2 * Real.pi * (t : ℝ)))‖ = 1 / 2 := by
    rw [norm_circleMap_zero]
    norm_num
  rw [hs] at hre
  norm_num at hre ⊢
  linarith

public theorem twicePuncturedClockwiseOnePoint_mem_right (t : unitInterval) :
    twicePuncturedClockwiseOnePoint t ∈ twicePuncturedComplexRight := by
  change 1 / 3 < (circleMap 1 (-(2 : ℝ)⁻¹) (-(2 * Real.pi * (t : ℝ)))).re
  have hre := Complex.abs_re_le_norm
    (circleMap 1 (-(2 : ℝ)⁻¹) (-(2 * Real.pi * (t : ℝ))) - 1)
  have hs : ‖circleMap 1 (-(2 : ℝ)⁻¹) (-(2 * Real.pi * (t : ℝ))) - 1‖ = 1 / 2 := by
    rw [circleMap_sub_center, norm_circleMap_zero]
    norm_num
  simp only [Complex.sub_re, Complex.one_re] at hre
  rw [hs] at hre
  norm_num at hre ⊢
  have hlower := (abs_le.mp hre).1
  linarith

/-- The zero meridian regarded as a loop in the left cover member. -/
public def twicePuncturedClockwiseZeroMeridianInLeft :
    Path twicePuncturedComplexLeftBasepoint twicePuncturedComplexLeftBasepoint where
  toFun t := ⟨twicePuncturedClockwiseZeroPoint t,
    twicePuncturedClockwiseZeroPoint_mem_left t⟩
  continuous_toFun :=
    twicePuncturedClockwiseZeroMeridian.continuous.subtype_mk _
  source' := by
    apply Subtype.ext
    exact twicePuncturedClockwiseZeroPoint_zero
  target' := by
    apply Subtype.ext
    exact twicePuncturedClockwiseZeroPoint_one

/-- The one meridian regarded as a loop in the right cover member. -/
public def twicePuncturedClockwiseOneMeridianInRight :
    Path twicePuncturedComplexRightBasepoint twicePuncturedComplexRightBasepoint where
  toFun t := ⟨twicePuncturedClockwiseOnePoint t,
    twicePuncturedClockwiseOnePoint_mem_right t⟩
  continuous_toFun :=
    twicePuncturedClockwiseOneMeridian.continuous.subtype_mk _
  source' := by
    apply Subtype.ext
    exact twicePuncturedClockwiseOnePoint_zero
  target' := by
    apply Subtype.ext
    exact twicePuncturedClockwiseOnePoint_one

/-- Under the literal left-piece equivalence, the zero meridian is the `-1` integer circle. -/
public theorem twicePuncturedClockwiseZeroMeridianInLeft_map :
    (twicePuncturedClockwiseZeroMeridianInLeft.map
        twicePuncturedComplexLeftHomotopyEquivPuncturedComplex.continuous).cast
          twicePuncturedComplexLeftHomotopyEquivPuncturedComplex_basepoint.symm
          twicePuncturedComplexLeftHomotopyEquivPuncturedComplex_basepoint.symm =
      puncturedComplexIntegerCircle (2 : ℂ)⁻¹ (by norm_num) (-1) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change circleMap 0 (2 : ℝ)⁻¹ (-(2 * Real.pi * (t : ℝ))) =
    (2 : ℂ)⁻¹ * Complex.exp
      ((2 * Real.pi * ((-1 : ℤ) : ℝ) * (t : ℝ) : ℂ) * Complex.I)
  simp only [circleMap_zero]
  norm_num

/-- Under reflection and the right-piece equivalence, the one meridian is also the `-1` integer
circle. -/
public theorem twicePuncturedClockwiseOneMeridianInRight_map :
    (twicePuncturedClockwiseOneMeridianInRight.map
        twicePuncturedComplexRightHomotopyEquivPuncturedComplex.continuous).cast
          twicePuncturedComplexRightHomotopyEquivPuncturedComplex_basepoint.symm
          twicePuncturedComplexRightHomotopyEquivPuncturedComplex_basepoint.symm =
      puncturedComplexIntegerCircle (2 : ℂ)⁻¹ (by norm_num) (-1) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change 1 - circleMap 1 (-(2 : ℝ)⁻¹) (-(2 * Real.pi * (t : ℝ))) =
    (2 : ℂ)⁻¹ * Complex.exp
      ((2 * Real.pi * ((-1 : ℤ) : ℝ) * (t : ℝ) : ℂ) * Complex.I)
  simp only [circleMap]
  norm_num

/-- The local fundamental group of the left piece, with its exponential-cover winding
coordinate. -/
public noncomputable def twicePuncturedComplexLeftFundamentalGroupEquiv :
    FundamentalGroup twicePuncturedComplexLeft twicePuncturedComplexLeftBasepoint ≃*
      (Multiplicative ComplexExpDeckGroup)ᵐᵒᵖ :=
  (fundamentalGroupMulEquivOfHomotopyEquiv
      twicePuncturedComplexLeftHomotopyEquivPuncturedComplex
      twicePuncturedComplexLeftBasepoint).trans
    ((fundamentalGroupMulEquivOfEq
      twicePuncturedComplexLeftHomotopyEquiv_basepoint).trans
        (puncturedComplexFundamentalGroupEquiv (2 : ℂ)⁻¹ (by norm_num)))

/-- The local fundamental group of the right piece, with its exponential-cover winding
coordinate. -/
public noncomputable def twicePuncturedComplexRightFundamentalGroupEquiv :
    FundamentalGroup twicePuncturedComplexRight twicePuncturedComplexRightBasepoint ≃*
      (Multiplicative ComplexExpDeckGroup)ᵐᵒᵖ :=
  (fundamentalGroupMulEquivOfHomotopyEquiv
      twicePuncturedComplexRightHomotopyEquivPuncturedComplex
      twicePuncturedComplexRightBasepoint).trans
    ((fundamentalGroupMulEquivOfEq
      twicePuncturedComplexRightHomotopyEquiv_basepoint).trans
        (puncturedComplexFundamentalGroupEquiv (2 : ℂ)⁻¹ (by norm_num)))

/-- The marked clockwise zero meridian has winding coordinate `-1` in the left piece. -/
public theorem twicePuncturedComplexLeftFundamentalGroupEquiv_meridian :
    twicePuncturedComplexLeftFundamentalGroupEquiv
        (Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft) =
      MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple (-1))) := by
  unfold twicePuncturedComplexLeftFundamentalGroupEquiv
  simp only [MulEquiv.trans_apply]
  rw [fundamentalGroupMulEquivOfEq_apply]
  rw [fundamentalGroupMulEquivOfHomotopyEquiv_apply]
  rw [FundamentalGroup.map_apply]
  rw [← Path.Homotopic.Quotient.mk_map]
  change puncturedComplexFundamentalGroupEquiv (2 : ℂ)⁻¹ (by norm_num)
      ((Path.Homotopic.Quotient.mk
        (twicePuncturedClockwiseZeroMeridianInLeft.map
          twicePuncturedComplexLeftHomotopyEquivPuncturedComplex.continuous)).cast
            twicePuncturedComplexLeftHomotopyEquiv_basepoint.symm
            twicePuncturedComplexLeftHomotopyEquiv_basepoint.symm) = _
  rw [← Path.Homotopic.Quotient.mk_cast,
    twicePuncturedClockwiseZeroMeridianInLeft_map]
  exact puncturedComplexFundamentalGroupEquiv_integerCircle
    (2 : ℂ)⁻¹ (by norm_num) (-1)

/-- The marked clockwise one meridian has winding coordinate `-1` in the right piece. -/
public theorem twicePuncturedComplexRightFundamentalGroupEquiv_meridian :
    twicePuncturedComplexRightFundamentalGroupEquiv
        (Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight) =
      MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple (-1))) := by
  unfold twicePuncturedComplexRightFundamentalGroupEquiv
  simp only [MulEquiv.trans_apply]
  rw [fundamentalGroupMulEquivOfEq_apply]
  rw [fundamentalGroupMulEquivOfHomotopyEquiv_apply]
  rw [FundamentalGroup.map_apply]
  rw [← Path.Homotopic.Quotient.mk_map]
  change puncturedComplexFundamentalGroupEquiv (2 : ℂ)⁻¹ (by norm_num)
      ((Path.Homotopic.Quotient.mk
        (twicePuncturedClockwiseOneMeridianInRight.map
          twicePuncturedComplexRightHomotopyEquivPuncturedComplex.continuous)).cast
            twicePuncturedComplexRightHomotopyEquiv_basepoint.symm
            twicePuncturedComplexRightHomotopyEquiv_basepoint.symm) = _
  rw [← Path.Homotopic.Quotient.mk_cast,
    twicePuncturedClockwiseOneMeridianInRight_map]
  exact puncturedComplexFundamentalGroupEquiv_integerCircle
    (2 : ℂ)⁻¹ (by norm_num) (-1)

end SphereSixComplex.Topology
