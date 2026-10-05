module

public import SphereSixComplex.Prerequisites.Topology.PuncturedPlane.TwicePuncturedGenerators
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.FreeLoop

@[expose] public section
noncomputable section
open Complex Metric Set Topology CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex.Topology.TwicePuncturedComplex.Circles

public def circlePoint (n : ℕ) (t : unitInterval) :
    TwicePuncturedComplex :=
  ⟨circleMap 0 (2 : ℝ)⁻¹ (2 * Real.pi * n * (t : ℝ)), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · exact circleMap_ne_center (by norm_num)
    · intro h
      have hs := circleMap_mem_sphere 0 (by positivity : 0 ≤ (2 : ℝ)⁻¹)
        (2 * Real.pi * n * (t : ℝ))
      rw [Metric.mem_sphere, h] at hs
      norm_num [Complex.dist_eq] at hs⟩

public theorem circlePoint_zero (n : ℕ) :
    (circlePoint n) 0 =
      twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [circlePoint,
    twicePuncturedComplexBasepoint, circleMap]

public theorem circlePoint_one (n : ℕ) :
    (circlePoint n) 1 =
      twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [circlePoint,
    twicePuncturedComplexBasepoint, circleMap]
  rw [show (2 : ℂ) * Real.pi * n * Complex.I =
      n * ((2 : ℂ) * Real.pi * Complex.I) by ring]
  exact Complex.exp_nat_mul_two_pi_mul_I n


public def circle (n : ℕ) :
    Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint where
  toFun := (circlePoint n)
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := (circlePoint_zero n)
  target' := (circlePoint_one n)

public theorem circlePoint_mem_left (n : ℕ)
    (t : unitInterval) :
    (circlePoint n) t ∈
      twicePuncturedComplexLeft := by
  change (circleMap 0 (2 : ℝ)⁻¹
    (2 * Real.pi * n * (t : ℝ))).re < 2 / 3
  have hre := Complex.re_le_norm
    (circleMap 0 (2 : ℝ)⁻¹ (2 * Real.pi * n * (t : ℝ)))
  have hs : ‖circleMap 0 (2 : ℝ)⁻¹
      (2 * Real.pi * n * (t : ℝ))‖ = 1 / 2 := by
    rw [norm_circleMap_zero]
    norm_num
  rw [hs] at hre
  norm_num at hre ⊢
  linarith

public def circleInLeft (n : ℕ) :
    Path twicePuncturedComplexLeftBasepoint twicePuncturedComplexLeftBasepoint where
  toFun t := ⟨(circlePoint n) t,
    (circlePoint_mem_left n) t⟩
  continuous_toFun :=
    (circle n).continuous.subtype_mk _
  source' := by
    apply Subtype.ext
    exact (circlePoint_zero n)
  target' := by
    apply Subtype.ext
    exact (circlePoint_one n)

public theorem basepoint_eq :
    twicePuncturedComplexLeftHomotopyEquivPuncturedComplex
        twicePuncturedComplexLeftBasepoint =
      (⟨(2 : ℂ)⁻¹, by norm_num⟩ : PuncturedComplex) := by
  simpa only [twicePuncturedComplexLeftBasepoint] using
    twicePuncturedComplexLeftHomotopyEquivPuncturedComplex_basepoint

public theorem circleInLeft_map (n : ℕ) :
    ((circleInLeft n).map
        twicePuncturedComplexLeftHomotopyEquivPuncturedComplex.continuous).cast
          basepoint_eq.symm
          basepoint_eq.symm =
      puncturedComplexIntegerCircle (2 : ℂ)⁻¹ (by norm_num) n := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change circleMap 0 (2 : ℝ)⁻¹ (2 * Real.pi * n * (t : ℝ)) =
    (2 : ℂ)⁻¹ * Complex.exp
      ((2 * Real.pi * ((n : ℤ) : ℝ) * (t : ℝ) : ℂ) * Complex.I)
  simp only [circleMap_zero]
  norm_num

public theorem circleInLeft_winding (n : ℕ) :
    twicePuncturedComplexLeftFundamentalGroupEquiv
        (Path.Homotopic.Quotient.mk
          (circleInLeft n)) =
      MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple n)) := by
  unfold twicePuncturedComplexLeftFundamentalGroupEquiv
  simp only [MulEquiv.trans_apply]
  rw [fundamentalGroupMulEquivOfEq_apply]
  rw [fundamentalGroupMulEquivOfHomotopyEquiv_apply]
  rw [FundamentalGroup.map_apply]
  rw [← Path.Homotopic.Quotient.mk_map]
  change puncturedComplexFundamentalGroupEquiv (2 : ℂ)⁻¹ (by norm_num)
      ((Path.Homotopic.Quotient.mk
        ((circleInLeft n).map
          twicePuncturedComplexLeftHomotopyEquivPuncturedComplex.continuous)).cast
            basepoint_eq.symm
            basepoint_eq.symm) = _
  rw [← Path.Homotopic.Quotient.mk_cast,
    (circleInLeft_map n)]
  exact puncturedComplexFundamentalGroupEquiv_integerCircle
    (2 : ℂ)⁻¹ (by norm_num) n


public theorem circle_class (n : ℕ) :
    Path.Homotopic.Quotient.mk (circle n) =
      TwicePuncturedComplex.zeroMeridianClass⁻¹ ^ n := by
  let circleClass : FundamentalGroup twicePuncturedComplexLeft
      twicePuncturedComplexLeftBasepoint :=
    Path.Homotopic.Quotient.mk
      (circleInLeft n)
  let meridianClass : FundamentalGroup twicePuncturedComplexLeft
      twicePuncturedComplexLeftBasepoint :=
    Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft
  have hlocal : circleClass = meridianClass⁻¹ ^ n := by
    apply twicePuncturedComplexLeftFundamentalGroupEquiv.injective
    change twicePuncturedComplexLeftFundamentalGroupEquiv
        (Path.Homotopic.Quotient.mk
          (circleInLeft n)) = _
    rw [(circleInLeft_winding n),
      map_pow, map_inv,
      twicePuncturedComplexLeftFundamentalGroupEquiv_meridian]
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, inv_pow]
    change Multiplicative.ofAdd (complexExpDeckMultiple n) =
      Multiplicative.ofAdd (-(n • complexExpDeckMultiple (-1)))
    congr 1
    ext
    simp [complexExpDeckMultiple]
  have htriplemap :
      TwicePuncturedComplex.leftFundamentalGroupMap circleClass =
        Path.Homotopic.Quotient.mk
          (circle n) := by
    unfold circleClass TwicePuncturedComplex.leftFundamentalGroupMap
    change Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk
          (circleInLeft n))
          TwicePuncturedComplex.leftInclusion = _
    rw [← Path.Homotopic.Quotient.mk_map]
    rfl
  have hmap := congrArg TwicePuncturedComplex.leftFundamentalGroupMap hlocal
  rw [htriplemap, map_pow, map_inv,
    TwicePuncturedComplex.leftFundamentalGroupMap_meridian] at hmap
  simpa only [TwicePuncturedComplex.zeroMeridianClass] using hmap


public def coefficientCircle (n : ℕ)
    (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1) :
    C(unitInterval, TwicePuncturedComplex) where
  toFun t :=
    ⟨d * Complex.exp
      (((2 * Real.pi * n * (t : ℝ) : ℝ) : ℂ) * Complex.I), by
      rw [Set.mem_compl_iff]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · exact mul_ne_zero hd (Complex.exp_ne_zero _)
      · intro h
        have hn := congrArg norm h
        rw [norm_mul, Complex.norm_exp] at hn
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, sub_self,
          Real.exp_zero, mul_one, norm_one] at hn
        exact ne_of_lt hd1 hn⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

public def coefficientHomotopyValue (n : ℕ)
    (d : ℂ) (p : unitInterval × unitInterval) : ℂ :=
  (((1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 : ℝ) : ℂ) *
    Complex.exp
      (((((1 - (p.1 : ℝ)) * d.arg : ℝ) : ℂ) * Complex.I)) *
    Complex.exp
      (((2 * Real.pi * n * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I)

public theorem coefficientHomotopyValue_norm (n : ℕ)
    (d : ℂ) (p : unitInterval × unitInterval) :
    ‖(coefficientHomotopyValue n) d p‖ =
      (1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 := by
  have hs0 : 0 ≤ (p.1 : ℝ) := p.1.property.1
  have hs1 : (p.1 : ℝ) ≤ 1 := p.1.property.2
  have hr : 0 ≤ (1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 := by
    positivity
  rw [coefficientHomotopyValue, norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_self,
    Real.exp_zero, mul_one]
  change ‖(((1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]


public def coefficientHomotopy (n : ℕ)
    (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1) :
    ContinuousMap.Homotopy
      ((coefficientCircle n) d hd hd1)
      (circle n).toContinuousMap where
  toFun p := ⟨(coefficientHomotopyValue n) d p, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    have hs0 : 0 ≤ (p.1 : ℝ) := p.1.property.1
    have hs1 : (p.1 : ℝ) ≤ 1 := p.1.property.2
    have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have hrpos : 0 < (1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 := by
      by_cases hs : (p.1 : ℝ) = 0
      · simpa [hs] using hdn
      · have hspos : 0 < (p.1 : ℝ) := lt_of_le_of_ne hs0 (Ne.symm hs)
        positivity
    have hrlt : (1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 < 1 := by
      nlinarith
    constructor
    · intro h
      have hn := congrArg norm h
      rw [(coefficientHomotopyValue_norm n), norm_zero] at hn
      exact ne_of_gt hrpos hn
    · intro h
      have hn := congrArg norm h
      rw [(coefficientHomotopyValue_norm n), norm_one] at hn
      exact ne_of_lt hrlt hn⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold coefficientHomotopyValue
    fun_prop
  map_zero_left t := by
    apply Subtype.ext
    simp [coefficientHomotopyValue,
      coefficientCircle,
      Complex.norm_mul_exp_arg_mul_I]
  map_one_left t := by
    apply Subtype.ext
    simp [coefficientHomotopyValue,
      circle,
      circlePoint, circleMap]


open SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree

theorem circle_homology (n : ℕ) :
    loopHomologyClass (circle n) =
      n • hurewiczFunction twicePuncturedComplexBasepoint
        TwicePuncturedComplex.zeroMeridianClass⁻¹ := by
  have h := congrArg (hurewiczFunction twicePuncturedComplexBasepoint) (circle_class n)
  refine h.trans ?_
  exact congrArg Multiplicative.toAdd
    ((hurewiczPi1 twicePuncturedComplexBasepoint).map_pow _ n)

theorem coefficientCircle_homology (n : ℕ) (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1)
    {x : TwicePuncturedComplex} (p : Path x x)
    (hp : ∀ t, (p t : ℂ) = d * Complex.exp
      ((2 * Real.pi * (n : ℝ) * (t : ℝ) : ℂ) * Complex.I)) :
    loopHomologyClass p = n • hurewiczFunction twicePuncturedComplexBasepoint
      TwicePuncturedComplex.zeroMeridianClass⁻¹ := by
  have he : p.toContinuousMap = coefficientCircle n d hd hd1 := by
    ext t
    simpa [coefficientCircle] using hp t
  let H : ContinuousMap.Homotopy p.toContinuousMap (circle n).toContinuousMap :=
    { toFun := coefficientHomotopy n d hd hd1
      continuous_toFun := (coefficientHomotopy n d hd hd1).continuous
      map_zero_left := by
        intro t
        exact ((coefficientHomotopy n d hd hd1).map_zero_left t).trans
          (congrArg (fun f ↦ f t) he.symm)
      map_one_left := (coefficientHomotopy n d hd hd1).map_one_left }
  have hperiod : Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I =
      n * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_nat_mul_two_pi_mul_I n
  have hclosed (s : unitInterval) : H (s, 0) = H (s, 1) := by
    apply Subtype.ext
    change coefficientHomotopyValue n d (s, 0) = coefficientHomotopyValue n d (s, 1)
    simp [coefficientHomotopyValue, hperiod]
  exact (loopHomologyClass_eq_of_freeHomotopy p (circle n) H hclosed).trans
    (circle_homology n)

end SphereSixComplex.Topology.TwicePuncturedComplex.Circles
