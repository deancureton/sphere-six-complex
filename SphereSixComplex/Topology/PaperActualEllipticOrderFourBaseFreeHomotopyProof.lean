module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourSmallCircleHomotopyProof
public import SphereSixComplex.Topology.TwicePuncturedComplexFundamentalGroupGeneration

@[expose] public section

noncomputable section

open Complex Metric Set Topology CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex.Topology

/-- Translation by one identifies the shifted punctures `{0,-1}` with `{1,0}`. -/
public def twoPunctureComplementNegOneHomeomorph :
    TwoPunctureComplement (-1 : ℂ) ≃ₜ TwicePuncturedComplex where
  toFun z := ⟨z.1 + 1, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      apply z.2.2
      linear_combination h
    · intro h
      apply z.2.1
      linear_combination h⟩
  invFun z := ⟨z.1 - 1, by
    have hz : z.1 ∉ ({0, 1} : Set ℂ) := z.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz ⊢
    constructor
    · intro h
      apply hz.2
      linear_combination h
    · intro h
      apply hz.1
      linear_combination h⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

public def twoPunctureComplementNegOneMap :
    C(TwoPunctureComplement (-1 : ℂ), TwicePuncturedComplex) :=
  ⟨twoPunctureComplementNegOneHomeomorph,
    twoPunctureComplementNegOneHomeomorph.continuous⟩

/-- Four counterclockwise turns on the marked radius-one-half circle about one. -/
public def twicePuncturedCounterclockwiseOneQuadruplePoint (t : unitInterval) :
    TwicePuncturedComplex :=
  ⟨circleMap 1 (-(2 : ℝ)⁻¹) (2 * Real.pi * 4 * (t : ℝ)), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      have hs := circleMap_mem_sphere' 1 (-(2 : ℝ)⁻¹)
        (2 * Real.pi * 4 * (t : ℝ))
      rw [Metric.mem_sphere, h] at hs
      norm_num [Complex.dist_eq] at hs
    · exact circleMap_ne_center (by norm_num)⟩

public theorem twicePuncturedCounterclockwiseOneQuadruplePoint_zero :
    twicePuncturedCounterclockwiseOneQuadruplePoint 0 =
      twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [twicePuncturedCounterclockwiseOneQuadruplePoint,
    twicePuncturedComplexBasepoint, circleMap]

public theorem twicePuncturedCounterclockwiseOneQuadruplePoint_one :
    twicePuncturedCounterclockwiseOneQuadruplePoint 1 =
      twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [twicePuncturedCounterclockwiseOneQuadruplePoint,
    twicePuncturedComplexBasepoint, circleMap]
  rw [show (2 : ℂ) * Real.pi * 4 * Complex.I =
      4 * ((2 : ℂ) * Real.pi * Complex.I) by ring]
  have hexp : Complex.exp (4 * ((2 : ℂ) * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_nat_mul_two_pi_mul_I 4 using 1
    all_goals norm_num
  rw [hexp]
  norm_num

/-- The standard based representative of four positive one meridians. -/
public def twicePuncturedCounterclockwiseOneQuadruple :
    Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint where
  toFun := twicePuncturedCounterclockwiseOneQuadruplePoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := twicePuncturedCounterclockwiseOneQuadruplePoint_zero
  target' := twicePuncturedCounterclockwiseOneQuadruplePoint_one

public theorem twicePuncturedCounterclockwiseOneQuadruplePoint_mem_right
    (t : unitInterval) :
    twicePuncturedCounterclockwiseOneQuadruplePoint t ∈
      twicePuncturedComplexRight := by
  change 1 / 3 < (circleMap 1 (-(2 : ℝ)⁻¹)
    (2 * Real.pi * 4 * (t : ℝ))).re
  have hre := Complex.abs_re_le_norm
    (circleMap 1 (-(2 : ℝ)⁻¹) (2 * Real.pi * 4 * (t : ℝ)) - 1)
  have hs : ‖circleMap 1 (-(2 : ℝ)⁻¹)
      (2 * Real.pi * 4 * (t : ℝ)) - 1‖ = 1 / 2 := by
    rw [circleMap_sub_center, norm_circleMap_zero]
    norm_num
  simp only [Complex.sub_re, Complex.one_re] at hre
  rw [hs] at hre
  have hlo := neg_le_of_abs_le hre
  norm_num at hlo ⊢
  linarith

public def twicePuncturedCounterclockwiseOneQuadrupleInRight :
    Path twicePuncturedComplexRightBasepoint twicePuncturedComplexRightBasepoint where
  toFun t := ⟨twicePuncturedCounterclockwiseOneQuadruplePoint t,
    twicePuncturedCounterclockwiseOneQuadruplePoint_mem_right t⟩
  continuous_toFun :=
    twicePuncturedCounterclockwiseOneQuadruple.continuous.subtype_mk _
  source' := by
    apply Subtype.ext
    exact twicePuncturedCounterclockwiseOneQuadruplePoint_zero
  target' := by
    apply Subtype.ext
    exact twicePuncturedCounterclockwiseOneQuadruplePoint_one

public theorem twicePuncturedComplexRightHomotopyEquiv_basepoint_exact :
    twicePuncturedComplexRightHomotopyEquivPuncturedComplex
        twicePuncturedComplexRightBasepoint =
      (⟨(2 : ℂ)⁻¹, by norm_num⟩ : PuncturedComplex) := by
  simpa only [twicePuncturedComplexRightBasepoint] using
    twicePuncturedComplexRightHomotopyEquivPuncturedComplex_basepoint

public theorem twicePuncturedCounterclockwiseOneQuadrupleInRight_map :
    (twicePuncturedCounterclockwiseOneQuadrupleInRight.map
        twicePuncturedComplexRightHomotopyEquivPuncturedComplex.continuous).cast
          twicePuncturedComplexRightHomotopyEquiv_basepoint_exact.symm
          twicePuncturedComplexRightHomotopyEquiv_basepoint_exact.symm =
      puncturedComplexIntegerCircle (2 : ℂ)⁻¹ (by norm_num) 4 := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change 1 - circleMap 1 (-(2 : ℝ)⁻¹) (2 * Real.pi * 4 * (t : ℝ)) =
    (2 : ℂ)⁻¹ * Complex.exp
      ((2 * Real.pi * ((4 : ℤ) : ℝ) * (t : ℝ) : ℂ) * Complex.I)
  simp only [circleMap]
  norm_num

public theorem twicePuncturedComplexRightFundamentalGroupEquiv_counterclockwiseOneQuadruple :
    twicePuncturedComplexRightFundamentalGroupEquiv
        (Path.Homotopic.Quotient.mk
          twicePuncturedCounterclockwiseOneQuadrupleInRight) =
      MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple 4)) := by
  unfold twicePuncturedComplexRightFundamentalGroupEquiv
  simp only [MulEquiv.trans_apply]
  rw [fundamentalGroupMulEquivOfEq_apply]
  rw [fundamentalGroupMulEquivOfHomotopyEquiv_apply]
  rw [FundamentalGroup.map_apply]
  rw [← Path.Homotopic.Quotient.mk_map]
  change puncturedComplexFundamentalGroupEquiv (2 : ℂ)⁻¹ (by norm_num)
      ((Path.Homotopic.Quotient.mk
        (twicePuncturedCounterclockwiseOneQuadrupleInRight.map
          twicePuncturedComplexRightHomotopyEquivPuncturedComplex.continuous)).cast
            twicePuncturedComplexRightHomotopyEquiv_basepoint_exact.symm
            twicePuncturedComplexRightHomotopyEquiv_basepoint_exact.symm) = _
  rw [← Path.Homotopic.Quotient.mk_cast,
    twicePuncturedCounterclockwiseOneQuadrupleInRight_map]
  exact puncturedComplexFundamentalGroupEquiv_integerCircle
    (2 : ℂ)⁻¹ (by norm_num) 4

/-- The positive quadruple circle represents the fourth power of the inverse clockwise one
meridian. -/
public theorem twicePuncturedCounterclockwiseOneQuadruple_class :
    Path.Homotopic.Quotient.mk twicePuncturedCounterclockwiseOneQuadruple =
      TwicePuncturedComplex.oneMeridianClass⁻¹ ^ 4 := by
  let quadrupleClass : FundamentalGroup twicePuncturedComplexRight
      twicePuncturedComplexRightBasepoint :=
    Path.Homotopic.Quotient.mk
      twicePuncturedCounterclockwiseOneQuadrupleInRight
  let meridianClass : FundamentalGroup twicePuncturedComplexRight
      twicePuncturedComplexRightBasepoint :=
    Path.Homotopic.Quotient.mk twicePuncturedClockwiseOneMeridianInRight
  have hlocal : quadrupleClass = meridianClass⁻¹ ^ 4 := by
    apply twicePuncturedComplexRightFundamentalGroupEquiv.injective
    change twicePuncturedComplexRightFundamentalGroupEquiv
        (Path.Homotopic.Quotient.mk
          twicePuncturedCounterclockwiseOneQuadrupleInRight) = _
    rw [twicePuncturedComplexRightFundamentalGroupEquiv_counterclockwiseOneQuadruple,
      map_pow, map_inv,
      twicePuncturedComplexRightFundamentalGroupEquiv_meridian]
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, inv_pow]
    change Multiplicative.ofAdd (complexExpDeckMultiple 4) =
      Multiplicative.ofAdd (-(4 • complexExpDeckMultiple (-1)))
    congr 1
    ext
    simp [complexExpDeckMultiple]
  have hquadruplemap :
      TwicePuncturedComplex.rightFundamentalGroupMap quadrupleClass =
        Path.Homotopic.Quotient.mk
          twicePuncturedCounterclockwiseOneQuadruple := by
    unfold quadrupleClass TwicePuncturedComplex.rightFundamentalGroupMap
    change Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk
          twicePuncturedCounterclockwiseOneQuadrupleInRight)
          TwicePuncturedComplex.rightInclusion = _
    rw [← Path.Homotopic.Quotient.mk_map]
    rfl
  have hmap := congrArg TwicePuncturedComplex.rightFundamentalGroupMap hlocal
  rw [hquadruplemap, map_pow, map_inv,
    TwicePuncturedComplex.rightFundamentalGroupMap_meridian] at hmap
  simpa only [TwicePuncturedComplex.oneMeridianClass] using hmap

/-- A positive four-turn circle about one with arbitrary nonzero coefficient of norm below one. -/
public def twicePuncturedPositiveOneQuadrupleCircle
    (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1) :
    C(unitInterval, TwicePuncturedComplex) where
  toFun t :=
    ⟨1 + d * Complex.exp
      (((2 * Real.pi * 4 * (t : ℝ) : ℝ) : ℂ) * Complex.I), by
      rw [Set.mem_compl_iff]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro h
        have hprod : d * Complex.exp
            (((2 * Real.pi * 4 * (t : ℝ) : ℝ) : ℂ) * Complex.I) = -1 := by
          linear_combination h
        have hn := congrArg norm hprod
        have him : (((2 * Real.pi * 4 * (t : ℝ) : ℝ) : ℂ) * Complex.I).re = 0 := by
          simp
        rw [norm_mul, Complex.norm_exp, him, Real.exp_zero, mul_one,
          norm_neg, norm_one] at hn
        exact ne_of_lt hd1 hn
      · intro h
        apply mul_ne_zero hd (Complex.exp_ne_zero _)
        linear_combination h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

public def positiveOneQuadrupleCoefficientHomotopyValue
    (d : ℂ) (p : unitInterval × unitInterval) : ℂ :=
  1 + (((1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 : ℝ) : ℂ) *
    Complex.exp
      (((((1 - (p.1 : ℝ)) * d.arg + (p.1 : ℝ) * Real.pi : ℝ) : ℂ) *
        Complex.I)) *
    Complex.exp
      (((2 * Real.pi * 4 * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I)

public theorem positiveOneQuadrupleCoefficientHomotopyValue_sub_one_norm
    (d : ℂ) (p : unitInterval × unitInterval) :
    ‖positiveOneQuadrupleCoefficientHomotopyValue d p - 1‖ =
      (1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 := by
  have hs0 : 0 ≤ (p.1 : ℝ) := p.1.property.1
  have hs1 : (p.1 : ℝ) ≤ 1 := p.1.property.2
  have hr : 0 ≤ (1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 := by
    positivity
  rw [positiveOneQuadrupleCoefficientHomotopyValue, add_sub_cancel_left,
    norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_self,
    Real.exp_zero, mul_one]
  change ‖(((1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

/-- Rotate and radially rescale any positive four-turn circle about one to the marked based
radius-one-half representative, without crossing either puncture. -/
public def positiveOneQuadrupleCoefficientHomotopy
    (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1) :
    ContinuousMap.Homotopy
      (twicePuncturedPositiveOneQuadrupleCircle d hd hd1)
      twicePuncturedCounterclockwiseOneQuadruple.toContinuousMap where
  toFun p := ⟨positiveOneQuadrupleCoefficientHomotopyValue d p, by
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
      have hn := congrArg (fun z : ℂ ↦ ‖z - 1‖) h
      rw [positiveOneQuadrupleCoefficientHomotopyValue_sub_one_norm] at hn
      norm_num at hn
      exact ne_of_lt hrlt hn
    · intro h
      have hn := congrArg (fun z : ℂ ↦ ‖z - 1‖) h
      rw [positiveOneQuadrupleCoefficientHomotopyValue_sub_one_norm,
        sub_self, norm_zero] at hn
      exact ne_of_gt hrpos hn⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold positiveOneQuadrupleCoefficientHomotopyValue
    fun_prop
  map_zero_left t := by
    apply Subtype.ext
    simp [positiveOneQuadrupleCoefficientHomotopyValue,
      twicePuncturedPositiveOneQuadrupleCircle,
      Complex.norm_mul_exp_arg_mul_I]
  map_one_left t := by
    apply Subtype.ext
    simp [positiveOneQuadrupleCoefficientHomotopyValue,
      twicePuncturedCounterclockwiseOneQuadruple,
      twicePuncturedCounterclockwiseOneQuadruplePoint, circleMap,
      Complex.exp_pi_mul_I]

/-- Transport a homotopy through translation from the shifted twice-punctured plane. -/
public def twoPunctureComplementNegOneHomotopyMap
    {f g : C(unitInterval, TwoPunctureComplement (-1 : ℂ))}
    (H : ContinuousMap.Homotopy f g) :
    ContinuousMap.Homotopy
      (twoPunctureComplementNegOneMap.comp f)
      (twoPunctureComplementNegOneMap.comp g) where
  toFun p := twoPunctureComplementNegOneHomeomorph (H p)
  continuous_toFun :=
    twoPunctureComplementNegOneHomeomorph.continuous.comp H.continuous
  map_zero_left t := by
    exact congrArg twoPunctureComplementNegOneHomeomorph (H.map_zero_left t)
  map_one_left t := by
    exact congrArg twoPunctureComplementNegOneHomeomorph (H.map_one_left t)

public theorem frozenLocalDegreeCircleTwoPunctures_map_eq_positiveOneQuadruple
    (u : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0)
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ 4 * ‖u z‖ < ‖(-1 : ℂ)‖) :
    let d := a ^ 4 * u 0
    twoPunctureComplementNegOneMap.comp
        (frozenLocalDegreeCircleTwoPunctures
          u 4 a (-1) ha hune hbound) =
      twicePuncturedPositiveOneQuadrupleCircle d
        (mul_ne_zero (pow_ne_zero 4 ha) (hune 0 (by simp)))
        (by
          rw [norm_mul, norm_pow]
          simpa using hbound 0 (by simp)) := by
  dsimp only
  ext t
  change localDegreeCirclePoint a t ^ 4 * u 0 + 1 =
    1 + (a ^ 4 * u 0) * Complex.exp
      (((2 * Real.pi * 4 * (t : ℝ) : ℝ) : ℂ) * Complex.I)
  rw [localDegreeCirclePoint, mul_pow]
  have hexp :
      Complex.exp (((2 * Real.pi * (t : ℝ) : ℂ) * Complex.I)) ^ 4 =
        Complex.exp
          (((2 * Real.pi * 4 * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

end SphereSixComplex.Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-- The actual order-four Cayley base circle is freely homotopic to the marked positive
four-turn circle about one. -/
public theorem orderFourActualCayleyBaseCoordinate_quadrupleHomotopy :
    Nonempty (ContinuousMap.Homotopy
      (twoPunctureComplementNegOneMap.comp
        (A.orderFourCayleyChartSubOneCircleMap
          A.orderFourFillingRelationCayleyBaseValue
          (norm_pos_iff.mpr A.orderFourFillingRelationCayleyBaseValue_ne_zero)
          (by
            rw [A.orderFourFillingRelationCayleyBaseValue_norm]
            exact A.orderFourActualEllipticBoundaryBase.1.2.2)))
      twicePuncturedCounterclockwiseOneQuadruple.toContinuousMap) := by
  obtain ⟨u, a, ha, hune, hbound, H⟩ :=
    A.exists_orderFourActualCayleyBaseCoordinate_fourTurnHomotopy
  rcases H with ⟨H⟩
  let d : ℂ := a ^ 4 * u 0
  have hd : d ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 ha) (hune 0 (by simp))
  have hd1 : ‖d‖ < 1 := by
    dsimp [d]
    rw [norm_mul, norm_pow]
    simpa using hbound 0 (by simp)
  let Hlocal := twoPunctureComplementNegOneHomotopyMap H
  have hfrozen :
      twoPunctureComplementNegOneMap.comp
          (frozenLocalDegreeCircleTwoPunctures
            u 4 a (-1) ha hune hbound) =
        twicePuncturedPositiveOneQuadrupleCircle d hd hd1 := by
    simpa [d] using
      frozenLocalDegreeCircleTwoPunctures_map_eq_positiveOneQuadruple
        u a ha hune hbound
  exact ⟨(Hlocal.cast rfl hfrozen).trans
    (positiveOneQuadrupleCoefficientHomotopy d hd hd1)⟩

/-- The affine base coordinate of the projected complete order-four filling loop. -/
public noncomputable def orderFourFillingRelationBaseCoordinateMap :
    C(unitInterval, TwicePuncturedComplex) := by
  letI := A.orderFourActualEllipticBoundaryAction
  let L :=
    (A.orderFourFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm
  let q : C(A.CentralFamily, TwicePuncturedComplex) :=
    ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
  exact q.comp L.toContinuousMap

public theorem orderFourFillingRelationBaseCoordinateMap_eq_cayley :
    A.orderFourFillingRelationBaseCoordinateMap =
      twoPunctureComplementNegOneMap.comp
        (A.orderFourCayleyChartSubOneCircleMap
          A.orderFourFillingRelationCayleyBaseValue
          (norm_pos_iff.mpr A.orderFourFillingRelationCayleyBaseValue_ne_zero)
          (by
            rw [A.orderFourFillingRelationCayleyBaseValue_norm]
            exact A.orderFourActualEllipticBoundaryBase.1.2.2)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  ext t
  have h := A.orderFourFillingRelation_baseCoordinate_eq_chartFunction t
  simpa [orderFourFillingRelationBaseCoordinateMap,
    twoPunctureComplementNegOneMap, twoPunctureComplementNegOneHomeomorph,
    orderFourCayleyChartSubOneCircleMap, localDegreeCirclePoint,
    orderFourFillingRelationCayleyLoop, puncturedComplexIntegerCircle,
    puncturedComplexIntegerCirclePoint] using h

/-- The projected order-four filling relation is freely homotopic to a loop representing the
fourth power of the inverse marked clockwise one meridian. -/
public theorem orderFourFillingRelation_baseCoordinate_freeHomotopy_oneMeridianFourth :
    ∃ gamma : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint,
      Path.Homotopic.Quotient.mk gamma =
        TwicePuncturedComplex.oneMeridianClass⁻¹ ^ 4 ∧
      Nonempty (ContinuousMap.Homotopy
        A.orderFourFillingRelationBaseCoordinateMap
        gamma.toContinuousMap) := by
  refine ⟨twicePuncturedCounterclockwiseOneQuadruple,
    twicePuncturedCounterclockwiseOneQuadruple_class, ?_⟩
  rcases A.orderFourActualCayleyBaseCoordinate_quadrupleHomotopy with ⟨H⟩
  exact ⟨H.cast A.orderFourFillingRelationBaseCoordinateMap_eq_cayley.symm rfl⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
