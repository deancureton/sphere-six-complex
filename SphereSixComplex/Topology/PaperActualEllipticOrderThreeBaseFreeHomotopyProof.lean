module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeSmallCircleHomotopyProof
public import SphereSixComplex.Topology.TwicePuncturedComplexFundamentalGroupGeneration

@[expose] public section

noncomputable section

open Complex Metric Set Topology CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex.Topology

/-- The proposition-style and set-complement presentations of the twice-punctured plane agree. -/
public def twoPunctureComplementOneHomeomorph :
    TwoPunctureComplement (1 : ℂ) ≃ₜ TwicePuncturedComplex where
  toFun z := ⟨z.1, by
    rw [Set.mem_compl_iff]
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using z.2⟩
  invFun z := ⟨z.1, by
    have hz : z.1 ∉ ({0, 1} : Set ℂ) := z.2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hz⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

public def twoPunctureComplementOneMap :
    C(TwoPunctureComplement (1 : ℂ), TwicePuncturedComplex) :=
  ⟨twoPunctureComplementOneHomeomorph,
    twoPunctureComplementOneHomeomorph.continuous⟩

/-- Three counterclockwise turns on the marked radius-one-half zero circle. -/
public def twicePuncturedCounterclockwiseZeroTriplePoint (t : unitInterval) :
    TwicePuncturedComplex :=
  ⟨circleMap 0 (2 : ℝ)⁻¹ (2 * Real.pi * 3 * (t : ℝ)), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · exact circleMap_ne_center (by norm_num)
    · intro h
      have hs := circleMap_mem_sphere 0 (by positivity : 0 ≤ (2 : ℝ)⁻¹)
        (2 * Real.pi * 3 * (t : ℝ))
      rw [Metric.mem_sphere, h] at hs
      norm_num [Complex.dist_eq] at hs⟩

public theorem twicePuncturedCounterclockwiseZeroTriplePoint_zero :
    twicePuncturedCounterclockwiseZeroTriplePoint 0 =
      twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [twicePuncturedCounterclockwiseZeroTriplePoint,
    twicePuncturedComplexBasepoint, circleMap]

public theorem twicePuncturedCounterclockwiseZeroTriplePoint_one :
    twicePuncturedCounterclockwiseZeroTriplePoint 1 =
      twicePuncturedComplexBasepoint := by
  apply Subtype.ext
  norm_num [twicePuncturedCounterclockwiseZeroTriplePoint,
    twicePuncturedComplexBasepoint, circleMap]
  rw [show (2 : ℂ) * Real.pi * 3 * Complex.I =
      3 * ((2 : ℂ) * Real.pi * Complex.I) by ring]
  exact Complex.exp_nat_mul_two_pi_mul_I 3

/-- The standard based representative of three positive zero meridians. -/
public def twicePuncturedCounterclockwiseZeroTriple :
    Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint where
  toFun := twicePuncturedCounterclockwiseZeroTriplePoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := twicePuncturedCounterclockwiseZeroTriplePoint_zero
  target' := twicePuncturedCounterclockwiseZeroTriplePoint_one

public theorem twicePuncturedCounterclockwiseZeroTriplePoint_mem_left
    (t : unitInterval) :
    twicePuncturedCounterclockwiseZeroTriplePoint t ∈
      twicePuncturedComplexLeft := by
  change (circleMap 0 (2 : ℝ)⁻¹
    (2 * Real.pi * 3 * (t : ℝ))).re < 2 / 3
  have hre := Complex.re_le_norm
    (circleMap 0 (2 : ℝ)⁻¹ (2 * Real.pi * 3 * (t : ℝ)))
  have hs : ‖circleMap 0 (2 : ℝ)⁻¹
      (2 * Real.pi * 3 * (t : ℝ))‖ = 1 / 2 := by
    rw [norm_circleMap_zero]
    norm_num
  rw [hs] at hre
  norm_num at hre ⊢
  linarith

public def twicePuncturedCounterclockwiseZeroTripleInLeft :
    Path twicePuncturedComplexLeftBasepoint twicePuncturedComplexLeftBasepoint where
  toFun t := ⟨twicePuncturedCounterclockwiseZeroTriplePoint t,
    twicePuncturedCounterclockwiseZeroTriplePoint_mem_left t⟩
  continuous_toFun :=
    twicePuncturedCounterclockwiseZeroTriple.continuous.subtype_mk _
  source' := by
    apply Subtype.ext
    exact twicePuncturedCounterclockwiseZeroTriplePoint_zero
  target' := by
    apply Subtype.ext
    exact twicePuncturedCounterclockwiseZeroTriplePoint_one

public theorem twicePuncturedComplexLeftHomotopyEquiv_basepoint_exact :
    twicePuncturedComplexLeftHomotopyEquivPuncturedComplex
        twicePuncturedComplexLeftBasepoint =
      (⟨(2 : ℂ)⁻¹, by norm_num⟩ : PuncturedComplex) := by
  simpa only [twicePuncturedComplexLeftBasepoint] using
    twicePuncturedComplexLeftHomotopyEquivPuncturedComplex_basepoint

public theorem twicePuncturedCounterclockwiseZeroTripleInLeft_map :
    (twicePuncturedCounterclockwiseZeroTripleInLeft.map
        twicePuncturedComplexLeftHomotopyEquivPuncturedComplex.continuous).cast
          twicePuncturedComplexLeftHomotopyEquiv_basepoint_exact.symm
          twicePuncturedComplexLeftHomotopyEquiv_basepoint_exact.symm =
      puncturedComplexIntegerCircle (2 : ℂ)⁻¹ (by norm_num) 3 := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change circleMap 0 (2 : ℝ)⁻¹ (2 * Real.pi * 3 * (t : ℝ)) =
    (2 : ℂ)⁻¹ * Complex.exp
      ((2 * Real.pi * ((3 : ℤ) : ℝ) * (t : ℝ) : ℂ) * Complex.I)
  simp only [circleMap_zero]
  norm_num

public theorem twicePuncturedComplexLeftFundamentalGroupEquiv_counterclockwiseTriple :
    twicePuncturedComplexLeftFundamentalGroupEquiv
        (Path.Homotopic.Quotient.mk
          twicePuncturedCounterclockwiseZeroTripleInLeft) =
      MulOpposite.op (Multiplicative.ofAdd (complexExpDeckMultiple 3)) := by
  unfold twicePuncturedComplexLeftFundamentalGroupEquiv
  simp only [MulEquiv.trans_apply]
  rw [fundamentalGroupMulEquivOfEq_apply]
  rw [fundamentalGroupMulEquivOfHomotopyEquiv_apply]
  rw [FundamentalGroup.map_apply]
  rw [← Path.Homotopic.Quotient.mk_map]
  change puncturedComplexFundamentalGroupEquiv (2 : ℂ)⁻¹ (by norm_num)
      ((Path.Homotopic.Quotient.mk
        (twicePuncturedCounterclockwiseZeroTripleInLeft.map
          twicePuncturedComplexLeftHomotopyEquivPuncturedComplex.continuous)).cast
            twicePuncturedComplexLeftHomotopyEquiv_basepoint_exact.symm
            twicePuncturedComplexLeftHomotopyEquiv_basepoint_exact.symm) = _
  rw [← Path.Homotopic.Quotient.mk_cast,
    twicePuncturedCounterclockwiseZeroTripleInLeft_map]
  exact puncturedComplexFundamentalGroupEquiv_integerCircle
    (2 : ℂ)⁻¹ (by norm_num) 3

/-- The positive triple circle represents the cube of the inverse clockwise zero meridian. -/
public theorem twicePuncturedCounterclockwiseZeroTriple_class :
    Path.Homotopic.Quotient.mk twicePuncturedCounterclockwiseZeroTriple =
      TwicePuncturedComplex.zeroMeridianClass⁻¹ ^ 3 := by
  let tripleClass : FundamentalGroup twicePuncturedComplexLeft
      twicePuncturedComplexLeftBasepoint :=
    Path.Homotopic.Quotient.mk
      twicePuncturedCounterclockwiseZeroTripleInLeft
  let meridianClass : FundamentalGroup twicePuncturedComplexLeft
      twicePuncturedComplexLeftBasepoint :=
    Path.Homotopic.Quotient.mk twicePuncturedClockwiseZeroMeridianInLeft
  have hlocal : tripleClass = meridianClass⁻¹ ^ 3 := by
    apply twicePuncturedComplexLeftFundamentalGroupEquiv.injective
    change twicePuncturedComplexLeftFundamentalGroupEquiv
        (Path.Homotopic.Quotient.mk
          twicePuncturedCounterclockwiseZeroTripleInLeft) = _
    rw [twicePuncturedComplexLeftFundamentalGroupEquiv_counterclockwiseTriple,
      map_pow, map_inv,
      twicePuncturedComplexLeftFundamentalGroupEquiv_meridian]
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, inv_pow]
    change Multiplicative.ofAdd (complexExpDeckMultiple 3) =
      Multiplicative.ofAdd (-(3 • complexExpDeckMultiple (-1)))
    congr 1
    ext
    simp [complexExpDeckMultiple]
  have htriplemap :
      TwicePuncturedComplex.leftFundamentalGroupMap tripleClass =
        Path.Homotopic.Quotient.mk
          twicePuncturedCounterclockwiseZeroTriple := by
    unfold tripleClass TwicePuncturedComplex.leftFundamentalGroupMap
    change Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk
          twicePuncturedCounterclockwiseZeroTripleInLeft)
          TwicePuncturedComplex.leftInclusion = _
    rw [← Path.Homotopic.Quotient.mk_map]
    rfl
  have hmap := congrArg TwicePuncturedComplex.leftFundamentalGroupMap hlocal
  rw [htriplemap, map_pow, map_inv,
    TwicePuncturedComplex.leftFundamentalGroupMap_meridian] at hmap
  simpa only [TwicePuncturedComplex.zeroMeridianClass] using hmap

/-- A positive three-turn circle with arbitrary nonzero coefficient inside the unit circle. -/
public def twicePuncturedPositiveTripleCircle
    (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1) :
    C(unitInterval, TwicePuncturedComplex) where
  toFun t :=
    ⟨d * Complex.exp
      (((2 * Real.pi * 3 * (t : ℝ) : ℝ) : ℂ) * Complex.I), by
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

public def positiveTripleCoefficientHomotopyValue
    (d : ℂ) (p : unitInterval × unitInterval) : ℂ :=
  (((1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 : ℝ) : ℂ) *
    Complex.exp
      (((((1 - (p.1 : ℝ)) * d.arg : ℝ) : ℂ) * Complex.I)) *
    Complex.exp
      (((2 * Real.pi * 3 * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I)

public theorem positiveTripleCoefficientHomotopyValue_norm
    (d : ℂ) (p : unitInterval × unitInterval) :
    ‖positiveTripleCoefficientHomotopyValue d p‖ =
      (1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 := by
  have hs0 : 0 ≤ (p.1 : ℝ) := p.1.property.1
  have hs1 : (p.1 : ℝ) ≤ 1 := p.1.property.2
  have hr : 0 ≤ (1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 := by
    positivity
  rw [positiveTripleCoefficientHomotopyValue, norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_self,
    Real.exp_zero, mul_one]
  change ‖(((1 - (p.1 : ℝ)) * ‖d‖ + (p.1 : ℝ) / 2 : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

/-- Rotate and radially rescale any positive three-turn circle inside the unit disc to the
marked radius-one-half representative, without crossing either puncture. -/
public def positiveTripleCoefficientHomotopy
    (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1) :
    ContinuousMap.Homotopy
      (twicePuncturedPositiveTripleCircle d hd hd1)
      twicePuncturedCounterclockwiseZeroTriple.toContinuousMap where
  toFun p := ⟨positiveTripleCoefficientHomotopyValue d p, by
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
      rw [positiveTripleCoefficientHomotopyValue_norm, norm_zero] at hn
      exact ne_of_gt hrpos hn
    · intro h
      have hn := congrArg norm h
      rw [positiveTripleCoefficientHomotopyValue_norm, norm_one] at hn
      exact ne_of_lt hrlt hn⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold positiveTripleCoefficientHomotopyValue
    fun_prop
  map_zero_left t := by
    apply Subtype.ext
    simp [positiveTripleCoefficientHomotopyValue,
      twicePuncturedPositiveTripleCircle,
      Complex.norm_mul_exp_arg_mul_I]
  map_one_left t := by
    apply Subtype.ext
    simp [positiveTripleCoefficientHomotopyValue,
      twicePuncturedCounterclockwiseZeroTriple,
      twicePuncturedCounterclockwiseZeroTriplePoint, circleMap]

/-- Transport a homotopy through the identification of the two twice-punctured-plane
presentations. -/
public def twoPunctureComplementOneHomotopyMap
    {f g : C(unitInterval, TwoPunctureComplement (1 : ℂ))}
    (H : ContinuousMap.Homotopy f g) :
    ContinuousMap.Homotopy
      (twoPunctureComplementOneMap.comp f)
      (twoPunctureComplementOneMap.comp g) where
  toFun p := twoPunctureComplementOneHomeomorph (H p)
  continuous_toFun :=
    twoPunctureComplementOneHomeomorph.continuous.comp H.continuous
  map_zero_left t := by
    exact congrArg twoPunctureComplementOneHomeomorph (H.map_zero_left t)
  map_one_left t := by
    exact congrArg twoPunctureComplementOneHomeomorph (H.map_one_left t)

public theorem frozenLocalDegreeCircleTwoPunctures_map_eq_positiveTriple
    (u : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0)
    (hune : ∀ z ∈ closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ 3 * ‖u z‖ < ‖(1 : ℂ)‖) :
    let d := a ^ 3 * u 0
    twoPunctureComplementOneMap.comp
        (frozenLocalDegreeCircleTwoPunctures
          u 3 a 1 ha hune hbound) =
      twicePuncturedPositiveTripleCircle d
        (mul_ne_zero (pow_ne_zero 3 ha) (hune 0 (by simp)))
        (by
          rw [norm_mul, norm_pow]
          simpa using hbound 0 (by simp)) := by
  dsimp only
  ext t
  change localDegreeCirclePoint a t ^ 3 * u 0 =
    (a ^ 3 * u 0) * Complex.exp
      (((2 * Real.pi * 3 * (t : ℝ) : ℝ) : ℂ) * Complex.I)
  rw [localDegreeCirclePoint, mul_pow]
  have hexp :
      Complex.exp (((2 * Real.pi * (t : ℝ) : ℂ) * Complex.I)) ^ 3 =
        Complex.exp
          (((2 * Real.pi * 3 * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
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

/-- The actual order-three Cayley base circle is freely homotopic to the marked positive
three-turn zero circle. -/
public theorem orderThreeActualCayleyBaseCoordinate_tripleHomotopy :
    Nonempty (ContinuousMap.Homotopy
      (twoPunctureComplementOneMap.comp
        (A.orderThreeCayleyChartCircleMap
          A.orderThreeFillingRelationCayleyBaseValue
          (norm_pos_iff.mpr A.orderThreeFillingRelationCayleyBaseValue_ne_zero)
          (by
            rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
            exact A.orderThreeActualEllipticBoundaryBase.1.2.2)))
      twicePuncturedCounterclockwiseZeroTriple.toContinuousMap) := by
  obtain ⟨u, a, ha, hune, hbound, H⟩ :=
    A.exists_orderThreeActualCayleyBaseCoordinate_threeTurnHomotopy
  rcases H with ⟨H⟩
  let d : ℂ := a ^ 3 * u 0
  have hd : d ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 ha) (hune 0 (by simp))
  have hd1 : ‖d‖ < 1 := by
    dsimp [d]
    rw [norm_mul, norm_pow]
    simpa using hbound 0 (by simp)
  let Hlocal := twoPunctureComplementOneHomotopyMap H
  have hfrozen :
      twoPunctureComplementOneMap.comp
          (frozenLocalDegreeCircleTwoPunctures
            u 3 a 1 ha hune hbound) =
        twicePuncturedPositiveTripleCircle d hd hd1 := by
    simpa [d] using
      frozenLocalDegreeCircleTwoPunctures_map_eq_positiveTriple
        u a ha hune hbound
  exact ⟨(Hlocal.cast rfl hfrozen).trans
    (positiveTripleCoefficientHomotopy d hd hd1)⟩

/-- The affine base coordinate of the projected complete order-three filling loop. -/
public noncomputable def orderThreeFillingRelationBaseCoordinateMap :
    C(unitInterval, TwicePuncturedComplex) := by
  letI := A.orderThreeActualEllipticBoundaryAction
  let L :=
    (A.orderThreeFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderThreeCollarRegularRepresentative_base_projects.symm
        A.orderThreeCollarRegularRepresentative_base_projects.symm
  let q : C(A.CentralFamily, TwicePuncturedComplex) :=
    ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
  exact q.comp L.toContinuousMap

public theorem orderThreeFillingRelationBaseCoordinateMap_eq_cayley :
    A.orderThreeFillingRelationBaseCoordinateMap =
      twoPunctureComplementOneMap.comp
        (A.orderThreeCayleyChartCircleMap
          A.orderThreeFillingRelationCayleyBaseValue
          (norm_pos_iff.mpr A.orderThreeFillingRelationCayleyBaseValue_ne_zero)
          (by
            rw [A.orderThreeFillingRelationCayleyBaseValue_norm]
            exact A.orderThreeActualEllipticBoundaryBase.1.2.2)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  ext t
  have h := A.orderThreeFillingRelation_baseCoordinate_eq_chartFunction t
  simpa [orderThreeFillingRelationBaseCoordinateMap,
    twoPunctureComplementOneMap, twoPunctureComplementOneHomeomorph,
    orderThreeCayleyChartCircleMap, localDegreeCirclePoint,
    orderThreeFillingRelationCayleyLoop, puncturedComplexIntegerCircle,
    puncturedComplexIntegerCirclePoint] using h

/-- The projected order-three filling relation is freely homotopic to a loop representing the
cube of the inverse marked clockwise zero meridian. -/
public theorem orderThreeFillingRelation_baseCoordinate_freeHomotopy_zeroMeridianCube :
    ∃ gamma : Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint,
      Path.Homotopic.Quotient.mk gamma =
        TwicePuncturedComplex.zeroMeridianClass⁻¹ ^ 3 ∧
      Nonempty (ContinuousMap.Homotopy
        A.orderThreeFillingRelationBaseCoordinateMap
        gamma.toContinuousMap) := by
  refine ⟨twicePuncturedCounterclockwiseZeroTriple,
    twicePuncturedCounterclockwiseZeroTriple_class, ?_⟩
  rcases A.orderThreeActualCayleyBaseCoordinate_tripleHomotopy with ⟨H⟩
  exact ⟨H.cast A.orderThreeFillingRelationBaseCoordinateMap_eq_cayley.symm rfl⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
