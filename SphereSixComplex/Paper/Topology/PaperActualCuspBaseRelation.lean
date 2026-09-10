module

public import SphereSixComplex.Paper.Topology.PaperActualCuspCoordinateWinding
public import SphereSixComplex.Prerequisites.Topology.TwicePuncturedComplexPairOfPants

/-!
# The actual cusp loop and the two finite base meridians

The selected cusp loop is rebased from its actual exterior coordinate to `1/2`.  Its logarithmic
lift identifies it with the counterclockwise exterior circle.  The explicit pair-of-pants
homotopy then identifies that class with the product of the two counterclockwise finite
meridians, in Mathlib's reversed path-composition convention.
-/

@[expose] public section

noncomputable section

open Set Metric Topology
open scoped ContinuousMap

namespace SphereSixComplex

open SphereSixComplex.Topology

/-- Radially push a nonzero complex number outside the radius-two disc. -/
public def puncturedExteriorRadialExpansionTwice :
    C(PuncturedComplex, TwicePuncturedComplex) where
  toFun z := ⟨(max 1 (2 * ‖z.1‖⁻¹) : ℝ) • z.1, by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    have hnpos : 0 < ‖z.1‖ := norm_pos_iff.mpr z.2
    have hspos : 0 < max 1 (2 * ‖z.1‖⁻¹) :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hnorm : 2 ≤ ‖(max 1 (2 * ‖z.1‖⁻¹) : ℝ) • z.1‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
      have hle : 2 * ‖z.1‖⁻¹ ≤ max 1 (2 * ‖z.1‖⁻¹) := le_max_right _ _
      have hmul : ‖z.1‖ * ‖z.1‖⁻¹ = 1 := mul_inv_cancel₀ hnpos.ne'
      nlinarith
    constructor
    · exact smul_ne_zero hspos.ne' z.2
    · intro hone
      rw [hone, norm_one] at hnorm
      norm_num at hnorm⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hn : Continuous (fun z : PuncturedComplex => ‖z.1‖) :=
      continuous_subtype_val.norm
    have hinv : Continuous (fun z : PuncturedComplex => ‖z.1‖⁻¹) :=
      hn.inv₀ (fun z => (norm_pos_iff.mpr z.2).ne')
    exact (continuous_const.max (continuous_const.mul hinv)).smul
      continuous_subtype_val

public theorem puncturedExteriorRadialExpansionTwice_eq (z : PuncturedComplex)
    (hz : 2 ≤ ‖z.1‖) :
    puncturedExteriorRadialExpansionTwice z = ⟨z.1, by
      rw [Set.mem_compl_iff]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨z.2, ?_⟩
      intro hone
      rw [hone, norm_one] at hz
      norm_num at hz⟩ := by
  apply Subtype.ext
  change (max 1 (2 * ‖z.1‖⁻¹) : ℝ) • z.1 = z.1
  have hnpos : 0 < ‖z.1‖ := norm_pos_iff.mpr z.2
  have hmul : ‖z.1‖ * ‖z.1‖⁻¹ = 1 := mul_inv_cancel₀ hnpos.ne'
  have hratio : 2 * ‖z.1‖⁻¹ ≤ 1 := by nlinarith
  rw [max_eq_left hratio, one_smul]

public theorem puncturedExteriorRadialExpansionTwice_standardBasepoint :
    TwicePuncturedComplex.PairOfPants.exteriorBasepoint =
      puncturedExteriorRadialExpansionTwice
        (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex) := by
  apply Subtype.ext
  exact congrArg Subtype.val
    (puncturedExteriorRadialExpansionTwice_eq
      (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex) (by norm_num)) |>.symm

end SphereSixComplex

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-! ## A coherent logarithmic whisker to the actual exterior basepoint -/

public noncomputable def cuspExteriorWhiskerLiftPoint (t : unitInterval) : ℂ :=
  ((1 - (t : ℝ) : ℝ) : ℂ) * Complex.log 2 +
    ((t : ℝ) : ℂ) * Complex.log A.cuspAngularZeroPuncturedBasepoint.1

public theorem cuspExteriorWhiskerLiftPoint_norm_ge (t : unitInterval) :
    2 ≤ ‖Complex.exp (A.cuspExteriorWhiskerLiftPoint t)‖ := by
  have hzgt : 2 < ‖A.cuspAngularZeroPuncturedBasepoint.1‖ := by
    have h := A.cuspAngularCoordinateLoop_norm_gt_two 0
    have hs := congrArg Subtype.val A.cuspAngularCoordinateLoop.source
    change 2 < ‖(A.centralFamilyCoordinate A.cuspCentralBase).1‖
    rw [← hs]
    exact h
  have hzpos : 0 < ‖A.cuspAngularZeroPuncturedBasepoint.1‖ :=
    norm_pos_iff.mpr A.cuspAngularZeroPuncturedBasepoint.2
  have hlog : Real.log 2 ≤
      Real.log ‖A.cuspAngularZeroPuncturedBasepoint.1‖ :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hzpos hzgt.le
  rw [Complex.norm_exp]
  apply (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm.trans_le
  apply Real.exp_le_exp.mpr
  unfold cuspExteriorWhiskerLiftPoint
  norm_num only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.log_re, Complex.log_re]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo]
  nlinarith [t.2.1, t.2.2]

@[simp]
public theorem cuspExteriorWhiskerLiftPoint_zero :
    A.cuspExteriorWhiskerLiftPoint 0 = Complex.log 2 := by
  simp [cuspExteriorWhiskerLiftPoint]

@[simp]
public theorem cuspExteriorWhiskerLiftPoint_one :
    A.cuspExteriorWhiskerLiftPoint 1 =
      Complex.log A.cuspAngularZeroPuncturedBasepoint.1 := by
  simp [cuspExteriorWhiskerLiftPoint]

public theorem continuous_cuspExteriorWhiskerLiftPoint :
    Continuous A.cuspExteriorWhiskerLiftPoint := by
  unfold cuspExteriorWhiskerLiftPoint
  fun_prop

public noncomputable def cuspExteriorWhiskerLift :
    Path (Complex.log 2)
      (Complex.log A.cuspAngularZeroPuncturedBasepoint.1) where
  toFun := A.cuspExteriorWhiskerLiftPoint
  continuous_toFun := A.continuous_cuspExteriorWhiskerLiftPoint
  source' := A.cuspExteriorWhiskerLiftPoint_zero
  target' := A.cuspExteriorWhiskerLiftPoint_one

public noncomputable def cuspExteriorPuncturedWhiskerPoint
    (t : unitInterval) : PuncturedComplex :=
  ⟨Complex.exp (A.cuspExteriorWhiskerLiftPoint t), Complex.exp_ne_zero _⟩

@[simp]
public theorem cuspExteriorPuncturedWhiskerPoint_zero :
    A.cuspExteriorPuncturedWhiskerPoint 0 =
      (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex) := by
  apply Subtype.ext
  change Complex.exp (A.cuspExteriorWhiskerLiftPoint 0) = 2
  rw [A.cuspExteriorWhiskerLiftPoint_zero, Complex.exp_log]
  norm_num

@[simp]
public theorem cuspExteriorPuncturedWhiskerPoint_one :
    A.cuspExteriorPuncturedWhiskerPoint 1 =
      A.cuspAngularZeroPuncturedBasepoint := by
  apply Subtype.ext
  change Complex.exp (A.cuspExteriorWhiskerLiftPoint 1) =
    A.cuspAngularZeroPuncturedBasepoint.1
  rw [A.cuspExteriorWhiskerLiftPoint_one,
    Complex.exp_log A.cuspAngularZeroPuncturedBasepoint.2]

public noncomputable def cuspExteriorPuncturedWhisker :
    Path (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex)
      A.cuspAngularZeroPuncturedBasepoint where
  toFun := A.cuspExteriorPuncturedWhiskerPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.continuous_exp.comp A.continuous_cuspExteriorWhiskerLiftPoint
  source' := A.cuspExteriorPuncturedWhiskerPoint_zero
  target' := A.cuspExteriorPuncturedWhiskerPoint_one

public noncomputable def cuspExteriorTwiceWhiskerPoint
    (t : unitInterval) : TwicePuncturedComplex :=
  ⟨Complex.exp (A.cuspExteriorWhiskerLiftPoint t), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨Complex.exp_ne_zero _, ?_⟩
    intro hone
    have hn := A.cuspExteriorWhiskerLiftPoint_norm_ge t
    rw [hone, norm_one] at hn
    norm_num at hn⟩

@[simp]
public theorem cuspExteriorTwiceWhiskerPoint_zero :
    A.cuspExteriorTwiceWhiskerPoint 0 = TwicePuncturedComplex.PairOfPants.exteriorBasepoint := by
  apply Subtype.ext
  change Complex.exp (A.cuspExteriorWhiskerLiftPoint 0) = 2
  rw [A.cuspExteriorWhiskerLiftPoint_zero, Complex.exp_log]
  norm_num

@[simp]
public theorem cuspExteriorTwiceWhiskerPoint_one :
    A.cuspExteriorTwiceWhiskerPoint 1 =
      A.centralFamilyCoordinate A.cuspCentralBase := by
  apply Subtype.ext
  change Complex.exp (A.cuspExteriorWhiskerLiftPoint 1) = _
  rw [A.cuspExteriorWhiskerLiftPoint_one,
    Complex.exp_log A.cuspAngularZeroPuncturedBasepoint.2]
  rfl

public noncomputable def cuspExteriorTwiceWhisker :
    Path TwicePuncturedComplex.PairOfPants.exteriorBasepoint
      (A.centralFamilyCoordinate A.cuspCentralBase) where
  toFun := A.cuspExteriorTwiceWhiskerPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.continuous_exp.comp A.continuous_cuspExteriorWhiskerLiftPoint
  source' := A.cuspExteriorTwiceWhiskerPoint_zero
  target' := A.cuspExteriorTwiceWhiskerPoint_one

/-! ## The actual loop is the positive exterior circle -/

public noncomputable def cuspExteriorShiftedReverseLiftPoint
    (t : unitInterval) : ℂ :=
  A.cuspExteriorWhiskerLiftPoint (unitInterval.symm t) +
    (1 : ℤ) • (2 * Real.pi * Complex.I)

public noncomputable def cuspExteriorShiftedReverseLift :
    Path
      (Complex.log A.cuspAngularZeroPuncturedBasepoint.1 +
        (1 : ℤ) • (2 * Real.pi * Complex.I))
      (Complex.log 2 + (1 : ℤ) • (2 * Real.pi * Complex.I)) where
  toFun := A.cuspExteriorShiftedReverseLiftPoint
  continuous_toFun := by
    unfold cuspExteriorShiftedReverseLiftPoint
    exact (A.continuous_cuspExteriorWhiskerLiftPoint.comp
      unitInterval.continuous_symm).add continuous_const
  source' := by simp [cuspExteriorShiftedReverseLiftPoint]
  target' := by simp [cuspExteriorShiftedReverseLiftPoint]

public theorem cuspExteriorShiftedReverseLiftPoint_exp (t : unitInterval) :
    Complex.exp (A.cuspExteriorShiftedReverseLiftPoint t) =
      (A.cuspExteriorPuncturedWhisker.symm t).1 := by
  unfold cuspExteriorShiftedReverseLiftPoint
  rw [Complex.exp_add]
  have hdeck : Complex.exp ((1 : ℤ) • (2 * Real.pi * Complex.I)) = 1 := by
    rw [show (1 : ℤ) • (2 * Real.pi * Complex.I) =
        ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_int_mul]
    simp
  rw [hdeck, mul_one]
  rfl

public noncomputable def cuspExteriorWhiskeredPuncturedLoop :
    Path (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex)
      (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex) :=
  A.cuspExteriorPuncturedWhisker.trans
    (A.cuspAngularZeroPuncturedLoop.trans
      A.cuspExteriorPuncturedWhisker.symm)

public noncomputable def cuspExteriorWhiskeredLogLift :
    Path (Complex.log 2)
      (Complex.log 2 + (1 : ℤ) • (2 * Real.pi * Complex.I)) :=
  A.cuspExteriorWhiskerLift.trans
    (A.cuspAngularZeroLogLift.trans
      A.cuspExteriorShiftedReverseLift)

public theorem cuspExteriorWhiskeredLogLift_map_exp :
    ((A.cuspExteriorWhiskeredLogLift.map
      complexExpCoverContinuousMap.continuous).cast
        (complexExpCoverContinuousMap_log 2 (by norm_num)).symm
        (complexExpCoverContinuousMap_log_add_deck 2 (by norm_num) 1).symm) =
      A.cuspExteriorWhiskeredPuncturedLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  unfold cuspExteriorWhiskeredLogLift
    cuspExteriorWhiskeredPuncturedLoop
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.trans_apply,
    Path.symm_apply]
  split_ifs
  · rfl
  · exact A.cuspAngularZeroLogLiftPoint_exp _
  · exact A.cuspExteriorShiftedReverseLiftPoint_exp _

public theorem cuspExteriorWhiskeredPuncturedLoop_class_eq_integerCircle :
    Path.Homotopic.Quotient.mk A.cuspExteriorWhiskeredPuncturedLoop =
      Path.Homotopic.Quotient.mk
        (puncturedComplexIntegerCircle 2 (by norm_num) 1) := by
  exact puncturedComplex_loopClass_eq_integerCircle_of_lift
    2 (by norm_num) 1 A.cuspExteriorWhiskeredPuncturedLoop
    A.cuspExteriorWhiskeredLogLift
    A.cuspExteriorWhiskeredLogLift_map_exp

public noncomputable def cuspExteriorWhiskeredTwiceLoop :
    Path TwicePuncturedComplex.PairOfPants.exteriorBasepoint
      TwicePuncturedComplex.PairOfPants.exteriorBasepoint :=
  A.cuspExteriorTwiceWhisker.trans
    (A.cuspAngularCoordinateLoop.trans A.cuspExteriorTwiceWhisker.symm)

public theorem cuspExteriorWhiskeredPuncturedLoop_map_expansion :
    (A.cuspExteriorWhiskeredPuncturedLoop.map
      puncturedExteriorRadialExpansionTwice.continuous).cast
        puncturedExteriorRadialExpansionTwice_standardBasepoint
        puncturedExteriorRadialExpansionTwice_standardBasepoint =
      A.cuspExteriorWhiskeredTwiceLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  unfold cuspExteriorWhiskeredPuncturedLoop
    cuspExteriorWhiskeredTwiceLoop
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.trans_apply,
    Path.symm_apply]
  split_ifs
  · let u : unitInterval := ⟨2 * (t : ℝ), by
      constructor <;> nlinarith [t.2.1]⟩
    exact congrArg Subtype.val
      (puncturedExteriorRadialExpansionTwice_eq
        (A.cuspExteriorPuncturedWhisker u)
        (A.cuspExteriorWhiskerLiftPoint_norm_ge u))
  · let u : unitInterval := ⟨2 * (2 * (t : ℝ) - 1), by
      constructor
      · nlinarith [t.2.1]
      · nlinarith⟩
    exact congrArg Subtype.val
      (puncturedExteriorRadialExpansionTwice_eq
        (A.cuspAngularZeroPuncturedLoop u)
        (A.cuspAngularCoordinateLoop_norm_gt_two u).le)
  · let u : unitInterval := ⟨2 * (2 * (t : ℝ) - 1) - 1, by
      constructor
      · nlinarith
      · nlinarith [t.2.2]⟩
    exact congrArg Subtype.val
      (puncturedExteriorRadialExpansionTwice_eq
        (A.cuspExteriorPuncturedWhisker (unitInterval.symm u))
        (A.cuspExteriorWhiskerLiftPoint_norm_ge (unitInterval.symm u)))

public theorem puncturedIntegerCircle_one_map_expansion :
    ((puncturedComplexIntegerCircle 2 (by norm_num) 1).map
      puncturedExteriorRadialExpansionTwice.continuous).cast
        puncturedExteriorRadialExpansionTwice_standardBasepoint
        puncturedExteriorRadialExpansionTwice_standardBasepoint =
      TwicePuncturedComplex.PairOfPants.clockwiseExteriorMeridian.symm := by
  apply Path.ext
  funext t
  apply Subtype.ext
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
  have hnorm : 2 ≤ ‖((puncturedComplexIntegerCircle 2 (by norm_num) 1) t).1‖ := by
    change 2 ≤ ‖2 * Complex.exp
      ((2 * Real.pi * ((1 : ℤ) : ℝ) * (t : ℝ) : ℂ) * Complex.I)‖
    rw [norm_mul, Complex.norm_exp]
    norm_num
  rw [congrArg Subtype.val (puncturedExteriorRadialExpansionTwice_eq
    ((puncturedComplexIntegerCircle 2 (by norm_num) 1) t) hnorm)]
  change 2 * Complex.exp
      ((2 * Real.pi * ((1 : ℤ) : ℝ) * (t : ℝ) : ℂ) * Complex.I) =
    2 * Complex.exp
      (((-2 * Real.pi * ((unitInterval.symm t : unitInterval) : ℝ) : ℝ) : ℂ) *
        Complex.I)
  have harg :
      (2 : ℂ) * (Real.pi : ℂ) * (((1 : ℤ) : ℝ) : ℂ) *
          ((t : ℝ) : ℂ) * Complex.I =
        (((-2 * Real.pi * ((unitInterval.symm t : unitInterval) : ℝ) : ℝ) : ℂ) *
          Complex.I) + 2 * Real.pi * Complex.I := by
      rw [unitInterval.coe_symm_eq]
      norm_num
      ring
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

public theorem cuspExteriorWhiskeredTwiceLoop_class_eq_counterclockwise :
    Path.Homotopic.Quotient.mk A.cuspExteriorWhiskeredTwiceLoop =
      Path.Homotopic.Quotient.mk TwicePuncturedComplex.PairOfPants.clockwiseExteriorMeridian.symm := by
  have h := congrArg
    (fun q : Path.Homotopic.Quotient
        (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex)
        (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex) =>
      q.map puncturedExteriorRadialExpansionTwice)
    A.cuspExteriorWhiskeredPuncturedLoop_class_eq_integerCircle
  have hc := congrArg (fun q => q.cast
      puncturedExteriorRadialExpansionTwice_standardBasepoint
      puncturedExteriorRadialExpansionTwice_standardBasepoint) h
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, ← Path.Homotopic.Quotient.mk_cast,
    A.cuspExteriorWhiskeredPuncturedLoop_map_expansion,
    puncturedIntegerCircle_one_map_expansion] at hc
  exact hc

/-! ## Rebase at `1/2` and apply the pair-of-pants relation -/

public noncomputable def cuspCommonCoordinateLoop :
    Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint :=
  TwicePuncturedComplex.PairOfPants.exteriorBridge.trans
    (A.cuspExteriorWhiskeredTwiceLoop.trans TwicePuncturedComplex.PairOfPants.exteriorBridge.symm)

/-- The actual cusp coordinate is the product of the two counterclockwise finite meridians.
Equivalently, it is the product of the inverses of the two marked clockwise classes. -/
public theorem cuspCommonCoordinateLoop_class_eq_finiteProduct :
    Path.Homotopic.Quotient.mk A.cuspCommonCoordinateLoop =
      (TwicePuncturedComplex.zeroMeridianClass)⁻¹ *
        (TwicePuncturedComplex.oneMeridianClass)⁻¹ := by
  have hcusp : Path.Homotopic.Quotient.mk A.cuspCommonCoordinateLoop =
      Path.Homotopic.Quotient.mk
        TwicePuncturedComplex.PairOfPants.clockwiseExteriorMeridianAtBasepoint.symm := by
    have h := congrArg
      (fun q : Path.Homotopic.Quotient TwicePuncturedComplex.PairOfPants.exteriorBasepoint
          TwicePuncturedComplex.PairOfPants.exteriorBasepoint =>
        (Path.Homotopic.Quotient.mk TwicePuncturedComplex.PairOfPants.exteriorBridge).trans
          (q.trans (Path.Homotopic.Quotient.mk
            TwicePuncturedComplex.PairOfPants.exteriorBridge).symm))
      A.cuspExteriorWhiskeredTwiceLoop_class_eq_counterclockwise
    have hinv :
        (Path.Homotopic.Quotient.mk TwicePuncturedComplex.PairOfPants.exteriorBridge).trans
            ((Path.Homotopic.Quotient.mk
                TwicePuncturedComplex.PairOfPants.clockwiseExteriorMeridian).symm.trans
              (Path.Homotopic.Quotient.mk TwicePuncturedComplex.PairOfPants.exteriorBridge).symm) =
          Path.Homotopic.Quotient.mk
            TwicePuncturedComplex.PairOfPants.clockwiseExteriorMeridianAtBasepoint.symm := by
      unfold TwicePuncturedComplex.PairOfPants.clockwiseExteriorMeridianAtBasepoint
      simp only [Path.Homotopic.Quotient.mk_symm,
        Path.Homotopic.Quotient.mk_trans]
      let p := Path.Homotopic.Quotient.mk TwicePuncturedComplex.PairOfPants.exteriorBridge
      let q := Path.Homotopic.Quotient.mk
        TwicePuncturedComplex.PairOfPants.clockwiseExteriorMeridian
      have hrightInverse :
          (p.trans (q.trans p.symm)).trans
              (p.trans (q.symm.trans p.symm)) =
            Path.Homotopic.Quotient.refl twicePuncturedComplexBasepoint := by
        calc
          (p.trans (q.trans p.symm)).trans
                (p.trans (q.symm.trans p.symm)) =
              p.trans (q.trans
                (p.symm.trans (p.trans (q.symm.trans p.symm)))) := by
            simp only [Path.Homotopic.Quotient.trans_assoc]
          _ = p.trans (q.trans (q.symm.trans p.symm)) := by
            rw [← Path.Homotopic.Quotient.trans_assoc p.symm p,
              Path.Homotopic.Quotient.symm_trans,
              Path.Homotopic.Quotient.refl_trans]
          _ = p.trans ((q.trans q.symm).trans p.symm) := by
            rw [Path.Homotopic.Quotient.trans_assoc]
          _ = p.trans p.symm := by
            rw [Path.Homotopic.Quotient.trans_symm,
              Path.Homotopic.Quotient.refl_trans]
          _ = Path.Homotopic.Quotient.refl twicePuncturedComplexBasepoint :=
            Path.Homotopic.Quotient.trans_symm p
      calc
        p.trans (q.symm.trans p.symm) =
            (Path.Homotopic.Quotient.refl twicePuncturedComplexBasepoint).trans
              (p.trans (q.symm.trans p.symm)) :=
          (Path.Homotopic.Quotient.refl_trans _).symm
        _ = ((p.trans (q.trans p.symm)).symm.trans
              (p.trans (q.trans p.symm))).trans
                (p.trans (q.symm.trans p.symm)) := by
          rw [Path.Homotopic.Quotient.symm_trans]
        _ = (p.trans (q.trans p.symm)).symm.trans
              ((p.trans (q.trans p.symm)).trans
                (p.trans (q.symm.trans p.symm))) :=
          Path.Homotopic.Quotient.trans_assoc _ _ _
        _ = (p.trans (q.trans p.symm)).symm := by
          rw [hrightInverse, Path.Homotopic.Quotient.trans_refl]
    unfold cuspCommonCoordinateLoop
    simpa only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm] using h.trans hinv
  rw [hcusp, Path.Homotopic.Quotient.mk_symm,
    TwicePuncturedComplex.PairOfPants.exterior_class_eq_finiteComposite]
  simp only [Path.Homotopic.Quotient.mk_trans]
  change
    (TwicePuncturedComplex.oneMeridianClass *
      TwicePuncturedComplex.zeroMeridianClass)⁻¹ =
    TwicePuncturedComplex.zeroMeridianClass⁻¹ *
      TwicePuncturedComplex.oneMeridianClass⁻¹
  exact mul_inv_rev _ _

end SphereSixComplex.Geometry.PaperAnalyticData

end
