module

public import SphereSixComplex.Topology.PaperActualCuspCoordinateWinding
public import SphereSixComplex.Topology.TwicePuncturedComplexPairOfPants

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
    paperStandardExteriorBasepoint =
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

public noncomputable def actualCuspExteriorWhiskerLiftPoint (t : unitInterval) : ℂ :=
  ((1 - (t : ℝ) : ℝ) : ℂ) * Complex.log 2 +
    ((t : ℝ) : ℂ) * Complex.log A.actualCuspAngularZeroPuncturedBasepoint.1

public theorem actualCuspExteriorWhiskerLiftPoint_norm_ge (t : unitInterval) :
    2 ≤ ‖Complex.exp (A.actualCuspExteriorWhiskerLiftPoint t)‖ := by
  have hzgt : 2 < ‖A.actualCuspAngularZeroPuncturedBasepoint.1‖ := by
    have h := A.actualCuspAngularCoordinateLoop_norm_gt_two 0
    have hs := congrArg Subtype.val A.actualCuspAngularCoordinateLoop.source
    change 2 < ‖(A.centralFamilyCoordinate A.actualCuspCentralBase).1‖
    rw [← hs]
    exact h
  have hzpos : 0 < ‖A.actualCuspAngularZeroPuncturedBasepoint.1‖ :=
    norm_pos_iff.mpr A.actualCuspAngularZeroPuncturedBasepoint.2
  have hlog : Real.log 2 ≤
      Real.log ‖A.actualCuspAngularZeroPuncturedBasepoint.1‖ :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hzpos hzgt.le
  rw [Complex.norm_exp]
  apply (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm.trans_le
  apply Real.exp_le_exp.mpr
  unfold actualCuspExteriorWhiskerLiftPoint
  norm_num only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.log_re, Complex.log_re]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo]
  nlinarith [t.2.1, t.2.2]

@[simp]
public theorem actualCuspExteriorWhiskerLiftPoint_zero :
    A.actualCuspExteriorWhiskerLiftPoint 0 = Complex.log 2 := by
  simp [actualCuspExteriorWhiskerLiftPoint]

@[simp]
public theorem actualCuspExteriorWhiskerLiftPoint_one :
    A.actualCuspExteriorWhiskerLiftPoint 1 =
      Complex.log A.actualCuspAngularZeroPuncturedBasepoint.1 := by
  simp [actualCuspExteriorWhiskerLiftPoint]

public theorem continuous_actualCuspExteriorWhiskerLiftPoint :
    Continuous A.actualCuspExteriorWhiskerLiftPoint := by
  unfold actualCuspExteriorWhiskerLiftPoint
  fun_prop

public noncomputable def actualCuspExteriorWhiskerLift :
    Path (Complex.log 2)
      (Complex.log A.actualCuspAngularZeroPuncturedBasepoint.1) where
  toFun := A.actualCuspExteriorWhiskerLiftPoint
  continuous_toFun := A.continuous_actualCuspExteriorWhiskerLiftPoint
  source' := A.actualCuspExteriorWhiskerLiftPoint_zero
  target' := A.actualCuspExteriorWhiskerLiftPoint_one

public noncomputable def actualCuspExteriorPuncturedWhiskerPoint
    (t : unitInterval) : PuncturedComplex :=
  ⟨Complex.exp (A.actualCuspExteriorWhiskerLiftPoint t), Complex.exp_ne_zero _⟩

@[simp]
public theorem actualCuspExteriorPuncturedWhiskerPoint_zero :
    A.actualCuspExteriorPuncturedWhiskerPoint 0 =
      (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex) := by
  apply Subtype.ext
  change Complex.exp (A.actualCuspExteriorWhiskerLiftPoint 0) = 2
  rw [A.actualCuspExteriorWhiskerLiftPoint_zero, Complex.exp_log]
  norm_num

@[simp]
public theorem actualCuspExteriorPuncturedWhiskerPoint_one :
    A.actualCuspExteriorPuncturedWhiskerPoint 1 =
      A.actualCuspAngularZeroPuncturedBasepoint := by
  apply Subtype.ext
  change Complex.exp (A.actualCuspExteriorWhiskerLiftPoint 1) =
    A.actualCuspAngularZeroPuncturedBasepoint.1
  rw [A.actualCuspExteriorWhiskerLiftPoint_one,
    Complex.exp_log A.actualCuspAngularZeroPuncturedBasepoint.2]

public noncomputable def actualCuspExteriorPuncturedWhisker :
    Path (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex)
      A.actualCuspAngularZeroPuncturedBasepoint where
  toFun := A.actualCuspExteriorPuncturedWhiskerPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.continuous_exp.comp A.continuous_actualCuspExteriorWhiskerLiftPoint
  source' := A.actualCuspExteriorPuncturedWhiskerPoint_zero
  target' := A.actualCuspExteriorPuncturedWhiskerPoint_one

public noncomputable def actualCuspExteriorTwiceWhiskerPoint
    (t : unitInterval) : TwicePuncturedComplex :=
  ⟨Complex.exp (A.actualCuspExteriorWhiskerLiftPoint t), by
    rw [Set.mem_compl_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨Complex.exp_ne_zero _, ?_⟩
    intro hone
    have hn := A.actualCuspExteriorWhiskerLiftPoint_norm_ge t
    rw [hone, norm_one] at hn
    norm_num at hn⟩

@[simp]
public theorem actualCuspExteriorTwiceWhiskerPoint_zero :
    A.actualCuspExteriorTwiceWhiskerPoint 0 = paperStandardExteriorBasepoint := by
  apply Subtype.ext
  change Complex.exp (A.actualCuspExteriorWhiskerLiftPoint 0) = 2
  rw [A.actualCuspExteriorWhiskerLiftPoint_zero, Complex.exp_log]
  norm_num

@[simp]
public theorem actualCuspExteriorTwiceWhiskerPoint_one :
    A.actualCuspExteriorTwiceWhiskerPoint 1 =
      A.centralFamilyCoordinate A.actualCuspCentralBase := by
  apply Subtype.ext
  change Complex.exp (A.actualCuspExteriorWhiskerLiftPoint 1) = _
  rw [A.actualCuspExteriorWhiskerLiftPoint_one,
    Complex.exp_log A.actualCuspAngularZeroPuncturedBasepoint.2]
  rfl

public noncomputable def actualCuspExteriorTwiceWhisker :
    Path paperStandardExteriorBasepoint
      (A.centralFamilyCoordinate A.actualCuspCentralBase) where
  toFun := A.actualCuspExteriorTwiceWhiskerPoint
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.continuous_exp.comp A.continuous_actualCuspExteriorWhiskerLiftPoint
  source' := A.actualCuspExteriorTwiceWhiskerPoint_zero
  target' := A.actualCuspExteriorTwiceWhiskerPoint_one

/-! ## The actual loop is the positive exterior circle -/

public noncomputable def actualCuspExteriorShiftedReverseLiftPoint
    (t : unitInterval) : ℂ :=
  A.actualCuspExteriorWhiskerLiftPoint (unitInterval.symm t) +
    (1 : ℤ) • (2 * Real.pi * Complex.I)

public noncomputable def actualCuspExteriorShiftedReverseLift :
    Path
      (Complex.log A.actualCuspAngularZeroPuncturedBasepoint.1 +
        (1 : ℤ) • (2 * Real.pi * Complex.I))
      (Complex.log 2 + (1 : ℤ) • (2 * Real.pi * Complex.I)) where
  toFun := A.actualCuspExteriorShiftedReverseLiftPoint
  continuous_toFun := by
    unfold actualCuspExteriorShiftedReverseLiftPoint
    exact (A.continuous_actualCuspExteriorWhiskerLiftPoint.comp
      unitInterval.continuous_symm).add continuous_const
  source' := by simp [actualCuspExteriorShiftedReverseLiftPoint]
  target' := by simp [actualCuspExteriorShiftedReverseLiftPoint]

public theorem actualCuspExteriorShiftedReverseLiftPoint_exp (t : unitInterval) :
    Complex.exp (A.actualCuspExteriorShiftedReverseLiftPoint t) =
      (A.actualCuspExteriorPuncturedWhisker.symm t).1 := by
  unfold actualCuspExteriorShiftedReverseLiftPoint
  rw [Complex.exp_add]
  have hdeck : Complex.exp ((1 : ℤ) • (2 * Real.pi * Complex.I)) = 1 := by
    rw [show (1 : ℤ) • (2 * Real.pi * Complex.I) =
        ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_int_mul]
    simp
  rw [hdeck, mul_one]
  rfl

public noncomputable def actualCuspExteriorWhiskeredPuncturedLoop :
    Path (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex)
      (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex) :=
  A.actualCuspExteriorPuncturedWhisker.trans
    (A.actualCuspAngularZeroPuncturedLoop.trans
      A.actualCuspExteriorPuncturedWhisker.symm)

public noncomputable def actualCuspExteriorWhiskeredLogLift :
    Path (Complex.log 2)
      (Complex.log 2 + (1 : ℤ) • (2 * Real.pi * Complex.I)) :=
  A.actualCuspExteriorWhiskerLift.trans
    (A.actualCuspAngularZeroLogLift.trans
      A.actualCuspExteriorShiftedReverseLift)

public theorem actualCuspExteriorWhiskeredLogLift_map_exp :
    ((A.actualCuspExteriorWhiskeredLogLift.map
      complexExpCoverContinuousMap.continuous).cast
        (complexExpCoverContinuousMap_log 2 (by norm_num)).symm
        (complexExpCoverContinuousMap_log_add_deck 2 (by norm_num) 1).symm) =
      A.actualCuspExteriorWhiskeredPuncturedLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  unfold actualCuspExteriorWhiskeredLogLift
    actualCuspExteriorWhiskeredPuncturedLoop
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.trans_apply,
    Path.symm_apply]
  split_ifs
  · rfl
  · exact A.actualCuspAngularZeroLogLiftPoint_exp _
  · exact A.actualCuspExteriorShiftedReverseLiftPoint_exp _

public theorem actualCuspExteriorWhiskeredPuncturedLoop_class_eq_integerCircle :
    Path.Homotopic.Quotient.mk A.actualCuspExteriorWhiskeredPuncturedLoop =
      Path.Homotopic.Quotient.mk
        (puncturedComplexIntegerCircle 2 (by norm_num) 1) := by
  exact puncturedComplex_loopClass_eq_integerCircle_of_lift
    2 (by norm_num) 1 A.actualCuspExteriorWhiskeredPuncturedLoop
    A.actualCuspExteriorWhiskeredLogLift
    A.actualCuspExteriorWhiskeredLogLift_map_exp

public noncomputable def actualCuspExteriorWhiskeredTwiceLoop :
    Path paperStandardExteriorBasepoint paperStandardExteriorBasepoint :=
  A.actualCuspExteriorTwiceWhisker.trans
    (A.actualCuspAngularCoordinateLoop.trans A.actualCuspExteriorTwiceWhisker.symm)

public theorem actualCuspExteriorWhiskeredPuncturedLoop_map_expansion :
    (A.actualCuspExteriorWhiskeredPuncturedLoop.map
      puncturedExteriorRadialExpansionTwice.continuous).cast
        puncturedExteriorRadialExpansionTwice_standardBasepoint
        puncturedExteriorRadialExpansionTwice_standardBasepoint =
      A.actualCuspExteriorWhiskeredTwiceLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  unfold actualCuspExteriorWhiskeredPuncturedLoop
    actualCuspExteriorWhiskeredTwiceLoop
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.trans_apply,
    Path.symm_apply]
  split_ifs
  · let u : unitInterval := ⟨2 * (t : ℝ), by
      constructor <;> nlinarith [t.2.1]⟩
    exact congrArg Subtype.val
      (puncturedExteriorRadialExpansionTwice_eq
        (A.actualCuspExteriorPuncturedWhisker u)
        (A.actualCuspExteriorWhiskerLiftPoint_norm_ge u))
  · let u : unitInterval := ⟨2 * (2 * (t : ℝ) - 1), by
      constructor
      · nlinarith [t.2.1]
      · nlinarith⟩
    exact congrArg Subtype.val
      (puncturedExteriorRadialExpansionTwice_eq
        (A.actualCuspAngularZeroPuncturedLoop u)
        (A.actualCuspAngularCoordinateLoop_norm_gt_two u).le)
  · let u : unitInterval := ⟨2 * (2 * (t : ℝ) - 1) - 1, by
      constructor
      · nlinarith
      · nlinarith [t.2.2]⟩
    exact congrArg Subtype.val
      (puncturedExteriorRadialExpansionTwice_eq
        (A.actualCuspExteriorPuncturedWhisker (unitInterval.symm u))
        (A.actualCuspExteriorWhiskerLiftPoint_norm_ge (unitInterval.symm u)))

public theorem puncturedIntegerCircle_one_map_expansion :
    ((puncturedComplexIntegerCircle 2 (by norm_num) 1).map
      puncturedExteriorRadialExpansionTwice.continuous).cast
        puncturedExteriorRadialExpansionTwice_standardBasepoint
        puncturedExteriorRadialExpansionTwice_standardBasepoint =
      paperStandardClockwiseExteriorMeridian.symm := by
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

public theorem actualCuspExteriorWhiskeredTwiceLoop_class_eq_counterclockwise :
    Path.Homotopic.Quotient.mk A.actualCuspExteriorWhiskeredTwiceLoop =
      Path.Homotopic.Quotient.mk paperStandardClockwiseExteriorMeridian.symm := by
  have h := congrArg
    (fun q : Path.Homotopic.Quotient
        (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex)
        (⟨(2 : ℂ), by norm_num⟩ : PuncturedComplex) =>
      q.map puncturedExteriorRadialExpansionTwice)
    A.actualCuspExteriorWhiskeredPuncturedLoop_class_eq_integerCircle
  have hc := congrArg (fun q => q.cast
      puncturedExteriorRadialExpansionTwice_standardBasepoint
      puncturedExteriorRadialExpansionTwice_standardBasepoint) h
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, ← Path.Homotopic.Quotient.mk_cast,
    A.actualCuspExteriorWhiskeredPuncturedLoop_map_expansion,
    puncturedIntegerCircle_one_map_expansion] at hc
  exact hc

/-! ## Rebase at `1/2` and apply the pair-of-pants relation -/

public noncomputable def actualCuspCommonCoordinateLoop :
    Path twicePuncturedComplexBasepoint twicePuncturedComplexBasepoint :=
  paperStandardExteriorBridge.trans
    (A.actualCuspExteriorWhiskeredTwiceLoop.trans paperStandardExteriorBridge.symm)

/-- The actual cusp coordinate is the product of the two counterclockwise finite meridians.
Equivalently, it is the product of the inverses of the two marked clockwise classes. -/
public theorem actualCuspCommonCoordinateLoop_class_eq_finiteProduct :
    Path.Homotopic.Quotient.mk A.actualCuspCommonCoordinateLoop =
      (TwicePuncturedComplex.zeroMeridianClass)⁻¹ *
        (TwicePuncturedComplex.oneMeridianClass)⁻¹ := by
  have hcusp : Path.Homotopic.Quotient.mk A.actualCuspCommonCoordinateLoop =
      Path.Homotopic.Quotient.mk
        paperStandardClockwiseExteriorMeridianAtCommonBasepoint.symm := by
    have h := congrArg
      (fun q : Path.Homotopic.Quotient paperStandardExteriorBasepoint
          paperStandardExteriorBasepoint =>
        (Path.Homotopic.Quotient.mk paperStandardExteriorBridge).trans
          (q.trans (Path.Homotopic.Quotient.mk paperStandardExteriorBridge).symm))
      A.actualCuspExteriorWhiskeredTwiceLoop_class_eq_counterclockwise
    have hinv :
        (Path.Homotopic.Quotient.mk paperStandardExteriorBridge).trans
            ((Path.Homotopic.Quotient.mk
                paperStandardClockwiseExteriorMeridian).symm.trans
              (Path.Homotopic.Quotient.mk paperStandardExteriorBridge).symm) =
          Path.Homotopic.Quotient.mk
            paperStandardClockwiseExteriorMeridianAtCommonBasepoint.symm := by
      unfold paperStandardClockwiseExteriorMeridianAtCommonBasepoint
      simp only [Path.Homotopic.Quotient.mk_symm,
        Path.Homotopic.Quotient.mk_trans]
      let p := Path.Homotopic.Quotient.mk paperStandardExteriorBridge
      let q := Path.Homotopic.Quotient.mk paperStandardClockwiseExteriorMeridian
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
    unfold actualCuspCommonCoordinateLoop
    simpa only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm] using h.trans hinv
  rw [hcusp, Path.Homotopic.Quotient.mk_symm,
    paperPairOfPantsExterior_class_eq_finiteComposite]
  simp only [Path.Homotopic.Quotient.mk_trans]
  change
    (TwicePuncturedComplex.oneMeridianClass *
      TwicePuncturedComplex.zeroMeridianClass)⁻¹ =
    TwicePuncturedComplex.zeroMeridianClass⁻¹ *
      TwicePuncturedComplex.oneMeridianClass⁻¹
  exact mul_inv_rev _ _

end SphereSixComplex.Geometry.PaperAnalyticData

end
