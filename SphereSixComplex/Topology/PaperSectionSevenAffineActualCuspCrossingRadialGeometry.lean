module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCayleyBoundsProof

/-!
# Radial geometry at the actual cusp crossing

The distinguished crossing has real coordinate `1 / 2` and lies outside the closed disc of
radius two.  The marked radial endpoints are positive radial rescalings of that crossing about
the order-three and order-four branch values.  In particular, neither endpoint lies on the real
axis.  These formulas isolate the geometric input still needed to identify the named sheets.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

/-- The actual cusp crossing has real coordinate `1 / 2`. -/
public theorem sectionSevenAffineActualCuspCrossingPoint_re
    (A : PaperAnalyticData) :
    (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ).re = 1 / 2 :=
  A.sectionSevenAffineActualCuspCrossingTime_re_eq_half

/-- The actual cusp crossing lies strictly outside the closed disc of radius two. -/
public theorem sectionSevenAffineActualCuspCrossingPoint_norm_gt_two
    (A : PaperAnalyticData) :
    2 < ‖(A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖ :=
  A.actualCuspAngularCoordinateLoop_norm_gt_two
    A.sectionSevenAffineActualCuspCrossingTime

/-- The actual cusp crossing does not lie on the real axis. -/
public theorem sectionSevenAffineActualCuspCrossingPoint_im_ne_zero
    (A : PaperAnalyticData) :
    (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ).im ≠ 0 := by
  intro him
  have hnorm : ‖(A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_def, Complex.normSq_apply, him,
      A.sectionSevenAffineActualCuspCrossingPoint_re]
    norm_num
  linarith [A.sectionSevenAffineActualCuspCrossingPoint_norm_gt_two]

/-- The order-three half-plane coordinate is the actual cusp coordinate at the crossing. -/
public theorem sectionSevenAffineOrderThreeHalfPlaneCoordinate_crossing
    (A : PaperAnalyticData) :
    ((A.sectionSevenAffineOrderThreeHalfPlaneCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1.1 : ℂ) =
      A.sectionSevenAffineActualCuspCrossingPoint.1 := by
  change (A.regularCoordinate
    (A.sectionSevenAffineNamedStripLift.lift
      A.sectionSevenAffineActualCuspCrossingPoint)).1 =
        A.sectionSevenAffineActualCuspCrossingPoint.1
  exact A.sectionSevenAffineNamedStripLift.lift_coordinate _

/-- The order-four half-plane coordinate is the actual cusp coordinate at the crossing. -/
public theorem sectionSevenAffineOrderFourHalfPlaneCoordinate_crossing
    (A : PaperAnalyticData) :
    ((A.sectionSevenAffineOrderFourHalfPlaneCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1.1 : ℂ) =
      A.sectionSevenAffineActualCuspCrossingPoint.1 := by
  change (A.regularCoordinate
    (A.sectionSevenAffineNamedStripLift.lift
      A.sectionSevenAffineActualCuspCrossingPoint)).1 =
        A.sectionSevenAffineActualCuspCrossingPoint.1
  exact A.sectionSevenAffineNamedStripLift.lift_coordinate _

/-- The order-three normalized endpoint is a positive radial rescaling of the crossing. -/
public theorem sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing
    (A : PaperAnalyticData) :
    (A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1 =
      (A.sectionSevenAffineOrderThreeMarkedDiscRadius / 2 *
        ‖(A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ : ℝ) •
          (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ) := by
  change (A.sectionSevenAffineOrderThreeMarkedDiscRadius / 2 *
      ‖((A.sectionSevenAffineOrderThreeHalfPlaneCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1.1 : ℂ)‖⁻¹ : ℝ) •
        ((A.sectionSevenAffineOrderThreeHalfPlaneCoordinate
          A.sectionSevenAffineActualCuspCrossingPoint).1.1 : ℂ) = _
  rw [A.sectionSevenAffineOrderThreeHalfPlaneCoordinate_crossing]

/-- The order-four normalized endpoint is a positive radial rescaling about `1`. -/
public theorem sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing
    (A : PaperAnalyticData) :
    (A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1 =
      1 - (A.sectionSevenAffineOrderFourMarkedDiscRadius / 2 *
        ‖1 - (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ : ℝ) •
          (1 - (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)) := by
  change 1 - (A.sectionSevenAffineOrderFourMarkedDiscRadius / 2 *
      ‖1 - ((A.sectionSevenAffineOrderFourHalfPlaneCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1.1 : ℂ)‖⁻¹ : ℝ) •
        (1 - ((A.sectionSevenAffineOrderFourHalfPlaneCoordinate
          A.sectionSevenAffineActualCuspCrossingPoint).1.1 : ℂ)) = _
  rw [A.sectionSevenAffineOrderFourHalfPlaneCoordinate_crossing]

/-- The order-three radial scaling factor at the crossing is positive. -/
public theorem sectionSevenAffineOrderThreeCrossingRadialScalar_pos
    (A : PaperAnalyticData) :
    0 < A.sectionSevenAffineOrderThreeMarkedDiscRadius / 2 *
      ‖(A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ := by
  apply mul_pos
  · exact div_pos A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1 (by norm_num)
  · exact inv_pos.mpr (by
      linarith [A.sectionSevenAffineActualCuspCrossingPoint_norm_gt_two])

/-- The displacement of the crossing from the order-four branch value is nonzero. -/
public theorem one_sub_sectionSevenAffineActualCuspCrossingPoint_ne_zero
    (A : PaperAnalyticData) :
    (1 - (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.sub_re, Complex.one_re,
    A.sectionSevenAffineActualCuspCrossingPoint_re] at hre
  norm_num at hre

/-- The order-four radial scaling factor at the crossing is positive. -/
public theorem sectionSevenAffineOrderFourCrossingRadialScalar_pos
    (A : PaperAnalyticData) :
    0 < A.sectionSevenAffineOrderFourMarkedDiscRadius / 2 *
      ‖1 - (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ := by
  apply mul_pos
  · exact div_pos A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1 (by norm_num)
  · exact inv_pos.mpr
      (norm_pos_iff.mpr A.one_sub_sectionSevenAffineActualCuspCrossingPoint_ne_zero)

/-- The imaginary part of the order-three endpoint is scaled by a positive real number. -/
public theorem sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing_im
    (A : PaperAnalyticData) :
    ((A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im =
      (A.sectionSevenAffineOrderThreeMarkedDiscRadius / 2 *
        ‖(A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹) *
          (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ).im := by
  rw [A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing,
    Complex.smul_im]
  rfl

/-- The imaginary part of the order-four endpoint has the same positive radial factor. -/
public theorem sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing_im
    (A : PaperAnalyticData) :
    ((A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im =
      (A.sectionSevenAffineOrderFourMarkedDiscRadius / 2 *
        ‖1 - (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹) *
          (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ).im := by
  rw [A.sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing,
    Complex.sub_im, Complex.one_im, Complex.smul_im, Complex.sub_im, Complex.one_im]
  ring

/-- The order-three endpoint has positive real part. -/
public theorem sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing_re_pos
    (A : PaperAnalyticData) :
    0 < ((A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).re := by
  rw [A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing,
    Complex.smul_re, A.sectionSevenAffineActualCuspCrossingPoint_re]
  change 0 < (A.sectionSevenAffineOrderThreeMarkedDiscRadius / 2 *
    ‖(A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹) * (1 / 2)
  exact mul_pos A.sectionSevenAffineOrderThreeCrossingRadialScalar_pos (by norm_num)

/-- The order-four endpoint has real part strictly below its branch value `1`. -/
public theorem sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing_re_lt_one
    (A : PaperAnalyticData) :
    ((A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).re < 1 := by
  rw [A.sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing,
    Complex.sub_re, Complex.one_re, Complex.smul_re, Complex.sub_re, Complex.one_re,
    A.sectionSevenAffineActualCuspCrossingPoint_re]
  have h := A.sectionSevenAffineOrderFourCrossingRadialScalar_pos
  change 1 - (A.sectionSevenAffineOrderFourMarkedDiscRadius / 2 *
    ‖1 - (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹) * (1 - 1 / 2) < 1
  nlinarith

/-- The order-three normalized endpoint is not on the real axis. -/
public theorem sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing_im_ne_zero
    (A : PaperAnalyticData) :
    ((A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im ≠ 0 := by
  rw [A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing_im]
  exact mul_ne_zero A.sectionSevenAffineOrderThreeCrossingRadialScalar_pos.ne'
    A.sectionSevenAffineActualCuspCrossingPoint_im_ne_zero

/-- The order-four normalized endpoint is not on the real axis. -/
public theorem sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing_im_ne_zero
    (A : PaperAnalyticData) :
    ((A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im ≠ 0 := by
  rw [A.sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing_im]
  exact mul_ne_zero A.sectionSevenAffineOrderFourCrossingRadialScalar_pos.ne'
    A.sectionSevenAffineActualCuspCrossingPoint_im_ne_zero

end SphereSixComplex.Geometry.PaperAnalyticData

end
