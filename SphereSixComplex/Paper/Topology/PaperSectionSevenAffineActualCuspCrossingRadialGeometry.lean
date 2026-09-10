module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCayleyBoundsProof

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
public theorem affineActualCuspCrossingPoint_re
    (A : PaperAnalyticData) :
    (A.affineActualCuspCrossingPoint.1 : ℂ).re = 1 / 2 :=
  A.affineActualCuspCrossingTime_re_eq_half

/-- The actual cusp crossing lies strictly outside the closed disc of radius two. -/
public theorem affineActualCuspCrossingPoint_norm_gt_two
    (A : PaperAnalyticData) :
    2 < ‖(A.affineActualCuspCrossingPoint.1 : ℂ)‖ :=
  A.cuspAngularCoordinateLoop_norm_gt_two
    A.affineActualCuspCrossingTime

/-- The actual cusp crossing does not lie on the real axis. -/
public theorem affineActualCuspCrossingPoint_im_ne_zero
    (A : PaperAnalyticData) :
    (A.affineActualCuspCrossingPoint.1 : ℂ).im ≠ 0 := by
  intro him
  have hnorm : ‖(A.affineActualCuspCrossingPoint.1 : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_def, Complex.normSq_apply, him,
      A.affineActualCuspCrossingPoint_re]
    norm_num
  linarith [A.affineActualCuspCrossingPoint_norm_gt_two]

/-- The order-three half-plane coordinate is the actual cusp coordinate at the crossing. -/
public theorem affineOrderThreeHalfPlaneCoordinate_crossing
    (A : PaperAnalyticData) :
    ((A.affineOrderThreeHalfPlaneCoordinate
      A.affineActualCuspCrossingPoint).1.1 : ℂ) =
      A.affineActualCuspCrossingPoint.1 := by
  change (A.regularCoordinate
    (A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint)).1 =
        A.affineActualCuspCrossingPoint.1
  exact A.affineNamedStripLift.lift_coordinate _

/-- The order-four half-plane coordinate is the actual cusp coordinate at the crossing. -/
public theorem affineOrderFourHalfPlaneCoordinate_crossing
    (A : PaperAnalyticData) :
    ((A.affineOrderFourHalfPlaneCoordinate
      A.affineActualCuspCrossingPoint).1.1 : ℂ) =
      A.affineActualCuspCrossingPoint.1 := by
  change (A.regularCoordinate
    (A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint)).1 =
        A.affineActualCuspCrossingPoint.1
  exact A.affineNamedStripLift.lift_coordinate _

/-- The order-three normalized endpoint is a positive radial rescaling of the crossing. -/
public theorem affineOrderThreeNormalizedBaseCoordinate_crossing
    (A : PaperAnalyticData) :
    (A.affineOrderThreeNormalizedBaseCoordinate
      A.affineActualCuspCrossingPoint).1 =
      (A.affineOrderThreeMarkedDiscRadius / 2 *
        ‖(A.affineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ : ℝ) •
          (A.affineActualCuspCrossingPoint.1 : ℂ) := by
  change (A.affineOrderThreeMarkedDiscRadius / 2 *
      ‖((A.affineOrderThreeHalfPlaneCoordinate
        A.affineActualCuspCrossingPoint).1.1 : ℂ)‖⁻¹ : ℝ) •
        ((A.affineOrderThreeHalfPlaneCoordinate
          A.affineActualCuspCrossingPoint).1.1 : ℂ) = _
  rw [A.affineOrderThreeHalfPlaneCoordinate_crossing]

/-- The order-four normalized endpoint is a positive radial rescaling about `1`. -/
public theorem affineOrderFourNormalizedBaseCoordinate_crossing
    (A : PaperAnalyticData) :
    (A.affineOrderFourNormalizedBaseCoordinate
      A.affineActualCuspCrossingPoint).1 =
      1 - (A.affineOrderFourMarkedDiscRadius / 2 *
        ‖1 - (A.affineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ : ℝ) •
          (1 - (A.affineActualCuspCrossingPoint.1 : ℂ)) := by
  change 1 - (A.affineOrderFourMarkedDiscRadius / 2 *
      ‖1 - ((A.affineOrderFourHalfPlaneCoordinate
        A.affineActualCuspCrossingPoint).1.1 : ℂ)‖⁻¹ : ℝ) •
        (1 - ((A.affineOrderFourHalfPlaneCoordinate
          A.affineActualCuspCrossingPoint).1.1 : ℂ)) = _
  rw [A.affineOrderFourHalfPlaneCoordinate_crossing]

/-- The order-three radial scaling factor at the crossing is positive. -/
public theorem affineOrderThreeCrossingRadialScalar_pos
    (A : PaperAnalyticData) :
    0 < A.affineOrderThreeMarkedDiscRadius / 2 *
      ‖(A.affineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ := by
  apply mul_pos
  · exact div_pos A.affineOrderThreeMarkedDiscRadius_spec.1 (by norm_num)
  · exact inv_pos.mpr (by
      linarith [A.affineActualCuspCrossingPoint_norm_gt_two])

/-- The displacement of the crossing from the order-four branch value is nonzero. -/
public theorem one_sub_sectionSevenAffineActualCuspCrossingPoint_ne_zero
    (A : PaperAnalyticData) :
    (1 - (A.affineActualCuspCrossingPoint.1 : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.sub_re, Complex.one_re,
    A.affineActualCuspCrossingPoint_re] at hre
  norm_num at hre

/-- The order-four radial scaling factor at the crossing is positive. -/
public theorem affineOrderFourCrossingRadialScalar_pos
    (A : PaperAnalyticData) :
    0 < A.affineOrderFourMarkedDiscRadius / 2 *
      ‖1 - (A.affineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ := by
  apply mul_pos
  · exact div_pos A.affineOrderFourMarkedDiscRadius_spec.1 (by norm_num)
  · exact inv_pos.mpr
      (norm_pos_iff.mpr A.one_sub_sectionSevenAffineActualCuspCrossingPoint_ne_zero)

/-- The imaginary part of the order-three endpoint is scaled by a positive real number. -/
public theorem affineOrderThreeNormalizedBaseCoordinate_crossing_im
    (A : PaperAnalyticData) :
    ((A.affineOrderThreeNormalizedBaseCoordinate
      A.affineActualCuspCrossingPoint).1 : ℂ).im =
      (A.affineOrderThreeMarkedDiscRadius / 2 *
        ‖(A.affineActualCuspCrossingPoint.1 : ℂ)‖⁻¹) *
          (A.affineActualCuspCrossingPoint.1 : ℂ).im := by
  rw [A.affineOrderThreeNormalizedBaseCoordinate_crossing,
    Complex.smul_im]
  rfl

/-- The imaginary part of the order-four endpoint has the same positive radial factor. -/
public theorem affineOrderFourNormalizedBaseCoordinate_crossing_im
    (A : PaperAnalyticData) :
    ((A.affineOrderFourNormalizedBaseCoordinate
      A.affineActualCuspCrossingPoint).1 : ℂ).im =
      (A.affineOrderFourMarkedDiscRadius / 2 *
        ‖1 - (A.affineActualCuspCrossingPoint.1 : ℂ)‖⁻¹) *
          (A.affineActualCuspCrossingPoint.1 : ℂ).im := by
  rw [A.affineOrderFourNormalizedBaseCoordinate_crossing,
    Complex.sub_im, Complex.one_im, Complex.smul_im, Complex.sub_im, Complex.one_im]
  ring

/-- The order-three endpoint has positive real part. -/
public theorem affineOrderThreeNormalizedBaseCoordinate_crossing_re_pos
    (A : PaperAnalyticData) :
    0 < ((A.affineOrderThreeNormalizedBaseCoordinate
      A.affineActualCuspCrossingPoint).1 : ℂ).re := by
  rw [A.affineOrderThreeNormalizedBaseCoordinate_crossing,
    Complex.smul_re, A.affineActualCuspCrossingPoint_re]
  change 0 < (A.affineOrderThreeMarkedDiscRadius / 2 *
    ‖(A.affineActualCuspCrossingPoint.1 : ℂ)‖⁻¹) * (1 / 2)
  exact mul_pos A.affineOrderThreeCrossingRadialScalar_pos (by norm_num)

/-- The order-four endpoint has real part strictly below its branch value `1`. -/
public theorem affineOrderFourNormalizedBaseCoordinate_crossing_re_lt_one
    (A : PaperAnalyticData) :
    ((A.affineOrderFourNormalizedBaseCoordinate
      A.affineActualCuspCrossingPoint).1 : ℂ).re < 1 := by
  rw [A.affineOrderFourNormalizedBaseCoordinate_crossing,
    Complex.sub_re, Complex.one_re, Complex.smul_re, Complex.sub_re, Complex.one_re,
    A.affineActualCuspCrossingPoint_re]
  have h := A.affineOrderFourCrossingRadialScalar_pos
  change 1 - (A.affineOrderFourMarkedDiscRadius / 2 *
    ‖1 - (A.affineActualCuspCrossingPoint.1 : ℂ)‖⁻¹) * (1 - 1 / 2) < 1
  nlinarith

/-- The order-three normalized endpoint is not on the real axis. -/
public theorem affineOrderThreeNormalizedBaseCoordinate_crossing_im_ne_zero
    (A : PaperAnalyticData) :
    ((A.affineOrderThreeNormalizedBaseCoordinate
      A.affineActualCuspCrossingPoint).1 : ℂ).im ≠ 0 := by
  rw [A.affineOrderThreeNormalizedBaseCoordinate_crossing_im]
  exact mul_ne_zero A.affineOrderThreeCrossingRadialScalar_pos.ne'
    A.affineActualCuspCrossingPoint_im_ne_zero

/-- The order-four normalized endpoint is not on the real axis. -/
public theorem affineOrderFourNormalizedBaseCoordinate_crossing_im_ne_zero
    (A : PaperAnalyticData) :
    ((A.affineOrderFourNormalizedBaseCoordinate
      A.affineActualCuspCrossingPoint).1 : ℂ).im ≠ 0 := by
  rw [A.affineOrderFourNormalizedBaseCoordinate_crossing_im]
  exact mul_ne_zero A.affineOrderFourCrossingRadialScalar_pos.ne'
    A.affineActualCuspCrossingPoint_im_ne_zero

end SphereSixComplex.Geometry.PaperAnalyticData

end
