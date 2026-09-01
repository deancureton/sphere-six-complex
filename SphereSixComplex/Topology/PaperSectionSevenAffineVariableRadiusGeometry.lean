module

public import SphereSixComplex.Topology.PaperSectionSevenAffineActualCuspCrossingCayleySeparation

/-!
# Variable-radius marked affine endpoints

The affine overlap discs may be shrunk arbitrarily while preserving their inclusion in the
actual overlaps.  The corresponding pinned radial endpoints approach the two branch values in
the affine quotient coordinate.  Passing from this quotient-coordinate convergence to Cayley
convergence on the named sheet is the remaining sheet-sensitive step.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

/-- The order-three affine overlap disc can be chosen below any prescribed positive radius. -/
public theorem exists_orderThree_discRegion_subset_overlap_lt
    (A : PaperAnalyticData) {b : ℝ} (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r < b ∧ r ≤ 1 / 3 ∧
      A.sectionSevenAffineOrderThreeDiscRegion r ⊆
        A.sectionSevenOrderThreeFillingImage ∩
          A.sectionSevenAffineOrderThreeCentralRegion := by
  obtain ⟨a, ha, ha3, hsub⟩ := A.exists_discRegion_subset_orderThreeOverlap
  let r := min (a / 2) (b / 2)
  have hr : 0 < r := lt_min (half_pos ha) (half_pos hb)
  have hra : r ≤ a := (min_le_left _ _).trans (half_le_self ha.le)
  refine ⟨r, hr, (min_le_right _ _).trans_lt (half_lt_self hb), hra.trans ha3, ?_⟩
  exact (A.discRegion_mono hra).trans hsub

/-- The order-four affine overlap disc can likewise be chosen below any prescribed positive
radius. -/
public theorem exists_orderFour_discRegion_subset_overlap_lt
    (A : PaperAnalyticData) {b : ℝ} (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r < b ∧ r ≤ 1 / 3 ∧
      A.sectionSevenAffineOrderFourDiscRegion r ⊆
        A.sectionSevenOrderFourFillingImage ∩
          A.sectionSevenAffineOrderFourCentralRegion := by
  obtain ⟨a, ha, ha3, hsub⟩ := A.exists_discRegion_subset_orderFourOverlap
  let r := min (a / 2) (b / 2)
  have hr : 0 < r := lt_min (half_pos ha) (half_pos hb)
  have hra : r ≤ a := (min_le_left _ _).trans (half_le_self ha.le)
  refine ⟨r, hr, (min_le_right _ _).trans_lt (half_lt_self hb), hra.trans ha3, ?_⟩
  exact (A.orderFourDiscRegion_mono hra).trans hsub

/-- The order-three radial inverse at a variable affine-disc radius, evaluated on the named
sheet at the pinned crossing. -/
public noncomputable def sectionSevenAffineOrderThreePinnedRadialBaseAtRadius
    (A : PaperAnalyticData) (r : ℝ) (hr : 0 < r) (hr3 : r ≤ 1 / 3) :=
  ((A.orderThreeBaseRadialEquiv (s := r / 2)
      (half_pos hr) (half_lt_self hr) (hr3.trans (by norm_num))).invFun
    (A.sectionSevenAffineOrderThreeHalfPlaneBaseLift
      A.sectionSevenAffineActualCuspCrossingPoint)).1

/-- The order-four radial inverse at a variable affine-disc radius, evaluated on the named
sheet at the pinned crossing. -/
public noncomputable def sectionSevenAffineOrderFourPinnedRadialBaseAtRadius
    (A : PaperAnalyticData) (r : ℝ) (hr : 0 < r) (hr3 : r ≤ 1 / 3) :=
  ((A.orderFourBaseRadialEquiv (s := r / 2)
      (half_pos hr) (half_lt_self hr) (hr3.trans (by norm_num))).invFun
    (A.sectionSevenAffineOrderFourHalfPlaneBaseLift
      A.sectionSevenAffineActualCuspCrossingPoint)).1

/-- The variable order-three endpoint has affine quotient-coordinate norm exactly `r / 2`. -/
public theorem regularCoordinate_orderThreePinnedRadialBaseAtRadius_norm
    (A : PaperAnalyticData) (r : ℝ) (hr : 0 < r) (hr3 : r ≤ 1 / 3) :
    ‖(A.regularCoordinate
      (A.sectionSevenAffineOrderThreePinnedRadialBaseAtRadius r hr hr3)).1‖ = r / 2 := by
  let w := A.sectionSevenAffineOrderThreeHalfPlaneCoordinate
    A.sectionSevenAffineActualCuspCrossingPoint
  rw [sectionSevenAffineOrderThreePinnedRadialBaseAtRadius,
    A.orderThreeBaseRadialEquiv_invFun_regularCoordinate]
  change ‖((r / 2 * ‖(w.1.1 : ℂ)‖⁻¹ : ℝ) • (w.1.1 : ℂ))‖ = r / 2
  have hw : (w.1.1 : ℂ) ≠ 0 := regularCoordinate_ne_zero w.1
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (mul_pos (half_pos hr) (inv_pos.mpr (norm_pos_iff.mpr hw))),
    mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mpr hw).ne', mul_one]

/-- The variable order-four endpoint has affine quotient-coordinate distance `r / 2` from the
order-four branch value. -/
public theorem regularCoordinate_orderFourPinnedRadialBaseAtRadius_sub_one_norm
    (A : PaperAnalyticData) (r : ℝ) (hr : 0 < r) (hr3 : r ≤ 1 / 3) :
    ‖(A.regularCoordinate
      (A.sectionSevenAffineOrderFourPinnedRadialBaseAtRadius r hr hr3)).1 - 1‖ = r / 2 := by
  let w := A.sectionSevenAffineOrderFourHalfPlaneCoordinate
    A.sectionSevenAffineActualCuspCrossingPoint
  rw [sectionSevenAffineOrderFourPinnedRadialBaseAtRadius,
    A.orderFourBaseRadialEquiv_invFun_regularCoordinate]
  change ‖1 - (r / 2 * ‖1 - (w.1.1 : ℂ)‖⁻¹ : ℝ) •
    (1 - (w.1.1 : ℂ)) - 1‖ = r / 2
  rw [show 1 - (r / 2 * ‖1 - (w.1.1 : ℂ)‖⁻¹ : ℝ) •
      (1 - (w.1.1 : ℂ)) - 1 =
        -((r / 2 * ‖1 - (w.1.1 : ℂ)‖⁻¹ : ℝ) •
          (1 - (w.1.1 : ℂ))) by ring,
    norm_neg, norm_smul, Real.norm_eq_abs]
  have hw : (1 - (w.1.1 : ℂ)) ≠ 0 := by
    intro h
    exact regularCoordinate_ne_one w.1 (sub_eq_zero.mp h).symm
  rw [abs_of_pos (mul_pos (half_pos hr) (inv_pos.mpr (norm_pos_iff.mpr hw))),
    mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mpr hw).ne', mul_one]

/-- The overlap radius can be chosen so that the pinned order-three endpoint is arbitrarily
close to the branch value in the affine quotient coordinate. -/
public theorem exists_orderThree_overlap_radius_with_pinned_affine_coordinate_lt
    (A : PaperAnalyticData) {b : ℝ} (hb : 0 < b) :
    ∃ (r : ℝ) (hr : 0 < r) (hr3 : r ≤ 1 / 3),
      A.sectionSevenAffineOrderThreeDiscRegion r ⊆
          A.sectionSevenOrderThreeFillingImage ∩
            A.sectionSevenAffineOrderThreeCentralRegion ∧
        ‖(A.regularCoordinate
          (A.sectionSevenAffineOrderThreePinnedRadialBaseAtRadius r hr hr3)).1‖ < b := by
  obtain ⟨r, hr, hrb, hr3, hsub⟩ := A.exists_orderThree_discRegion_subset_overlap_lt hb
  refine ⟨r, hr, hr3, hsub, ?_⟩
  rw [A.regularCoordinate_orderThreePinnedRadialBaseAtRadius_norm]
  exact (half_lt_self hr).trans hrb

/-- The analogous arbitrarily small affine quotient-coordinate result for order four. -/
public theorem exists_orderFour_overlap_radius_with_pinned_affine_coordinate_lt
    (A : PaperAnalyticData) {b : ℝ} (hb : 0 < b) :
    ∃ (r : ℝ) (hr : 0 < r) (hr3 : r ≤ 1 / 3),
      A.sectionSevenAffineOrderFourDiscRegion r ⊆
          A.sectionSevenOrderFourFillingImage ∩
            A.sectionSevenAffineOrderFourCentralRegion ∧
        ‖(A.regularCoordinate
          (A.sectionSevenAffineOrderFourPinnedRadialBaseAtRadius r hr hr3)).1 - 1‖ < b := by
  obtain ⟨r, hr, hrb, hr3, hsub⟩ := A.exists_orderFour_discRegion_subset_overlap_lt hb
  refine ⟨r, hr, hr3, hsub, ?_⟩
  rw [A.regularCoordinate_orderFourPinnedRadialBaseAtRadius_sub_one_norm]
  exact (half_lt_self hr).trans hrb

end SphereSixComplex.Geometry.PaperAnalyticData

end
