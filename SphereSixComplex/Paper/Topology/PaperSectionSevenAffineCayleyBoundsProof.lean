module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandBasepointReduction

/-!
# Coordinate calculation for the marked affine radial lifts

The radial normalization puts the two marked lifts on the circles of half the chosen affine
disc radii.  These equalities isolate the coordinate-level content available before identifying
the named covering sheets with the selected Cayley collars.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

/-- The order-three normalized coordinate has exactly half the chosen affine-disc radius. -/
public theorem affineOrderThreeNormalizedBaseCoordinate_norm
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    ‖(A.affineOrderThreeNormalizedBaseCoordinate z).1‖ =
      A.affineOrderThreeMarkedDiscRadius / 2 := by
  let w := A.affineOrderThreeHalfPlaneCoordinate z
  change ‖((A.affineOrderThreeMarkedDiscRadius / 2 *
      ‖(w.1.1 : ℂ)‖⁻¹ : ℝ) • (w.1.1 : ℂ))‖ =
    A.affineOrderThreeMarkedDiscRadius / 2
  have hw : (w.1.1 : ℂ) ≠ 0 := regularCoordinate_ne_zero w.1
  rw [norm_smul, Real.norm_eq_abs]
  have hr : 0 < A.affineOrderThreeMarkedDiscRadius / 2 :=
    div_pos A.affineOrderThreeMarkedDiscRadius_spec.1 (by norm_num)
  rw [abs_of_pos (mul_pos hr (inv_pos.mpr (norm_pos_iff.mpr hw))),
    mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mpr hw).ne', mul_one]

/-- The order-four normalized coordinate has exactly half the chosen affine-disc radius about
the order-four branch value. -/
public theorem affineOrderFourNormalizedBaseCoordinate_sub_one_norm
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    ‖(A.affineOrderFourNormalizedBaseCoordinate z).1 - 1‖ =
      A.affineOrderFourMarkedDiscRadius / 2 := by
  let w := A.affineOrderFourHalfPlaneCoordinate z
  let q : ℂ := w.1.1
  let a : ℝ := A.affineOrderFourMarkedDiscRadius / 2 * ‖1 - q‖⁻¹
  change ‖(1 - a • (1 - q)) - 1‖ =
    A.affineOrderFourMarkedDiscRadius / 2
  rw [show (1 - a • (1 - q) : ℂ) - 1 = -(a • (1 - q)) by ring,
    norm_neg, norm_smul, Real.norm_eq_abs]
  have hw : (1 - q) ≠ 0 := by
    intro h
    exact regularCoordinate_ne_one w.1 (sub_eq_zero.mp h).symm
  have hr : 0 < A.affineOrderFourMarkedDiscRadius / 2 :=
    div_pos A.affineOrderFourMarkedDiscRadius_spec.1 (by norm_num)
  change |A.affineOrderFourMarkedDiscRadius / 2 * ‖1 - q‖⁻¹| *
    ‖1 - q‖ = A.affineOrderFourMarkedDiscRadius / 2
  rw [abs_of_pos (mul_pos hr (inv_pos.mpr (norm_pos_iff.mpr hw))),
    mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mpr hw).ne', mul_one]

/-- The lifted order-three radial endpoint has the same exact quotient-coordinate radius. -/
public theorem regularCoordinate_sectionSevenAffineOrderThreeRadialBaseLift_norm
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    ‖(A.regularCoordinate (A.affineOrderThreeRadialBaseLift z)).1‖ =
      A.affineOrderThreeMarkedDiscRadius / 2 := by
  rw [A.regularCoordinate_sectionSevenAffineOrderThreeRadialBaseLift]
  exact A.affineOrderThreeNormalizedBaseCoordinate_norm z

/-- The lifted order-four radial endpoint has the same exact quotient-coordinate radius about
the order-four branch value. -/
public theorem regularCoordinate_sectionSevenAffineOrderFourRadialBaseLift_sub_one_norm
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    ‖(A.regularCoordinate (A.affineOrderFourRadialBaseLift z)).1 - 1‖ =
      A.affineOrderFourMarkedDiscRadius / 2 := by
  rw [A.regularCoordinate_sectionSevenAffineOrderFourRadialBaseLift]
  exact A.affineOrderFourNormalizedBaseCoordinate_sub_one_norm z

end SphereSixComplex.Geometry.PaperAnalyticData

end
