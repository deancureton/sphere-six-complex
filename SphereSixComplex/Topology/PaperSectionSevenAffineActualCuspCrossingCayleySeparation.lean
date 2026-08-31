module

public import SphereSixComplex.Topology.PaperSectionSevenAffineActualCuspCrossingRadialGeometry

/-!
# Separation at the pinned actual-cusp crossing

The two normalized quotient coordinates lie strictly away from their real branch rays and on the
same side of the real axis.  Their chosen regular lifts have nonzero Cayley coordinates in the
open unit disc.  These facts do not identify a regular deck sheet or compare either Cayley norm
with the smaller radii selected by the collar-separation construction.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open Complex
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates

/-- The two normalized quotient endpoints lie on the same strict side of the real axis. -/
public theorem sectionSevenAffineNormalizedCrossing_im_mul_pos
    (A : PaperAnalyticData) :
    0 < ((A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
      A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im *
      ((A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im := by
  rw [A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing_im,
    A.sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing_im]
  let a₃ := A.sectionSevenAffineOrderThreeMarkedDiscRadius / 2 *
    ‖(A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹
  let a₄ := A.sectionSevenAffineOrderFourMarkedDiscRadius / 2 *
    ‖1 - (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹
  let y := (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ).im
  change 0 < (a₃ * y) * (a₄ * y)
  rw [show (a₃ * y) * (a₄ * y) = (a₃ * a₄) * y ^ 2 by ring]
  exact mul_pos
    (mul_pos A.sectionSevenAffineOrderThreeCrossingRadialScalar_pos
      A.sectionSevenAffineOrderFourCrossingRadialScalar_pos)
    (sq_pos_of_ne_zero A.sectionSevenAffineActualCuspCrossingPoint_im_ne_zero)

/-- In particular, the normalized endpoints are either both strictly above or both strictly
below the real axis. -/
public theorem sectionSevenAffineNormalizedCrossing_same_open_halfPlane
    (A : PaperAnalyticData) :
    (0 < ((A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im ∧
      0 < ((A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im) ∨
    (((A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im < 0 ∧
      ((A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im < 0) := by
  exact mul_pos_iff.mp A.sectionSevenAffineNormalizedCrossing_im_mul_pos

/-- The pinned normalized endpoints are nonreal and point into their respective affine
half-planes. -/
public theorem sectionSevenAffineNormalizedCrossing_strict_separation
    (A : PaperAnalyticData) :
    0 < ((A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).re ∧
      ((A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).re < 1 ∧
      0 < ((A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im *
        ((A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
          A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ).im :=
  ⟨A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing_re_pos,
    A.sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing_re_lt_one,
    A.sectionSevenAffineNormalizedCrossing_im_mul_pos⟩

/-- Reflection across the vertical line through the two affine branch values sends the pinned
crossing to its complex conjugate. -/
public theorem one_sub_sectionSevenAffineActualCuspCrossingPoint_eq_conj
    (A : PaperAnalyticData) :
    1 - (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ) =
      star (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    rw [A.sectionSevenAffineActualCuspCrossingPoint_re]
    norm_num
  · simp only [Complex.sub_im, Complex.one_im, Complex.star_def, Complex.conj_im]
    ring

/-- After compensating for their positive radial factors, the two normalized endpoints are
complex-conjugate rays about the affine branch values `0` and `1`. -/
public theorem sectionSevenAffineNormalizedCrossing_conjugate_rays
    (A : PaperAnalyticData) :
    (A.sectionSevenAffineOrderFourMarkedDiscRadius / 2 *
      ‖1 - (A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ : ℝ) •
      star ((A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ) =
    (A.sectionSevenAffineOrderThreeMarkedDiscRadius / 2 *
        ‖(A.sectionSevenAffineActualCuspCrossingPoint.1 : ℂ)‖⁻¹ : ℝ) •
      (1 - (A.sectionSevenAffineOrderFourNormalizedBaseCoordinate
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ) := by
  rw [A.sectionSevenAffineOrderThreeNormalizedBaseCoordinate_crossing,
    A.sectionSevenAffineOrderFourNormalizedBaseCoordinate_crossing]
  apply Complex.ext
  · simp only [Complex.smul_re, Complex.star_def, Complex.conj_re,
      Complex.sub_re, Complex.one_re]
    rw [A.sectionSevenAffineActualCuspCrossingPoint_re]
    ring
  · simp only [Complex.smul_im, Complex.star_def, Complex.conj_im,
      Complex.sub_im, Complex.one_im]
    ring

/-- The order-three pinned regular lift has nonzero Cayley coordinate. -/
public theorem sectionSevenAffineOrderThreePinnedCayley_norm_pos
    (A : PaperAnalyticData) :
    0 < ‖(orderThreeCayleyHomeomorph
      (A.sectionSevenAffineOrderThreeRadialBaseLift
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ := by
  let x := A.sectionSevenAffineMarkedBandPointOfStrip
    A.sectionSevenAffineActualCuspCrossingPoint
  have h := A.orderThreeFamilyRadius_namedCollarTotalPoint_pos x
  rw [A.orderThreeFamilyRadius_namedCollarTotalPoint x] at h
  simpa [x] using h

/-- The order-four pinned regular lift has nonzero Cayley coordinate. -/
public theorem sectionSevenAffineOrderFourPinnedCayley_norm_pos
    (A : PaperAnalyticData) :
    0 < ‖(orderFourCayleyHomeomorph
      (A.sectionSevenAffineOrderFourRadialBaseLift
        A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ := by
  let x := A.sectionSevenAffineMarkedBandPointOfStrip
    A.sectionSevenAffineActualCuspCrossingPoint
  have h := A.orderFourFamilyRadius_namedCollarTotalPoint_pos x
  rw [A.orderFourFamilyRadius_namedCollarTotalPoint x] at h
  simpa [x] using h

/-- Both pinned Cayley coordinates lie strictly in the punctured open unit disc. -/
public theorem sectionSevenAffinePinnedCayley_unitDisc_separation
    (A : PaperAnalyticData) :
    (0 < ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ ∧
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ < 1) ∧
    (0 < ‖(orderFourCayleyHomeomorph
        (A.sectionSevenAffineOrderFourRadialBaseLift
          A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ ∧
      ‖(orderFourCayleyHomeomorph
        (A.sectionSevenAffineOrderFourRadialBaseLift
          A.sectionSevenAffineActualCuspCrossingPoint).1 : ℂ)‖ < 1) := by
  exact ⟨⟨A.sectionSevenAffineOrderThreePinnedCayley_norm_pos,
      norm_orderThreeCayley_lt_one _⟩,
    ⟨A.sectionSevenAffineOrderFourPinnedCayley_norm_pos,
      norm_orderFourCayley_lt_one _⟩⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
