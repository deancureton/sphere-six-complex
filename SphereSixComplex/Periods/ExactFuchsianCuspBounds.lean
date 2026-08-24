module

public import SphereSixComplex.Periods.FuchsianModularParameterExistence
public import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
import all SphereSixComplex.Periods.Functions

/-!
# Bounds for an exact Fuchsian quotient coordinate at the distinguished cusp

The reduced-word arithmetic shows that the order-three elliptic point has maximal imaginary
height in its orbit.  Consequently the zero orbit of an exact quotient coordinate is disjoint
from the standard cusp region.  The exact cusp factorization then makes the reciprocal coordinate
tend to zero at infinity; translation-centering and compactness give a uniform bound on the whole
cusp region.
-/

noncomputable section

namespace SphereSixComplex.Periods

open Set Metric Filter
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
open SphereSixComplex.TriangleGroup.FuchsianArithmetic
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianTessellation

private theorem deltaNormalForm_indexedToDelta_prod
    {i j : Bool} (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    deltaNormalForm (indexedToDelta w.prod) = w.toWord := by
  apply (Monoid.CoprodI.Word.equiv (M := DeltaFactor)).symm.injective
  change (deltaNormalForm (indexedToDelta w.prod)).prod = w.toWord.prod
  rw [deltaNormalForm_prod]
  change (deltaToIndexed.comp indexedToDelta) w.prod = w.prod
  rw [DFunLike.congr_fun deltaToIndexed_comp_indexedToDelta]
  rfl

private theorem one_le_abs_positiveEmbedding_of_coeffNonnegative
    {x : QuadraticInteger} (hx : CoeffNonnegative x)
    (hne : positiveEmbedding x ≠ 0) :
    1 ≤ |positiveEmbedding x| := by
  change 0 ≤ x.re ∧ 0 ≤ x.im at hx
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hre_nonneg : (0 : ℝ) ≤ (x.re : ℝ) := by exact_mod_cast hx.1
  have him_nonneg : (0 : ℝ) ≤ (x.im : ℝ) := by exact_mod_cast hx.2
  rw [positiveEmbedding_apply, abs_of_nonneg
    (add_nonneg hre_nonneg (mul_nonneg him_nonneg (Real.sqrt_nonneg 2)))]
  by_cases hre : x.re = 0
  · have him : x.im ≠ 0 := by
      intro him
      apply hne
      simp [positiveEmbedding_apply, hre, him]
    have him_one : (1 : ℤ) ≤ x.im := by omega
    have him_one_real : (1 : ℝ) ≤ (x.im : ℝ) := by exact_mod_cast him_one
    have hmul : (1 : ℝ) ≤ (x.im : ℝ) * Real.sqrt 2 := by
      nlinarith [mul_le_mul him_one_real hsqrt (by norm_num : (0 : ℝ) ≤ 1) him_nonneg]
    simpa [hre] using hmul
  · have hre_one : (1 : ℤ) ≤ x.re := by omega
    have hre_one_real : (1 : ℝ) ≤ (x.re : ℝ) := by exact_mod_cast hre_one
    exact hre_one_real.trans (le_add_of_nonneg_right
      (mul_nonneg him_nonneg (Real.sqrt_nonneg 2)))

private theorem one_le_abs_positiveEmbedding_of_coeffNonpositive
    {x : QuadraticInteger} (hx : CoeffNonpositive x)
    (hne : positiveEmbedding x ≠ 0) :
    1 ≤ |positiveEmbedding x| := by
  have hneg : CoeffNonnegative (-x) := by
    exact ⟨by simpa using neg_nonneg.mpr hx.1, by simpa using neg_nonneg.mpr hx.2⟩
  have hneneg : positiveEmbedding (-x) ≠ 0 := by
    rw [map_neg]
    exact neg_ne_zero.mpr hne
  have h := one_le_abs_positiveEmbedding_of_coeffNonnegative hneg hneneg
  rw [map_neg, abs_neg] at h
  exact h

private theorem one_le_normSq_at_one_of_sameQuadrant
    {c d : QuadraticInteger} (hcd : SameQuadrantRow c d)
    (hpos : 0 < Complex.normSq
      (positiveEmbedding c * (fuchsianOneFixedPoint : ℂ) + positiveEmbedding d)) :
    1 ≤ Complex.normSq
      (positiveEmbedding c * (fuchsianOneFixedPoint : ℂ) + positiveEmbedding d) := by
  let cr := positiveEmbedding c
  let dr := positiveEmbedding d
  have hformula : Complex.normSq
      (positiveEmbedding c * (fuchsianOneFixedPoint : ℂ) + positiveEmbedding d) =
        cr ^ 2 + cr * dr + dr ^ 2 := by
    norm_num [cr, dr, fuchsianOneFixedPoint, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    ring_nf
    rw [hsqrt]
    ring
  rw [hformula] at hpos ⊢
  rcases hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · have hcr : 0 ≤ cr := by
      exact add_nonneg (by exact_mod_cast hc.1) (mul_nonneg (by exact_mod_cast hc.2)
        (Real.sqrt_nonneg 2))
    have hdr : 0 ≤ dr := by
      exact add_nonneg (by exact_mod_cast hd.1) (mul_nonneg (by exact_mod_cast hd.2)
        (Real.sqrt_nonneg 2))
    by_cases hcr0 : cr = 0
    · have hdr0 : dr ≠ 0 := by
        intro hdr0
        rw [hcr0, hdr0] at hpos
        norm_num at hpos
      have hone := one_le_abs_positiveEmbedding_of_coeffNonnegative hd hdr0
      rw [abs_of_nonneg hdr] at hone
      nlinarith
    · have hone := one_le_abs_positiveEmbedding_of_coeffNonnegative hc hcr0
      rw [abs_of_nonneg hcr] at hone
      nlinarith
  · have hcr : cr ≤ 0 := by
      exact add_nonpos (by exact_mod_cast hc.1) (mul_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast hc.2) (Real.sqrt_nonneg 2))
    have hdr : dr ≤ 0 := by
      exact add_nonpos (by exact_mod_cast hd.1) (mul_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast hd.2) (Real.sqrt_nonneg 2))
    by_cases hcr0 : cr = 0
    · have hdr0 : dr ≠ 0 := by
        intro hdr0
        rw [hcr0, hdr0] at hpos
        norm_num at hpos
      have hone := one_le_abs_positiveEmbedding_of_coeffNonpositive hd hdr0
      rw [abs_of_nonpos hdr] at hone
      nlinarith
    · have hone := one_le_abs_positiveEmbedding_of_coeffNonpositive hc hcr0
      rw [abs_of_nonpos hcr] at hone
      nlinarith

private theorem one_le_sq_sub_sqrtTwo_mul_add_sq_of_opposite_signs
    {c d : ℝ} (hopp : (0 ≤ c ∧ d ≤ 0) ∨ (c ≤ 0 ∧ 0 ≤ d))
    (hc : 1 ≤ |c| ∨ c = 0) (hd : 1 ≤ |d| ∨ d = 0)
    (hpos : 0 < c ^ 2 - Real.sqrt 2 * c * d + d ^ 2) :
    1 ≤ c ^ 2 - Real.sqrt 2 * c * d + d ^ 2 := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rcases hopp with ⟨hc0, hd0⟩ | ⟨hc0, hd0⟩
  · have hcross : Real.sqrt 2 * c * d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hsqrt hc0) hd0
    rcases hc with hcabs | rfl
    · rw [abs_of_nonneg hc0] at hcabs
      nlinarith [sq_nonneg d]
    · rcases hd with hdabs | rfl
      · rw [abs_of_nonpos hd0] at hdabs
        nlinarith
      · norm_num at hpos
  · have hcross : Real.sqrt 2 * c * d ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hsqrt hc0) hd0
    rcases hc with hcabs | rfl
    · rw [abs_of_nonpos hc0] at hcabs
      nlinarith [sq_nonneg d]
    · rcases hd with hdabs | rfl
      · rw [abs_of_nonneg hd0] at hdabs
        nlinarith
      · norm_num at hpos

private theorem one_le_normSq_at_two_of_oppositeQuadrant
    {c d : QuadraticInteger} (hcd : OppositeQuadrantRow c d)
    (hpos : 0 < Complex.normSq
      (positiveEmbedding c * (fuchsianTwoFixedPoint : ℂ) + positiveEmbedding d)) :
    1 ≤ Complex.normSq
      (positiveEmbedding c * (fuchsianTwoFixedPoint : ℂ) + positiveEmbedding d) := by
  let cr := positiveEmbedding c
  let dr := positiveEmbedding d
  have hgeneric (a b : ℝ) : Complex.normSq
      ((a : ℂ) * (fuchsianTwoFixedPoint : ℂ) + (b : ℂ)) =
        a ^ 2 - Real.sqrt 2 * a * b + b ^ 2 := by
    norm_num [fuchsianTwoFixedPoint, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    ring_nf
    rw [hsqrt]
    ring
  have hformula : Complex.normSq
      (positiveEmbedding c * (fuchsianTwoFixedPoint : ℂ) + positiveEmbedding d) =
        cr ^ 2 - Real.sqrt 2 * cr * dr + dr ^ 2 := by
    exact hgeneric (positiveEmbedding c) (positiveEmbedding d)
  rw [hformula] at hpos ⊢
  have hcr : 1 ≤ |cr| ∨ cr = 0 := by
    by_cases hc0 : cr = 0
    · exact Or.inr hc0
    rcases hcd with ⟨hc, _⟩ | ⟨hc, _⟩
    · exact Or.inl (one_le_abs_positiveEmbedding_of_coeffNonnegative hc hc0)
    · exact Or.inl (one_le_abs_positiveEmbedding_of_coeffNonpositive hc hc0)
  have hdr : 1 ≤ |dr| ∨ dr = 0 := by
    by_cases hd0 : dr = 0
    · exact Or.inr hd0
    rcases hcd with ⟨_, hd⟩ | ⟨_, hd⟩
    · exact Or.inl (one_le_abs_positiveEmbedding_of_coeffNonpositive hd hd0)
    · exact Or.inl (one_le_abs_positiveEmbedding_of_coeffNonnegative hd hd0)
  have hoppsign : (0 ≤ cr ∧ dr ≤ 0) ∨ (cr ≤ 0 ∧ 0 ≤ dr) := by
    rcases hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · left
      exact ⟨add_nonneg (by exact_mod_cast hc.1)
          (mul_nonneg (by exact_mod_cast hc.2) (Real.sqrt_nonneg 2)),
        add_nonpos (by exact_mod_cast hd.1)
          (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hd.2)
            (Real.sqrt_nonneg 2))⟩
    · right
      exact ⟨add_nonpos (by exact_mod_cast hc.1)
          (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hc.2)
            (Real.sqrt_nonneg 2)),
        add_nonneg (by exact_mod_cast hd.1)
          (mul_nonneg (by exact_mod_cast hd.2) (Real.sqrt_nonneg 2))⟩
  exact one_le_sq_sub_sqrtTwo_mul_add_sq_of_opposite_signs hoppsign hcr hdr hpos

private theorem neWord_ends_true_height_le {i : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i true) :
    (fuchsianSourceAction (indexedToDelta w.prod) • fuchsianOneFixedPoint).im ≤
      fuchsianOneFixedPoint.im := by
  let g : Delta := indexedToDelta w.prod
  have hnormal : deltaNormalForm g = w.toWord :=
    deltaNormalForm_indexedToDelta_prod w
  have hrow : SameQuadrantRow (deltaBottomRow g).1 (deltaBottomRow g).2 := by
    change SameQuadrantRow
      (wordMatrix (deltaNormalForm g) 1 0) (wordMatrix (deltaNormalForm g) 1 1)
    rw [hnormal, ← neWordMatrix_eq_wordMatrix]
    have hrows := neWordMatrix_rowsForFactor w
    change MatrixRowsSameQuadrant (neWordMatrix w) at hrows
    exact hrows 1
  have hdenpos : 0 < Complex.normSq
      (positiveEmbedding (deltaBottomRow g).1 * (fuchsianOneFixedPoint : ℂ) +
        positiveEmbedding (deltaBottomRow g).2) := by
    simpa [bottomRowDenominatorNormSq] using
      bottomRowDenominatorNormSq_deltaBottomRow_pos g fuchsianOneFixedPoint
  have hden := one_le_normSq_at_one_of_sameQuadrant hrow hdenpos
  rw [show indexedToDelta w.prod = g by rfl,
    fuchsianSourceAction_im_eq_div_wordBottomNormSq]
  exact (div_le_iff₀ hdenpos).2 (by
    nlinarith [fuchsianOneFixedPoint.im_pos])

private theorem neWord_ends_false_height_le {i : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i false) :
    (fuchsianSourceAction (indexedToDelta w.prod) • fuchsianTwoFixedPoint).im ≤
      fuchsianTwoFixedPoint.im := by
  let g : Delta := indexedToDelta w.prod
  have hnormal : deltaNormalForm g = w.toWord :=
    deltaNormalForm_indexedToDelta_prod w
  have hrow : OppositeQuadrantRow (deltaBottomRow g).1 (deltaBottomRow g).2 := by
    change OppositeQuadrantRow
      (wordMatrix (deltaNormalForm g) 1 0) (wordMatrix (deltaNormalForm g) 1 1)
    rw [hnormal, ← neWordMatrix_eq_wordMatrix]
    have hrows := neWordMatrix_rowsForFactor w
    change MatrixRowsOppositeQuadrant (neWordMatrix w) at hrows
    exact hrows 1
  have hdenpos : 0 < Complex.normSq
      (positiveEmbedding (deltaBottomRow g).1 * (fuchsianTwoFixedPoint : ℂ) +
        positiveEmbedding (deltaBottomRow g).2) := by
    simpa [bottomRowDenominatorNormSq] using
      bottomRowDenominatorNormSq_deltaBottomRow_pos g fuchsianTwoFixedPoint
  have hden := one_le_normSq_at_two_of_oppositeQuadrant hrow hdenpos
  rw [show indexedToDelta w.prod = g by rfl,
    fuchsianSourceAction_im_eq_div_wordBottomNormSq]
  exact (div_le_iff₀ hdenpos).2 (by
    nlinarith [fuchsianTwoFixedPoint.im_pos])

private theorem indexedToDelta_neWord_eq_of_normalForm
    {i j : Bool} {g : Delta} {w : Monoid.CoprodI.NeWord DeltaFactor i j}
    (hw : w.toWord = deltaNormalForm g) :
    indexedToDelta w.prod = g := by
  rw [← indexedToDelta_deltaNormalForm_prod g, ← hw]
  rfl

private theorem fuchsianOneFixedPoint_orbitHeightMaximal :
    IsOrbitHeightMaximal fuchsianOneFixedPoint := by
  intro g
  by_cases hgempty : deltaNormalForm g = Monoid.CoprodI.Word.empty
  · have hg : g = 1 := by
      calc
        g = indexedToDelta (deltaNormalForm g).prod :=
          (indexedToDelta_deltaNormalForm_prod g).symm
        _ = 1 := by rw [hgempty]; simp
    simp [hg]
  · obtain ⟨i, j, w, hw⟩ := Monoid.CoprodI.NeWord.of_word (deltaNormalForm g) hgempty
    have hg : indexedToDelta w.prod = g := indexedToDelta_neWord_eq_of_normalForm hw
    cases j with
    | true =>
        rw [← hg]
        exact neWord_ends_true_height_le w
    | false =>
        rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
          hsingle | ⟨k, p, hk, hprod, hlen⟩
        · have hlast : w.last ≠ 1 := BinaryIndexedCoprod.NeWord.last_ne_one w
          have hfix0 : fuchsianSourceAction
              (Monoid.Coprod.inl (show CyclicThree from w.last)) •
              fuchsianOneFixedPoint = fuchsianOneFixedPoint :=
            (FreeProductTorsion.fuchsianSourceAction_inl_fixed_iff
              (show CyclicThree from w.last) hlast fuchsianOneFixedPoint).2 rfl
          have hfix : fuchsianSourceAction
              (indexedToDelta (Monoid.CoprodI.of w.last)) •
              fuchsianOneFixedPoint = fuchsianOneFixedPoint := by
            rw [indexedToDelta_of_false]
            exact hfix0
          rw [← hg, hsingle.2.1, hfix]
        · have hktrue : k = true := by cases k <;> simp_all
          subst k
          have hlast : w.last ≠ 1 := BinaryIndexedCoprod.NeWord.last_ne_one w
          have hfix0 : fuchsianSourceAction
              (Monoid.Coprod.inl (show CyclicThree from w.last)) •
              fuchsianOneFixedPoint = fuchsianOneFixedPoint :=
            (FreeProductTorsion.fuchsianSourceAction_inl_fixed_iff
              (show CyclicThree from w.last) hlast fuchsianOneFixedPoint).2 rfl
          have hfix : fuchsianSourceAction
              (indexedToDelta (Monoid.CoprodI.of w.last)) •
              fuchsianOneFixedPoint = fuchsianOneFixedPoint := by
            rw [indexedToDelta_of_false]
            exact hfix0
          rw [← hg, hprod, map_mul indexedToDelta,
            map_mul fuchsianSourceAction, mul_smul, hfix]
          exact neWord_ends_true_height_le p

private theorem fuchsianTwoFixedPoint_orbitHeightMaximal :
    IsOrbitHeightMaximal fuchsianTwoFixedPoint := by
  intro g
  by_cases hgempty : deltaNormalForm g = Monoid.CoprodI.Word.empty
  · have hg : g = 1 := by
      calc
        g = indexedToDelta (deltaNormalForm g).prod :=
          (indexedToDelta_deltaNormalForm_prod g).symm
        _ = 1 := by rw [hgempty]; simp
    simp [hg]
  · obtain ⟨i, j, w, hw⟩ := Monoid.CoprodI.NeWord.of_word (deltaNormalForm g) hgempty
    have hg : indexedToDelta w.prod = g := indexedToDelta_neWord_eq_of_normalForm hw
    cases j with
    | false =>
        rw [← hg]
        exact neWord_ends_false_height_le w
    | true =>
        rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
          hsingle | ⟨k, p, hk, hprod, hlen⟩
        · have hlast : w.last ≠ 1 := BinaryIndexedCoprod.NeWord.last_ne_one w
          have hfix0 : fuchsianSourceAction
              (Monoid.Coprod.inr (show CyclicFour from w.last)) •
              fuchsianTwoFixedPoint = fuchsianTwoFixedPoint :=
            (FreeProductTorsion.fuchsianSourceAction_inr_fixed_iff
              (show CyclicFour from w.last) hlast fuchsianTwoFixedPoint).2 rfl
          have hfix : fuchsianSourceAction
              (indexedToDelta (Monoid.CoprodI.of w.last)) •
              fuchsianTwoFixedPoint = fuchsianTwoFixedPoint := by
            rw [indexedToDelta_of_true]
            exact hfix0
          rw [← hg, hsingle.2.1, hfix]
        · have hkfalse : k = false := by cases k <;> simp_all
          subst k
          have hlast : w.last ≠ 1 := BinaryIndexedCoprod.NeWord.last_ne_one w
          have hfix0 : fuchsianSourceAction
              (Monoid.Coprod.inr (show CyclicFour from w.last)) •
              fuchsianTwoFixedPoint = fuchsianTwoFixedPoint :=
            (FreeProductTorsion.fuchsianSourceAction_inr_fixed_iff
              (show CyclicFour from w.last) hlast fuchsianTwoFixedPoint).2 rfl
          have hfix : fuchsianSourceAction
              (indexedToDelta (Monoid.CoprodI.of w.last)) •
              fuchsianTwoFixedPoint = fuchsianTwoFixedPoint := by
            rw [indexedToDelta_of_true]
            exact hfix0
          rw [← hg, hprod, map_mul indexedToDelta,
            map_mul fuchsianSourceAction, mul_smul, hfix]
          exact neWord_ends_false_height_le p

/-- An exact Fuchsian quotient coordinate has no zero in the standard cusp region. -/
public theorem ExactFuchsianOrbifoldCoordinate.coordinate_ne_zero_on_cusp
    (C : ExactFuchsianOrbifoldCoordinate) (z : UpperHalfPlane)
    (hz : z ∈ fuchsianCuspRegion) :
    C.coordinate z ≠ 0 := by
  intro hzero
  have hcoord : C.coordinate z = C.coordinate fuchsianOneFixedPoint := by
    rw [hzero, C.coordinate_at_one]
  obtain ⟨g, hg⟩ := (C.coordinate_eq_iff_orbit z fuchsianOneFixedPoint).1 hcoord
  have hzorb : z = fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint := by
    calc
      z = fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) := by simp
      _ = fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint := congrArg _ hg
  have hheight := fuchsianOneFixedPoint_orbitHeightMaximal g⁻¹
  rw [← hzorb] at hheight
  have hsqrt : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  change 1 ≤ z.im at hz
  change z.im ≤ Real.sqrt 3 / 2 at hheight
  linarith

/-- An exact Fuchsian quotient coordinate never takes the order-four branch value in the
standard cusp region. -/
public theorem ExactFuchsianOrbifoldCoordinate.coordinate_ne_one_on_cusp
    (C : ExactFuchsianOrbifoldCoordinate) (z : UpperHalfPlane)
    (hz : z ∈ fuchsianCuspRegion) :
    C.coordinate z ≠ 1 := by
  intro hone
  have hcoord : C.coordinate z = C.coordinate fuchsianTwoFixedPoint := by
    rw [hone, C.coordinate_at_two]
  obtain ⟨g, hg⟩ := (C.coordinate_eq_iff_orbit z fuchsianTwoFixedPoint).1 hcoord
  have hzorb : z = fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint := by
    calc
      z = fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) := by simp
      _ = fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint := congrArg _ hg
  have hheight := fuchsianTwoFixedPoint_orbitHeightMaximal g⁻¹
  rw [← hzorb] at hheight
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  change 1 ≤ z.im at hz
  change z.im ≤ Real.sqrt 2 / 2 at hheight
  linarith

private theorem fuchsianSourceCuspQ_tendsto_zero :
    Tendsto fuchsianSourceCuspQ upperHalfPlaneAtInfinity (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hrange : Set.range UpperHalfPlane.im ∈ (atTop : Filter ℝ) := by
    apply eventually_atTop.2
    refine ⟨1, fun y hy => ?_⟩
    refine ⟨⟨⟨0, y⟩, by linarith⟩, rfl⟩
  change Tendsto
    ((fun z : UpperHalfPlane => ‖Function.Periodic.qParam sourceCuspWidth (z : ℂ)‖))
    (comap UpperHalfPlane.im atTop) (nhds 0)
  simp_rw [Function.Periodic.norm_qParam]
  apply (tendsto_comap'_iff (m := fun y : ℝ =>
    Real.exp (-2 * Real.pi * y / sourceCuspWidth)) hrange).2
  exact Real.tendsto_exp_atBot.comp
    (.atBot_div_const sourceCuspWidth_pos
      (tendsto_id.const_mul_atTop_of_neg (by simpa using Real.pi_pos)))

/-- The reciprocal exact quotient coordinate converges to the completed cusp point. -/
public theorem ExactFuchsianOrbifoldCoordinate.inverse_coordinate_tendsto_zero
    (C : ExactFuchsianOrbifoldCoordinate) :
    Tendsto (fun z => (C.coordinate z)⁻¹) upperHalfPlaneAtInfinity (nhds 0) := by
  have hq := fuchsianSourceCuspQ_tendsto_zero
  have hzero_mem : (0 : ℂ) ∈ Metric.ball 0 C.cusp.cuspRadius := by
    simpa using C.cusp.cuspRadius_pos
  have hunit : Tendsto (fun z => C.cusp.cuspUnit (fuchsianSourceCuspQ z))
      upperHalfPlaneAtInfinity (nhds (C.cusp.cuspUnit 0)) :=
    (C.cusp.cuspUnit_holomorphic 0 hzero_mem).continuousAt.tendsto.comp hq
  have hproduct : Tendsto
      (fun z => fuchsianSourceCuspQ z * C.cusp.cuspUnit (fuchsianSourceCuspQ z))
      upperHalfPlaneAtInfinity (nhds 0) := by
    simpa using hq.mul hunit
  apply hproduct.congr'
  filter_upwards [C.cusp.reciprocal_factorization] with z hz
  exact hz.symm

private def centeredCuspTruncation (H : ℝ) : Set UpperHalfPlane :=
  {z | -FuchsianFundamentalDomain.cuspWidth / 2 ≤ z.re ∧
    z.re ≤ FuchsianFundamentalDomain.cuspWidth / 2 ∧
    1 ≤ z.im ∧ z.im ≤ max 1 H}

private theorem centeredCuspTruncation_isCompact (H : ℝ) :
    IsCompact (centeredCuspTruncation H) := by
  have hrect : IsCompact
      ((Set.Icc (-FuchsianFundamentalDomain.cuspWidth / 2)
          (FuchsianFundamentalDomain.cuspWidth / 2)) ×ℂ
        Set.Icc (1 : ℝ) (max 1 H)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  convert hrect using 1
  ext z
  constructor
  · rintro ⟨w, ⟨hwreLower, hwreUpper, hwimLower, hwimUpper⟩, rfl⟩
    exact ⟨⟨hwreLower, hwreUpper⟩, hwimLower, hwimUpper⟩
  · rintro ⟨⟨hzreLower, hzreUpper⟩, hzimLower, hzimUpper⟩
    have hzimPos : 0 < z.im := lt_of_lt_of_le (by norm_num) hzimLower
    let w : UpperHalfPlane := ⟨z, hzimPos⟩
    refine ⟨w, ?_, rfl⟩
    exact ⟨hzreLower, hzreUpper, hzimLower, hzimUpper⟩

/-- The reciprocal of an exact Fuchsian quotient coordinate is uniformly bounded on the
standard cusp region. -/
public theorem ExactFuchsianOrbifoldCoordinate.inverse_coordinate_bounded_on_cusp
    (C : ExactFuchsianOrbifoldCoordinate) :
    SphereSixComplex.Periods.BoundedOn
      (fun z => (C.coordinate z)⁻¹) fuchsianCuspRegion := by
  have heventually : ∀ᶠ z in upperHalfPlaneAtInfinity,
      (C.coordinate z)⁻¹ ∈ Metric.ball 0 1 :=
    (inverse_coordinate_tendsto_zero C).eventually
      (Metric.ball_mem_nhds 0 (by norm_num))
  rw [upperHalfPlaneAtInfinity, eventually_comap, eventually_atTop] at heventually
  obtain ⟨H, hH⟩ := heventually
  let K := centeredCuspTruncation H
  have hK : IsCompact K := centeredCuspTruncation_isCompact H
  have hcontinuous : ContinuousOn (fun z => (C.coordinate z)⁻¹) K := by
    apply C.coordinate_holomorphic.continuous.continuousOn.inv₀
    intro z hz
    exact C.coordinate_ne_zero_on_cusp z hz.2.2.1
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcontinuous.norm
  rw [SphereSixComplex.Periods.BoundedOn.eq_def]
  refine ⟨max B 1, by positivity, ?_⟩
  intro z hz
  by_cases hhigh : H ≤ z.im
  · have hball := hH z.im hhigh z rfl
    have hlt : ‖(C.coordinate z)⁻¹‖ < 1 := by simpa using hball
    exact hlt.le.trans (le_max_right B 1)
  · let w := centerPoint z
    have hwmem : w ∈ K := by
      refine ⟨centerPoint_re_lower z, (centerPoint_re_upper z).le, ?_, ?_⟩
      · rw [centerPoint_im]
        exact hz
      · rw [centerPoint_im]
        exact (le_of_not_ge hhigh).trans (le_max_right 1 H)
    have hcoord : C.coordinate w = C.coordinate z := by
      exact C.coordinate_invariant
        ((g₁ * g₂) ^ FuchsianTessellation.centerExponent z) z
    calc
      ‖(C.coordinate z)⁻¹‖ = ‖(C.coordinate w)⁻¹‖ := by rw [hcoord]
      _ ≤ B := hB ⟨_, hwmem, rfl⟩
      _ ≤ max B 1 := le_max_left B 1

end SphereSixComplex.Periods
