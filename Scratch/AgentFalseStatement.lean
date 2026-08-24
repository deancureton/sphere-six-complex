import SphereSixComplex.Periods.EstablishedOrbifoldAffineTorsorDescent
import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
import SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open Set Metric Filter
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
open SphereSixComplex.TriangleGroup.FuchsianArithmetic
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianTessellation
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain

/-! The cusp bounds are reproved locally here rather than imported from any untracked module. -/

private theorem deltaNormalForm_indexedToDelta_prod_falseStatement
    {i j : Bool} (w : Monoid.CoprodI.NeWord DeltaFactor i j) :
    deltaNormalForm (indexedToDelta w.prod) = w.toWord := by
  apply (Monoid.CoprodI.Word.equiv (M := DeltaFactor)).symm.injective
  change (deltaNormalForm (indexedToDelta w.prod)).prod = w.toWord.prod
  rw [deltaNormalForm_prod]
  change (deltaToIndexed.comp indexedToDelta) w.prod = w.prod
  rw [DFunLike.congr_fun deltaToIndexed_comp_indexedToDelta]
  rfl

private theorem one_le_abs_positiveEmbedding_of_coeffNonnegative_falseStatement
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

private theorem one_le_abs_positiveEmbedding_of_coeffNonpositive_falseStatement
    {x : QuadraticInteger} (hx : CoeffNonpositive x)
    (hne : positiveEmbedding x ≠ 0) :
    1 ≤ |positiveEmbedding x| := by
  have hneg : CoeffNonnegative (-x) := by
    exact ⟨by simpa using neg_nonneg.mpr hx.1, by simpa using neg_nonneg.mpr hx.2⟩
  have hneneg : positiveEmbedding (-x) ≠ 0 := by
    rw [map_neg]
    exact neg_ne_zero.mpr hne
  have h := one_le_abs_positiveEmbedding_of_coeffNonnegative_falseStatement hneg hneneg
  rw [map_neg, abs_neg] at h
  exact h

private theorem one_le_normSq_at_one_of_sameQuadrant_falseStatement
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
      have hone := one_le_abs_positiveEmbedding_of_coeffNonnegative_falseStatement hd hdr0
      rw [abs_of_nonneg hdr] at hone
      nlinarith
    · have hone := one_le_abs_positiveEmbedding_of_coeffNonnegative_falseStatement hc hcr0
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
      have hone := one_le_abs_positiveEmbedding_of_coeffNonpositive_falseStatement hd hdr0
      rw [abs_of_nonpos hdr] at hone
      nlinarith
    · have hone := one_le_abs_positiveEmbedding_of_coeffNonpositive_falseStatement hc hcr0
      rw [abs_of_nonpos hcr] at hone
      nlinarith

private theorem neWord_ends_true_height_le_falseStatement {i : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i true) :
    (fuchsianSourceAction (indexedToDelta w.prod) • fuchsianOneFixedPoint).im ≤
      fuchsianOneFixedPoint.im := by
  let g : Delta := indexedToDelta w.prod
  have hnormal : deltaNormalForm g = w.toWord :=
    deltaNormalForm_indexedToDelta_prod_falseStatement w
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
  have hden := one_le_normSq_at_one_of_sameQuadrant_falseStatement hrow hdenpos
  rw [show indexedToDelta w.prod = g by rfl,
    fuchsianSourceAction_im_eq_div_wordBottomNormSq]
  exact (div_le_iff₀ hdenpos).2 (by
    nlinarith [fuchsianOneFixedPoint.im_pos])

private theorem indexedToDelta_neWord_eq_of_normalForm_falseStatement
    {i j : Bool} {g : Delta} {w : Monoid.CoprodI.NeWord DeltaFactor i j}
    (hw : w.toWord = deltaNormalForm g) :
    indexedToDelta w.prod = g := by
  rw [← indexedToDelta_deltaNormalForm_prod g, ← hw]
  rfl

private theorem fuchsianOneFixedPoint_orbitHeightMaximal_falseStatement :
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
    have hg : indexedToDelta w.prod = g :=
      indexedToDelta_neWord_eq_of_normalForm_falseStatement hw
    cases j with
    | true =>
        rw [← hg]
        exact neWord_ends_true_height_le_falseStatement w
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
          exact neWord_ends_true_height_le_falseStatement p

private theorem exactCoordinate_ne_zero_on_cusp_falseStatement
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
  have hheight := fuchsianOneFixedPoint_orbitHeightMaximal_falseStatement g⁻¹
  rw [← hzorb] at hheight
  have hsqrt : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  change 1 ≤ z.im at hz
  change z.im ≤ Real.sqrt 3 / 2 at hheight
  linarith

private theorem fuchsianSourceCuspQ_tendsto_zero_falseStatement :
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

private theorem exactCoordinate_inverse_tendsto_zero_falseStatement
    (C : ExactFuchsianOrbifoldCoordinate) :
    Tendsto (fun z => (C.coordinate z)⁻¹) upperHalfPlaneAtInfinity (nhds 0) := by
  have hq := fuchsianSourceCuspQ_tendsto_zero_falseStatement
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

private def centeredCuspTruncation_falseStatement (H : ℝ) : Set UpperHalfPlane :=
  {z | -cuspWidth / 2 ≤ z.re ∧
    z.re ≤ cuspWidth / 2 ∧
    1 ≤ z.im ∧ z.im ≤ max 1 H}

private theorem centeredCuspTruncation_isCompact_falseStatement (H : ℝ) :
    IsCompact (centeredCuspTruncation_falseStatement H) := by
  have hrect : IsCompact
      ((Set.Icc (-cuspWidth / 2) (cuspWidth / 2)) ×ℂ
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

private theorem exactCoordinate_inverse_bounded_on_cusp_falseStatement
    (C : ExactFuchsianOrbifoldCoordinate) :
    BoundedOn (fun z => (C.coordinate z)⁻¹) fuchsianCuspRegion := by
  have heventually : ∀ᶠ z in upperHalfPlaneAtInfinity,
      (C.coordinate z)⁻¹ ∈ Metric.ball 0 1 :=
    (exactCoordinate_inverse_tendsto_zero_falseStatement C).eventually
      (Metric.ball_mem_nhds 0 (by norm_num))
  rw [upperHalfPlaneAtInfinity, eventually_comap, eventually_atTop] at heventually
  obtain ⟨H, hH⟩ := heventually
  let K := centeredCuspTruncation_falseStatement H
  have hK : IsCompact K := centeredCuspTruncation_isCompact_falseStatement H
  have hcontinuous : ContinuousOn (fun z => (C.coordinate z)⁻¹) K := by
    apply C.coordinate_holomorphic.continuous.continuousOn.inv₀
    intro z hz
    exact exactCoordinate_ne_zero_on_cusp_falseStatement C z hz.2.2.1
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcontinuous.norm
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
      exact C.coordinate_invariant ((g₁ * g₂) ^ centerExponent z) z
    calc
      ‖(C.coordinate z)⁻¹‖ = ‖(C.coordinate w)⁻¹‖ := by rw [hcoord]
      _ ≤ B := hB ⟨_, hwmem, rfl⟩
      _ ≤ max B 1 := le_max_left B 1

private noncomputable def exactCoordinateCuspBound_falseStatement
    (C : ExactFuchsianOrbifoldCoordinate) : ℝ :=
  Classical.choose (exactCoordinate_inverse_bounded_on_cusp_falseStatement C)

private theorem exactCoordinateCuspBound_nonneg_falseStatement
    (C : ExactFuchsianOrbifoldCoordinate) :
    0 ≤ exactCoordinateCuspBound_falseStatement C :=
  (Classical.choose_spec (exactCoordinate_inverse_bounded_on_cusp_falseStatement C)).1

private theorem exactCoordinateCuspBound_spec_falseStatement
    (C : ExactFuchsianOrbifoldCoordinate) (z : UpperHalfPlane)
    (hz : z ∈ fuchsianCuspRegion) :
    ‖(C.coordinate z)⁻¹‖ ≤ exactCoordinateCuspBound_falseStatement C :=
  (Classical.choose_spec (exactCoordinate_inverse_bounded_on_cusp_falseStatement C)).2 z hz

private theorem fuchsianSourceCuspQ_holomorphic_falseStatement :
    MDiff fuchsianSourceCuspQ := by
  change MDiff (fun z : UpperHalfPlane ↦
    Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / sourceCuspWidth))
  have harg : MDiff (fun z : UpperHalfPlane ↦
      2 * Real.pi * Complex.I * (z : ℂ) / sourceCuspWidth) := by
    apply (mdifferentiable_const.mul UpperHalfPlane.mdifferentiable_coe).div
      mdifferentiable_const
    intro z
    exact_mod_cast sourceCuspWidth_pos.ne'
  have hexp : MDiff (Complex.exp : ℂ → ℂ) :=
    mdifferentiable_iff_differentiable.mpr Complex.differentiable_exp
  exact hexp.comp harg

private theorem fuchsianSourceCuspQ_gOne_I_ne_falseStatement :
    fuchsianSourceCuspQ (fuchsianSourceAction g₁ • UpperHalfPlane.I) ≠
      fuchsianSourceCuspQ UpperHalfPlane.I := by
  intro h
  have ha : ((fuchsianSourceAction g₁ • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      1 + Complex.I := by
    change (((fuchsianSourceAction g₁) UpperHalfPlane.I : UpperHalfPlane) : ℂ) = _
    rw [fuchsianSourceAction_g₁_apply]
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq]
  simp only [fuchsianSourceCuspQ] at h
  rw [ha, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have him := congrArg Complex.im hn
  simp [Complex.div_im, Complex.normSq] at him
  have hp0 : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have him' : (2 * Real.pi) * (1 / sourceCuspWidth) =
      (2 * Real.pi) * (n : ℝ) := by
    calc
      (2 * Real.pi) * (1 / sourceCuspWidth) =
          2 * Real.pi * sourceCuspWidth /
            (sourceCuspWidth * sourceCuspWidth) := by field_simp
      _ = (n : ℝ) * (2 * Real.pi) := him
      _ = (2 * Real.pi) * (n : ℝ) := by ring
  have heq : 1 / sourceCuspWidth = (n : ℝ) :=
    mul_left_cancel₀ hp0 him'
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hwone : 1 < sourceCuspWidth := by
    rw [sourceCuspWidth]
    linarith
  have hfracpos : 0 < 1 / sourceCuspWidth := one_div_pos.mpr sourceCuspWidth_pos
  have hfraclt : 1 / sourceCuspWidth < 1 := by
    apply (div_lt_iff₀ sourceCuspWidth_pos).2
    simpa using hwone
  have hnpos : 0 < (n : ℝ) := heq ▸ hfracpos
  have hnlt : (n : ℝ) < 1 := heq ▸ hfraclt
  have hnposZ : 0 < n := by exact_mod_cast hnpos
  have hnltZ : n < 1 := by exact_mod_cast hnlt
  omega

/-- A counterexample problem over an arbitrary exact Fuchsian quotient coordinate.  Its affine
cocycle and both homogeneous frames are the identity; only the unconstrained normalization is
adversarial. -/
public noncomputable def falseStatementProblem
    (C : ExactFuchsianOrbifoldCoordinate) :
    OrbifoldAffineLineTorsorDescentProblem where
  quotient := C
  affineOne := fun _ u ↦ u
  affineTwo := fun _ u ↦ u
  affineCusp := fun _ u ↦ u
  affineOne_holomorphic := fun _ hs ↦ hs
  affineTwo_holomorphic := fun _ hs ↦ hs
  affineCusp_holomorphic := fun _ hs ↦ hs
  linearOne := fun _ ↦ 1
  linearTwo := fun _ ↦ 1
  affineOne_sub := by simp
  affineTwo_sub := by simp
  affineOne_cycle := by simp
  affineTwo_cycle := by simp
  product_cusp := by simp
  cusp_product := by simp
  frameZero := fun _ ↦ 1
  frameInfinity := fun _ ↦ 1
  frameZero_holomorphic := mdifferentiable_const
  frameInfinity_holomorphic := fun _ _ ↦ mdifferentiableAt_const
  frameZero_one := by simp
  frameZero_two := by simp
  frameInfinity_one := by simp
  frameInfinity_two := by simp
  frameOrderOne := 0
  frameOrderTwo := 0
  frameZero_branch_one := {
    uniformizer := C.branch_one.uniformizer
    uniformizer_center := C.branch_one.uniformizer_center
    uniformizer_isLocalDiffeomorph := C.branch_one.uniformizer_isLocalDiffeomorph
    unit := fun _ ↦ 1
    unit_holomorphic := mdifferentiableAt_const
    unit_ne_zero := one_ne_zero
    factorization := Filter.Eventually.of_forall (by simp) }
  frameZero_branch_two := {
    uniformizer := C.branch_two.uniformizer
    uniformizer_center := C.branch_two.uniformizer_center
    uniformizer_isLocalDiffeomorph := C.branch_two.uniformizer_isLocalDiffeomorph
    unit := fun _ ↦ 1
    unit_holomorphic := mdifferentiableAt_const
    unit_ne_zero := one_ne_zero
    factorization := Filter.Eventually.of_forall (by simp) }
  frameZero_zero_iff := by simp
  frameTransition := fun _ ↦ 1
  frameTransition_holomorphic := fun _ _ ↦ mdifferentiableAt_const
  frame_transition := by simp
  cuspFrameUnit := fun _ ↦ 1
  cuspFrameRadius := 2 * (exactCoordinateCuspBound_falseStatement C + 1)
  cuspFrameRadius_pos := by
    have hB := exactCoordinateCuspBound_nonneg_falseStatement C
    positivity
  cuspFrameUnit_holomorphic := fun _ _ ↦ mdifferentiableAt_const
  cuspFrameUnit_zero_ne := one_ne_zero
  inverse_coordinate_mem_closedBall := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := exactCoordinateCuspBound_spec_falseStatement C z hz
    linarith
  frameInfinity_cusp_factorization := by simp
  ellipticOne := fun _ ↦ 0
  ellipticTwo := fun _ ↦ 0
  ellipticOne_holomorphic := mdifferentiable_const
  ellipticTwo_holomorphic := mdifferentiable_const
  ellipticOne_equivariant := by simp
  ellipticTwo_equivariant := by simp
  cuspSection := fuchsianSourceCuspQ
  cuspSection_holomorphic := fuchsianSourceCuspQ_holomorphic_falseStatement
  cuspSection_equivariant := fuchsianSourceCuspQ_invariant
  cusp_coordinate_ne_zero := exactCoordinate_ne_zero_on_cusp_falseStatement C
  cuspNormalize := fun z u ↦
    if u = fuchsianSourceCuspQ z then 0 else (z.re : ℂ)
  cuspSection_normalized_bounded := by
    refine ⟨0, le_rfl, ?_⟩
    simp

private theorem falseStatement_sectionInfinity_eq_cusp
    (C : ExactFuchsianOrbifoldCoordinate)
    (S : (falseStatementProblem C).TwoChartSections)
    (z : UpperHalfPlane) (hz : z ∈ fuchsianCuspRegion) :
    S.sectionInfinity z = fuchsianSourceCuspQ z := by
  let s := S.sectionInfinity
  have hcoord (w : UpperHalfPlane) (hw : C.coordinate w ≠ 0)
      (g : Delta) : C.coordinate (fuchsianSourceAction g • w) ≠ 0 := by
    rwa [C.coordinate_invariant]
  have hOne (w : UpperHalfPlane) (hw : C.coordinate w ≠ 0) :
      s (fuchsianSourceAction g₁ • w) = s w := by
    simpa [s, falseStatementProblem] using S.sectionInfinity_one w hw
  have hTwo (w : UpperHalfPlane) (hw : C.coordinate w ≠ 0) :
      s (fuchsianSourceAction g₂ • w) = s w := by
    simpa [s, falseStatementProblem] using S.sectionInfinity_two w hw
  have hZero (w : UpperHalfPlane) (hw : C.coordinate w ≠ 0) :
      s (fuchsianSourceAction g₀ • w) = s w := by
    have h2 := hTwo (fuchsianSourceAction g₀ • w) (hcoord w hw g₀)
    have h1 := hOne (fuchsianSourceAction g₂ •
      (fuchsianSourceAction g₀ • w))
      (hcoord (fuchsianSourceAction g₀ • w) (hcoord w hw g₀) g₂)
    calc
      s (fuchsianSourceAction g₀ • w) =
          s (fuchsianSourceAction g₂ • (fuchsianSourceAction g₀ • w)) := h2.symm
      _ = s (fuchsianSourceAction g₁ •
          (fuchsianSourceAction g₂ • (fuchsianSourceAction g₀ • w))) := h1.symm
      _ = s w := by
        congr 1
        rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul,
          g₁_mul_g₂_mul_g₀, map_one, one_smul]
  have hzcoord : C.coordinate z ≠ 0 :=
    exactCoordinate_ne_zero_on_cusp_falseStatement C z hz
  have hpow (n : ℕ) : s (fuchsianSourceAction (g₀ ^ n) • z) = s z := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', map_mul, mul_smul]
        rw [hZero _ (hcoord z hzcoord (g₀ ^ n)), ih]
  have hqpow (n : ℕ) :
      fuchsianSourceCuspQ (fuchsianSourceAction (g₀ ^ n) • z) =
        fuchsianSourceCuspQ z := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', map_mul, mul_smul, fuchsianSourceCuspQ_invariant, ih]
  obtain ⟨M, hM, hbound⟩ := S.sectionInfinity_normalized_cusp_bounded
  by_contra hne
  obtain ⟨n, hn⟩ := exists_nat_gt ((M + |z.re|) / cuspWidth)
  let w := fuchsianSourceAction (g₀ ^ n) • z
  have hwmem : w ∈ fuchsianCuspRegion := by
    change 1 ≤ w.im
    have happly := cusp_pow_apply n z
    have him := congrArg Complex.im happly
    have him' : w.im = z.im := by simpa [w] using him
    rw [him']
    exact hz
  have hwne : s w ≠ fuchsianSourceCuspQ w := by
    rw [hpow n, hqpow n]
    exact hne
  have hb := hbound w hwmem
  simp only [falseStatementProblem, s, hwne, if_false,
    Complex.norm_real, Real.norm_eq_abs] at hb
  rw [cusp_pow_re] at hb
  have hn' : M + |z.re| < (n : ℝ) * cuspWidth :=
    (div_lt_iff₀ cuspWidth_pos).mp hn
  have hzle : z.re ≤ |z.re| := le_abs_self z.re
  have hneg : z.re - (n : ℝ) * cuspWidth < -M := by linarith
  have habs : M < |z.re - (n : ℝ) * cuspWidth| := by
    rw [abs_of_neg (lt_of_lt_of_le hneg (neg_nonpos.mpr hM))]
    linarith
  exact (not_lt_of_ge hb) habs

/-- The exact universal descent theorem is false for every exact quotient coordinate, even when
all affine substitutions and both homogeneous frames are the identity. -/
public theorem falseStatementProblem_no_twoChartSections
    (C : ExactFuchsianOrbifoldCoordinate) :
    ¬ Nonempty (falseStatementProblem C).TwoChartSections := by
  rintro ⟨S⟩
  have hI : UpperHalfPlane.I ∈ fuchsianCuspRegion := by
    change 1 ≤ UpperHalfPlane.I.im
    norm_num
  have hgI : fuchsianSourceAction g₁ • UpperHalfPlane.I ∈ fuchsianCuspRegion := by
    change 1 ≤ (((fuchsianSourceAction g₁) UpperHalfPlane.I : UpperHalfPlane) : ℂ).im
    rw [fuchsianSourceAction_g₁_apply]
    norm_num [Complex.div_im, Complex.normSq]
  have hsectionI := falseStatement_sectionInfinity_eq_cusp C S UpperHalfPlane.I hI
  have hsectiongI := falseStatement_sectionInfinity_eq_cusp C S
    (fuchsianSourceAction g₁ • UpperHalfPlane.I) hgI
  have hcoordI : C.coordinate UpperHalfPlane.I ≠ 0 :=
    exactCoordinate_ne_zero_on_cusp_falseStatement C UpperHalfPlane.I hI
  have hOne := S.sectionInfinity_one UpperHalfPlane.I hcoordI
  have hOne' :
      S.sectionInfinity (fuchsianSourceAction g₁ • UpperHalfPlane.I) =
        S.sectionInfinity UpperHalfPlane.I := by
    simpa [falseStatementProblem] using hOne
  apply fuchsianSourceCuspQ_gOne_I_ne_falseStatement
  calc
    fuchsianSourceCuspQ (fuchsianSourceAction g₁ • UpperHalfPlane.I) =
        S.sectionInfinity (fuchsianSourceAction g₁ • UpperHalfPlane.I) := hsectiongI.symm
    _ = S.sectionInfinity UpperHalfPlane.I := hOne'
    _ = fuchsianSourceCuspQ UpperHalfPlane.I := hsectionI

/-- Exact negation of the claimed universal descent statement: every exact quotient coordinate
supplies a concrete problem witnessing failure of universal two-chart section existence. -/
public theorem not_forall_twoChartSections
    (C : ExactFuchsianOrbifoldCoordinate) :
    ¬ (∀ P : OrbifoldAffineLineTorsorDescentProblem, Nonempty P.TwoChartSections) := by
  intro h
  exact falseStatementProblem_no_twoChartSections C (h (falseStatementProblem C))

#print axioms falseStatementProblem_no_twoChartSections
#print axioms not_forall_twoChartSections

end SphereSixComplex.Periods
