module

public import SphereSixComplex.Periods.Uniformization.ScalarExactCusp
import all SphereSixComplex.Periods.Uniformization.ScalarExactCusp

@[expose] public section

/-!
# Exact high cusp fibres from the scalar Schwarz seed

The open right double is injective on a full-period strip except for its vertical edges.  A
half-open choice leaves only the left edge, which lies inside the independently constructed left
Schwarz double.  Its values are real, while an interior high-strip value is real only on the
middle reflection seam.  Closed-triangle injectivity rules out a collision between those two
different sides.  Thus no cusp-centralizer theorem is needed for exact high fibres.
-/

open Complex Filter Function Metric Set Topology UpperHalfPlane

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.Periods.TriangleReflections

def sourceScalarHalfOpenCuspStrip : Set ℂ :=
  {z | -Real.sqrt 2 / 2 ≤ z.re ∧
    z.re < 1 + Real.sqrt 2 / 2 ∧ 2 < z.im}

theorem globalScalar_eq_seed_on_high_leftEdge
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber)
    {z : ℂ} (hre : z.re = -Real.sqrt 2 / 2) (hhigh : 2 < z.im) :
    F z = sourceScalarTriangleMap S z := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hzleft : z ∈ sourceScalarLeftCuspDoubleStrip := by
    change -Real.sqrt 2 - 1 / 2 < z.re ∧ z.re < 1 / 2 ∧ 2 < z.im
    rw [hre]
    exact ⟨by nlinarith, by nlinarith, hhigh⟩
  have h := globalScalar_eqOn_leftDoubleMap_on_highStrip S F hF hseed hzleft
  rw [sourceScalarLeftDoubleMap_eq_seed_of_left_le_re S (by rw [hre])] at h
  exact h

theorem globalScalar_im_ne_zero_on_cuspStrip_of_re_ne_half
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber)
    {z : ℂ} (hz : z ∈ sourceScalarCuspStrip) (hre : z.re ≠ 1 / 2) :
    (F z).im ≠ 0 := by
  let d : ℝ := scalarTriangleDenominator (sourceCuspCircle S)
    (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S)
  have hglobal := globalScalar_eqOn_rightDoubleMap_on_cuspStrip S F hF hseed hz
  rcases lt_or_gt_of_ne hre with hleft | hright
  · have hopen := sourceScalarCuspStrip_mem_sourceOpenChamber_of_re_lt_half hz hleft
    have himage := (sourceScalarOpenChamberMap_bijOn S
      (sourceOrderThreeCircle_ne_otherElliptic S)).mapsTo hopen
    change 0 < d * (sourceScalarOpenChamberMap S z).im at himage
    rw [← sourceScalarTriangleMap_eq_open_of_mem S hopen] at himage
    rw [sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hleft.le] at hglobal
    intro him
    have himSeed : (sourceScalarTriangleMap S z).im = 0 := by
      rw [← hglobal]
      exact him
    rw [himSeed, mul_zero] at himage
    exact (lt_irrefl 0 himage).elim
  · have hopen := sourceRight_mem_sourceOpenChamber_of_mem_cuspStrip_of_half_lt hz hright
    have himage := (sourceScalarOpenChamberMap_bijOn S
      (sourceOrderThreeCircle_ne_otherElliptic S)).mapsTo hopen
    change 0 < d * (sourceScalarOpenChamberMap S (sourceRight z)).im at himage
    rw [← sourceScalarTriangleMap_eq_open_of_mem S hopen] at himage
    rw [sourceScalarRightDoubleMap_eq_conj_seed_of_mem_cuspStrip_of_half_lt
      S hz hright] at hglobal
    intro him
    have him' := congrArg Complex.im hglobal
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_im, him] at him'
    have hzIm : (sourceScalarTriangleMap S (sourceRight z)).im = 0 := by linarith
    rw [hzIm, mul_zero] at himage
    exact (lt_irrefl 0 himage).elim

private theorem high_mem_fundamentalTriangle {z : ℂ}
    (hleft : -Real.sqrt 2 / 2 ≤ z.re) (hright : z.re ≤ 1 / 2)
    (hhigh : 2 < z.im) :
    (⟨z, lt_trans (by norm_num) hhigh⟩ : UpperHalfPlane) ∈ fundamentalTriangle := by
  refine ⟨hleft, hright, ?_⟩
  rw [normSq_apply]
  nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 2)]

private theorem no_high_leftEdge_interior_collision
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber)
    {z w : ℂ} (hz : z ∈ sourceScalarHalfOpenCuspStrip)
    (hw : w ∈ sourceScalarHalfOpenCuspStrip)
    (hzedge : z.re = -Real.sqrt 2 / 2)
    (hwedge : w.re ≠ -Real.sqrt 2 / 2) (hzw : F z = F w) : False := by
  have hwleft : -Real.sqrt 2 / 2 < w.re := lt_of_le_of_ne hw.1 (Ne.symm hwedge)
  have hwopen : w ∈ sourceScalarCuspStrip := ⟨hwleft, hw.2⟩
  have hzseed := globalScalar_eq_seed_on_high_leftEdge S F hF hseed hzedge hz.2.2
  have hhighz : 2 < z.im := hz.2.2
  have hzim : (F z).im = 0 := by
    rw [hzseed]
    apply sourceScalarTriangleMap_im_eq_zero_of_leftSide S hzedge
    · exact lt_trans (by norm_num) hhighz
    · rw [normSq_apply]
      have himsq : 1 < z.im * z.im := by
        nlinarith [hhighz, sq_nonneg (z.im - 1)]
      nlinarith [mul_self_nonneg z.re]
  have hwim : (F w).im = 0 := by rw [← hzw]; exact hzim
  have hwseam : w.re = 1 / 2 := by
    by_contra hne
    exact globalScalar_im_ne_zero_on_cuspStrip_of_re_ne_half
      S F hF hseed hwopen hne hwim
  let zu : UpperHalfPlane := ⟨z, lt_trans (by norm_num) hz.2.2⟩
  let wu : UpperHalfPlane := ⟨w, lt_trans (by norm_num) hw.2.2⟩
  have hzfund : zu ∈ fundamentalTriangle :=
    high_mem_fundamentalTriangle hz.1 (by rw [hzedge]; nlinarith) hz.2.2
  have hwfund : wu ∈ fundamentalTriangle :=
    high_mem_fundamentalTriangle hw.1 hwseam.le hw.2.2
  have hwglobal := globalScalar_eqOn_rightDoubleMap_on_cuspStrip S F hF hseed hwopen
  rw [sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hwseam.le] at hwglobal
  have heq : zu = wu := sourceScalarTriangleMap_injective_on_fundamentalTriangle
    S hzfund hwfund (by simpa [zu, wu, hzseed, hwglobal] using hzw)
  have hre := congrArg (fun q : UpperHalfPlane ↦ q.re) heq
  change z.re = w.re at hre
  rw [hzedge, hwseam] at hre
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  nlinarith

theorem globalScalar_injOn_halfOpenCuspStrip
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    InjOn F sourceScalarHalfOpenCuspStrip := by
  intro z hz w hw hzw
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  by_cases hzedge : z.re = -Real.sqrt 2 / 2
  · by_cases hwedge : w.re = -Real.sqrt 2 / 2
    · let zu : UpperHalfPlane := ⟨z, lt_trans (by norm_num) hz.2.2⟩
      let wu : UpperHalfPlane := ⟨w, lt_trans (by norm_num) hw.2.2⟩
      have hzfund : zu ∈ fundamentalTriangle :=
        high_mem_fundamentalTriangle hz.1 (by rw [hzedge]; nlinarith) hz.2.2
      have hwfund : wu ∈ fundamentalTriangle :=
        high_mem_fundamentalTriangle hw.1 (by rw [hwedge]; nlinarith) hw.2.2
      have hzseed := globalScalar_eq_seed_on_high_leftEdge S F hF hseed hzedge hz.2.2
      have hwseed := globalScalar_eq_seed_on_high_leftEdge S F hF hseed hwedge hw.2.2
      have heq : zu = wu := sourceScalarTriangleMap_injective_on_fundamentalTriangle
        S hzfund hwfund (by simpa [zu, wu, hzseed, hwseed] using hzw)
      exact congrArg ((↑) : UpperHalfPlane → ℂ) heq
    · exact (no_high_leftEdge_interior_collision S F hF hseed
        hz hw hzedge hwedge hzw).elim
  · have hzleft : -Real.sqrt 2 / 2 < z.re := lt_of_le_of_ne hz.1 (Ne.symm hzedge)
    have hzopen : z ∈ sourceScalarCuspStrip := ⟨hzleft, hz.2⟩
    by_cases hwedge : w.re = -Real.sqrt 2 / 2
    · exact (no_high_leftEdge_interior_collision S F hF hseed
        hw hz hwedge hzedge hzw.symm).elim
    · have hwleft : -Real.sqrt 2 / 2 < w.re := lt_of_le_of_ne hw.1 (Ne.symm hwedge)
      have hwopen : w ∈ sourceScalarCuspStrip := ⟨hwleft, hw.2⟩
      exact globalScalar_injOn_cuspStrip S F hF hseed hzopen hwopen hzw

theorem sourceQParam_periodic :
    Function.Periodic (Function.Periodic.qParam sourceCuspWidth) sourceCuspWidth := by
  intro z
  unfold Function.Periodic.qParam
  have heq : 2 * Real.pi * Complex.I * (z + (sourceCuspWidth : ℂ)) / sourceCuspWidth =
      2 * Real.pi * Complex.I * z / sourceCuspWidth + 2 * Real.pi * Complex.I := by
    field_simp [show (sourceCuspWidth : ℂ) ≠ 0 by
      exact_mod_cast sourceCuspWidth_pos.ne']
  rw [heq]
  exact Complex.exp_periodic _

theorem fuchsianCoordinateReciprocal_high_fibres_of_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (C : FuchsianOrbifoldCoordinate) (F : ℂ → ℂ)
    (hcoordinate : ∀ z : UpperHalfPlane, C.coordinate z = F (z : ℂ))
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hseed : EqOn F (sourceScalarTriangleMap S) sourceOpenChamber) :
    ∃ A : ℝ, ∀ z w : ℂ,
      A < z.im → A < w.im →
        fuchsianCoordinateReciprocal C z = fuchsianCoordinateReciprocal C w →
        Function.Periodic.qParam sourceCuspWidth z =
          Function.Periodic.qParam sourceCuspWidth w := by
  refine ⟨2, ?_⟩
  intro z w hzHigh hwHigh hrEq
  let nz : ℤ := ⌊(z.re + Real.sqrt 2 / 2) / sourceCuspWidth⌋
  let nw : ℤ := ⌊(w.re + Real.sqrt 2 / 2) / sourceCuspWidth⌋
  let z₀ : ℂ := z - (nz : ℂ) * (sourceCuspWidth : ℂ)
  let w₀ : ℂ := w - (nw : ℂ) * (sourceCuspWidth : ℂ)
  have hzrem_nonneg := Int.sub_floor_div_mul_nonneg
    (z.re + Real.sqrt 2 / 2) sourceCuspWidth_pos
  have hzrem_lt := Int.sub_floor_div_mul_lt
    (z.re + Real.sqrt 2 / 2) sourceCuspWidth_pos
  have hwrem_nonneg := Int.sub_floor_div_mul_nonneg
    (w.re + Real.sqrt 2 / 2) sourceCuspWidth_pos
  have hwrem_lt := Int.sub_floor_div_mul_lt
    (w.re + Real.sqrt 2 / 2) sourceCuspWidth_pos
  change 0 ≤ z.re + Real.sqrt 2 / 2 - (nz : ℝ) * sourceCuspWidth at hzrem_nonneg
  change z.re + Real.sqrt 2 / 2 - (nz : ℝ) * sourceCuspWidth <
    sourceCuspWidth at hzrem_lt
  change 0 ≤ w.re + Real.sqrt 2 / 2 - (nw : ℝ) * sourceCuspWidth at hwrem_nonneg
  change w.re + Real.sqrt 2 / 2 - (nw : ℝ) * sourceCuspWidth <
    sourceCuspWidth at hwrem_lt
  have hz₀re : z₀.re = z.re - (nz : ℝ) * sourceCuspWidth := by simp [z₀]
  have hw₀re : w₀.re = w.re - (nw : ℝ) * sourceCuspWidth := by simp [w₀]
  have hz₀im : z₀.im = z.im := by simp [z₀]
  have hw₀im : w₀.im = w.im := by simp [w₀]
  have hz₀mem : z₀ ∈ sourceScalarHalfOpenCuspStrip := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hz₀re]
      linarith
    · rw [hz₀re, sourceCuspWidth]
      rw [sourceCuspWidth] at hzrem_lt
      linarith
    · simpa only [hz₀im] using hzHigh
  have hw₀mem : w₀ ∈ sourceScalarHalfOpenCuspStrip := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hw₀re]
      linarith
    · rw [hw₀re, sourceCuspWidth]
      rw [sourceCuspWidth] at hwrem_lt
      linarith
    · simpa only [hw₀im] using hwHigh
  have hrz := (fuchsianCoordinateReciprocal_periodic C).sub_int_mul_eq (x := z) nz
  have hrw := (fuchsianCoordinateReciprocal_periodic C).sub_int_mul_eq (x := w) nw
  change fuchsianCoordinateReciprocal C z₀ =
    fuchsianCoordinateReciprocal C z at hrz
  change fuchsianCoordinateReciprocal C w₀ =
    fuchsianCoordinateReciprocal C w at hrw
  have hr₀ : fuchsianCoordinateReciprocal C z₀ =
      fuchsianCoordinateReciprocal C w₀ := hrz.trans (hrEq.trans hrw.symm)
  have hz₀pos : 0 < z₀.im := lt_trans (by norm_num) hz₀mem.2.2
  have hw₀pos : 0 < w₀.im := lt_trans (by norm_num) hw₀mem.2.2
  have hF₀ : F z₀ = F w₀ := by
    apply inv_injective
    rw [fuchsianCoordinateReciprocal, dif_pos hz₀pos,
      fuchsianCoordinateReciprocal, dif_pos hw₀pos] at hr₀
    simpa only [hcoordinate] using hr₀
  have hzw₀ : z₀ = w₀ :=
    globalScalar_injOn_halfOpenCuspStrip S F hF hseed hz₀mem hw₀mem hF₀
  have hqz := sourceQParam_periodic.sub_int_mul_eq (x := z) nz
  have hqw := sourceQParam_periodic.sub_int_mul_eq (x := w) nw
  change Function.Periodic.qParam sourceCuspWidth z₀ =
    Function.Periodic.qParam sourceCuspWidth z at hqz
  change Function.Periodic.qParam sourceCuspWidth w₀ =
    Function.Periodic.qParam sourceCuspWidth w at hqw
  exact hqz.symm.trans
    ((congrArg (Function.Periodic.qParam sourceCuspWidth) hzw₀).trans hqw)


end SphereSixComplex.Periods.SourceChamberTopology
