module

public import SphereSixComplex.Periods.Uniformization.ScalarBoundarySurjective
import all SphereSixComplex.Periods.Uniformization.ScalarBoundarySurjective
public import SphereSixComplex.Periods.Uniformization.ScalarRightReflectionInjective
import all SphereSixComplex.Periods.Uniformization.ScalarRightReflectionInjective
public import SphereSixComplex.TriangleGroup.FuchsianTriangleCover
import all SphereSixComplex.TriangleGroup.FuchsianTriangleCover

@[expose] public section

/-!
# Lifting finite scalar boundary values to the Fuchsian fundamental triangle

The bounded cusp model compactifies the ideal vertex by the radial coordinate `t = 0`.
Every other point of its Jordan frontier therefore comes from an honest point of the closed
Fuchsian triangle.  Combined with the real-boundary surjectivity of the scalar seed, this gives
the finite real part of fundamental-region surjectivity.
-/

open Complex Metric Set Topology
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.Periods.TriangleReflections

private theorem re_sq_lt_one_of_source_closed_bounds {x : ℝ}
    (hl : -Real.sqrt 2 / 2 ≤ x) (hr : x ≤ 1 / 2) : x ^ 2 < 1 := by
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hs2n : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2lt : Real.sqrt 2 < 2 := by nlinarith
  have hxlo : -1 < x := by nlinarith
  have hxhi : x < 1 := by linarith
  nlinarith

private theorem semicircleHeight_sq_of_source_closed_bounds {x : ℝ}
    (hl : -Real.sqrt 2 / 2 ≤ x) (hr : x ≤ 1 / 2) :
    semicircleHeight x ^ 2 = 1 - x ^ 2 := by
  have hx := re_sq_lt_one_of_source_closed_bounds hl hr
  rw [semicircleHeight, max_eq_right (by linarith), Real.sq_sqrt (by linarith)]

/-- Every non-cusp point of the compactified source-chamber frontier is the cusp exponential of
an honest point of the closed Fuchsian fundamental triangle. -/
theorem exists_fundamentalTriangle_cuspExponential_eq_of_frontier_ne_cusp
    {q : ℂ} (hq : q ∈ frontier sourceBoundedChamber) (hne : q ≠ sourceCuspVertex) :
    ∃ z : UpperHalfPlane, z ∈ fundamentalTriangle ∧
      cuspExponential (1 + Real.sqrt 2) (z : ℂ) = q := by
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary] at hq
  obtain ⟨⟨x, t⟩, hp, hqeq⟩ := hq
  have hrect := (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      linarith) (x, t)).mp hp
  rcases hrect.1 with ⟨⟨hxl, hxr⟩, ht0, ht1⟩
  have htne : t ≠ 0 := by
    intro ht
    apply hne
    rw [← hqeq, sourceCuspVertex, cuspPolar, ht]
    simp
  have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
  let y : ℝ := semicircleHeight x -
    (1 + Real.sqrt 2) * Real.log t / (2 * Real.pi)
  let zc : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hxsq : x ^ 2 < 1 := re_sq_lt_one_of_source_closed_bounds hxl hxr
  have hhsq : semicircleHeight x ^ 2 = 1 - x ^ 2 :=
    semicircleHeight_sq_of_source_closed_bounds hxl hxr
  have hh0 : 0 ≤ semicircleHeight x := by
    unfold semicircleHeight
    positivity
  have hhp : 0 < semicircleHeight x := by nlinarith
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0 ht1
  have hw : 0 < 1 + Real.sqrt 2 := by positivity
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hterm : (1 + Real.sqrt 2) * Real.log t / (2 * Real.pi) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hw.le hlog) hpi.le
  have hyge : semicircleHeight x ≤ y := by dsimp [y]; linarith
  have hyp : 0 < y := lt_of_lt_of_le hhp hyge
  let z : UpperHalfPlane := ⟨zc, by simpa [zc] using hyp⟩
  refine ⟨z, ?_, ?_⟩
  · change -Real.sqrt 2 / 2 ≤ zc.re ∧ zc.re ≤ 1 / 2 ∧ 1 ≤ normSq zc
    simp only [zc, Complex.add_re, ofReal_re, Complex.mul_re, Complex.mul_im, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, mul_one, zero_add]
    refine ⟨hxl, hxr, ?_⟩
    rw [normSq_apply]
    simp only [zc, Complex.add_re, ofReal_re, Complex.mul_re, Complex.mul_im, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, mul_one, zero_add]
    have hy0 : 0 ≤ y := hyp.le
    have hmul : 0 ≤ (y - semicircleHeight x) * (y + semicircleHeight x) :=
      mul_nonneg (sub_nonneg.mpr hyge) (add_nonneg hy0 hh0)
    nlinarith
  · have hpolar := cuspPolar_eq_cuspExponential (1 + Real.sqrt 2)
      (ne_of_gt hw) semicircleHeight x ht
    simpa [z, zc, y] using hpolar.symm.trans hqeq

/-- Every finite real scalar value already occurs on the closed Fuchsian fundamental triangle. -/
theorem exists_fundamentalTriangle_sourceScalarTriangleMap_eq_real
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (a : ℝ) :
    ∃ z : UpperHalfPlane, z ∈ fundamentalTriangle ∧
      sourceScalarTriangleMap S (z : ℂ) = (a : ℂ) := by
  obtain ⟨q, hqfront, hqne, hqval⟩ :=
    exists_sourceFrontier_scalarClosureMap_eq_real S a
  obtain ⟨z, hz, hzq⟩ :=
    exists_fundamentalTriangle_cuspExponential_eq_of_frontier_ne_cusp hqfront hqne
  refine ⟨z, hz, ?_⟩
  simpa only [sourceScalarTriangleMap, Function.comp_apply, hzq] using hqval

/-- On the closed seed side of the right Schwarz double, the reflected function is definitionally
the original scalar triangle map. -/
theorem sourceScalarRightDoubleMap_eq_seed_of_re_le_public
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z.re ≤ 1 / 2) :
    sourceScalarRightDoubleMap S z = sourceScalarTriangleMap S z := by
  apply TauCeti.lineSchwarzReflection_of_coord_im_nonneg
    (sourceScalarTriangleMap S) Complex.I_ne_zero one_ne_zero
  rw [sourceRight_coord_im]
  linarith

private theorem sourceOpenChamber_mem_fundamentalTriangle
    {w : ℂ} (hw : w ∈ sourceOpenChamber) :
    (⟨w, hw.2.2.1⟩ : UpperHalfPlane) ∈ fundamentalTriangle := by
  exact ⟨hw.1.le, hw.2.1.le, hw.2.2.2.le⟩

private theorem sourceRight_sourceOpenChamber_mem_rightFundamentalTriangle
    {w : ℂ} (hw : w ∈ sourceOpenChamber) :
    (⟨sourceRight w, by simpa [sourceRight] using hw.2.2.1⟩ : UpperHalfPlane) ∈
      rightFundamentalTriangle := by
  change 1 / 2 ≤ (sourceRight w).re ∧
    (sourceRight w).re ≤ 1 + Real.sqrt 2 / 2 ∧
      1 ≤ normSq (1 - sourceRight w)
  rw [sourceRight_re]
  refine ⟨by linarith [hw.2.1], by linarith [hw.1], ?_⟩
  have heq : normSq (1 - sourceRight w) = normSq w := by
    simp [sourceRight, normSq_apply]
  rw [heq]
  exact hw.2.2.2.le

/-- The first right-side Schwarz double already realizes every finite complex value on the
closed doubled (orientation-preserving) fundamental region. -/
theorem sourceScalarRightDoubleMap_surjective_on_orientedFundamentalRegion
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (q : ℂ) :
    ∃ z : UpperHalfPlane, z ∈ orientedFundamentalRegion ∧
      sourceScalarRightDoubleMap S (z : ℂ) = q := by
  let d : ℝ := scalarTriangleDenominator (sourceCuspCircle S)
    (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S)
  have hd : d ≠ 0 := by
    exact scalarTriangleDenominator_ne_zero
      (sourceOrderThreeCircle_ne_cusp S) (sourceOtherEllipticCircle_ne_cusp S)
        (sourceOrderThreeCircle_ne_otherElliptic S)
  rcases lt_trichotomy (d * q.im) 0 with hneg | hzero | hpos
  · have hconj : (starRingEnd ℂ) q ∈ signedHalfPlane d := by
      change 0 < d * ((starRingEnd ℂ) q).im
      rw [starRingEnd_apply, Complex.star_def, Complex.conj_im]
      linarith
    obtain ⟨w, hw, hwval⟩ := (sourceScalarOpenChamberMap_bijOn S
      (sourceOrderThreeCircle_ne_otherElliptic S)).surjOn hconj
    let z : UpperHalfPlane :=
      ⟨sourceRight w, by simpa [sourceRight] using hw.2.2.1⟩
    have hwDouble : w ∈ sourceRightDouble :=
      sourceOpenChamber_subset_sourceRightDouble hw
    have hwmap : sourceScalarRightDoubleMap S w = (starRingEnd ℂ) q := by
      calc
        sourceScalarRightDoubleMap S w = sourceScalarTriangleMap S w :=
          sourceScalarRightDoubleMap_eq_seed S hw
        _ = sourceScalarOpenChamberMap S w :=
          sourceScalarTriangleMap_eq_open_of_mem S hw
        _ = (starRingEnd ℂ) q := hwval
    refine ⟨z, Or.inr (sourceRight_sourceOpenChamber_mem_rightFundamentalTriangle hw), ?_⟩
    change sourceScalarRightDoubleMap S (sourceRight w) = q
    rw [sourceScalarRightDoubleMap_reflection S hwDouble, hwmap]
    simp
  · have hqim : q.im = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left hd
    obtain ⟨z, hz, hzval⟩ :=
      exists_fundamentalTriangle_sourceScalarTriangleMap_eq_real S q.re
    refine ⟨z, Or.inl hz, ?_⟩
    rw [sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hz.2.1]
    simpa [Complex.ext_iff, hqim] using hzval
  · have hqmem : q ∈ signedHalfPlane d := hpos
    obtain ⟨w, hw, hwval⟩ := (sourceScalarOpenChamberMap_bijOn S
      (sourceOrderThreeCircle_ne_otherElliptic S)).surjOn hqmem
    let z : UpperHalfPlane := ⟨w, hw.2.2.1⟩
    refine ⟨z, Or.inl (sourceOpenChamber_mem_fundamentalTriangle hw), ?_⟩
    calc
      sourceScalarRightDoubleMap S w = sourceScalarTriangleMap S w :=
        sourceScalarRightDoubleMap_eq_seed S hw
      _ = sourceScalarOpenChamberMap S w :=
        sourceScalarTriangleMap_eq_open_of_mem S hw
      _ = q := hwval


end SphereSixComplex.Periods.SourceChamberTopology
