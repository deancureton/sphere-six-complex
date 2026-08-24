module

public import SphereSixComplex.Periods.Uniformization.ScalarTriangleSeed
import all SphereSixComplex.Periods.Uniformization.ScalarTriangleSeed
public import SphereSixComplex.Periods.Uniformization.FiniteCornerReflection
import all SphereSixComplex.Periods.Uniformization.FiniteCornerReflection
public import TauCeti.Analysis.Complex.Conformal.Reflection.Line
import all TauCeti.Analysis.Complex.Conformal.Reflection.Line

@[expose] public section

/-!
# Schwarz reflection of the scalar source-triangle coordinate

The right vertical side is the first completely concrete doubled chamber.  Its symmetric open
double is cut out by the original circular inequality and its reflected copy.  Tau Ceti's affine
line reflection theorem then extends the scalar Carathéodory seed holomorphically across the seam.

The last two theorems record the algebraic payoff needed globally: scalar reflection identities
across the pairs of sides imply invariance under the holomorphic generators `g₁` and `g₂`.
-/

open Complex Filter Metric Set Topology
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods.TriangleReflections

/-- The open union of the source chamber, its right-side reflection, and the intervening seam.
The two norm inequalities are exchanged by the right reflection. -/
def sourceRightDouble : Set ℂ :=
  {z | -Real.sqrt 2 / 2 < z.re ∧ z.re < 1 + Real.sqrt 2 / 2 ∧
    0 < z.im ∧ 1 < normSq z ∧ 1 < normSq (sourceRight z)}

theorem sourceRightDouble_isOpen : IsOpen sourceRightDouble := by
  have hsourceRight : Continuous sourceRight := by
    unfold sourceRight
    fun_prop
  rw [show sourceRightDouble =
      {z : ℂ | -Real.sqrt 2 / 2 < z.re} ∩
        ({z : ℂ | z.re < 1 + Real.sqrt 2 / 2} ∩
          ({z : ℂ | 0 < z.im} ∩
            ({z : ℂ | 1 < normSq z} ∩ {z : ℂ | 1 < normSq (sourceRight z)}))) by
    ext z
    simp [sourceRightDouble]]
  apply (isOpen_lt continuous_const Complex.continuous_re).inter
  apply (isOpen_lt Complex.continuous_re continuous_const).inter
  apply (isOpen_lt continuous_const Complex.continuous_im).inter
  apply (isOpen_lt continuous_const Complex.continuous_normSq).inter
  exact isOpen_lt continuous_const
    (Complex.continuous_normSq.comp hsourceRight)

@[simp] theorem sourceRight_involutive (z : ℂ) : sourceRight (sourceRight z) = z := by
  simp [sourceRight]

theorem sourceRight_re (z : ℂ) : (sourceRight z).re = 1 - z.re := by
  simp [sourceRight]

theorem sourceRight_normSq (z : ℂ) :
    normSq (sourceRight z) = (1 - z.re) ^ 2 + z.im ^ 2 := by
  simp [sourceRight, normSq_apply]
  ring

theorem sourceRightDouble_mapsTo : MapsTo sourceRight sourceRightDouble sourceRightDouble := by
  intro z hz
  rcases hz with ⟨hl, hr, hi, hn, hnr⟩
  refine ⟨?_, ?_, by simpa using hi, ?_, ?_⟩
  · rw [sourceRight_re]
    linarith
  · rw [sourceRight_re]
    linarith
  · simpa using hnr
  · simpa using hn

/-- The affine reflection in the vertical line `re z = 1/2` is `sourceRight`. -/
theorem sourceRight_affineReflection (z : ℂ) :
    ((1 / 2 : ℂ) + I * (starRingEnd ℂ) ((z - (1 / 2 : ℂ)) / I)) = sourceRight z := by
  apply Complex.ext <;>
    simp [sourceRight, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  <;> ring

theorem sourceRight_coord_im (z : ℂ) :
    ((z - (1 / 2 : ℂ)) / I).im = 1 / 2 - z.re := by
  simp [Complex.div_im, Complex.normSq_apply]

theorem sourceOpenChamber_subset_sourceRightDouble :
    sourceOpenChamber ⊆ sourceRightDouble := by
  rintro z ⟨hl, hr, hi, hn⟩
  refine ⟨hl, ?_, hi, hn, ?_⟩
  · have hs := Real.sqrt_nonneg 2
    linarith
  · rw [sourceRight_normSq]
    have hsq : z.re ^ 2 < (1 - z.re) ^ 2 := by nlinarith
    rw [normSq_apply] at hn
    nlinarith

private theorem semicircleHeight_one_half_reflection :
    semicircleHeight (1 / 2 : ℝ) = Real.sqrt 3 / 2 := by
  rw [semicircleHeight, max_eq_right (by norm_num : (0 : ℝ) ≤ 1 - (1 / 2) ^ 2)]
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ht : 0 ≤ Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) := Real.sqrt_nonneg _
  have ht2 : (Real.sqrt (1 - (1 / 2 : ℝ) ^ 2)) ^ 2 =
      1 - (1 / 2 : ℝ) ^ 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- A finite point of the right vertical side maps to the right radial component of the bounded
chamber frontier. -/
theorem cuspExponential_mem_source_frontier_of_rightSide {z : ℂ}
    (hre : z.re = 1 / 2) (him : 0 < z.im) (hnorm : 1 < normSq z) :
    cuspExponential (1 + Real.sqrt 2) z ∈ frontier sourceBoundedChamber := by
  let width : ℝ := 1 + Real.sqrt 2
  let t : ℝ := Real.exp
    (-2 * Real.pi * (z.im - semicircleHeight (1 / 2)) / width)
  have hwidth : 0 < width := by dsimp [width]; positivity
  have hheight : semicircleHeight (1 / 2) < z.im := by
    rw [semicircleHeight_one_half_reflection]
    have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [normSq_apply, hre] at hnorm
    nlinarith
  have htpos : 0 < t := Real.exp_pos _
  have htlt : t < 1 := by
    dsimp [t]
    rw [Real.exp_lt_one_iff]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hdiff : 0 < z.im - semicircleHeight (1 / 2) := sub_pos.mpr hheight
    have hnum : -2 * Real.pi * (z.im - semicircleHeight (1 / 2)) < 0 := by
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hpi) hdiff
    exact div_neg_of_neg_of_pos hnum hwidth
  have hzrepr : z = ((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have heq : cuspExponential width z =
      cuspPolar width semicircleHeight ((1 / 2 : ℝ), t) := by
    rw [hzrepr]
    exact cuspExponential_eq_cuspPolar width hwidth.ne' semicircleHeight _ _
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨((1 / 2 : ℝ), t), ?_, by simpa [width] using heq.symm⟩
  apply (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) _).2
  exact ⟨⟨⟨by
    have hs := Real.sqrt_nonneg 2
    linarith, le_rfl⟩, htpos.le, htlt.le⟩, Or.inr (Or.inl rfl)⟩

/-- The scalar triangle seed is real on the finite right side. -/
theorem sourceScalarTriangleMap_im_eq_zero_of_rightSide
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hre : z.re = 1 / 2) (him : 0 < z.im) (hnorm : 1 < normSq z) :
    (sourceScalarTriangleMap S z).im = 0 := by
  rw [sourceScalarTriangleMap, Function.comp_apply]
  exact sourceScalarClosureMap_im_eq_zero_of_frontier S
    (cuspExponential_mem_source_frontier_of_rightSide hre him hnorm)

private theorem sourceRightDouble_closedPositive_mapsTo
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    MapsTo (cuspExponential (1 + Real.sqrt 2))
      (sourceRightDouble ∩ {z : ℂ | 0 ≤ ((z - (1 / 2 : ℂ)) / I).im})
      (closure sourceBoundedChamber \ {sourceCuspVertex}) := by
  intro z hz
  rcases hz with ⟨⟨hl, _hrwide, hi, hn, _hnr⟩, hcoord⟩
  change 0 ≤ ((z - (1 / 2 : ℂ)) / I).im at hcoord
  have hrele : z.re ≤ 1 / 2 := by
    rw [sourceRight_coord_im] at hcoord
    linarith
  refine ⟨?_, ?_⟩
  · rcases hrele.lt_or_eq with hre | hre
    · apply subset_closure
      exact ⟨z, ⟨hl, hre, hi, hn⟩, rfl⟩
    · exact frontier_subset_closure
        (cuspExponential_mem_source_frontier_of_rightSide hre hi hn)
  · simpa [sourceCuspVertex] using cuspExponential_ne_zero (1 + Real.sqrt 2) z

theorem sourceScalarTriangleMap_continuousOn_rightClosedPositive
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousOn (sourceScalarTriangleMap S)
      (sourceRightDouble ∩ {z : ℂ | 0 ≤ ((z - (1 / 2 : ℂ)) / I).im}) := by
  exact (sourceScalarClosureMap_continuousOn_away_cusp S).comp
    (cuspExponential_continuous (1 + Real.sqrt 2)).continuousOn
    (sourceRightDouble_closedPositive_mapsTo S)

private theorem sourceRightDouble_openPositive_subset :
    sourceRightDouble ∩ {z : ℂ | 0 < ((z - (1 / 2 : ℂ)) / I).im} ⊆
      sourceOpenChamber := by
  rintro z ⟨⟨hl, _hrwide, hi, hn, _hnr⟩, hcoord⟩
  change 0 < ((z - (1 / 2 : ℂ)) / I).im at hcoord
  rw [sourceRight_coord_im] at hcoord
  exact ⟨hl, by linarith, hi, hn⟩

private theorem sourceScalarTriangleMap_differentiableOn_sourceOpen
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    DifferentiableOn ℂ (sourceScalarTriangleMap S) sourceOpenChamber := by
  exact (sourceScalarOpenChamberMap_differentiableOn S
    (sourceOrderThreeCircle_ne_otherElliptic S)).congr
      (fun z hz => sourceScalarTriangleMap_eq_open_of_mem S hz)

private theorem sourceScalarTriangleMap_rightLine
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ∀ z ∈ sourceRightDouble, ((z - (1 / 2 : ℂ)) / I).im = 0 →
      ((sourceScalarTriangleMap S z - 0) / 1).im = 0 := by
  intro z hz hcoord
  rw [sourceRight_coord_im] at hcoord
  have hre : z.re = 1 / 2 := by linarith
  simpa using sourceScalarTriangleMap_im_eq_zero_of_rightSide S hre hz.2.2.1 hz.2.2.2.1

/-- The explicit scalar Schwarz-reflection extension across the right side. -/
def sourceScalarRightDoubleMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℂ → ℂ :=
  TauCeti.lineSchwarzReflection (1 / 2 : ℂ) I 0 1 (sourceScalarTriangleMap S)

theorem sourceScalarRightDoubleMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    DifferentiableOn ℂ (sourceScalarRightDoubleMap S) sourceRightDouble := by
  apply TauCeti.differentiableOn_lineSchwarzReflection_of_symmetric
    (f := sourceScalarTriangleMap S) Complex.I_ne_zero sourceRightDouble_isOpen
  · intro z hz
    change ((1 / 2 : ℂ) + I * (starRingEnd ℂ) ((z - (1 / 2 : ℂ)) / I)) ∈
      sourceRightDouble
    rw [sourceRight_affineReflection]
    exact sourceRightDouble_mapsTo hz
  · exact sourceScalarTriangleMap_continuousOn_rightClosedPositive S
  · exact (sourceScalarTriangleMap_differentiableOn_sourceOpen S).mono
      sourceRightDouble_openPositive_subset
  · exact sourceScalarTriangleMap_rightLine S

theorem sourceScalarRightDoubleMap_eq_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    EqOn (sourceScalarRightDoubleMap S) (sourceScalarTriangleMap S) sourceOpenChamber := by
  intro z hz
  apply TauCeti.lineSchwarzReflection_of_coord_im_nonneg
    (sourceScalarTriangleMap S) Complex.I_ne_zero one_ne_zero
  rw [sourceRight_coord_im]
  linarith [hz.2.1]

theorem sourceScalarRightDoubleMap_reflection
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceRightDouble) :
    sourceScalarRightDoubleMap S (sourceRight z) =
      (starRingEnd ℂ) (sourceScalarRightDoubleMap S z) := by
  have h := TauCeti.lineSchwarzReflection_sourceReflection
    (f := sourceScalarTriangleMap S) Complex.I_ne_zero one_ne_zero
      (sourceScalarTriangleMap_rightLine S) hz
  rw [sourceRight_affineReflection] at h
  simpa only [sourceScalarRightDoubleMap, sub_zero, div_one, one_mul, zero_add] using h

/-! ## The left-side double -/

/-- The corresponding open double across the left vertical side. -/
def sourceLeftDouble : Set ℂ :=
  {z | -Real.sqrt 2 - 1 / 2 < z.re ∧ z.re < 1 / 2 ∧
    0 < z.im ∧ 1 < normSq z ∧ 1 < normSq (sourceLeft z)}

theorem sourceLeftDouble_isOpen : IsOpen sourceLeftDouble := by
  have hsourceLeft : Continuous sourceLeft := by
    unfold sourceLeft
    fun_prop
  rw [show sourceLeftDouble =
      {z : ℂ | -Real.sqrt 2 - 1 / 2 < z.re} ∩
        ({z : ℂ | z.re < 1 / 2} ∩
          ({z : ℂ | 0 < z.im} ∩
            ({z : ℂ | 1 < normSq z} ∩ {z : ℂ | 1 < normSq (sourceLeft z)}))) by
    ext z
    simp [sourceLeftDouble]]
  apply (isOpen_lt continuous_const Complex.continuous_re).inter
  apply (isOpen_lt Complex.continuous_re continuous_const).inter
  apply (isOpen_lt continuous_const Complex.continuous_im).inter
  apply (isOpen_lt continuous_const Complex.continuous_normSq).inter
  exact isOpen_lt continuous_const (Complex.continuous_normSq.comp hsourceLeft)

@[simp] theorem sourceLeft_involutive (z : ℂ) : sourceLeft (sourceLeft z) = z := by
  simp [sourceLeft]

theorem sourceLeft_re (z : ℂ) : (sourceLeft z).re = -Real.sqrt 2 - z.re := by
  simp [sourceLeft]

theorem sourceLeft_normSq (z : ℂ) :
    normSq (sourceLeft z) = (Real.sqrt 2 + z.re) ^ 2 + z.im ^ 2 := by
  simp [sourceLeft, normSq_apply]
  ring

theorem sourceLeftDouble_mapsTo : MapsTo sourceLeft sourceLeftDouble sourceLeftDouble := by
  intro z hz
  rcases hz with ⟨hl, hr, hi, hn, hnl⟩
  refine ⟨?_, ?_, by simpa using hi, ?_, ?_⟩
  · rw [sourceLeft_re]
    linarith
  · rw [sourceLeft_re]
    linarith
  · simpa using hnl
  · simpa using hn

/-- The affine reflection in `re z = -sqrt 2 / 2` is `sourceLeft`. -/
theorem sourceLeft_affineReflection (z : ℂ) :
    ((-(Real.sqrt 2 : ℂ) / 2) + (-I) *
      (starRingEnd ℂ) ((z - (-(Real.sqrt 2 : ℂ) / 2)) / (-I))) = sourceLeft z := by
  apply Complex.ext <;>
    simp [sourceLeft, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  <;> ring

theorem sourceLeft_coord_im (z : ℂ) :
    ((z - (-(Real.sqrt 2 : ℂ) / 2)) / (-I)).im = z.re + Real.sqrt 2 / 2 := by
  simp [Complex.div_im, Complex.normSq_apply]
  ring

theorem sourceOpenChamber_subset_sourceLeftDouble :
    sourceOpenChamber ⊆ sourceLeftDouble := by
  rintro z ⟨hl, hr, hi, hn⟩
  refine ⟨?_, hr, hi, hn, ?_⟩
  · have hs := Real.sqrt_nonneg 2
    linarith
  · rw [sourceLeft_normSq]
    rw [normSq_apply] at hn
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsq : z.re ^ 2 < (Real.sqrt 2 + z.re) ^ 2 := by nlinarith
    nlinarith

private theorem semicircleHeight_neg_sqrt_two_half_reflection :
    semicircleHeight (-Real.sqrt 2 / 2) = Real.sqrt 2 / 2 := by
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [semicircleHeight, max_eq_right]
  · have ht : 0 ≤ Real.sqrt (1 - (-Real.sqrt 2 / 2 : ℝ) ^ 2) := Real.sqrt_nonneg _
    have ht2 : (Real.sqrt (1 - (-Real.sqrt 2 / 2 : ℝ) ^ 2)) ^ 2 =
        1 - (-Real.sqrt 2 / 2 : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith)
    nlinarith
  · nlinarith

/-- A finite point of the left vertical side maps to the left radial frontier component. -/
theorem cuspExponential_mem_source_frontier_of_leftSide {z : ℂ}
    (hre : z.re = -Real.sqrt 2 / 2) (him : 0 < z.im) (hnorm : 1 < normSq z) :
    cuspExponential (1 + Real.sqrt 2) z ∈ frontier sourceBoundedChamber := by
  let width : ℝ := 1 + Real.sqrt 2
  let t : ℝ := Real.exp
    (-2 * Real.pi * (z.im - semicircleHeight (-Real.sqrt 2 / 2)) / width)
  have hwidth : 0 < width := by dsimp [width]; positivity
  have hheight : semicircleHeight (-Real.sqrt 2 / 2) < z.im := by
    rw [semicircleHeight_neg_sqrt_two_half_reflection]
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [normSq_apply, hre] at hnorm
    nlinarith
  have htpos : 0 < t := Real.exp_pos _
  have htlt : t < 1 := by
    dsimp [t]
    rw [Real.exp_lt_one_iff]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hdiff : 0 < z.im - semicircleHeight (-Real.sqrt 2 / 2) := sub_pos.mpr hheight
    have hnum : -2 * Real.pi * (z.im - semicircleHeight (-Real.sqrt 2 / 2)) < 0 := by
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hpi) hdiff
    exact div_neg_of_neg_of_pos hnum hwidth
  have hzrepr : z = ((-Real.sqrt 2 / 2 : ℝ) : ℂ) + (z.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have heq : cuspExponential width z =
      cuspPolar width semicircleHeight ((-Real.sqrt 2 / 2 : ℝ), t) := by
    rw [hzrepr]
    exact cuspExponential_eq_cuspPolar width hwidth.ne' semicircleHeight _ _
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨((-Real.sqrt 2 / 2 : ℝ), t), ?_, by simpa [width] using heq.symm⟩
  apply (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) _).2
  exact ⟨⟨⟨le_rfl, by
    have hs := Real.sqrt_nonneg 2
    linarith⟩, htpos.le, htlt.le⟩, Or.inl rfl⟩

/-- The scalar triangle seed is real on the finite left side. -/
theorem sourceScalarTriangleMap_im_eq_zero_of_leftSide
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hre : z.re = -Real.sqrt 2 / 2) (him : 0 < z.im) (hnorm : 1 < normSq z) :
    (sourceScalarTriangleMap S z).im = 0 := by
  rw [sourceScalarTriangleMap, Function.comp_apply]
  exact sourceScalarClosureMap_im_eq_zero_of_frontier S
    (cuspExponential_mem_source_frontier_of_leftSide hre him hnorm)

private theorem sourceLeftDouble_closedPositive_mapsTo
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    MapsTo (cuspExponential (1 + Real.sqrt 2))
      (sourceLeftDouble ∩
        {z : ℂ | 0 ≤ ((z - (-(Real.sqrt 2 : ℂ) / 2)) / (-I)).im})
      (closure sourceBoundedChamber \ {sourceCuspVertex}) := by
  intro z hz
  rcases hz with ⟨⟨_hlwide, hr, hi, hn, _hnl⟩, hcoord⟩
  change 0 ≤ ((z - (-(Real.sqrt 2 : ℂ) / 2)) / (-I)).im at hcoord
  have hrege : -Real.sqrt 2 / 2 ≤ z.re := by
    rw [sourceLeft_coord_im] at hcoord
    linarith
  refine ⟨?_, ?_⟩
  · rcases hrege.lt_or_eq with hre | hre
    · apply subset_closure
      exact ⟨z, ⟨hre, hr, hi, hn⟩, rfl⟩
    · exact frontier_subset_closure
        (cuspExponential_mem_source_frontier_of_leftSide hre.symm hi hn)
  · simpa [sourceCuspVertex] using cuspExponential_ne_zero (1 + Real.sqrt 2) z

theorem sourceScalarTriangleMap_continuousOn_leftClosedPositive
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousOn (sourceScalarTriangleMap S)
      (sourceLeftDouble ∩
        {z : ℂ | 0 ≤ ((z - (-(Real.sqrt 2 : ℂ) / 2)) / (-I)).im}) := by
  exact (sourceScalarClosureMap_continuousOn_away_cusp S).comp
    (cuspExponential_continuous (1 + Real.sqrt 2)).continuousOn
    (sourceLeftDouble_closedPositive_mapsTo S)

private theorem sourceLeftDouble_openPositive_subset :
    sourceLeftDouble ∩
        {z : ℂ | 0 < ((z - (-(Real.sqrt 2 : ℂ) / 2)) / (-I)).im} ⊆
      sourceOpenChamber := by
  rintro z ⟨⟨_hlwide, hr, hi, hn, _hnl⟩, hcoord⟩
  change 0 < ((z - (-(Real.sqrt 2 : ℂ) / 2)) / (-I)).im at hcoord
  rw [sourceLeft_coord_im] at hcoord
  exact ⟨by linarith, hr, hi, hn⟩

private theorem sourceScalarTriangleMap_leftLine
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ∀ z ∈ sourceLeftDouble,
      ((z - (-(Real.sqrt 2 : ℂ) / 2)) / (-I)).im = 0 →
      ((sourceScalarTriangleMap S z - 0) / 1).im = 0 := by
  intro z hz hcoord
  rw [sourceLeft_coord_im] at hcoord
  have hre : z.re = -Real.sqrt 2 / 2 := by linarith
  simpa using sourceScalarTriangleMap_im_eq_zero_of_leftSide S hre
    hz.2.2.1 hz.2.2.2.1

/-- The explicit scalar Schwarz-reflection extension across the left side. -/
def sourceScalarLeftDoubleMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℂ → ℂ :=
  TauCeti.lineSchwarzReflection (-(Real.sqrt 2 : ℂ) / 2) (-I) 0 1
    (sourceScalarTriangleMap S)

theorem sourceScalarLeftDoubleMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    DifferentiableOn ℂ (sourceScalarLeftDoubleMap S) sourceLeftDouble := by
  apply TauCeti.differentiableOn_lineSchwarzReflection_of_symmetric
    (f := sourceScalarTriangleMap S) (by simp) sourceLeftDouble_isOpen
  · intro z hz
    change (-(Real.sqrt 2 : ℂ) / 2 + (-I) *
      (starRingEnd ℂ) ((z - (-(Real.sqrt 2 : ℂ) / 2)) / (-I))) ∈ sourceLeftDouble
    rw [sourceLeft_affineReflection]
    exact sourceLeftDouble_mapsTo hz
  · exact sourceScalarTriangleMap_continuousOn_leftClosedPositive S
  · exact (sourceScalarTriangleMap_differentiableOn_sourceOpen S).mono
      sourceLeftDouble_openPositive_subset
  · exact sourceScalarTriangleMap_leftLine S

theorem sourceScalarLeftDoubleMap_eq_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    EqOn (sourceScalarLeftDoubleMap S) (sourceScalarTriangleMap S) sourceOpenChamber := by
  intro z hz
  apply TauCeti.lineSchwarzReflection_of_coord_im_nonneg
    (sourceScalarTriangleMap S) (by simp) one_ne_zero
  rw [sourceLeft_coord_im]
  linarith [hz.1]

theorem sourceScalarLeftDoubleMap_reflection
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceLeftDouble) :
    sourceScalarLeftDoubleMap S (sourceLeft z) =
      (starRingEnd ℂ) (sourceScalarLeftDoubleMap S z) := by
  have h := TauCeti.lineSchwarzReflection_sourceReflection
    (f := sourceScalarTriangleMap S) (by simp : (-I : ℂ) ≠ 0) one_ne_zero
      (sourceScalarTriangleMap_leftLine S) hz
  rw [sourceLeft_affineReflection] at h
  simpa only [sourceScalarLeftDoubleMap, sub_zero, div_one, one_mul, zero_add] using h

/-! ## Generator invariance from scalar side reflections -/

/-- Scalar reflection identities across the right and circular sides imply `g₁`-invariance. -/
theorem invariant_g1_of_scalar_side_reflections (F : ℂ → ℂ)
    (hright : ∀ z : ℂ, F (sourceRight z) = (starRingEnd ℂ) (F z))
    (hcircle : ∀ z : ℂ, F (sourceCircle z) = (starRingEnd ℂ) (F z))
    (z : UpperHalfPlane) :
    F (((fuchsianSourceAction g₁ • z : UpperHalfPlane) : ℂ)) = F (z : ℂ) := by
  have hprod := congrArg ((↑) : UpperHalfPlane → ℂ) (sourceRight_sourceCircle z)
  calc
    F (((fuchsianSourceAction g₁ • z : UpperHalfPlane) : ℂ)) =
        F (sourceRight (sourceCircle (z : ℂ))) :=
      congrArg F hprod.symm
    _ = (starRingEnd ℂ) (F (sourceCircle (z : ℂ))) := hright _
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) (F (z : ℂ))) :=
      congrArg (starRingEnd ℂ) (hcircle _)
    _ = F (z : ℂ) := starRingEnd_self_apply (R := ℂ) _

/-- Scalar reflection identities across the circular and left sides imply `g₂`-invariance. -/
theorem invariant_g2_of_scalar_side_reflections (F : ℂ → ℂ)
    (hcircle : ∀ z : ℂ, F (sourceCircle z) = (starRingEnd ℂ) (F z))
    (hleft : ∀ z : ℂ, F (sourceLeft z) = (starRingEnd ℂ) (F z))
    (z : UpperHalfPlane) :
    F (((fuchsianSourceAction g₂ • z : UpperHalfPlane) : ℂ)) = F (z : ℂ) := by
  have hprod := congrArg ((↑) : UpperHalfPlane → ℂ) (sourceCircle_sourceLeft z)
  calc
    F (((fuchsianSourceAction g₂ • z : UpperHalfPlane) : ℂ)) =
        F (sourceCircle (sourceLeft (z : ℂ))) :=
      congrArg F hprod.symm
    _ = (starRingEnd ℂ) (F (sourceLeft (z : ℂ))) := hcircle _
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) (F (z : ℂ))) :=
      congrArg (starRingEnd ℂ) (hleft _)
    _ = F (z : ℂ) := starRingEnd_self_apply (R := ℂ) _


end SphereSixComplex.Periods.SourceChamberTopology
