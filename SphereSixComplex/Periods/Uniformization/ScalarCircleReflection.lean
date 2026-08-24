module

public import SphereSixComplex.Periods.Uniformization.ScalarTriangleReflection
import all SphereSixComplex.Periods.Uniformization.ScalarTriangleReflection
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import all Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import TauCeti.Analysis.Complex.Conformal.Reflection.Arc
import all TauCeti.Analysis.Complex.Conformal.Reflection.Arc

@[expose] public section

/-!
# Circular Schwarz reflection of the scalar triangle seed

The negative Cayley coordinate sends the unit-circle exterior to the upper half-plane and
intertwines inversion in the circle with complex conjugation.  Restricting that chart to a
reflection-symmetric double lets Tau Ceti's charted Schwarz-reflection theorem extend the scalar
triangle seed across its circular side.
-/

open Complex Filter Metric Set Topology
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.Periods.TriangleReflections

/-- Cayley coordinate oriented so that the unit-circle exterior has positive imaginary part. -/
def sourceCircleCayley (z : ℂ) : ℂ := -boundaryCayley 1 z

/-- Inverse to `sourceCircleCayley` away from its pole `I`. -/
def sourceCircleCayleyInv (w : ℂ) : ℂ := boundaryCayleyInv 1 (-w)

theorem sourceCircleCayleyInv_sourceCircleCayley {z : ℂ} (hz : z ≠ 1) :
    sourceCircleCayleyInv (sourceCircleCayley z) = z := by
  simpa [sourceCircleCayley, sourceCircleCayleyInv] using
    (boundaryCayleyInv_boundaryCayley (zeta := (1 : ℂ)) (z := z) one_ne_zero hz)

theorem sourceCircleCayley_sourceCircleCayleyInv {w : ℂ} (hw : w ≠ I) :
    sourceCircleCayley (sourceCircleCayleyInv w) = w := by
  have hn : -w ≠ -I := by
    intro h
    apply hw
    simpa using congrArg Neg.neg h
  simpa [sourceCircleCayley, sourceCircleCayleyInv] using congrArg Neg.neg
    (boundaryCayley_boundaryCayleyInv (zeta := (1 : ℂ)) (w := -w) one_ne_zero hn)

theorem sourceCircleCayley_ne_I {z : ℂ} (hz : z ≠ 1) :
    sourceCircleCayley z ≠ I := by
  intro h
  have h' := congrArg sourceCircleCayleyInv h
  rw [sourceCircleCayleyInv_sourceCircleCayley hz] at h'
  have hI : sourceCircleCayleyInv I = 0 := by
    simp [sourceCircleCayleyInv, boundaryCayleyInv]
  rw [hI] at h'
  subst z
  have hzero : sourceCircleCayley 0 = -I := by
    simp [sourceCircleCayley, boundaryCayley]
  rw [hzero] at h
  have him := congrArg Complex.im h
  norm_num at him

theorem sourceCircleCayleyInv_ne_one {w : ℂ} (hw : w ≠ I) :
    sourceCircleCayleyInv w ≠ 1 := by
  intro h
  have h' := congrArg sourceCircleCayley h
  rw [sourceCircleCayley_sourceCircleCayleyInv hw] at h'
  norm_num [sourceCircleCayley, boundaryCayley] at h'
  subst w
  have hzero : sourceCircleCayleyInv 0 = -1 := by
    norm_num [sourceCircleCayleyInv, boundaryCayleyInv]
  rw [hzero] at h
  norm_num at h

/-- The negative Cayley transform as an open partial homeomorphism of punctured planes. -/
def sourceCircleCayleyChartBase : OpenPartialHomeomorph ℂ ℂ where
  toFun := sourceCircleCayley
  invFun := sourceCircleCayleyInv
  source := ({1} : Set ℂ)ᶜ
  target := ({I} : Set ℂ)ᶜ
  map_source' := fun _ hz => by
    exact Set.mem_compl_singleton_iff.mpr
      (sourceCircleCayley_ne_I (Set.mem_compl_singleton_iff.mp hz))
  map_target' := fun _ hw => by
    exact Set.mem_compl_singleton_iff.mpr
      (sourceCircleCayleyInv_ne_one (Set.mem_compl_singleton_iff.mp hw))
  left_inv' := fun _ hz =>
    sourceCircleCayleyInv_sourceCircleCayley (Set.mem_compl_singleton_iff.mp hz)
  right_inv' := fun _ hw =>
    sourceCircleCayley_sourceCircleCayleyInv (Set.mem_compl_singleton_iff.mp hw)
  open_source := isClosed_singleton.isOpen_compl
  open_target := isClosed_singleton.isOpen_compl
  continuousOn_toFun := by
    intro z hz
    apply (differentiableAt_boundaryCayley ?_).neg.continuousAt.continuousWithinAt
    exact sub_ne_zero.mpr (Ne.symm (Set.mem_compl_singleton_iff.mp hz))
  continuousOn_invFun := by
    intro w hw
    have hwi : w ≠ I := Set.mem_compl_singleton_iff.mp hw
    have hden : -w + I ≠ 0 := by
      intro hzero
      apply hwi
      linear_combination -hzero
    have hd : DifferentiableAt ℂ (fun u : ℂ => boundaryCayleyInv 1 (-u)) w :=
      (differentiableAt_boundaryCayleyInv hden).comp w differentiableAt_id.neg
    change ContinuousWithinAt (fun u : ℂ => boundaryCayleyInv 1 (-u)) ({I} : Set ℂ)ᶜ w
    exact hd.continuousAt.continuousWithinAt

@[simp] theorem sourceCircleCayleyChartBase_apply (z : ℂ) :
    sourceCircleCayleyChartBase z = sourceCircleCayley z := rfl

@[simp] theorem sourceCircleCayleyChartBase_symm_apply (w : ℂ) :
    sourceCircleCayleyChartBase.symm w = sourceCircleCayleyInv w := rfl

theorem sourceCircleCayley_im (z : ℂ) :
    (sourceCircleCayley z).im =
      (normSq z - 1) / normSq (1 - z) := by
  rw [sourceCircleCayley, neg_im, boundaryCayley_im]
  simp
  ring

theorem sourceCircleCayley_sourceReflection {z : ℂ} (hz : z ≠ 0) :
    sourceCircleCayley (sourceCircle z) = (starRingEnd ℂ) (sourceCircleCayley z) := by
  by_cases hz1 : z = 1
  · subst z
    simp [sourceCircleCayley, boundaryCayley, sourceCircle]
  have hc1 : (starRingEnd ℂ) z ≠ 1 := by
    intro h
    apply hz1
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  unfold sourceCircleCayley boundaryCayley sourceCircle
  rw [map_neg, map_div₀, map_mul, map_add, map_sub, map_one,
    starRingEnd_apply, Complex.star_def, Complex.conj_I]
  field_simp [hz, hz1, hc1]
  ring

/-! ## A symmetric circular double -/

/-- A polynomial presentation of the chamber and its reflection across the unit circle.  The last
two inequalities say that the reflected real part remains between the two vertical sides. -/
def sourceCircleDouble : Set ℂ :=
  {z | 0 < z.im ∧
    -Real.sqrt 2 / 2 < z.re ∧ z.re < 1 / 2 ∧
    (-Real.sqrt 2 / 2) * normSq z < z.re ∧ z.re < (1 / 2) * normSq z}

theorem sourceCircleDouble_isOpen : IsOpen sourceCircleDouble := by
  rw [show sourceCircleDouble =
      {z : ℂ | 0 < z.im} ∩
        ({z : ℂ | -Real.sqrt 2 / 2 < z.re} ∩
          ({z : ℂ | z.re < 1 / 2} ∩
            ({z : ℂ | (-Real.sqrt 2 / 2) * normSq z < z.re} ∩
              {z : ℂ | z.re < (1 / 2) * normSq z}))) by
    ext z
    simp [sourceCircleDouble]]
  apply (isOpen_lt continuous_const Complex.continuous_im).inter
  apply (isOpen_lt continuous_const Complex.continuous_re).inter
  apply (isOpen_lt Complex.continuous_re continuous_const).inter
  apply (isOpen_lt (continuous_const.mul Complex.continuous_normSq)
    Complex.continuous_re).inter
  exact isOpen_lt Complex.continuous_re
    (continuous_const.mul Complex.continuous_normSq)

theorem sourceCircle_re (z : ℂ) :
    (sourceCircle z).re = z.re / normSq z := by
  rw [sourceCircle, inv_re]
  simp

theorem sourceCircle_normSq (z : ℂ) :
    normSq (sourceCircle z) = (normSq z)⁻¹ := by
  simp [sourceCircle, Complex.normSq_inv, Complex.normSq_conj]

theorem sourceCircleDouble_mapsTo : MapsTo sourceCircle sourceCircleDouble sourceCircleDouble := by
  intro z hz
  rcases hz with ⟨hi, hl, hr, hrl, hrr⟩
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hi
  have hn : 0 < normSq z := Complex.normSq_pos.mpr hz0
  change 0 < (sourceCircle z).im ∧
    -Real.sqrt 2 / 2 < (sourceCircle z).re ∧ (sourceCircle z).re < 1 / 2 ∧
    (-Real.sqrt 2 / 2) * normSq (sourceCircle z) < (sourceCircle z).re ∧
    (sourceCircle z).re < (1 / 2) * normSq (sourceCircle z)
  rw [sourceCircle_im, sourceCircle_re, sourceCircle_normSq]
  refine ⟨div_pos hi hn, ?_, ?_, ?_, ?_⟩
  · exact (lt_div_iff₀ hn).2 hrl
  · exact (div_lt_iff₀ hn).2 hrr
  · simpa [div_eq_mul_inv] using (div_lt_div_iff_of_pos_right hn).2 hl
  · simpa [div_eq_mul_inv] using (div_lt_div_iff_of_pos_right hn).2 hr

theorem sourceOpenChamber_subset_sourceCircleDouble :
    sourceOpenChamber ⊆ sourceCircleDouble := by
  rintro z ⟨hl, hr, hi, hn⟩
  refine ⟨hi, hl, hr, ?_, ?_⟩
  · have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  · nlinarith

/-- The Cayley chart restricted exactly to the reflection-symmetric circular double. -/
def sourceCircleCayleyChart : OpenPartialHomeomorph ℂ ℂ :=
  sourceCircleCayleyChartBase.restrOpen sourceCircleDouble sourceCircleDouble_isOpen

@[simp] theorem sourceCircleCayleyChart_apply (z : ℂ) :
    sourceCircleCayleyChart z = sourceCircleCayley z := rfl

@[simp] theorem sourceCircleCayleyChart_symm_apply (w : ℂ) :
    sourceCircleCayleyChart.symm w = sourceCircleCayleyInv w := rfl

theorem sourceCircleCayleyChart_source :
    sourceCircleCayleyChart.source = sourceCircleDouble := by
  rw [sourceCircleCayleyChart, OpenPartialHomeomorph.restrOpen_source]
  apply inter_eq_right.mpr
  intro z hz
  exact Set.mem_compl_singleton_iff.mpr fun h => by
    subst z
    norm_num [sourceCircleDouble] at hz

theorem sourceCircleCayleyChart_differentiableOn :
    DifferentiableOn ℂ sourceCircleCayleyChart sourceCircleCayleyChart.source := by
  rw [sourceCircleCayleyChart_source]
  intro z hz
  change DifferentiableWithinAt ℂ sourceCircleCayley sourceCircleDouble z
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num [sourceCircleDouble] at hz
  exact (differentiableAt_boundaryCayley (sub_ne_zero.mpr (Ne.symm hz1))).neg
    |>.differentiableWithinAt

theorem sourceCircleCayleyChart_target_conj :
    MapsTo (starRingEnd ℂ) sourceCircleCayleyChart.target
      sourceCircleCayleyChart.target := by
  intro w hw
  let z : ℂ := sourceCircleCayleyChart.symm w
  have hzsrc : z ∈ sourceCircleCayleyChart.source :=
    sourceCircleCayleyChart.map_target hw
  have hzD : z ∈ sourceCircleDouble := by
    rwa [sourceCircleCayleyChart_source] at hzsrc
  have hi : 0 < z.im := hzD.1
  have hz0 : z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    exact (ne_of_gt hi) (by simpa using him)
  have hrefD : sourceCircle z ∈ sourceCircleDouble := sourceCircleDouble_mapsTo hzD
  have hrefsrc : sourceCircle z ∈ sourceCircleCayleyChart.source := by
    rwa [sourceCircleCayleyChart_source]
  have hmap := sourceCircleCayleyChart.map_source hrefsrc
  rw [sourceCircleCayleyChart_apply, sourceCircleCayley_sourceReflection hz0] at hmap
  have hzw : sourceCircleCayley z = w := by
    simpa [z] using sourceCircleCayleyChart.right_inv hw
  rw [hzw] at hmap
  exact hmap

theorem sourceCircleCayleyChart_sourceReflection {z : ℂ}
    (hz : z ∈ sourceCircleCayleyChart.source) :
    sourceCircleCayleyChart.symm
        ((starRingEnd ℂ) (sourceCircleCayleyChart z)) = sourceCircle z := by
  have hzD : z ∈ sourceCircleDouble := by
    rwa [sourceCircleCayleyChart_source] at hz
  have hi : 0 < z.im := hzD.1
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hi
  have href : sourceCircle z ∈ sourceCircleCayleyChart.source := by
    rw [sourceCircleCayleyChart_source]
    exact sourceCircleDouble_mapsTo hzD
  have heq : (starRingEnd ℂ) (sourceCircleCayleyChart z) =
      sourceCircleCayleyChart (sourceCircle z) := by
    rw [sourceCircleCayleyChart_apply, sourceCircleCayleyChart_apply]
    exact (sourceCircleCayley_sourceReflection hz0).symm
  rw [heq, sourceCircleCayleyChart.left_inv href]

private theorem sourceCircleCayleyChart_openPositive_subset :
    sourceCircleCayleyChart.source ∩
        {z : ℂ | 0 < (sourceCircleCayleyChart z).im} ⊆ sourceOpenChamber := by
  rintro z ⟨hz, hcoord⟩
  have hzD : z ∈ sourceCircleDouble := by
    rwa [sourceCircleCayleyChart_source] at hz
  rcases hzD with ⟨hi, hl, hr, _hrl, _hrr⟩
  change 0 < (sourceCircleCayleyChart z).im at hcoord
  rw [sourceCircleCayleyChart_apply, sourceCircleCayley_im] at hcoord
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hi
  have hden : 0 < normSq (1 - z) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1.symm)
  have hn : 1 < normSq z := by
    have := (div_pos_iff_of_pos_right hden).mp hcoord
    linarith
  exact ⟨hl, hr, hi, hn⟩

/-! ## Boundary control for the circular seam -/

/-- A point on the upper unit-circle arc maps to the top edge of the cusp rectangle. -/
theorem cuspExponential_mem_source_frontier_of_circleSide {z : ℂ}
    (hl : -Real.sqrt 2 / 2 ≤ z.re) (hr : z.re ≤ 1 / 2)
    (hi : 0 < z.im) (hnorm : normSq z = 1) :
    cuspExponential (1 + Real.sqrt 2) z ∈ frontier sourceBoundedChamber := by
  have harg : 0 ≤ 1 - z.re ^ 2 := by
    rw [normSq_apply] at hnorm
    nlinarith
  have hheight : semicircleHeight z.re = z.im := by
    rw [semicircleHeight, max_eq_right harg]
    have hs : 0 ≤ Real.sqrt (1 - z.re ^ 2) := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt (1 - z.re ^ 2)) ^ 2 = 1 - z.re ^ 2 :=
      Real.sq_sqrt harg
    rw [normSq_apply] at hnorm
    nlinarith
  let width : ℝ := 1 + Real.sqrt 2
  have hwidth : 0 < width := by dsimp [width]; positivity
  have hzrepr : z = (z.re : ℂ) + (z.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have heq : cuspExponential width z =
      cuspPolar width semicircleHeight (z.re, 1) := by
    rw [hzrepr]
    simpa [hheight] using
      (cuspExponential_eq_cuspPolar width hwidth.ne' semicircleHeight z.re z.im)
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨(z.re, 1), ?_, by simpa [width] using heq.symm⟩
  apply (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) _).2
  exact ⟨⟨⟨hl, hr⟩, zero_le_one, le_rfl⟩, Or.inr (Or.inr rfl)⟩

theorem sourceScalarTriangleMap_im_eq_zero_of_circleSide
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hl : -Real.sqrt 2 / 2 ≤ z.re) (hr : z.re ≤ 1 / 2)
    (hi : 0 < z.im) (hnorm : normSq z = 1) :
    (sourceScalarTriangleMap S z).im = 0 := by
  rw [sourceScalarTriangleMap, Function.comp_apply]
  exact sourceScalarClosureMap_im_eq_zero_of_frontier S
    (cuspExponential_mem_source_frontier_of_circleSide hl hr hi hnorm)

private theorem sourceCircleCayleyChart_closedPositive_mapsTo
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    MapsTo (cuspExponential (1 + Real.sqrt 2))
      (sourceCircleCayleyChart.source ∩
        {z : ℂ | 0 ≤ (sourceCircleCayleyChart z).im})
      (closure sourceBoundedChamber \ {sourceCuspVertex}) := by
  intro z hz
  rcases hz with ⟨hzsrc, hcoord⟩
  have hzD : z ∈ sourceCircleDouble := by
    rwa [sourceCircleCayleyChart_source] at hzsrc
  rcases hzD with ⟨hi, hl, hr, _hrl, _hrr⟩
  change 0 ≤ (sourceCircleCayleyChart z).im at hcoord
  rw [sourceCircleCayleyChart_apply, sourceCircleCayley_im] at hcoord
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hi
  have hden : 0 < normSq (1 - z) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1.symm)
  have hn : 1 ≤ normSq z := by
    have hnum := (le_div_iff₀ hden).mp (by simpa using hcoord)
    linarith
  refine ⟨?_, ?_⟩
  · rcases hn.lt_or_eq with hnlt | hneq
    · apply subset_closure
      exact ⟨z, ⟨hl, hr, hi, hnlt⟩, rfl⟩
    · exact frontier_subset_closure
        (cuspExponential_mem_source_frontier_of_circleSide hl.le hr.le hi hneq.symm)
  · simpa [sourceCuspVertex] using cuspExponential_ne_zero (1 + Real.sqrt 2) z

private theorem sourceScalarTriangleMap_continuousOn_circleClosedPositive
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousOn (sourceScalarTriangleMap S)
      (sourceCircleCayleyChart.source ∩
        {z : ℂ | 0 ≤ (sourceCircleCayleyChart z).im}) := by
  exact (sourceScalarClosureMap_continuousOn_away_cusp S).comp
    (cuspExponential_continuous (1 + Real.sqrt 2)).continuousOn
    (sourceCircleCayleyChart_closedPositive_mapsTo S)

private theorem sourceScalarTriangleMap_differentiableOn_circlePositive
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    DifferentiableOn ℂ (sourceScalarTriangleMap S)
      (sourceCircleCayleyChart.source ∩
        {z : ℂ | 0 < (sourceCircleCayleyChart z).im}) := by
  have hseed : DifferentiableOn ℂ (sourceScalarTriangleMap S) sourceOpenChamber :=
    (sourceScalarOpenChamberMap_differentiableOn S
      (sourceOrderThreeCircle_ne_otherElliptic S)).congr
        (fun z hz => sourceScalarTriangleMap_eq_open_of_mem S hz)
  exact hseed.mono sourceCircleCayleyChart_openPositive_subset

private theorem sourceScalarTriangleMap_circleLine
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ∀ z ∈ sourceCircleCayleyChart.source,
      (sourceCircleCayleyChart z).im = 0 → (sourceScalarTriangleMap S z).im = 0 := by
  intro z hz hcoord
  have hzD : z ∈ sourceCircleDouble := by
    rwa [sourceCircleCayleyChart_source] at hz
  rcases hzD with ⟨hi, hl, hr, _hrl, _hrr⟩
  rw [sourceCircleCayleyChart_apply, sourceCircleCayley_im] at hcoord
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hi
  have hden : normSq (1 - z) ≠ 0 :=
    (Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1.symm)).ne'
  have hn : normSq z = 1 := by
    apply sub_eq_zero.mp
    exact (div_eq_zero_iff.mp hcoord).resolve_right hden
  exact sourceScalarTriangleMap_im_eq_zero_of_circleSide S hl.le hr.le hi hn

/-! ## The reflected scalar map -/

/-- The identity chart straightens the target real line. -/
def sourceScalarTargetLineChart : OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.refl ℂ

/-- The explicit charted Schwarz-reflection extension across the source circular side. -/
def sourceScalarCircleDoubleMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℂ → ℂ :=
  TauCeti.chartedSchwarzReflection sourceCircleCayleyChart sourceScalarTargetLineChart
    (sourceScalarTriangleMap S)

theorem sourceScalarCircleDoubleMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    DifferentiableOn ℂ (sourceScalarCircleDoubleMap S) sourceCircleDouble := by
  rw [← sourceCircleCayleyChart_source]
  apply TauCeti.differentiableOn_chartedSchwarzReflection_of_symmetric
    sourceCircleCayleyChart sourceScalarTargetLineChart (sourceScalarTriangleMap S)
  · exact sourceCircleCayleyChart_differentiableOn
  · simpa [sourceScalarTargetLineChart] using
      (differentiableOn_id : DifferentiableOn ℂ id (Set.univ : Set ℂ))
  · exact sourceCircleCayleyChart_target_conj
  · intro w hw
    simpa [sourceScalarTargetLineChart] using hw
  · intro z hz
    simp [sourceScalarTargetLineChart]
  · exact sourceScalarTriangleMap_continuousOn_circleClosedPositive S
  · exact sourceScalarTriangleMap_differentiableOn_circlePositive S
  · intro z hz hcoord
    simpa [sourceScalarTargetLineChart] using
      sourceScalarTriangleMap_circleLine S z hz hcoord

theorem sourceScalarCircleDoubleMap_eq_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    EqOn (sourceScalarCircleDoubleMap S) (sourceScalarTriangleMap S) sourceOpenChamber := by
  intro z hz
  apply TauCeti.chartedSchwarzReflection_of_coord_im_nonneg
    sourceCircleCayleyChart sourceScalarTargetLineChart (sourceScalarTriangleMap S)
  · intro w hw
    simp [sourceScalarTargetLineChart]
  · rw [sourceCircleCayleyChart_source]
    exact sourceOpenChamber_subset_sourceCircleDouble hz
  · rw [sourceCircleCayleyChart_apply, sourceCircleCayley_im]
    have hz1 : z ≠ 1 := by
      have hi : 0 < z.im := hz.2.2.1
      intro h
      subst z
      norm_num at hi
    have hden : 0 < normSq (1 - z) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1.symm)
    exact (div_nonneg_iff.mpr (Or.inl ⟨by linarith [hz.2.2.2], hden.le⟩))

theorem sourceScalarCircleDoubleMap_reflection
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceCircleDouble) :
    sourceScalarCircleDoubleMap S (sourceCircle z) =
      (starRingEnd ℂ) (sourceScalarCircleDoubleMap S z) := by
  have hzsrc : z ∈ sourceCircleCayleyChart.source := by
    rwa [sourceCircleCayleyChart_source]
  have h := TauCeti.chartedSchwarzReflection_sourceReflection
    sourceCircleCayleyChart sourceScalarTargetLineChart (sourceScalarTriangleMap S)
    sourceCircleCayleyChart_target_conj
    (by intro w hw; simpa [sourceScalarTargetLineChart] using hw)
    (by intro w hw; simp [sourceScalarTargetLineChart])
    (by
      intro w hw hcoord
      simpa [sourceScalarTargetLineChart] using
        sourceScalarTriangleMap_circleLine S w hw hcoord)
    hzsrc
  rw [sourceCircleCayleyChart_sourceReflection hzsrc] at h
  simpa [sourceScalarCircleDoubleMap, sourceScalarTargetLineChart] using h


end SphereSixComplex.Periods.SourceChamberTopology
