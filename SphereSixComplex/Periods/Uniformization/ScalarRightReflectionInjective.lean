module

public import SphereSixComplex.Periods.Uniformization.ScalarSeedInjective
import all SphereSixComplex.Periods.Uniformization.ScalarSeedInjective

@[expose] public section

/-!
# Injectivity on the right Schwarz double

The original closed half is injective by the Carathéodory/Cayley argument.  Its open interior
lands in one signed half-plane, while the reflected half lands in the opposite signed half-plane.
Consequently the two branches cannot collide, and Tau Ceti's explicit line reflection is
injective on the entire right double.
-/

open Complex Metric Set Topology
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.Periods.TriangleReflections

private def sourceScalarSign (S : ChamberCaratheodorySeed sourceBoundedChamber) : ℝ :=
  scalarTriangleDenominator (sourceCuspCircle S) (sourceOrderThreeCircle S)
    (sourceOtherEllipticCircle S)

private theorem sourceScalarRightDoubleMap_eq_seed_of_re_le
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z.re ≤ 1 / 2) :
    sourceScalarRightDoubleMap S z = sourceScalarTriangleMap S z := by
  apply TauCeti.lineSchwarzReflection_of_coord_im_nonneg
    (sourceScalarTriangleMap S) Complex.I_ne_zero one_ne_zero
  rw [sourceRight_coord_im]
  linarith

private theorem sourceScalarTriangleMap_mem_signed_of_mem_rightDouble_of_re_lt
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceRightDouble) (hre : z.re < 1 / 2) :
    sourceScalarTriangleMap S z ∈ signedHalfPlane (sourceScalarSign S) := by
  have hopen : z ∈ sourceOpenChamber := ⟨hz.1, hre, hz.2.2.1, hz.2.2.2.1⟩
  have himage := (sourceScalarOpenChamberMap_bijOn S
    (sourceOrderThreeCircle_ne_otherElliptic S)).mapsTo hopen
  simpa [sourceScalarSign, sourceScalarTriangleMap_eq_open_of_mem S hopen] using himage

private theorem sourceScalarRightDoubleMap_signed_nonneg_of_re_le
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceRightDouble) (hre : z.re ≤ 1 / 2) :
    0 ≤ sourceScalarSign S * (sourceScalarRightDoubleMap S z).im := by
  rw [sourceScalarRightDoubleMap_eq_seed_of_re_le S hre]
  rcases hre.lt_or_eq with hlt | heq
  · exact (sourceScalarTriangleMap_mem_signed_of_mem_rightDouble_of_re_lt S hz hlt).le
  · have him := sourceScalarTriangleMap_im_eq_zero_of_rightSide S heq
      hz.2.2.1 hz.2.2.2.1
    rw [him, mul_zero]

private theorem sourceRight_mem_sourceOpen_of_mem_rightDouble_of_re_gt
    {z : ℂ} (hz : z ∈ sourceRightDouble) (hre : 1 / 2 < z.re) :
    sourceRight z ∈ sourceOpenChamber := by
  have hr := sourceRightDouble_mapsTo hz
  refine ⟨hr.1, ?_, hr.2.2.1, hr.2.2.2.1⟩
  rw [sourceRight_re]
  linarith

private theorem sourceScalarRightDoubleMap_eq_conj_seed_of_re_gt
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceRightDouble) (hre : 1 / 2 < z.re) :
    sourceScalarRightDoubleMap S z =
      (starRingEnd ℂ) (sourceScalarTriangleMap S (sourceRight z)) := by
  have hrmem := sourceRightDouble_mapsTo hz
  have hrle : (sourceRight z).re ≤ 1 / 2 := by
    rw [sourceRight_re]
    linarith
  have hreflect := sourceScalarRightDoubleMap_reflection S hz
  have hback := congrArg (starRingEnd ℂ) hreflect
  have hbranch : sourceScalarRightDoubleMap S z =
      (starRingEnd ℂ) (sourceScalarRightDoubleMap S (sourceRight z)) := by
    simpa using hback.symm
  rw [hbranch, sourceScalarRightDoubleMap_eq_seed_of_re_le S hrle]

private theorem sourceScalarRightDoubleMap_signed_neg_of_re_gt
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceRightDouble) (hre : 1 / 2 < z.re) :
    sourceScalarSign S * (sourceScalarRightDoubleMap S z).im < 0 := by
  rw [sourceScalarRightDoubleMap_eq_conj_seed_of_re_gt S hz hre]
  have hrDouble := sourceRightDouble_mapsTo hz
  have hrlt : (sourceRight z).re < 1 / 2 := by
    rw [sourceRight_re]
    linarith
  have hpos := sourceScalarTriangleMap_mem_signed_of_mem_rightDouble_of_re_lt
    S hrDouble hrlt
  change 0 < sourceScalarSign S * (sourceScalarTriangleMap S (sourceRight z)).im at hpos
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_im]
  linarith

/-- The explicit scalar Schwarz extension is injective throughout the open right double. -/
theorem sourceScalarRightDoubleMap_injOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    InjOn (sourceScalarRightDoubleMap S) sourceRightDouble := by
  intro z hz w hw hzw
  by_cases hzle : z.re ≤ 1 / 2
  · by_cases hwle : w.re ≤ 1 / 2
    · apply sourceScalarTriangleMap_injOn_rightClosedPositive S
        ⟨hz, hzle⟩ ⟨hw, hwle⟩
      simpa [sourceScalarRightDoubleMap_eq_seed_of_re_le S hzle,
        sourceScalarRightDoubleMap_eq_seed_of_re_le S hwle] using hzw
    · have hwgt : 1 / 2 < w.re := lt_of_not_ge hwle
      have hznonneg := sourceScalarRightDoubleMap_signed_nonneg_of_re_le S hz hzle
      have hwneg := sourceScalarRightDoubleMap_signed_neg_of_re_gt S hw hwgt
      have him := congrArg Complex.im hzw
      rw [him] at hznonneg
      exact ((not_lt_of_ge hznonneg) hwneg).elim
  · have hzgt : 1 / 2 < z.re := lt_of_not_ge hzle
    by_cases hwle : w.re ≤ 1 / 2
    · have hzneg := sourceScalarRightDoubleMap_signed_neg_of_re_gt S hz hzgt
      have hwnonneg := sourceScalarRightDoubleMap_signed_nonneg_of_re_le S hw hwle
      have him := congrArg Complex.im hzw
      rw [him] at hzneg
      exact ((not_lt_of_ge hwnonneg) hzneg).elim
    · have hwgt : 1 / 2 < w.re := lt_of_not_ge hwle
      have hzbranch := sourceScalarRightDoubleMap_eq_conj_seed_of_re_gt S hz hzgt
      have hwbranch := sourceScalarRightDoubleMap_eq_conj_seed_of_re_gt S hw hwgt
      have hseedConj :
          (starRingEnd ℂ) (sourceScalarTriangleMap S (sourceRight z)) =
            (starRingEnd ℂ) (sourceScalarTriangleMap S (sourceRight w)) := by
        simpa only [hzbranch, hwbranch] using hzw
      have hseed : sourceScalarTriangleMap S (sourceRight z) =
          sourceScalarTriangleMap S (sourceRight w) := by
        simpa using congrArg (starRingEnd ℂ) hseedConj
      have hrz := sourceRightDouble_mapsTo hz
      have hrw := sourceRightDouble_mapsTo hw
      have hrzle : (sourceRight z).re ≤ 1 / 2 := by rw [sourceRight_re]; linarith
      have hrwle : (sourceRight w).re ≤ 1 / 2 := by rw [sourceRight_re]; linarith
      have hrEq := sourceScalarTriangleMap_injOn_rightClosedPositive S
        ⟨hrz, hrzle⟩ ⟨hrw, hrwle⟩ hseed
      simpa using congrArg sourceRight hrEq

/-- The right-side extension is conformal, including all points of the reflected seam. -/
theorem sourceScalarRightDoubleMap_conformalAt
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceRightDouble) :
    ConformalAt (sourceScalarRightDoubleMap S) z :=
  TauCeti.DifferentiableOn.conformalAt_of_isOpen_of_injOn
    (sourceScalarRightDoubleMap_differentiableOn S) sourceRightDouble_isOpen
    (sourceScalarRightDoubleMap_injOn S) hz


end SphereSixComplex.Periods.SourceChamberTopology
