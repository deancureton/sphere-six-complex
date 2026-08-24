module

public import SphereSixComplex.Periods.Uniformization.ScalarFundamentalBoundary
import all SphereSixComplex.Periods.Uniformization.ScalarFundamentalBoundary
public import SphereSixComplex.Periods.Uniformization.ScalarCircleReflection
import all SphereSixComplex.Periods.Uniformization.ScalarCircleReflection

@[expose] public section

/-!
# Fibre separation on the doubled scalar fundamental region

The Carathéodory boundary map makes the scalar seed injective on the whole closed reflection
triangle (the ideal cusp is not a point of the upper half-plane).  The adjacent reflected triangle
has conjugate values.  Equal values on opposite halves are therefore forced onto the boundary,
where the corresponding points are paired by the orientation-preserving triangle group.
-/

open Complex Metric Set Topology UpperHalfPlane
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.Periods.TriangleReflections

private theorem cuspExponential_mem_sourceClosure_of_mem_fundamentalTriangle
    {z : UpperHalfPlane} (hz : z ∈ fundamentalTriangle) :
    cuspExponential (1 + Real.sqrt 2) (z : ℂ) ∈ closure sourceBoundedChamber := by
  rcases hz with ⟨hl, hr, hn⟩
  by_cases hcircle : normSq (z : ℂ) = 1
  · exact frontier_subset_closure
      (cuspExponential_mem_source_frontier_of_circleSide hl hr z.im_pos hcircle)
  have hn' : 1 < normSq (z : ℂ) := lt_of_le_of_ne hn (Ne.symm hcircle)
  by_cases hleft : (z : ℂ).re = -Real.sqrt 2 / 2
  · exact frontier_subset_closure
      (cuspExponential_mem_source_frontier_of_leftSide hleft z.im_pos hn')
  by_cases hright : (z : ℂ).re = 1 / 2
  · exact frontier_subset_closure
      (cuspExponential_mem_source_frontier_of_rightSide hright z.im_pos hn')
  apply subset_closure
  exact ⟨(z : ℂ),
    ⟨lt_of_le_of_ne hl (Ne.symm hleft), lt_of_le_of_ne hr hright, z.im_pos, hn'⟩, rfl⟩

/-- The scalar triangle seed separates every two finite points of the closed source triangle. -/
theorem sourceScalarTriangleMap_injective_on_fundamentalTriangle
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    {z w : UpperHalfPlane} (hz : z ∈ fundamentalTriangle)
    (hw : w ∈ fundamentalTriangle)
    (hzw : sourceScalarTriangleMap S (z : ℂ) = sourceScalarTriangleMap S (w : ℂ)) :
    z = w := by
  have hze := cuspExponential_mem_sourceClosure_of_mem_fundamentalTriangle hz
  have hwe := cuspExponential_mem_sourceClosure_of_mem_fundamentalTriangle hw
  have hene_z : cuspExponential (1 + Real.sqrt 2) (z : ℂ) ≠ sourceCuspVertex := by
    simpa [sourceCuspVertex] using
      cuspExponential_ne_zero (1 + Real.sqrt 2) (z : ℂ)
  have hene_w : cuspExponential (1 + Real.sqrt 2) (w : ℂ) ≠ sourceCuspVertex := by
    simpa [sourceCuspVertex] using
      cuspExponential_ne_zero (1 + Real.sqrt 2) (w : ℂ)
  have hexp : cuspExponential (1 + Real.sqrt 2) (z : ℂ) =
      cuspExponential (1 + Real.sqrt 2) (w : ℂ) := by
    apply sourceScalarClosureMap_injOn_away_cusp S
      ⟨hze, by simpa using hene_z⟩ ⟨hwe, by simpa using hene_w⟩
    simpa only [sourceScalarTriangleMap, Function.comp_apply] using hzw
  apply UpperHalfPlane.coe_injective
  apply source_cuspExponential_injOn_closedStrip
    ⟨hz.1, hz.2.1⟩ ⟨hw.1, hw.2.1⟩ hexp

private theorem sourceScalarTriangleMap_im_eq_zero_of_mem_fundamental_not_open
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    {z : UpperHalfPlane} (hz : z ∈ fundamentalTriangle)
    (hnot : (z : ℂ) ∉ sourceOpenChamber) :
    (sourceScalarTriangleMap S (z : ℂ)).im = 0 := by
  rcases hz with ⟨hl, hr, hn⟩
  by_cases hcircle : normSq (z : ℂ) = 1
  · exact sourceScalarTriangleMap_im_eq_zero_of_circleSide S hl hr z.im_pos hcircle
  have hn' : 1 < normSq (z : ℂ) := lt_of_le_of_ne hn (Ne.symm hcircle)
  by_cases hleft : (z : ℂ).re = -Real.sqrt 2 / 2
  · exact sourceScalarTriangleMap_im_eq_zero_of_leftSide S hleft z.im_pos hn'
  by_cases hright : (z : ℂ).re = 1 / 2
  · exact sourceScalarTriangleMap_im_eq_zero_of_rightSide S hright z.im_pos hn'
  exact (hnot ⟨lt_of_le_of_ne hl (Ne.symm hleft),
    lt_of_le_of_ne hr hright, z.im_pos, hn'⟩).elim

private theorem sourceScalarTriangleMap_signed_nonneg_of_mem_fundamental
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    {z : UpperHalfPlane} (hz : z ∈ fundamentalTriangle) :
    0 ≤ scalarTriangleDenominator (sourceCuspCircle S) (sourceOrderThreeCircle S)
      (sourceOtherEllipticCircle S) * (sourceScalarTriangleMap S (z : ℂ)).im := by
  by_cases hopen : (z : ℂ) ∈ sourceOpenChamber
  · have hm := (sourceScalarOpenChamberMap_bijOn S
      (sourceOrderThreeCircle_ne_otherElliptic S)).mapsTo hopen
    change 0 < scalarTriangleDenominator (sourceCuspCircle S)
      (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S) *
        (sourceScalarOpenChamberMap S (z : ℂ)).im at hm
    rw [← sourceScalarTriangleMap_eq_open_of_mem S hopen] at hm
    exact hm.le
  · rw [sourceScalarTriangleMap_im_eq_zero_of_mem_fundamental_not_open S hz hopen, mul_zero]

private theorem sourceScalarRightDoubleMap_reflected_fundamental
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    {z : UpperHalfPlane} (hz : z ∈ fundamentalTriangle) :
    sourceScalarRightDoubleMap S (sourceRight (z : ℂ)) =
      (starRingEnd ℂ) (sourceScalarTriangleMap S (z : ℂ)) := by
  rcases lt_or_eq_of_le hz.2.1 with hright | hright
  · change (z : ℂ).re < 1 / 2 at hright
    have hcoord : (((sourceRight (z : ℂ)) - (1 / 2 : ℂ)) / Complex.I).im < 0 := by
      rw [sourceRight_coord_im, sourceRight_re]
      linarith
    rw [sourceScalarRightDoubleMap]
    rw [TauCeti.lineSchwarzReflection_of_coord_im_neg
      (f := sourceScalarTriangleMap S) hcoord]
    simp only [sub_zero, div_one, one_mul, zero_add]
    rw [sourceRight_affineReflection, sourceRight_involutive]
  · have hnot : (z : ℂ) ∉ sourceOpenChamber := by
      intro h
      exact (ne_of_lt h.2.1) hright
    have him := sourceScalarTriangleMap_im_eq_zero_of_mem_fundamental_not_open S hz hnot
    change (z : ℂ).re = 1 / 2 at hright
    have hfix : sourceRight (z : ℂ) = z := by
      apply Complex.ext
      · rw [sourceRight_re, hright]
        norm_num
      · simp [sourceRight]
    rw [hfix, sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hz.2.1]
    rw [starRingEnd_apply, Complex.star_def]
    exact (Complex.conj_eq_iff_im.mpr him).symm

private theorem sourceRightUHP_mem_fundamentalTriangle_of_mem_right_public
    {z : UpperHalfPlane} (hz : z ∈ rightFundamentalTriangle) :
    sourceRightUHP z ∈ fundamentalTriangle := by
  rcases hz with ⟨hl, hr, hn⟩
  change 1 / 2 ≤ (z : ℂ).re at hl
  change (z : ℂ).re ≤ 1 + Real.sqrt 2 / 2 at hr
  refine ⟨?_, ?_, ?_⟩
  · change -Real.sqrt 2 / 2 ≤ (sourceRight (z : ℂ)).re
    rw [sourceRight_re]
    linarith
  · change (sourceRight (z : ℂ)).re ≤ 1 / 2
    rw [sourceRight_re]
    linarith
  · change 1 ≤ normSq (sourceRight (z : ℂ))
    have heq : normSq (sourceRight (z : ℂ)) = normSq (1 - (z : ℂ)) := by
      simp [sourceRight, normSq_apply]
    rwa [heq]

private theorem sourceCircleUHP_fixed_of_normSq_eq_one
    (z : UpperHalfPlane) (hz : normSq (z : ℂ) = 1) :
    sourceCircleUHP z = z := by
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · simp [sourceCircle, Complex.inv_re, normSq_conj, hz]
  · simp [sourceCircle, Complex.inv_im, normSq_conj, hz]

private theorem sourceRightUHP_fixed_of_re_eq
    (z : UpperHalfPlane) (hz : (z : ℂ).re = 1 / 2) :
    sourceRightUHP z = z := by
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · change (sourceRight (z : ℂ)).re = (z : ℂ).re
    rw [sourceRight_re, hz]
    norm_num
  · simp [sourceRight]

private theorem sourceLeftUHP_fixed_of_re_eq
    (z : UpperHalfPlane) (hz : (z : ℂ).re = -Real.sqrt 2 / 2) :
    sourceLeftUHP z = z := by
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · change ((-Real.sqrt 2 : ℂ) - (starRingEnd ℂ) (z : ℂ)).re = (z : ℂ).re
    rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_re, hz]
    ring
  · simp [sourceLeft]

private theorem sourceRightUHP_involutive_public (z : UpperHalfPlane) :
    sourceRightUHP (sourceRightUHP z) = z := by
  apply UpperHalfPlane.coe_injective
  exact sourceRight_involutive (z : ℂ)

private theorem sourceCircleUHP_involutive_public (z : UpperHalfPlane) :
    sourceCircleUHP (sourceCircleUHP z) = z := by
  apply UpperHalfPlane.coe_injective
  change sourceCircle (sourceCircle (z : ℂ)) = z
  simp [sourceCircle]

private theorem exists_orbit_sourceRightUHP_of_mem_fundamental_not_open
    (z : UpperHalfPlane) (hz : z ∈ fundamentalTriangle)
    (hnot : (z : ℂ) ∉ sourceOpenChamber) :
    ∃ g : Delta, fuchsianSourceAction g • z = sourceRightUHP z := by
  by_cases hcircle : normSq (z : ℂ) = 1
  · refine ⟨g₁, ?_⟩
    have hc := sourceCircleUHP_fixed_of_normSq_eq_one z hcircle
    simpa [hc] using (sourceRight_sourceCircle z).symm
  by_cases hleft : (z : ℂ).re = -Real.sqrt 2 / 2
  · refine ⟨g₁ * g₂, ?_⟩
    have hl := sourceLeftUHP_fixed_of_re_eq z hleft
    calc
      fuchsianSourceAction (g₁ * g₂) • z =
          fuchsianSourceAction g₁ • (fuchsianSourceAction g₂ • z) := by
            rw [map_mul, mul_smul]
      _ = fuchsianSourceAction g₁ •
          (sourceCircleUHP (sourceLeftUHP z)) := by
            rw [sourceCircle_sourceLeft]
      _ = sourceRightUHP
          (sourceCircleUHP (sourceCircleUHP (sourceLeftUHP z))) := by
            rw [sourceRight_sourceCircle]
      _ = sourceRightUHP (sourceLeftUHP z) := by
            rw [sourceCircleUHP_involutive_public]
      _ = sourceRightUHP z := by rw [hl]
  by_cases hright : (z : ℂ).re = 1 / 2
  · refine ⟨1, ?_⟩
    rw [map_one, one_smul, sourceRightUHP_fixed_of_re_eq z hright]
  exfalso
  apply hnot
  exact ⟨lt_of_le_of_ne hz.1 (Ne.symm hleft),
    lt_of_le_of_ne hz.2.1 hright, z.im_pos,
    lt_of_le_of_ne hz.2.2 (Ne.symm hcircle)⟩

private theorem cross_fundamental_fibre
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    {z w : UpperHalfPlane} (hz : z ∈ fundamentalTriangle)
    (hw : w ∈ fundamentalTriangle)
    (hzw : sourceScalarRightDoubleMap S (z : ℂ) =
      sourceScalarRightDoubleMap S (sourceRight (w : ℂ))) :
    ∃ g : Delta, fuchsianSourceAction g • z = sourceRightUHP w := by
  have hzseed : sourceScalarRightDoubleMap S (z : ℂ) =
      sourceScalarTriangleMap S (z : ℂ) :=
    sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hz.2.1
  have hwreflect := sourceScalarRightDoubleMap_reflected_fundamental S hw
  have hseedconj : sourceScalarTriangleMap S (z : ℂ) =
      (starRingEnd ℂ) (sourceScalarTriangleMap S (w : ℂ)) := by
    rw [← hzseed, ← hwreflect]
    exact hzw
  let d : ℝ := scalarTriangleDenominator (sourceCuspCircle S)
    (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S)
  have hd : d ≠ 0 := scalarTriangleDenominator_ne_zero
    (sourceOrderThreeCircle_ne_cusp S) (sourceOtherEllipticCircle_ne_cusp S)
      (sourceOrderThreeCircle_ne_otherElliptic S)
  have hznonneg := sourceScalarTriangleMap_signed_nonneg_of_mem_fundamental S hz
  have hwnonneg := sourceScalarTriangleMap_signed_nonneg_of_mem_fundamental S hw
  change 0 ≤ d * (sourceScalarTriangleMap S (z : ℂ)).im at hznonneg
  change 0 ≤ d * (sourceScalarTriangleMap S (w : ℂ)).im at hwnonneg
  have him := congrArg Complex.im hseedconj
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_im] at him
  have hprod : d * (sourceScalarTriangleMap S (z : ℂ)).im =
      -(d * (sourceScalarTriangleMap S (w : ℂ)).im) := by
    rw [him]
    ring
  have hdzero : d * (sourceScalarTriangleMap S (z : ℂ)).im = 0 := by
    apply le_antisymm
    · rw [hprod]
      exact neg_nonpos.mpr hwnonneg
    · exact hznonneg
  have hdz : (sourceScalarTriangleMap S (z : ℂ)).im = 0 :=
    (mul_eq_zero.mp hdzero).resolve_left hd
  have hdw : (sourceScalarTriangleMap S (w : ℂ)).im = 0 := by linarith
  have hseed : sourceScalarTriangleMap S (z : ℂ) =
      sourceScalarTriangleMap S (w : ℂ) := by
    rw [hseedconj, starRingEnd_apply, Complex.star_def,
      Complex.conj_eq_iff_im.mpr hdw]
  have hzwPoint := sourceScalarTriangleMap_injective_on_fundamentalTriangle S hz hw hseed
  subst w
  have hnot : (z : ℂ) ∉ sourceOpenChamber := by
    intro hopen
    have hm := (sourceScalarOpenChamberMap_bijOn S
      (sourceOrderThreeCircle_ne_otherElliptic S)).mapsTo hopen
    change 0 < d * (sourceScalarOpenChamberMap S (z : ℂ)).im at hm
    rw [← sourceScalarTriangleMap_eq_open_of_mem S hopen, hdz, mul_zero] at hm
    exact (lt_irrefl 0 hm).elim
  exact exists_orbit_sourceRightUHP_of_mem_fundamental_not_open z hz hnot

/-- Equal scalar values on the doubled closed fundamental region imply equality up to the source
Fuchsian action. -/
theorem sourceScalarRightDoubleMap_fundamental_fibres
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    {z w : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion)
    (hw : w ∈ orientedFundamentalRegion)
    (hzw : sourceScalarRightDoubleMap S (z : ℂ) =
      sourceScalarRightDoubleMap S (w : ℂ)) :
    ∃ g : Delta, fuchsianSourceAction g • z = w := by
  rcases hz with hz | hz <;> rcases hw with hw | hw
  · have hseed : sourceScalarTriangleMap S (z : ℂ) =
        sourceScalarTriangleMap S (w : ℂ) := by
      rw [← sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hz.2.1,
        ← sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hw.2.1]
      exact hzw
    have heq := sourceScalarTriangleMap_injective_on_fundamentalTriangle S hz hw hseed
    exact ⟨1, by simpa [heq]⟩
  · let w₀ : UpperHalfPlane := sourceRightUHP w
    have hw₀ : w₀ ∈ fundamentalTriangle :=
      sourceRightUHP_mem_fundamentalTriangle_of_mem_right_public hw
    have hcross : sourceScalarRightDoubleMap S (z : ℂ) =
        sourceScalarRightDoubleMap S (sourceRight (w₀ : ℂ)) := by
      simpa [w₀, sourceRight_involutive] using hzw
    obtain ⟨g, hg⟩ := cross_fundamental_fibre S hz hw₀ hcross
    exact ⟨g, hg.trans (sourceRightUHP_involutive_public w)⟩
  · let z₀ : UpperHalfPlane := sourceRightUHP z
    have hz₀ : z₀ ∈ fundamentalTriangle :=
      sourceRightUHP_mem_fundamentalTriangle_of_mem_right_public hz
    have hcross : sourceScalarRightDoubleMap S (w : ℂ) =
        sourceScalarRightDoubleMap S (sourceRight (z₀ : ℂ)) := by
      simpa [z₀, sourceRight_involutive] using hzw.symm
    obtain ⟨g, hg⟩ := cross_fundamental_fibre S hw hz₀ hcross
    have hg' : fuchsianSourceAction g • w = z :=
      hg.trans (sourceRightUHP_involutive_public z)
    refine ⟨g⁻¹, ?_⟩
    rw [← hg', ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  · let z₀ : UpperHalfPlane := sourceRightUHP z
    let w₀ : UpperHalfPlane := sourceRightUHP w
    have hz₀ : z₀ ∈ fundamentalTriangle :=
      sourceRightUHP_mem_fundamentalTriangle_of_mem_right_public hz
    have hw₀ : w₀ ∈ fundamentalTriangle :=
      sourceRightUHP_mem_fundamentalTriangle_of_mem_right_public hw
    have hzform := sourceScalarRightDoubleMap_reflected_fundamental S hz₀
    have hwform := sourceScalarRightDoubleMap_reflected_fundamental S hw₀
    have hconj : (starRingEnd ℂ) (sourceScalarTriangleMap S (z₀ : ℂ)) =
        (starRingEnd ℂ) (sourceScalarTriangleMap S (w₀ : ℂ)) := by
      rw [← hzform, ← hwform]
      simpa [z₀, w₀, sourceRight_involutive] using hzw
    have hseed : sourceScalarTriangleMap S (z₀ : ℂ) =
        sourceScalarTriangleMap S (w₀ : ℂ) := by
      simpa using congrArg (starRingEnd ℂ) hconj
    have heq := sourceScalarTriangleMap_injective_on_fundamentalTriangle S hz₀ hw₀ hseed
    have hzw' : z = w := by
      simpa [z₀, w₀] using congrArg sourceRightUHP heq
    exact ⟨1, by simpa [hzw']⟩


end SphereSixComplex.Periods.SourceChamberTopology
