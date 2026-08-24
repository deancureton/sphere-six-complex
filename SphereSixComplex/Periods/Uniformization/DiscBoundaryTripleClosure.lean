module

public import SphereSixComplex.Periods.Uniformization.DiscBoundaryTriple
import all SphereSixComplex.Periods.Uniformization.DiscBoundaryTriple

@[expose] public section

open Complex Metric Set Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

/-! The Cayley-affine-Cayley map as a single linear-fractional expression.  This removes the
apparent singularity at the source Cayley pole and supplies the closed-disc API. -/

def orientedCircleTripleNumerator
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) (z : ℂ) : ℂ :=
  (circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) * I * ((s₀ : ℂ) + z) +
    ((circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) - I) * ((s₀ : ℂ) - z)

def orientedCircleTripleDenominator
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) (z : ℂ) : ℂ :=
  (circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) * I * ((s₀ : ℂ) + z) +
    ((circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂ : ℂ) + I) * ((s₀ : ℂ) - z)

def orientedCircleTripleLinearFractionalMap
    (s₀ s₁ s₂ t₀ t₁ t₂ : Circle) (z : ℂ) : ℂ :=
  (t₀ : ℂ) * orientedCircleTripleNumerator s₀ s₁ s₂ t₀ t₁ t₂ z /
    orientedCircleTripleDenominator s₀ s₁ s₂ t₀ t₁ t₂ z

theorem orientedCircleTripleDenominator_ne_zero
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    orientedCircleTripleDenominator s₀ s₁ s₂ t₀ t₁ t₂ z ≠ 0 := by
  let a : ℝ := circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂
  let b : ℝ := circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂
  have ha : 0 < a := circleTripleScale_pos horient
  by_cases hzs : z = (s₀ : ℂ)
  · subst z
    unfold orientedCircleTripleDenominator
    simp only [sub_self, mul_zero, add_zero]
    have hadd : (s₀ : ℂ) + s₀ ≠ 0 := by
      intro h
      apply s₀.coe_ne_zero
      linear_combination (1 / 2 : ℂ) * h
    exact mul_ne_zero
      (mul_ne_zero (by exact_mod_cast ha.ne') Complex.I_ne_zero) hadd
  · have hsub : (s₀ : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzs)
    have hzle : ‖z‖ ≤ 1 := by
      have hdist : dist z 0 ≤ 1 := mem_closedBall.mp hz
      simpa only [dist_zero_right] using hdist
    have hcim : 0 ≤ (boundaryCayley s₀ z).im := by
      rw [boundaryCayley_im]
      have hnum : 0 ≤ Complex.normSq (s₀ : ℂ) - Complex.normSq z := by
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Circle.norm_coe]
        nlinarith [norm_nonneg z]
      exact div_nonneg hnum (Complex.normSq_nonneg _)
    have hfactor :
        orientedCircleTripleDenominator s₀ s₁ s₂ t₀ t₁ t₂ z =
          ((s₀ : ℂ) - z) *
            ((a : ℂ) * boundaryCayley s₀ z + (b : ℂ) + I) := by
      unfold orientedCircleTripleDenominator boundaryCayley
      dsimp only [a, b]
      field_simp [hsub]
      ring
    intro hzero
    rw [hfactor] at hzero
    have hwzero : (a : ℂ) * boundaryCayley s₀ z + (b : ℂ) + I = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hsub
    have him := congrArg Complex.im hwzero
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, zero_mul, add_zero] at him
    have him' : a * (boundaryCayley (s₀ : ℂ) z).im + 1 = 0 := by
      simpa using him
    nlinarith [mul_nonneg ha.le hcim]

theorem orientedCircleTripleMap_eq_linearFractionalMap
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂ z =
      orientedCircleTripleLinearFractionalMap s₀ s₁ s₂ t₀ t₁ t₂ z := by
  have hD := orientedCircleTripleDenominator_ne_zero horient hz
  by_cases hzs : z = (s₀ : ℂ)
  · subst z
    rw [orientedCircleTripleMap_pole]
    unfold orientedCircleTripleLinearFractionalMap
    have hND :
        orientedCircleTripleNumerator s₀ s₁ s₂ t₀ t₁ t₂ (s₀ : ℂ) =
          orientedCircleTripleDenominator s₀ s₁ s₂ t₀ t₁ t₂ (s₀ : ℂ) := by
      unfold orientedCircleTripleNumerator orientedCircleTripleDenominator
      ring
    rw [hND]
    field_simp [hD]
  · rw [orientedCircleTripleMap_eq_openMap_of_ne _ _ _ _ _ _ hzs]
    let a : ℝ := circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂
    let b : ℝ := circleTripleShift s₀ s₁ s₂ t₀ t₁ t₂
    have hsub : (s₀ : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzs)
    have hfactor :
        orientedCircleTripleDenominator s₀ s₁ s₂ t₀ t₁ t₂ z =
          ((s₀ : ℂ) - z) *
            ((a : ℂ) * boundaryCayley s₀ z + (b : ℂ) + I) := by
      unfold orientedCircleTripleDenominator boundaryCayley
      dsimp only [a, b]
      field_simp [hsub]
      ring
    have hwden : (a : ℂ) * boundaryCayley s₀ z + (b : ℂ) + I ≠ 0 := by
      intro hzero
      apply hD
      rw [hfactor, hzero, mul_zero]
    unfold orientedCircleTripleOpenMap boundaryCayleyInv
      orientedCircleTripleLinearFractionalMap orientedCircleTripleNumerator
      orientedCircleTripleDenominator boundaryCayley
    dsimp only [a, b] at hwden ⊢
    field_simp [hsub, hwden, hD]
    ring

theorem orientedCircleTripleLinearFractionalMap_continuousOn_closedBall
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    ContinuousOn
      (orientedCircleTripleLinearFractionalMap s₀ s₁ s₂ t₀ t₁ t₂)
      (closedBall (0 : ℂ) 1) := by
  have hN : Continuous (fun z : ℂ =>
      (t₀ : ℂ) * orientedCircleTripleNumerator s₀ s₁ s₂ t₀ t₁ t₂ z) := by
    unfold orientedCircleTripleNumerator
    fun_prop
  have hD : Continuous (orientedCircleTripleDenominator s₀ s₁ s₂ t₀ t₁ t₂) := by
    unfold orientedCircleTripleDenominator
    fun_prop
  exact hN.continuousOn.div hD.continuousOn
    (fun z hz ↦ orientedCircleTripleDenominator_ne_zero horient hz)

theorem orientedCircleTripleMap_continuousOn_closedBall
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    ContinuousOn (orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂)
      (closedBall (0 : ℂ) 1) := by
  exact (orientedCircleTripleLinearFractionalMap_continuousOn_closedBall horient).congr
    fun z hz ↦ orientedCircleTripleMap_eq_linearFractionalMap horient hz

private theorem orientedCircleTripleLinearFractionalMap_injOn_closedBall
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    InjOn (orientedCircleTripleLinearFractionalMap s₀ s₁ s₂ t₀ t₁ t₂)
      (closedBall (0 : ℂ) 1) := by
  intro z hz w hw hzw
  let a : ℝ := circleTripleScale s₀ s₁ s₂ t₀ t₁ t₂
  have ha : 0 < a := circleTripleScale_pos horient
  let N : ℂ → ℂ := orientedCircleTripleNumerator s₀ s₁ s₂ t₀ t₁ t₂
  let D : ℂ → ℂ := orientedCircleTripleDenominator s₀ s₁ s₂ t₀ t₁ t₂
  have hDz : D z ≠ 0 := orientedCircleTripleDenominator_ne_zero horient hz
  have hDw : D w ≠ 0 := orientedCircleTripleDenominator_ne_zero horient hw
  have ht : (t₀ : ℂ) ≠ 0 := t₀.coe_ne_zero
  have hcross : N z * D w = N w * D z := by
    change (t₀ : ℂ) * N z / D z = (t₀ : ℂ) * N w / D w at hzw
    field_simp [hDz, hDw, ht] at hzw
    simpa only [mul_comm] using hzw
  have hfactor : (-4 : ℂ) * (a : ℂ) * (s₀ : ℂ) * (z - w) = 0 := by
    have hI : Complex.I * Complex.I = (-1 : ℂ) := by
      simpa only [pow_two] using Complex.I_sq
    calc
      (-4 : ℂ) * (a : ℂ) * (s₀ : ℂ) * (z - w) =
          (4 : ℂ) * (a : ℂ) * (Complex.I * Complex.I) * (s₀ : ℂ) * (z - w) := by
        rw [hI]
        ring
      _ = N z * D w - N w * D z := by
        simp only [N, D, orientedCircleTripleNumerator, orientedCircleTripleDenominator]
        dsimp only [a]
        ring
      _ = 0 := sub_eq_zero.mpr hcross
  have hcoef : (-4 : ℂ) * (a : ℂ) * (s₀ : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast ha.ne')) s₀.coe_ne_zero
  rcases mul_eq_zero.mp hfactor with hbad | hdiff
  · exact absurd hbad hcoef
  · exact sub_eq_zero.mp hdiff

theorem orientedCircleTripleMap_injOn_closedBall
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    InjOn (orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂)
      (closedBall (0 : ℂ) 1) := by
  intro z hz w hw hzw
  apply orientedCircleTripleLinearFractionalMap_injOn_closedBall horient hz hw
  rw [← orientedCircleTripleMap_eq_linearFractionalMap horient hz,
    ← orientedCircleTripleMap_eq_linearFractionalMap horient hw]
  exact hzw

theorem orientedCircleTripleMap_mapsTo_closedBall
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    MapsTo (orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂)
      (closedBall (0 : ℂ) 1) (closedBall 0 1) := by
  let A := orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂
  have hAc : ContinuousOn A (closure (ball (0 : ℂ) 1)) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact orientedCircleTripleMap_continuousOn_closedBall horient
  have himage := hAc.image_closure
  have hopen := orientedCircleTripleMap_bijOn_ball s₀ s₁ s₂ t₀ t₁ t₂ horient
  intro z hz
  have hzcl : z ∈ closure (ball (0 : ℂ) 1) := by
    rwa [closure_ball (0 : ℂ) one_ne_zero]
  have hmem : A z ∈ closure (A '' ball (0 : ℂ) 1) := himage ⟨z, hzcl, rfl⟩
  rw [hopen.image_eq, closure_ball (0 : ℂ) one_ne_zero] at hmem
  exact hmem

theorem orientedCircleTripleMap_bijOn_closedBall
    {s₀ s₁ s₂ t₀ t₁ t₂ : Circle}
    (horient : SameCircleTripleOrientation s₀ s₁ s₂ t₀ t₁ t₂) :
    BijOn (orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂)
      (closedBall (0 : ℂ) 1) (closedBall 0 1) := by
  let A := orientedCircleTripleMap s₀ s₁ s₂ t₀ t₁ t₂
  have hAc : ContinuousOn A (closedBall (0 : ℂ) 1) :=
    orientedCircleTripleMap_continuousOn_closedBall horient
  have hmaps : MapsTo A (closedBall (0 : ℂ) 1) (closedBall 0 1) :=
    orientedCircleTripleMap_mapsTo_closedBall horient
  have hcpt : IsCompact (A '' closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hAc
  have hopen := orientedCircleTripleMap_bijOn_ball s₀ s₁ s₂ t₀ t₁ t₂ horient
  have hball : ball (0 : ℂ) 1 ⊆ A '' closedBall (0 : ℂ) 1 := by
    rw [← hopen.image_eq]
    exact image_mono ball_subset_closedBall
  have hclosed : closedBall (0 : ℂ) 1 ⊆ A '' closedBall (0 : ℂ) 1 := by
    have hcl := closure_minimal hball hcpt.isClosed
    simpa only [closure_ball (0 : ℂ) one_ne_zero] using hcl
  have himage : A '' closedBall (0 : ℂ) 1 = closedBall 0 1 :=
    (image_subset_iff.mpr hmaps).antisymm hclosed
  have h := (orientedCircleTripleMap_injOn_closedBall horient).bijOn_image
  rw [himage] at h
  exact h


end SphereSixComplex.Periods.SourceChamberTopology
