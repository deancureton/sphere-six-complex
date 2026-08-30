module

public import SphereSixComplex.Periods.OrbifoldAffineTorsorCechGluing
public import SphereSixComplex.Periods.ExactFuchsianCuspBounds
import SphereSixComplex.TriangleGroup.FuchsianTessellation
import all SphereSixComplex.Periods.Functions

/-!
# Cusp bounds for a general orbifold affine-torsor frame

The completed-cusp factorization in `OrbifoldAffineLineTorsorDescentProblem` implies that the
infinity frame is bounded on the whole distinguished cusp component.  Combined with boundedness
of the reciprocal quotient coordinate, this controls every entire Cech correction.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open Filter Metric Set
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTessellation

namespace OrbifoldAffineLineTorsorDescentProblem

/-- The infinity frame is invariant under the positive cusp translation on the cusp region. -/
public theorem frameInfinity_product_invariant_on_cusp
    (P : OrbifoldAffineLineTorsorDescentProblem) (z : UpperHalfPlane)
    (hz : z ∈ fuchsianCuspRegion) :
    P.frameInfinity (fuchsianSourceAction (g₁ * g₂) • z) = P.frameInfinity z := by
  have hzq : P.quotient.coordinate z ≠ 0 := P.cusp_coordinate_ne_zero z hz
  have hg₂q :
      P.quotient.coordinate (fuchsianSourceAction g₂ • z) ≠ 0 := by
    rw [P.quotient.coordinate_invariant]
    exact hzq
  rw [map_mul, mul_smul, P.frameInfinity_one _ hg₂q, P.frameInfinity_two z hzq]
  have h := P.linearOne_mul_linearTwo_cusp z
  linear_combination P.frameInfinity z * h

/-- The infinity frame is invariant under every integral cusp translation on the cusp region. -/
public theorem frameInfinity_zpow_invariant_on_cusp
    (P : OrbifoldAffineLineTorsorDescentProblem) (n : ℤ) (z : UpperHalfPlane)
    (hz : z ∈ fuchsianCuspRegion) :
    P.frameInfinity (fuchsianSourceAction ((g₁ * g₂) ^ n) • z) = P.frameInfinity z := by
  have hnat (m : ℕ) (w : UpperHalfPlane) (hw : w ∈ fuchsianCuspRegion) :
      P.frameInfinity (fuchsianSourceAction ((g₁ * g₂) ^ m) • w) =
        P.frameInfinity w := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ', map_mul, mul_smul]
        have hwm :
            fuchsianSourceAction ((g₁ * g₂) ^ m) • w ∈ fuchsianCuspRegion := by
          change 1 ≤ (fuchsianSourceAction ((g₁ * g₂) ^ m) • w).im
          rw [show ((g₁ * g₂) ^ m : Delta) = (g₁ * g₂) ^ (m : ℤ) by simp,
            product_zpow_im]
          exact hw
        rw [P.frameInfinity_product_invariant_on_cusp _ hwm, ih]
  cases n with
  | ofNat m => simpa [zpow_ofNat] using hnat m z hz
  | negSucc m =>
      let w := fuchsianSourceAction ((g₁ * g₂) ^ (Int.negSucc m)) • z
      have hw : w ∈ fuchsianCuspRegion := by
        change 1 ≤ w.im
        rw [show w = fuchsianSourceAction ((g₁ * g₂) ^ (Int.negSucc m)) • z by rfl,
          product_zpow_im]
        exact hz
      have h := hnat (m + 1) w hw
      have hcancel :
          fuchsianSourceAction ((g₁ * g₂) ^ (m + 1)) • w = z := by
        change fuchsianSourceAction ((g₁ * g₂) ^ (m + 1)) •
          (fuchsianSourceAction ((g₁ * g₂) ^ (Int.negSucc m)) • z) = z
        rw [← mul_smul, ← map_mul]
        simp [zpow_negSucc]
      rw [hcancel] at h
      exact h.symm

private def centeredCuspTruncationForFrame (H : ℝ) : Set UpperHalfPlane :=
  {z | -cuspWidth / 2 ≤ z.re ∧ z.re ≤ cuspWidth / 2 ∧
    1 ≤ z.im ∧ z.im ≤ max 1 H}

private theorem centeredCuspTruncationForFrame_isCompact (H : ℝ) :
    IsCompact (centeredCuspTruncationForFrame H) := by
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
    exact ⟨w, ⟨hzreLower, hzreUpper, hzimLower, hzimUpper⟩, rfl⟩

private theorem boundedOn_cusp_of_eventually_bounded
    (h : UpperHalfPlane → ℂ)
    (hcontinuous : ContinuousOn h fuchsianCuspRegion)
    (hinvariant : ∀ (n : ℤ) z, z ∈ fuchsianCuspRegion →
      h (fuchsianSourceAction ((g₁ * g₂) ^ n) • z) = h z)
    {B : ℝ} (hB : 0 ≤ B)
    (heventually : ∀ᶠ z in upperHalfPlaneAtInfinity, ‖h z‖ ≤ B) :
    BoundedOn h fuchsianCuspRegion := by
  rw [upperHalfPlaneAtInfinity, eventually_comap, eventually_atTop] at heventually
  obtain ⟨H, hH⟩ := heventually
  let K := centeredCuspTruncationForFrame H
  have hK : IsCompact K := centeredCuspTruncationForFrame_isCompact H
  have hKsub : K ⊆ fuchsianCuspRegion := fun _ hz ↦ hz.2.2.1
  obtain ⟨A, hA⟩ := hK.bddAbove_image (hcontinuous.mono hKsub).norm
  unfold BoundedOn
  refine ⟨max A B, le_max_of_le_right hB, ?_⟩
  intro z hz
  by_cases hhigh : H ≤ z.im
  · exact (hH z.im hhigh z rfl).trans (le_max_right A B)
  · let w := centerPoint z
    have hwmem : w ∈ K := by
      refine ⟨centerPoint_re_lower z, (centerPoint_re_upper z).le, ?_, ?_⟩
      · rw [centerPoint_im]
        exact hz
      · rw [centerPoint_im]
        exact (le_of_not_ge hhigh).trans (le_max_right 1 H)
    have hwcusp : w ∈ fuchsianCuspRegion := hKsub hwmem
    calc
      ‖h z‖ = ‖h w‖ := by
        exact congrArg norm (hinvariant (centerExponent z) z hz).symm
      _ ≤ A := hA ⟨_, hwmem, rfl⟩
      _ ≤ max A B := le_max_left A B

/-- The completed-cusp factorization makes the infinity frame bounded on the distinguished cusp
component. -/
public theorem frameInfinity_cusp_bounded
    (P : OrbifoldAffineLineTorsorDescentProblem) :
    BoundedOn P.frameInfinity fuchsianCuspRegion := by
  let K : Set ℂ := Metric.closedBall 0 (P.cuspFrameRadius / 2)
  have hK : IsCompact K := isCompact_closedBall 0 (P.cuspFrameRadius / 2)
  have hKsub : K ⊆ Metric.ball 0 P.cuspFrameRadius := by
    intro q hq
    have hdist := Metric.mem_closedBall.mp hq
    apply Metric.mem_ball.mpr
    linarith [P.cuspFrameRadius_pos]
  have hunit : ContinuousOn P.cuspFrameUnit K := by
    intro q hq
    exact (P.cuspFrameUnit_holomorphic q (hKsub hq)).continuousAt.continuousWithinAt
  obtain ⟨B, hBound⟩ := hK.bddAbove_image hunit.norm
  have heventually : ∀ᶠ z in upperHalfPlaneAtInfinity,
      ‖P.frameInfinity z‖ ≤ max B 0 := by
    filter_upwards [P.inverse_coordinate_eventually_mem_closedBall,
      P.frameInfinity_cusp_factorization_eventually] with z hzmem hzfactor
    rw [hzfactor]
    exact (hBound ⟨_, hzmem, rfl⟩).trans (le_max_left B 0)
  apply boundedOn_cusp_of_eventually_bounded P.frameInfinity
  · intro z hz
    exact (P.frameInfinity_holomorphic z
      (P.cusp_coordinate_ne_zero z hz)).continuousAt.continuousWithinAt
  · exact P.frameInfinity_zpow_invariant_on_cusp
  · exact le_max_right B 0
  · exact heventually

/-- An entire function of the reciprocal quotient coordinate is bounded on the distinguished
cusp component. -/
public theorem entire_inverseCoordinate_cusp_bounded
    (P : OrbifoldAffineLineTorsorDescentProblem) (f : ℂ → ℂ) (hf : MDiff f) :
    BoundedOn (fun z ↦ f ((P.quotient.coordinate z)⁻¹)) fuchsianCuspRegion := by
  obtain ⟨B, hB, hqB⟩ := P.quotient.inverse_coordinate_bounded_on_cusp
  let K : Set ℂ := Metric.closedBall 0 B
  have hK : IsCompact K := isCompact_closedBall 0 B
  obtain ⟨A, hA⟩ := hK.bddAbove_image (hf.continuous.continuousOn.norm)
  unfold BoundedOn
  refine ⟨max A 0, le_max_right A 0, ?_⟩
  intro z hz
  have hqK : (P.quotient.coordinate z)⁻¹ ∈ K := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hqB z hz
  exact (hA ⟨_, hqK, rfl⟩).trans (le_max_left A 0)

private theorem boundedOn_mul
    {f g : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (hf : BoundedOn f s) (hg : BoundedOn g s) :
    BoundedOn (fun z ↦ f z * g z) s := by
  unfold BoundedOn at hf hg ⊢
  obtain ⟨B, hB, hf⟩ := hf
  obtain ⟨C, hC, hg⟩ := hg
  refine ⟨B * C, mul_nonneg hB hC, ?_⟩
  intro z hz
  rw [norm_mul]
  exact mul_le_mul (hf z hz) (hg z hz) (norm_nonneg _) hB

/-- Every entire infinity-chart coefficient times the infinity frame is bounded at the cusp. -/
public theorem infinityCorrection_cusp_bounded
    (P : OrbifoldAffineLineTorsorDescentProblem) (f : ℂ → ℂ) (hf : MDiff f) :
    BoundedOn
      (fun z ↦ f ((P.quotient.coordinate z)⁻¹) * P.frameInfinity z)
      fuchsianCuspRegion :=
  boundedOn_mul (P.entire_inverseCoordinate_cusp_bounded f hf)
    P.frameInfinity_cusp_bounded

/-- Once local analytic descent and the standard frame identification are supplied, all Cech
gluing and cusp estimates are formal consequences. -/
@[expose] public noncomputable def CechGluingData.ofAnalyticDescent
    (P : OrbifoldAffineLineTorsorDescentProblem) (A : P.AnalyticDescentData)
    (frame : HolomorphicAffineTorsorHOne.AcyclicProjectiveLineFrame)
    (hframe : P.frameTransition = frame.transition) :
    P.CechGluingData where
  descent := A
  frame := frame
  frameTransition_eq := hframe
  infinityCorrection_cusp_bounded := P.infinityCorrection_cusp_bounded

/-- Analytic descent together with either standard acyclic transition function gives the
original cusp-bounded correction. -/
public theorem nonempty_cuspBoundedEllipticOneCorrection_of_analyticDescent
    (P : OrbifoldAffineLineTorsorDescentProblem) (A : P.AnalyticDescentData)
    (hframe :
      P.frameTransition = HolomorphicAffineTorsorHOne.negOneTransition ∨
      P.frameTransition = HolomorphicAffineTorsorHOne.zeroTransition) :
    Nonempty P.CuspBoundedEllipticOneCorrection := by
  rcases hframe with hnegOne | hzero
  · exact P.nonempty_cuspBoundedEllipticOneCorrection_of_cechGluingData
      (CechGluingData.ofAnalyticDescent P A
        HolomorphicAffineTorsorHOne.AcyclicProjectiveLineFrame.negOne hnegOne)
  · exact P.nonempty_cuspBoundedEllipticOneCorrection_of_cechGluingData
      (CechGluingData.ofAnalyticDescent P A
        HolomorphicAffineTorsorHOne.AcyclicProjectiveLineFrame.zero hzero)

end OrbifoldAffineLineTorsorDescentProblem

end SphereSixComplex.Periods
