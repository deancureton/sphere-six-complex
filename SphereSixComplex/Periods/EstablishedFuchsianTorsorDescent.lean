module

public import SphereSixComplex.Periods.ExactFuchsianModularFrameData
public import SphereSixComplex.Periods.ExactFuchsianModularFrameConstruction
public import SphereSixComplex.Periods.EstablishedOrbifoldAffineTorsorAnalyticDescent
import all SphereSixComplex.Periods.Functions
import all SphereSixComplex.Periods.FuchsianModularParameterExistence
import SphereSixComplex.TriangleGroup.FuchsianTessellation

/-!
# Exact modular-form input for the additive Fuchsian torsors

The paper's identification of the homogeneous `mu` sheaf with `O(-1)` is not a formal consequence
of cyclic consistency.  It uses the divisor and cusp behavior of
`E4^2 * sqrt(E6) / Delta` after pullback by the modular parameter.  This file isolates that
classical modular-form interface and the resulting affine-torsor assembly.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianTessellation
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open Filter Set Metric

variable (E : EstablishedFuchsianModularParameter)

variable (F : ExactLiftedModularNegOneFrame E)

/-- Every entire coefficient evaluated in the completed infinity coordinate is bounded on the
fixed distinguished cusp component. -/
public theorem ExactLiftedModularNegOneFrame.infinity_coordinate_cusp_bounded
    (_F : ExactLiftedModularNegOneFrame E) (f : ℂ → ℂ) (hf : MDiff f) :
    BoundedOn (fun z ↦ f ((E.sourceCoordinate.coordinate z)⁻¹))
      fuchsianCuspRegion := by
  obtain ⟨B, hB, hqB⟩ :=
    E.sourceCoordinate.inverse_coordinate_bounded_on_cusp
  let K : Set ℂ := Metric.closedBall 0 B
  have hK : IsCompact K := isCompact_closedBall 0 B
  obtain ⟨A, hA⟩ := hK.bddAbove_image (hf.continuous.continuousOn.norm)
  refine ⟨max A 0, le_max_right A 0, ?_⟩
  intro z hz
  have hqK : (E.sourceCoordinate.coordinate z)⁻¹ ∈ K := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hqB z hz
  exact (hA ⟨_, hqK, rfl⟩).trans (le_max_left A 0)

/-- The pullback of the infinity-chart `O(-1)` frame.  Parentheses record that the reciprocal is
taken before multiplication by the modular frame. -/
@[expose] public def liftedNegOneInfinityFrame (z : UpperHalfPlane) : ℂ :=
  (E.sourceCoordinate.coordinate z)⁻¹ * F.frame z

public theorem liftedNegOneInfinityFrame_holomorphicAt {z : UpperHalfPlane}
    (hz : E.sourceCoordinate.coordinate z ≠ 0) :
    MDiffAt (liftedNegOneInfinityFrame E F) z := by
  exact (E.sourceCoordinate.coordinate_holomorphic z).inv hz |>.mul
    (F.frame_holomorphic z)

public theorem liftedNegOneInfinityFrame_one (z : UpperHalfPlane) :
    liftedNegOneInfinityFrame E F (fuchsianSourceAction g₁ • z) =
      -liftedNegOneInfinityFrame E F z / E.modularParameter.tau z := by
  rw [liftedNegOneInfinityFrame, liftedNegOneInfinityFrame,
    E.sourceCoordinate.coordinate_invariant, F.frame_one]
  ring

public theorem liftedNegOneInfinityFrame_two (z : UpperHalfPlane) :
    liftedNegOneInfinityFrame E F (fuchsianSourceAction g₂ • z) =
      liftedNegOneInfinityFrame E F z / E.modularParameter.tau z := by
  rw [liftedNegOneInfinityFrame, liftedNegOneInfinityFrame,
    E.sourceCoordinate.coordinate_invariant, F.frame_two]
  ring

/-- The two finite-generator laws imply invariance of the infinity frame under the positive cusp
translation. -/
public theorem liftedNegOneInfinityFrame_product_invariant (z : UpperHalfPlane) :
    liftedNegOneInfinityFrame E F
        (fuchsianSourceAction (g₁ * g₂) • z) =
      liftedNegOneInfinityFrame E F z := by
  rw [map_mul, mul_smul, liftedNegOneInfinityFrame_one,
    liftedNegOneInfinityFrame_two]
  have htau := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.transform_two z)
  rw [rhoTauReal_g₂_smul] at htau
  rw [htau]
  field_simp [(E.modularParameter.tau z).ne_zero]

/-- Hence the infinity frame is invariant under every integral cusp translation. -/
public theorem liftedNegOneInfinityFrame_zpow_invariant (n : ℤ) (z : UpperHalfPlane) :
    liftedNegOneInfinityFrame E F
        (fuchsianSourceAction ((g₁ * g₂) ^ n) • z) =
      liftedNegOneInfinityFrame E F z := by
  have hnat (m : ℕ) (w : UpperHalfPlane) :
      liftedNegOneInfinityFrame E F
          (fuchsianSourceAction ((g₁ * g₂) ^ m) • w) =
        liftedNegOneInfinityFrame E F w := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ', map_mul, mul_smul,
          liftedNegOneInfinityFrame_product_invariant E F, ih]
  cases n with
  | ofNat m => simpa [zpow_ofNat] using hnat m z
  | negSucc m =>
      have h := hnat (m + 1)
        (fuchsianSourceAction ((g₁ * g₂) ^ (Int.negSucc m)) • z)
      have hcancel :
          fuchsianSourceAction ((g₁ * g₂) ^ (m + 1)) •
              (fuchsianSourceAction
                ((g₁ * g₂) ^ (Int.negSucc m)) • z) = z := by
        rw [← mul_smul, ← map_mul]
        simp [zpow_negSucc]
      rw [hcancel] at h
      exact h.symm

private def frameCenteredCuspTruncation (H : ℝ) : Set UpperHalfPlane :=
  {z | -cuspWidth / 2 ≤ z.re ∧ z.re ≤ cuspWidth / 2 ∧
    1 ≤ z.im ∧ z.im ≤ max 1 H}

private theorem frameCenteredCuspTruncation_isCompact (H : ℝ) :
    IsCompact (frameCenteredCuspTruncation H) := by
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
    (hinvariant : ∀ (n : ℤ) z,
      h (fuchsianSourceAction ((g₁ * g₂) ^ n) • z) = h z)
    {B : ℝ} (hB : 0 ≤ B)
    (heventually : ∀ᶠ z in upperHalfPlaneAtInfinity, ‖h z‖ ≤ B) :
    BoundedOn h fuchsianCuspRegion := by
  rw [upperHalfPlaneAtInfinity, eventually_comap, eventually_atTop] at heventually
  obtain ⟨H, hH⟩ := heventually
  let K := frameCenteredCuspTruncation H
  have hK : IsCompact K := frameCenteredCuspTruncation_isCompact H
  have hKsub : K ⊆ fuchsianCuspRegion := fun _ hz ↦ hz.2.2.1
  obtain ⟨A, hA⟩ := hK.bddAbove_image (hcontinuous.mono hKsub).norm
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
    calc
      ‖h z‖ = ‖h w‖ := by
        exact congrArg norm (hinvariant (centerExponent z) z).symm
      _ ≤ A := hA ⟨_, hwmem, rfl⟩
      _ ≤ max A B := le_max_left A B

/-- The eventual completed-cusp factorization and parabolic invariance imply boundedness on the
whole distinguished cusp component. -/
public theorem ExactLiftedModularNegOneFrame.infinity_frame_cusp_bounded :
    BoundedOn (liftedNegOneInfinityFrame E F) fuchsianCuspRegion := by
  let K : Set ℂ := Metric.closedBall 0 (F.cuspRadius / 2)
  have hK : IsCompact K := isCompact_closedBall 0 (F.cuspRadius / 2)
  have hKsub : K ⊆ Metric.ball 0 F.cuspRadius := by
    intro q hq
    have hdist := Metric.mem_closedBall.mp hq
    apply Metric.mem_ball.mpr
    linarith [F.cuspRadius_pos]
  have hunit : ContinuousOn F.cuspUnit K := by
    intro q hq
    exact (F.cuspUnit_holomorphic q (hKsub hq)).continuousAt.continuousWithinAt
  obtain ⟨B, hBound⟩ := hK.bddAbove_image hunit.norm
  have heventually : ∀ᶠ z in upperHalfPlaneAtInfinity,
      ‖liftedNegOneInfinityFrame E F z‖ ≤ max B 0 := by
    filter_upwards [F.inverse_coordinate_eventually_mem_closedBall,
      F.cusp_factorization_eventually] with z hzmem hzfactor
    rw [liftedNegOneInfinityFrame, hzfactor]
    exact (hBound ⟨_, hzmem, rfl⟩).trans (le_max_left B 0)
  apply boundedOn_cusp_of_eventually_bounded
    (liftedNegOneInfinityFrame E F)
  · intro z hz
    exact (liftedNegOneInfinityFrame_holomorphicAt E F
      (E.sourceCoordinate.coordinate_ne_zero_on_cusp z hz)).continuousAt.continuousWithinAt
  · exact liftedNegOneInfinityFrame_zpow_invariant E F
  · exact le_max_right B 0
  · exact heventually

private theorem bounded_comp_mul_of_bounded
    {q h : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (hq : BoundedOn q s) (hh : BoundedOn h s)
    (f : ℂ → ℂ) (hf : MDiff f) :
    BoundedOn (fun z ↦ f (q z) * h z) s := by
  obtain ⟨B, hB, hqB⟩ := hq
  obtain ⟨D, hD, hhD⟩ := hh
  let K : Set ℂ := Metric.closedBall 0 B
  have hK : IsCompact K := isCompact_closedBall 0 B
  obtain ⟨A, hA⟩ := hK.bddAbove_image (hf.continuous.continuousOn.norm)
  refine ⟨max A 0 * D, mul_nonneg (le_max_right A 0) hD, ?_⟩
  intro z hz
  have hqK : q z ∈ K := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hqB z hz
  have hfA : ‖f (q z)‖ ≤ max A 0 :=
    (hA ⟨q z, hqK, rfl⟩).trans (le_max_left A 0)
  rw [norm_mul]
  exact mul_le_mul hfA (hhD z hz) (norm_nonneg _) (le_max_right A 0)

/-- The local cusp-unit theorem implies boundedness of every entire Cech correction on the fixed
distinguished cusp component. -/
public theorem ExactLiftedModularNegOneFrame.cusp_correction_bounded
    (f : ℂ → ℂ) (hf : MDiff f) :
    BoundedOn
      (fun z ↦ f ((E.sourceCoordinate.coordinate z)⁻¹) *
        ((E.sourceCoordinate.coordinate z)⁻¹ * F.frame z))
      fuchsianCuspRegion := by
  simpa only [liftedNegOneInfinityFrame] using
    bounded_comp_mul_of_bounded
      E.sourceCoordinate.inverse_coordinate_bounded_on_cusp
      (F.infinity_frame_cusp_bounded E) f hf

/-- The source preimage of the standard infinity chart. -/
@[expose] public def liftedInfinityRegion : Set UpperHalfPlane :=
  {z | E.sourceCoordinate.coordinate z ≠ 0}

public theorem liftedInfinityRegion_open : IsOpen (liftedInfinityRegion E) := by
  exact isOpen_compl_singleton.preimage E.sourceCoordinate.coordinate_holomorphic.continuous

public theorem liftedInfinityRegion_invariant (g : Delta) (z : UpperHalfPlane) :
    fuchsianSourceAction g • z ∈ liftedInfinityRegion E ↔ z ∈ liftedInfinityRegion E := by
  simp only [liftedInfinityRegion, Set.mem_ofPred_eq]
  rw [E.sourceCoordinate.coordinate_invariant]

public theorem fuchsianCuspRegion_subset_liftedInfinityRegion
    (_F : ExactLiftedModularNegOneFrame E) :
    fuchsianCuspRegion ⊆ liftedInfinityRegion E := by
  intro z hz
  exact E.sourceCoordinate.coordinate_ne_zero_on_cusp z hz

/-- The paper's local beta section at the completed cusp. -/
@[expose] public def cuspLocalBeta (z : UpperHalfPlane) : ℂ :=
  -(E.modularParameter.tau z : ℂ)

public theorem cuspLocalBeta_properties :
    MDiff (cuspLocalBeta E) ∧
      (∀ z, cuspLocalBeta E (fuchsianSourceAction g₀ • z) = cuspLocalBeta E z + 1) ∧
      BoundedOn (fun z ↦ cuspLocalBeta E z + E.modularParameter.tau z)
        fuchsianCuspRegion := by
  have htau : MDiff (fun z ↦ (E.modularParameter.tau z : ℂ)) := by
    intro z
    exact (E.modularParameter.tau z).mdifferentiable_coe.comp z
      (E.modularParameter.tau_holomorphic z)
  refine ⟨htau.neg, ?_, ?_⟩
  · intro z
    have h := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
      (E.modularParameter.equivariant g₀ z)
    rw [rhoTauReal_g0_smul] at h
    change -(E.modularParameter.tau (fuchsianSourceAction g₀ • z) : ℂ) =
      -(E.modularParameter.tau z : ℂ) + 1
    rw [h]
    ring
  · convert (cuspLocalMu_properties E).2.2 using 1
    funext z
    simp [cuspLocalBeta, cuspLocalMu]

/-- All finite cyclic algebraic consistency checks needed before applying affine-torsor descent.
These are the computations in Propositions 3.11 and 3.13, independent of sheaf cohomology. -/
public structure FuchsianAffineCycleCertificate where
  mu_one_closes : ∀ z mu,
    muAffineOne
        (tauOneStep (tauOneStep (E.modularParameter.tau z)))
        (muAffineOne (tauOneStep (E.modularParameter.tau z))
          (muAffineOne (E.modularParameter.tau z) mu)) = mu
  mu_two_closes : ∀ z mu,
    muAffineTwo
        (tauTwoStep (tauTwoStep (tauTwoStep (E.modularParameter.tau z))))
        (muAffineTwo (tauTwoStep (tauTwoStep (E.modularParameter.tau z)))
          (muAffineTwo (tauTwoStep (E.modularParameter.tau z))
            (muAffineTwo (E.modularParameter.tau z) mu))) = mu
  beta_one_cycle : ∀ z mu,
    let x : Parameters := ⟨E.modularParameter.tau z, mu, 0⟩
    betaCocycleOne x + betaCocycleOne (transformOne x) +
      betaCocycleOne (transformOne (transformOne x)) = 0
  beta_two_cycle : ∀ z mu,
    let x : Parameters := ⟨E.modularParameter.tau z, mu, 0⟩
    betaCocycleTwo x + betaCocycleTwo (transformTwo x) +
        betaCocycleTwo (transformTwo (transformTwo x)) +
      betaCocycleTwo (transformTwo (transformTwo (transformTwo x))) = 0

/-- The explicit substitutions supply the complete finite-cycle certificate. -/
public theorem establishedFuchsianAffineCycleCertificate :
    FuchsianAffineCycleCertificate E where
  mu_one_closes := muAffineOne_closes E
  mu_two_closes := muAffineTwo_closes E
  beta_one_cycle := by
    intro z mu
    exact betaCocycleOne_cycle _ (E.modularParameter.tau z).ne_zero (tau_coe_ne_one E z)
  beta_two_cycle := by
    intro z mu
    exact betaCocycleTwo_cycle _ (E.modularParameter.tau z).ne_zero

@[expose] public def fuchsianMuAffineOne (z : UpperHalfPlane) (mu : ℂ) : ℂ :=
  (1 - mu) / E.modularParameter.tau z

@[expose] public def fuchsianMuAffineTwo (z : UpperHalfPlane) (mu : ℂ) : ℂ :=
  1 + mu / E.modularParameter.tau z

@[expose] public def fuchsianMuLinearOne (z : UpperHalfPlane) : ℂ :=
  -1 / E.modularParameter.tau z

@[expose] public def fuchsianMuLinearTwo (z : UpperHalfPlane) : ℂ :=
  1 / E.modularParameter.tau z

private theorem tau_coe_mdifferentiable :
    MDiff (fun z ↦ (E.modularParameter.tau z : ℂ)) := by
  intro z
  exact (E.modularParameter.tau z).mdifferentiable_coe.comp z
    (E.modularParameter.tau_holomorphic z)

private theorem tau_one_coe (z : UpperHalfPlane) :
    (E.modularParameter.tau (fuchsianSourceAction g₁ • z) : ℂ) =
      tauOneStep (E.modularParameter.tau z) := by
  exact (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.transform_one z)).trans (rhoTauReal_g₁_smul _)

private theorem tau_two_coe (z : UpperHalfPlane) :
    (E.modularParameter.tau (fuchsianSourceAction g₂ • z) : ℂ) =
      tauTwoStep (E.modularParameter.tau z) := by
  exact (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.transform_two z)).trans (rhoTauReal_g₂_smul _)

private theorem tau_one_sq_coe (z : UpperHalfPlane) :
    (E.modularParameter.tau (fuchsianSourceAction (g₁ ^ 2) • z) : ℂ) =
      tauOneStep (tauOneStep (E.modularParameter.tau z)) := by
  rw [map_pow, pow_two, mul_smul, tau_one_coe E, tau_one_coe E]

private theorem tau_two_sq_coe (z : UpperHalfPlane) :
    (E.modularParameter.tau (fuchsianSourceAction (g₂ ^ 2) • z) : ℂ) =
      tauTwoStep (tauTwoStep (E.modularParameter.tau z)) := by
  rw [map_pow, pow_two, mul_smul, tau_two_coe E, tau_two_coe E]

private theorem tau_two_cube_coe (z : UpperHalfPlane) :
    (E.modularParameter.tau (fuchsianSourceAction (g₂ ^ 3) • z) : ℂ) =
      tauTwoStep (tauTwoStep (tauTwoStep (E.modularParameter.tau z))) := by
  rw [show g₂ ^ 3 = g₂ ^ 2 * g₂ by rw [pow_succ], map_mul, mul_smul,
    tau_two_sq_coe E, tau_two_coe E]

private theorem fuchsianMuAffine_product (z : UpperHalfPlane) (mu : ℂ) :
    fuchsianMuAffineOne E (fuchsianSourceAction g₂ • z)
        (fuchsianMuAffineTwo E z mu) = mu := by
  rw [fuchsianMuAffineOne, fuchsianMuAffineTwo, tau_two_coe E]
  simp only [tauTwoStep]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- The explicit affine `mu` substitutions and local primitives satisfy every hypothesis of the
general orbifold affine-torsor descent theorem. -/
@[expose] public noncomputable def fuchsianMuDescentProblem :
    OrbifoldAffineLineTorsorDescentProblem where
  quotient := E.sourceCoordinate
  affineOne := fuchsianMuAffineOne E
  affineTwo := fuchsianMuAffineTwo E
  affineCusp := fun _ mu ↦ mu
  affineOne_holomorphic := by
    intro s hs
    exact (mdifferentiable_const.sub hs).div (tau_coe_mdifferentiable E)
      (fun z ↦ (E.modularParameter.tau z).ne_zero)
  affineTwo_holomorphic := by
    intro s hs
    exact mdifferentiable_const.add
      (hs.div (tau_coe_mdifferentiable E) (fun z ↦ (E.modularParameter.tau z).ne_zero))
  affineCusp_holomorphic := fun s hs ↦ hs
  linearOne := fuchsianMuLinearOne E
  linearTwo := fuchsianMuLinearTwo E
  affineOne_sub := by
    intro z u v
    simp only [fuchsianMuAffineOne, fuchsianMuLinearOne]
    field_simp [(E.modularParameter.tau z).ne_zero]
    ring
  affineTwo_sub := by
    intro z u v
    simp only [fuchsianMuAffineTwo, fuchsianMuLinearTwo]
    field_simp [(E.modularParameter.tau z).ne_zero]
    ring
  affineOne_cycle := by
    intro z mu
    rw [fuchsianMuAffineOne, fuchsianMuAffineOne, fuchsianMuAffineOne,
      tau_one_coe E, tau_one_sq_coe E]
    exact (establishedFuchsianAffineCycleCertificate E).mu_one_closes z mu
  affineTwo_cycle := by
    intro z mu
    rw [fuchsianMuAffineTwo, fuchsianMuAffineTwo, fuchsianMuAffineTwo,
      fuchsianMuAffineTwo, tau_two_coe E, tau_two_sq_coe E, tau_two_cube_coe E]
    exact (establishedFuchsianAffineCycleCertificate E).mu_two_closes z mu
  product_cusp := by
    intro z mu
    exact fuchsianMuAffine_product E z mu
  cusp_product := by
    intro z mu
    exact fuchsianMuAffine_product E (fuchsianSourceAction g₀ • z) mu
  frameZero := F.frame
  frameInfinity := liftedNegOneInfinityFrame E F
  frameZero_holomorphic := F.frame_holomorphic
  frameInfinity_holomorphic := fun _ hz ↦
    liftedNegOneInfinityFrame_holomorphicAt E F hz
  frameZero_one := by
    intro z
    rw [F.frame_one]
    simp only [fuchsianMuLinearOne]
    ring
  frameZero_two := by
    intro z
    rw [F.frame_two]
    simp only [fuchsianMuLinearTwo]
    ring
  frameInfinity_one := by
    intro z _
    rw [liftedNegOneInfinityFrame_one E F]
    simp only [fuchsianMuLinearOne]
    ring
  frameInfinity_two := by
    intro z _
    rw [liftedNegOneInfinityFrame_two E F]
    simp only [fuchsianMuLinearTwo]
    ring
  frameOrderOne := 2
  frameOrderTwo := 1
  frameZero_branch_one := {
    uniformizer := F.frame_branch_one.uniformizer
    uniformizer_center := F.frame_branch_one.uniformizer_center
    uniformizer_isLocalDiffeomorph := F.frame_branch_one.uniformizer_isLocalDiffeomorph
    unit := F.frame_branch_one.unit
    unit_holomorphic := F.frame_branch_one.unit_holomorphic
    unit_ne_zero := F.frame_branch_one.unit_ne_zero
    factorization := by
      simpa using F.frame_branch_one.factorization }
  frameZero_branch_two := {
    uniformizer := F.frame_branch_two.uniformizer
    uniformizer_center := F.frame_branch_two.uniformizer_center
    uniformizer_isLocalDiffeomorph := F.frame_branch_two.uniformizer_isLocalDiffeomorph
    unit := F.frame_branch_two.unit
    unit_holomorphic := F.frame_branch_two.unit_holomorphic
    unit_ne_zero := F.frame_branch_two.unit_ne_zero
    factorization := by
      simpa using F.frame_branch_two.factorization }
  frameZero_zero_iff := by
    intro z
    simpa using F.frame_zero_iff z
  frameTransition := fun q ↦ q⁻¹
  frameTransition_holomorphic := by
    intro q hq
    exact mdifferentiableAt_id.inv hq
  frame_transition := fun _ _ ↦ rfl
  cuspFrameUnit := F.cuspUnit
  cuspFrameRadius := F.cuspRadius
  cuspFrameRadius_pos := F.cuspRadius_pos
  cuspFrameUnit_holomorphic := F.cuspUnit_holomorphic
  cuspFrameUnit_zero_ne := F.cuspUnit_zero_ne
  inverse_coordinate_eventually_mem_closedBall :=
    F.inverse_coordinate_eventually_mem_closedBall
  frameInfinity_cusp_factorization_eventually :=
    F.cusp_factorization_eventually
  ellipticOne := ellipticMuOne E
  ellipticTwo := ellipticMuTwo E
  ellipticOne_holomorphic := ellipticMuOne_holomorphic E
  ellipticTwo_holomorphic := ellipticMuTwo_holomorphic E
  ellipticOne_equivariant := by
    intro z
    exact ellipticMuOne_transform E z
  ellipticTwo_equivariant := by
    intro z
    exact ellipticMuTwo_transform E z
  cuspSection := cuspLocalMu E
  cuspSection_holomorphic := (cuspLocalMu_properties E).1
  cuspSection_equivariant := fun _ ↦ rfl
  cusp_coordinate_ne_zero := E.sourceCoordinate.coordinate_ne_zero_on_cusp
  cuspNormalize := fun _ mu ↦ mu
  cuspNormalize_sub := by
    intro z u v
    rfl
  cuspNormalize_holomorphic := by
    intro s hs
    exact hs
  cuspNormalize_equivariant := by
    intro z u
    rfl
  cuspSection_normalized_bounded := (cuspLocalMu_properties E).2.2

/-- The exact modular frame supplies the full `O(-1)` frame portion of the paper's Cech
presentation.  The only data still absent are affine local sections of the torsor. -/
public structure MuAffineCechSections where
  sectionZero : UpperHalfPlane → ℂ
  sectionInfinity : UpperHalfPlane → ℂ
  sectionZero_holomorphic : MDiff sectionZero
  sectionInfinity_holomorphic : ∀ z, z ∈ liftedInfinityRegion E →
    MDiffAt sectionInfinity z
  sectionZero_one : ∀ z,
    sectionZero (fuchsianSourceAction g₁ • z) =
      (1 - sectionZero z) / E.modularParameter.tau z
  sectionZero_two : ∀ z,
    sectionZero (fuchsianSourceAction g₂ • z) =
      1 + sectionZero z / E.modularParameter.tau z
  sectionInfinity_one : ∀ z, z ∈ liftedInfinityRegion E →
    sectionInfinity (fuchsianSourceAction g₁ • z) =
      (1 - sectionInfinity z) / E.modularParameter.tau z
  sectionInfinity_two : ∀ z, z ∈ liftedInfinityRegion E →
    sectionInfinity (fuchsianSourceAction g₂ • z) =
      1 + sectionInfinity z / E.modularParameter.tau z
  overlapCocycle : ℂ → ℂ
  overlapCocycle_holomorphic : HolomorphicOnPuncturedPlane overlapCocycle
  section_mismatch : ∀ z, z ∈ liftedInfinityRegion E →
    sectionZero z - sectionInfinity z =
      overlapCocycle (E.sourceCoordinate.coordinate z) * F.frame z
  sectionInfinity_cusp_bounded :
    BoundedOn sectionInfinity fuchsianCuspRegion

/-- Convert one concrete analytic descent certificate into the exact `mu` Cech sections consumed
by the Fuchsian construction. -/
@[expose] public def muAffineCechSectionsOfAnalyticDescentData
    (A : (fuchsianMuDescentProblem E F).AnalyticDescentData) :
    MuAffineCechSections E F := by
  let S := A.toTwoChartSections
  refine {
    sectionZero := S.sectionZero
    sectionInfinity := S.sectionInfinity
    sectionZero_holomorphic := S.sectionZero_holomorphic
    sectionInfinity_holomorphic := S.sectionInfinity_holomorphic
    sectionZero_one := ?_
    sectionZero_two := ?_
    sectionInfinity_one := ?_
    sectionInfinity_two := ?_
    overlapCocycle := S.overlapCocycle
    overlapCocycle_holomorphic := S.overlapCocycle_holomorphic
    section_mismatch := S.section_mismatch
    sectionInfinity_cusp_bounded := S.sectionInfinity_normalized_cusp_bounded }
  · intro z
    exact S.sectionZero_one z
  · intro z
    exact S.sectionZero_two z
  · intro z hz
    exact S.sectionInfinity_one z hz
  · intro z hz
    exact S.sectionInfinity_two z hz

/-- Analytic orbifold affine-torsor descent supplies the two exact `mu` chart sections from the
explicit modular frame, finite-cycle certificate, elliptic primitives, and cusp primitive. -/
public theorem exists_muAffineCechSections
    (A : (fuchsianMuDescentProblem E F).AnalyticDescentData) :
    Nonempty (MuAffineCechSections E F) :=
  ⟨muAffineCechSectionsOfAnalyticDescentData E F A⟩

/-- Combining the independent modular-frame theorem with affine local triviality gives exactly the
`mu` local data consumed by the Cech splitting theorem. -/
@[expose] public noncomputable def MuAffineCechSections.toLocalData
    (S : MuAffineCechSections E F) : MuTorsorCechLocalData E where
  zeroRegion := Set.univ
  infinityRegion := liftedInfinityRegion E
  zeroRegion_open := isOpen_univ
  infinityRegion_open := liftedInfinityRegion_open E
  regions_cover := Set.univ_union _
  zeroRegion_invariant := by simp
  infinityRegion_invariant := liftedInfinityRegion_invariant E
  sectionZero := S.sectionZero
  sectionInfinity := S.sectionInfinity
  sectionZero_holomorphic := fun z _ ↦ S.sectionZero_holomorphic z
  sectionInfinity_holomorphic := S.sectionInfinity_holomorphic
  sectionZero_one := fun z _ ↦ S.sectionZero_one z
  sectionZero_two := fun z _ ↦ S.sectionZero_two z
  sectionInfinity_one := S.sectionInfinity_one
  sectionInfinity_two := S.sectionInfinity_two
  frameZero := F.frame
  frameInfinity := liftedNegOneInfinityFrame E F
  frameZero_holomorphic := fun z _ ↦ F.frame_holomorphic z
  frameInfinity_holomorphic := fun _ hz ↦
    liftedNegOneInfinityFrame_holomorphicAt E F hz
  frameZero_one := fun z _ ↦ F.frame_one z
  frameZero_two := fun z _ ↦ F.frame_two z
  frameInfinity_one := fun z _ ↦ liftedNegOneInfinityFrame_one E F z
  frameInfinity_two := fun z _ ↦ liftedNegOneInfinityFrame_two E F z
  overlapCocycle := S.overlapCocycle
  overlapCocycle_holomorphic := S.overlapCocycle_holomorphic
  infinity_coordinate_ne_zero := fun z hz ↦ hz
  frame_transition := by
    intro z _
    rfl
  section_mismatch := fun z hz ↦ S.section_mismatch z hz.2
  cusp_subset_infinity := fuchsianCuspRegion_subset_liftedInfinityRegion E F
  sectionInfinity_cusp_bounded := S.sectionInfinity_cusp_bounded
  infinity_frame_cusp_bounded := F.cusp_correction_bounded E

/-- Exact affine local sections for the structure-sheaf `beta` torsor.  Unlike the modular frame
above, this is not assumed as established input: it names the remaining application of general
holomorphic affine-torsor local triviality. -/
public structure BetaAffineCechSections (mu : UpperHalfPlane → ℂ) where
  data : BetaTorsorCechLocalData E mu

@[expose] public def fuchsianBetaParameter
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : Parameters :=
  ⟨E.modularParameter.tau z, mu z, 0⟩

@[expose] public def fuchsianBetaAffineOne
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) (beta : ℂ) : ℂ :=
  beta + betaCocycleOne (fuchsianBetaParameter E mu z)

@[expose] public def fuchsianBetaAffineTwo
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) (beta : ℂ) : ℂ :=
  beta + betaCocycleTwo (fuchsianBetaParameter E mu z)

@[expose] public def ellipticBetaOne
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  localBetaOne (fuchsianBetaParameter E mu z)

@[expose] public def ellipticBetaTwo
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  localBetaTwo (fuchsianBetaParameter E mu z)

private theorem fuchsianBetaParameter_one_tau
    {mu : UpperHalfPlane → ℂ} (z : UpperHalfPlane) :
    (fuchsianBetaParameter E mu (fuchsianSourceAction g₁ • z)).tau =
      (transformOne (fuchsianBetaParameter E mu z)).tau := by
  rw [fuchsianBetaParameter, fuchsianBetaParameter, transformOne_tau]
  exact tau_one_coe E z

private theorem fuchsianBetaParameter_two_tau
    {mu : UpperHalfPlane → ℂ} (z : UpperHalfPlane) :
    (fuchsianBetaParameter E mu (fuchsianSourceAction g₂ • z)).tau =
      (transformTwo (fuchsianBetaParameter E mu z)).tau := by
  rw [fuchsianBetaParameter, fuchsianBetaParameter, transformTwo_tau]
  exact tau_two_coe E z

private theorem fuchsianBetaParameter_one_mu
    {mu : UpperHalfPlane → ℂ}
    (hmuOne : ∀ z, mu (fuchsianSourceAction g₁ • z) =
      (1 - mu z) / E.modularParameter.tau z) (z : UpperHalfPlane) :
    (fuchsianBetaParameter E mu (fuchsianSourceAction g₁ • z)).mu =
      (transformOne (fuchsianBetaParameter E mu z)).mu := by
  rw [fuchsianBetaParameter, fuchsianBetaParameter, transformOne_mu]
  exact hmuOne z

private theorem fuchsianBetaParameter_two_mu
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    (fuchsianBetaParameter E mu (fuchsianSourceAction g₂ • z)).mu =
      (transformTwo (fuchsianBetaParameter E mu z)).mu := by
  rw [fuchsianBetaParameter, fuchsianBetaParameter, transformTwo_mu]
  exact hmuTwo z

private theorem betaCocycleOne_fuchsian_step
    {mu : UpperHalfPlane → ℂ}
    (hmuOne : ∀ z, mu (fuchsianSourceAction g₁ • z) =
      (1 - mu z) / E.modularParameter.tau z) (z : UpperHalfPlane) :
    betaCocycleOne (fuchsianBetaParameter E mu (fuchsianSourceAction g₁ • z)) =
      betaCocycleOne (transformOne (fuchsianBetaParameter E mu z)) := by
  rw [betaCocycleOne, fuchsianBetaParameter_one_mu E hmuOne z,
    fuchsianBetaParameter_one_tau E z]
  rfl

private theorem betaCocycleTwo_fuchsian_step
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    betaCocycleTwo (fuchsianBetaParameter E mu (fuchsianSourceAction g₂ • z)) =
      betaCocycleTwo (transformTwo (fuchsianBetaParameter E mu z)) := by
  rw [betaCocycleTwo, fuchsianBetaParameter_two_mu E hmuTwo z,
    fuchsianBetaParameter_two_tau E z]
  rfl

private theorem localBetaOne_congr_tau_mu (x y : Parameters)
    (htau : x.tau = y.tau) (hmu : x.mu = y.mu) :
    localBetaOne x = localBetaOne y := by
  cases x with
  | mk xt xm xb =>
    cases y with
    | mk yt ym yb =>
      simp only at htau hmu
      subst yt
      subst ym
      simp [localBetaOne, betaCocycleOne, transformOne]

private theorem localBetaTwo_congr_tau_mu (x y : Parameters)
    (htau : x.tau = y.tau) (hmu : x.mu = y.mu) :
    localBetaTwo x = localBetaTwo y := by
  cases x with
  | mk xt xm xb =>
    cases y with
    | mk yt ym yb =>
      simp only at htau hmu
      subst yt
      subst ym
      simp [localBetaTwo, betaCocycleTwo, transformTwo]

private theorem betaCocycleOne_transform_congr_tau_mu (x y : Parameters)
    (htau : x.tau = y.tau) (hmu : x.mu = y.mu) :
    betaCocycleOne (transformOne x) = betaCocycleOne (transformOne y) := by
  cases x with
  | mk xt xm xb =>
    cases y with
    | mk yt ym yb =>
      simp only at htau hmu
      subst yt
      subst ym
      simp [betaCocycleOne, transformOne]

private theorem betaCocycleTwo_transform_congr_tau_mu (x y : Parameters)
    (htau : x.tau = y.tau) (hmu : x.mu = y.mu) :
    betaCocycleTwo (transformTwo x) = betaCocycleTwo (transformTwo y) := by
  cases x with
  | mk xt xm xb =>
    cases y with
    | mk yt ym yb =>
      simp only at htau hmu
      subst yt
      subst ym
      simp [betaCocycleTwo, transformTwo]

private theorem betaCocycleOne_fuchsian_sq
    {mu : UpperHalfPlane → ℂ}
    (hmuOne : ∀ z, mu (fuchsianSourceAction g₁ • z) =
      (1 - mu z) / E.modularParameter.tau z) (z : UpperHalfPlane) :
    betaCocycleOne (fuchsianBetaParameter E mu (fuchsianSourceAction (g₁ ^ 2) • z)) =
      betaCocycleOne (transformOne (transformOne (fuchsianBetaParameter E mu z))) := by
  rw [map_pow, pow_two, mul_smul, betaCocycleOne_fuchsian_step E hmuOne]
  exact betaCocycleOne_transform_congr_tau_mu _ _
    (fuchsianBetaParameter_one_tau E z) (fuchsianBetaParameter_one_mu E hmuOne z)

private theorem betaCocycleTwo_fuchsian_sq
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    betaCocycleTwo (fuchsianBetaParameter E mu (fuchsianSourceAction (g₂ ^ 2) • z)) =
      betaCocycleTwo (transformTwo (transformTwo (fuchsianBetaParameter E mu z))) := by
  rw [map_pow, pow_two, mul_smul, betaCocycleTwo_fuchsian_step E hmuTwo]
  exact betaCocycleTwo_transform_congr_tau_mu _ _
    (fuchsianBetaParameter_two_tau E z) (fuchsianBetaParameter_two_mu E hmuTwo z)

private theorem fuchsianBetaParameter_two_sq_tau
    {mu : UpperHalfPlane → ℂ} (z : UpperHalfPlane) :
    (fuchsianBetaParameter E mu (fuchsianSourceAction (g₂ ^ 2) • z)).tau =
      (transformTwo (transformTwo (fuchsianBetaParameter E mu z))).tau := by
  rw [map_pow, pow_two, mul_smul, fuchsianBetaParameter_two_tau E,
    transformTwo_tau, fuchsianBetaParameter_two_tau E, transformTwo_tau]
  rw [transformTwo_tau, transformTwo_tau]

private theorem fuchsianBetaParameter_two_sq_mu
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    (fuchsianBetaParameter E mu (fuchsianSourceAction (g₂ ^ 2) • z)).mu =
      (transformTwo (transformTwo (fuchsianBetaParameter E mu z))).mu := by
  rw [map_pow, pow_two, mul_smul, fuchsianBetaParameter_two_mu E hmuTwo,
    transformTwo_mu, fuchsianBetaParameter_two_tau E,
    fuchsianBetaParameter_two_mu E hmuTwo, transformTwo_mu]
  rw [← transformTwo_mu, ← transformTwo_mu]

private theorem betaCocycleTwo_fuchsian_cube
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    betaCocycleTwo (fuchsianBetaParameter E mu (fuchsianSourceAction (g₂ ^ 3) • z)) =
      betaCocycleTwo
        (transformTwo (transformTwo (transformTwo (fuchsianBetaParameter E mu z)))) := by
  rw [show g₂ ^ 3 = g₂ * (g₂ ^ 2) by rw [pow_succ'], map_mul, mul_smul,
    betaCocycleTwo_fuchsian_step E hmuTwo]
  exact betaCocycleTwo_transform_congr_tau_mu _ _
    (fuchsianBetaParameter_two_sq_tau E z)
    (fuchsianBetaParameter_two_sq_mu E hmuTwo z)

public theorem ellipticBetaOne_equivariant
    {mu : UpperHalfPlane → ℂ}
    (hmuOne : ∀ z, mu (fuchsianSourceAction g₁ • z) =
      (1 - mu z) / E.modularParameter.tau z) (z : UpperHalfPlane) :
    ellipticBetaOne E mu (fuchsianSourceAction g₁ • z) =
      fuchsianBetaAffineOne E mu z (ellipticBetaOne E mu z) := by
  have hcongr :
      localBetaOne (fuchsianBetaParameter E mu (fuchsianSourceAction g₁ • z)) =
        localBetaOne (transformOne (fuchsianBetaParameter E mu z)) :=
    localBetaOne_congr_tau_mu _ _ (fuchsianBetaParameter_one_tau E z)
      (fuchsianBetaParameter_one_mu E hmuOne z)
  rw [ellipticBetaOne, ellipticBetaOne, hcongr, fuchsianBetaAffineOne]
  exact localBetaOne_transform _ (E.modularParameter.tau z).ne_zero (tau_coe_ne_one E z)

public theorem ellipticBetaTwo_equivariant
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    ellipticBetaTwo E mu (fuchsianSourceAction g₂ • z) =
      fuchsianBetaAffineTwo E mu z (ellipticBetaTwo E mu z) := by
  have hcongr :
      localBetaTwo (fuchsianBetaParameter E mu (fuchsianSourceAction g₂ • z)) =
        localBetaTwo (transformTwo (fuchsianBetaParameter E mu z)) :=
    localBetaTwo_congr_tau_mu _ _ (fuchsianBetaParameter_two_tau E z)
      (fuchsianBetaParameter_two_mu E hmuTwo z)
  rw [ellipticBetaTwo, ellipticBetaTwo, hcongr, fuchsianBetaAffineTwo]
  exact localBetaTwo_transform _ (E.modularParameter.tau z).ne_zero

private def ellipticBetaOneFormula
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  let tau : ℂ := E.modularParameter.tau z
  2 + (-2 * (tau - 1 + mu z) ^ 2 + 4 * mu z ^ 2 * tau) / (tau * (tau - 1))

private def ellipticBetaTwoFormula
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  let tau : ℂ := E.modularParameter.tau z
  (-9 / 2 : ℂ) + (3 / 2) *
    (((tau + mu z) ^ 2 - 2 * (1 - tau - mu z) ^ 2 + 3 * (1 - mu z) ^ 2) / tau)

private theorem ellipticBetaOne_eq_formula
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ellipticBetaOne E mu z = ellipticBetaOneFormula E mu z := by
  unfold ellipticBetaOne ellipticBetaOneFormula localBetaOne betaCocycleOne
    fuchsianBetaParameter
  dsimp only [transformOne]
  have hsub : (E.modularParameter.tau z : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (tau_coe_ne_one E z)
  field_simp [(E.modularParameter.tau z).ne_zero, hsub]
  ring

private theorem ellipticBetaTwo_eq_formula
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ellipticBetaTwo E mu z = ellipticBetaTwoFormula E mu z := by
  unfold ellipticBetaTwo ellipticBetaTwoFormula localBetaTwo betaCocycleTwo
    fuchsianBetaParameter
  dsimp only [transformTwo]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

public theorem ellipticBetaOne_holomorphic
    {mu : UpperHalfPlane → ℂ} (hmu : MDiff mu) :
    MDiff (ellipticBetaOne E mu) := by
  have heq : ellipticBetaOne E mu = ellipticBetaOneFormula E mu := by
    funext z
    exact ellipticBetaOne_eq_formula E mu z
  rw [heq]
  intro z
  unfold ellipticBetaOneFormula
  have ht := tau_coe_mdifferentiable E z
  have hm := hmu z
  have hsub : (E.modularParameter.tau z : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (tau_coe_ne_one E z)
  have hnum : MDiffAt
      (fun w ↦ -2 * ((E.modularParameter.tau w : ℂ) - 1 + mu w) ^ 2 +
        4 * mu w ^ 2 * E.modularParameter.tau w : UpperHalfPlane → ℂ) z :=
    (mdifferentiableAt_const.mul (((ht.sub mdifferentiableAt_const).add hm).pow 2)).add
      ((mdifferentiableAt_const.mul (hm.pow 2)).mul ht)
  exact mdifferentiableAt_const.add
    (hnum.div (ht.mul (ht.sub mdifferentiableAt_const))
      (mul_ne_zero (E.modularParameter.tau z).ne_zero hsub))

public theorem ellipticBetaTwo_holomorphic
    {mu : UpperHalfPlane → ℂ} (hmu : MDiff mu) :
    MDiff (ellipticBetaTwo E mu) := by
  have heq : ellipticBetaTwo E mu = ellipticBetaTwoFormula E mu := by
    funext z
    exact ellipticBetaTwo_eq_formula E mu z
  rw [heq]
  intro z
  unfold ellipticBetaTwoFormula
  have ht := tau_coe_mdifferentiable E z
  have hm := hmu z
  have hnum : MDiffAt
      (fun w ↦ ((E.modularParameter.tau w : ℂ) + mu w) ^ 2 -
          2 * (1 - E.modularParameter.tau w - mu w) ^ 2 +
        3 * (1 - mu w) ^ 2 : UpperHalfPlane → ℂ) z :=
    ((ht.add hm).pow 2).sub
        (mdifferentiableAt_const.mul
          ((mdifferentiableAt_const.sub ht |>.sub hm).pow 2)) |>.add
      (mdifferentiableAt_const.mul ((mdifferentiableAt_const.sub hm).pow 2))
  exact mdifferentiableAt_const.add
    (mdifferentiableAt_const.mul
      (hnum.div ht (E.modularParameter.tau z).ne_zero))

public theorem fuchsianBetaAffineOne_cycle
    {mu : UpperHalfPlane → ℂ}
    (hmuOne : ∀ z, mu (fuchsianSourceAction g₁ • z) =
      (1 - mu z) / E.modularParameter.tau z) (z : UpperHalfPlane) (beta : ℂ) :
    fuchsianBetaAffineOne E mu (fuchsianSourceAction (g₁ ^ 2) • z)
        (fuchsianBetaAffineOne E mu (fuchsianSourceAction g₁ • z)
          (fuchsianBetaAffineOne E mu z beta)) = beta := by
  simp only [fuchsianBetaAffineOne]
  rw [betaCocycleOne_fuchsian_step E hmuOne z,
    betaCocycleOne_fuchsian_sq E hmuOne z]
  have hcycle := (establishedFuchsianAffineCycleCertificate E).beta_one_cycle z (mu z)
  dsimp only at hcycle
  have hcycle' :
      betaCocycleOne (fuchsianBetaParameter E mu z) +
          betaCocycleOne (transformOne (fuchsianBetaParameter E mu z)) +
        betaCocycleOne (transformOne (transformOne (fuchsianBetaParameter E mu z))) = 0 := by
    simpa only [fuchsianBetaParameter] using hcycle
  linear_combination hcycle'

public theorem fuchsianBetaAffineTwo_cycle
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) (beta : ℂ) :
    fuchsianBetaAffineTwo E mu (fuchsianSourceAction (g₂ ^ 3) • z)
        (fuchsianBetaAffineTwo E mu (fuchsianSourceAction (g₂ ^ 2) • z)
          (fuchsianBetaAffineTwo E mu (fuchsianSourceAction g₂ • z)
            (fuchsianBetaAffineTwo E mu z beta))) = beta := by
  simp only [fuchsianBetaAffineTwo]
  rw [betaCocycleTwo_fuchsian_step E hmuTwo z,
    betaCocycleTwo_fuchsian_sq E hmuTwo z,
    betaCocycleTwo_fuchsian_cube E hmuTwo z]
  have hcycle := (establishedFuchsianAffineCycleCertificate E).beta_two_cycle z (mu z)
  dsimp only at hcycle
  have hcycle' :
      betaCocycleTwo (fuchsianBetaParameter E mu z) +
            betaCocycleTwo (transformTwo (fuchsianBetaParameter E mu z)) +
          betaCocycleTwo (transformTwo (transformTwo (fuchsianBetaParameter E mu z))) +
        betaCocycleTwo
          (transformTwo (transformTwo (transformTwo (fuchsianBetaParameter E mu z)))) = 0 := by
    simpa only [fuchsianBetaParameter] using hcycle
  linear_combination hcycle'

public theorem fuchsianBetaAffine_product
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) (beta : ℂ) :
    fuchsianBetaAffineOne E mu (fuchsianSourceAction g₂ • z)
        (fuchsianBetaAffineTwo E mu z beta) = beta - 1 := by
  unfold fuchsianBetaAffineOne fuchsianBetaAffineTwo fuchsianBetaParameter
    betaCocycleOne betaCocycleTwo
  rw [tau_two_coe E, hmuTwo]
  simp only [tauTwoStep]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- The selected descended `mu` supplies an exact structure-sheaf affine torsor for `beta`; all
paper-specific algebra and local primitives are discharged before the general descent theorem is
invoked. -/
@[expose] public noncomputable def fuchsianBetaDescentProblem
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    OrbifoldAffineLineTorsorDescentProblem := by
  let mu := descendedFuchsianMu E Dmu
  have hmu := descendedFuchsianMu_spec E Dmu
  exact {
    quotient := E.sourceCoordinate
    affineOne := fuchsianBetaAffineOne E mu
    affineTwo := fuchsianBetaAffineTwo E mu
    affineCusp := fun _ beta ↦ beta + 1
    affineOne_holomorphic := by
      intro s hs
      exact hs.add
        (mdifferentiable_const.sub
          ((mdifferentiable_const.mul ((mdifferentiable_const.sub hmu.1).pow 2)).div
            (tau_coe_mdifferentiable E) (fun z ↦ (E.modularParameter.tau z).ne_zero)))
    affineTwo_holomorphic := by
      intro s hs
      exact hs.add
        (mdifferentiable_const.sub
          ((mdifferentiable_const.mul (hmu.1.pow 2)).div
            (tau_coe_mdifferentiable E) (fun z ↦ (E.modularParameter.tau z).ne_zero)))
    affineCusp_holomorphic := by
      intro s hs
      exact hs.add mdifferentiable_const
    linearOne := fun _ ↦ 1
    linearTwo := fun _ ↦ 1
    affineOne_sub := by
      intro z u v
      simp only [fuchsianBetaAffineOne]
      ring
    affineTwo_sub := by
      intro z u v
      simp only [fuchsianBetaAffineTwo]
      ring
    affineOne_cycle := fuchsianBetaAffineOne_cycle E hmu.2.1
    affineTwo_cycle := fuchsianBetaAffineTwo_cycle E hmu.2.2.1
    product_cusp := by
      intro z beta
      rw [fuchsianBetaAffine_product E hmu.2.2.1]
      ring
    cusp_product := by
      intro z beta
      rw [map_mul, mul_smul, fuchsianBetaAffine_product E hmu.2.2.1]
      ring
    frameZero := fun _ ↦ 1
    frameInfinity := fun _ ↦ 1
    frameZero_holomorphic := mdifferentiable_const
    frameInfinity_holomorphic := fun _ _ ↦ mdifferentiableAt_const
    frameZero_one := fun _ ↦ by simp
    frameZero_two := fun _ ↦ by simp
    frameInfinity_one := fun _ _ ↦ by simp
    frameInfinity_two := fun _ _ ↦ by simp
    frameOrderOne := 0
    frameOrderTwo := 0
    frameZero_branch_one := {
      uniformizer := E.sourceCoordinate.branch_one.uniformizer
      uniformizer_center := E.sourceCoordinate.branch_one.uniformizer_center
      uniformizer_isLocalDiffeomorph :=
        E.sourceCoordinate.branch_one.uniformizer_isLocalDiffeomorph
      unit := fun _ ↦ 1
      unit_holomorphic := mdifferentiableAt_const
      unit_ne_zero := one_ne_zero
      factorization := Filter.Eventually.of_forall (by simp) }
    frameZero_branch_two := {
      uniformizer := E.sourceCoordinate.branch_two.uniformizer
      uniformizer_center := E.sourceCoordinate.branch_two.uniformizer_center
      uniformizer_isLocalDiffeomorph :=
        E.sourceCoordinate.branch_two.uniformizer_isLocalDiffeomorph
      unit := fun _ ↦ 1
      unit_holomorphic := mdifferentiableAt_const
      unit_ne_zero := one_ne_zero
      factorization := Filter.Eventually.of_forall (by simp) }
    frameZero_zero_iff := by simp
    frameTransition := fun _ ↦ 1
    frameTransition_holomorphic := by
      intro q _
      exact mdifferentiableAt_const
    frame_transition := fun _ _ ↦ by simp
    cuspFrameUnit := fun _ ↦ 1
    cuspFrameRadius := F.cuspRadius
    cuspFrameRadius_pos := F.cuspRadius_pos
    cuspFrameUnit_holomorphic := fun _ _ ↦ mdifferentiableAt_const
    cuspFrameUnit_zero_ne := one_ne_zero
    inverse_coordinate_eventually_mem_closedBall :=
      F.inverse_coordinate_eventually_mem_closedBall
    frameInfinity_cusp_factorization_eventually :=
      Filter.Eventually.of_forall (by simp)
    ellipticOne := ellipticBetaOne E mu
    ellipticTwo := ellipticBetaTwo E mu
    ellipticOne_holomorphic := ellipticBetaOne_holomorphic E hmu.1
    ellipticTwo_holomorphic := ellipticBetaTwo_holomorphic E hmu.1
    ellipticOne_equivariant := ellipticBetaOne_equivariant E hmu.2.1
    ellipticTwo_equivariant := ellipticBetaTwo_equivariant E hmu.2.2.1
    cuspSection := cuspLocalBeta E
    cuspSection_holomorphic := (cuspLocalBeta_properties E).1
    cuspSection_equivariant := (cuspLocalBeta_properties E).2.1
    cusp_coordinate_ne_zero := E.sourceCoordinate.coordinate_ne_zero_on_cusp
    cuspNormalize := fun z beta ↦ beta + E.modularParameter.tau z
    cuspNormalize_sub := by
      intro z u v
      ring
    cuspNormalize_holomorphic := by
      intro s hs
      exact hs.add (tau_coe_mdifferentiable E)
    cuspNormalize_equivariant := by
      intro z u
      have htau := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
        (E.modularParameter.equivariant g₀ z)
      rw [rhoTauReal_g0_smul] at htau
      rw [htau]
      ring
    cuspSection_normalized_bounded := (cuspLocalBeta_properties E).2.2 }

/-- General orbifold affine-torsor descent supplies the exact local structure-sheaf data for
`beta` once the descended `mu` has been selected. -/
public theorem exists_betaAffineCechSections
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E)
    (A : (fuchsianBetaDescentProblem E F Dmu).AnalyticDescentData) :
    Nonempty (BetaAffineCechSections E (descendedFuchsianMu E Dmu)) := by
  obtain ⟨S⟩ := establishedOrbifoldAffineLineTorsorTwoChartDescent
    (fuchsianBetaDescentProblem E F Dmu) A
  refine ⟨⟨{
    zeroRegion := Set.univ
    infinityRegion := liftedInfinityRegion E
    zeroRegion_open := isOpen_univ
    infinityRegion_open := liftedInfinityRegion_open E
    regions_cover := Set.univ_union _
    zeroRegion_invariant := by simp
    infinityRegion_invariant := liftedInfinityRegion_invariant E
    sectionZero := S.sectionZero
    sectionInfinity := S.sectionInfinity
    sectionZero_holomorphic := fun z _ ↦ S.sectionZero_holomorphic z
    sectionInfinity_holomorphic := S.sectionInfinity_holomorphic
    sectionZero_one := ?_
    sectionZero_two := ?_
    sectionInfinity_one := ?_
    sectionInfinity_two := ?_
    overlapCocycle := S.overlapCocycle
    overlapCocycle_holomorphic := S.overlapCocycle_holomorphic
    infinity_coordinate_ne_zero := fun _ hz ↦ hz
    section_mismatch := ?_
    cusp_subset_infinity := fuchsianCuspRegion_subset_liftedInfinityRegion E F
    sectionInfinity_add_tau_cusp_bounded := S.sectionInfinity_normalized_cusp_bounded
    infinity_coordinate_cusp_bounded := F.infinity_coordinate_cusp_bounded E }⟩⟩
  · intro z _
    convert S.sectionZero_one z using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineOne, fuchsianBetaParameter,
      betaCocycleOne]
    ring
  · intro z _
    convert S.sectionZero_two z using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineTwo, fuchsianBetaParameter,
      betaCocycleTwo]
    ring
  · intro z hz
    convert S.sectionInfinity_one z hz using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineOne, fuchsianBetaParameter,
      betaCocycleOne]
    ring
  · intro z hz
    convert S.sectionInfinity_two z hz using 1
    simp [fuchsianBetaDescentProblem, fuchsianBetaAffineTwo, fuchsianBetaParameter,
      betaCocycleTwo]
    ring
  · intro z hz
    simpa [fuchsianBetaDescentProblem] using S.section_mismatch z hz.2

/-- Conditional construction of the sole period-specific local-data package from the independent
modular frame and the two affine local-triviality inputs. -/
@[expose] public noncomputable def exactFuchsianPeriodLocalData
    (Smu : MuAffineCechSections E F)
    (Sbeta : BetaAffineCechSections E
      (descendedFuchsianMu E (Smu.toLocalData E F))) :
    FuchsianPeriodLocalData E where
  muLocal := Smu.toLocalData E F
  betaLocal := Sbeta.data

/-- The exact affine local-triviality statement after the modular `O(-1)` frame and every finite
cyclic consistency check have been supplied. -/
@[expose] public def FuchsianAffineTorsorLocalTriviality : Prop :=
  ∃ Smu : MuAffineCechSections E F,
    Nonempty (BetaAffineCechSections E
      (descendedFuchsianMu E (Smu.toLocalData E F)))

/-- The single beta descent certificate needed after applying a chosen mu descent certificate. -/
public abbrev FuchsianBetaAnalyticDescentData
    (Amu : (fuchsianMuDescentProblem E F).AnalyticDescentData) :=
  (fuchsianBetaDescentProblem E F
    ((muAffineCechSectionsOfAnalyticDescentData E F Amu).toLocalData E F)).AnalyticDescentData

/-- The production `mu` analytic-descent certificate selected from the general
Cartan--B/Cousin theorem. -/
@[expose] public noncomputable def establishedFuchsianMuAnalyticDescentData :
    (fuchsianMuDescentProblem E F).AnalyticDescentData :=
  Classical.choice
    (establishedOrbifoldAffineLineTorsorAnalyticDescent (fuchsianMuDescentProblem E F)
      (Or.inl ⟨rfl, rfl, rfl⟩))

/-- The production `beta` analytic-descent certificate.  Its type depends on the actual `mu`
certificate selected above, so both certificates determine one coherent period package. -/
@[expose] public noncomputable def establishedFuchsianBetaAnalyticDescentData :
    FuchsianBetaAnalyticDescentData E F
      (establishedFuchsianMuAnalyticDescentData E F) :=
  Classical.choice
    (establishedOrbifoldAffineLineTorsorAnalyticDescent
      (fuchsianBetaDescentProblem E F
        ((muAffineCechSectionsOfAnalyticDescentData E F
          (establishedFuchsianMuAnalyticDescentData E F)).toLocalData E F))
      (Or.inr ⟨rfl, rfl, rfl⟩))

/-- Explicit analytic descent certificates discharge both concrete local-triviality problems. -/
public theorem establishedFuchsianAffineTorsorLocalTriviality
    (Amu : (fuchsianMuDescentProblem E F).AnalyticDescentData)
    (Abeta : FuchsianBetaAnalyticDescentData E F Amu) :
    FuchsianAffineTorsorLocalTriviality E F := by
  let Smu := muAffineCechSectionsOfAnalyticDescentData E F Amu
  obtain ⟨Sbeta⟩ := exists_betaAffineCechSections E F (Smu.toLocalData E F)
    Abeta
  exact ⟨Smu, ⟨Sbeta⟩⟩

/-- A general affine-torsor local-triviality theorem, once supplied, completes the exact local
period package. -/
public theorem exists_fuchsianPeriodLocalData_of_affineTorsorLocalTriviality
    (hdescent : ∀ F : ExactLiftedModularNegOneFrame E,
      FuchsianAffineTorsorLocalTriviality E F) :
    Nonempty (FuchsianPeriodLocalData E) := by
  obtain ⟨F⟩ := establishedExactLiftedModularNegOneFrame E
  obtain ⟨Smu, ⟨Sbeta⟩⟩ := hdescent F
  exact ⟨exactFuchsianPeriodLocalData E F Smu Sbeta⟩

/-- One concrete modular frame and its two explicit analytic descent certificates construct the
complete local period package used by the paper. -/
public theorem exists_fuchsianPeriodLocalData
    (F : ExactLiftedModularNegOneFrame E)
    (Amu : (fuchsianMuDescentProblem E F).AnalyticDescentData)
    (Abeta : FuchsianBetaAnalyticDescentData E F Amu) :
    Nonempty (FuchsianPeriodLocalData E) := by
  obtain ⟨Smu, ⟨Sbeta⟩⟩ :=
    establishedFuchsianAffineTorsorLocalTriviality E F Amu Abeta
  exact ⟨exactFuchsianPeriodLocalData E F Smu Sbeta⟩

/-- One concrete modular frame and its explicit analytic descent certificates therefore produce
the paper's actual nondegenerate Fuchsian period functions. -/
public theorem exists_establishedFuchsianPeriodFunctions
    (F : ExactLiftedModularNegOneFrame E)
    (Amu : (fuchsianMuDescentProblem E F).AnalyticDescentData)
    (Abeta : FuchsianBetaAnalyticDescentData E F Amu) :
    Nonempty (PeriodFunctions E.modularParameter.toTriangleUniformization) := by
  obtain ⟨D⟩ := exists_fuchsianPeriodLocalData E F Amu Abeta
  exact exists_assembledFuchsianPeriodFunctions E D

/-- The two production analytic-descent certificates construct the complete local period data. -/
public theorem exists_fuchsianPeriodLocalData_of_establishedAnalyticDescent
    (F : ExactLiftedModularNegOneFrame E) :
    Nonempty (FuchsianPeriodLocalData E) :=
  exists_fuchsianPeriodLocalData E F
    (establishedFuchsianMuAnalyticDescentData E F)
    (establishedFuchsianBetaAnalyticDescentData E F)

/-- A coherent production choice of the local period package. -/
@[expose] public noncomputable def establishedFuchsianPeriodLocalData
    (F : ExactLiftedModularNegOneFrame E) : FuchsianPeriodLocalData E :=
  Classical.choice (exists_fuchsianPeriodLocalData_of_establishedAnalyticDescent E F)

/-- The general analytic descent theorem and exact Fuchsian inputs produce nondegenerate period
functions without any paper-specific existence assumption. -/
public theorem exists_establishedFuchsianPeriodFunctions_of_generalDescent
    (F : ExactLiftedModularNegOneFrame E) :
    Nonempty (PeriodFunctions E.modularParameter.toTriangleUniformization) :=
  exists_assembledFuchsianPeriodFunctions E (establishedFuchsianPeriodLocalData E F)

end SphereSixComplex.Periods
