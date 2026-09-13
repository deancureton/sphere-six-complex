module

public import SphereSixComplex.Paper.Periods.ModularFrame.Basic
public import SphereSixComplex.Paper.Periods.FuchsianMuTorsor
public import SphereSixComplex.Paper.Periods.ModularFrame.Construction
public import SphereSixComplex.Paper.Periods.OrbifoldAffineTorsorStandardFrameDescent
import all SphereSixComplex.Paper.Periods.Functions
import all SphereSixComplex.Prerequisites.Periods.FuchsianModularParameterExistence
import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianTessellation

/-!
# Exact modular-form input for the additive Fuchsian torsors

The paper's identification of the homogeneous `mu` sheaf with `O(-1)` is not a formal consequence
of cyclic consistency.  It uses the divisor and cusp behavior of
`E4^2 * sqrt(E6) / Delta` after pullback by the modular parameter.  This file isolates that
classical modular-form interface and the resulting affine-torsor assembly.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.FuchsianAffineDescent

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianTessellation
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open Filter Set Metric

variable (E : FuchsianModularLift)

variable (F : ModularNegOneFrame E)


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
    E.sourceCoordinate.coordinate_invariant, ModularNegOneFrame.frame, F.frame_one]
  ring

public theorem liftedNegOneInfinityFrame_two (z : UpperHalfPlane) :
    liftedNegOneInfinityFrame E F (fuchsianSourceAction g₂ • z) =
      liftedNegOneInfinityFrame E F z / E.modularParameter.tau z := by
  rw [liftedNegOneInfinityFrame, liftedNegOneInfinityFrame,
    E.sourceCoordinate.coordinate_invariant, ModularNegOneFrame.frame, F.frame_two]
  ring


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

@[expose] public def muAffineMapOne (z : UpperHalfPlane) (mu : ℂ) : ℂ :=
  (1 - mu) / E.modularParameter.tau z

@[expose] public def muAffineMapTwo (z : UpperHalfPlane) (mu : ℂ) : ℂ :=
  1 + mu / E.modularParameter.tau z

@[expose] public def muLinearOne (z : UpperHalfPlane) : ℂ :=
  -1 / E.modularParameter.tau z

@[expose] public def muLinearTwo (z : UpperHalfPlane) : ℂ :=
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
    muAffineMapOne E (fuchsianSourceAction g₂ • z)
        (muAffineMapTwo E z mu) = mu := by
  rw [muAffineMapOne, muAffineMapTwo, tau_two_coe E]
  simp only [tauTwoStep]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- The explicit affine `mu` substitutions and local primitives satisfy every hypothesis of the
general orbifold affine-torsor descent theorem. -/
@[expose] public noncomputable def muDescentData :
    OrbifoldAffineDescentData where
  quotient := E.sourceCoordinate
  affineOne := muAffineMapOne E
  affineTwo := muAffineMapTwo E
  affineCusp := fun _ mu ↦ mu
  affineOne_holomorphic := by
    intro s hs
    exact (mdifferentiable_const.sub hs).div (tau_coe_mdifferentiable E)
      (fun z ↦ (E.modularParameter.tau z).ne_zero)
  affineTwo_holomorphic := by
    intro s hs
    exact mdifferentiable_const.add
      (hs.div (tau_coe_mdifferentiable E) (fun z ↦ (E.modularParameter.tau z).ne_zero))
  linearOne := muLinearOne E
  linearTwo := muLinearTwo E
  affineOne_sub := by
    intro z u v
    simp only [muAffineMapOne, muLinearOne]
    field_simp [(E.modularParameter.tau z).ne_zero]
    ring
  affineTwo_sub := by
    intro z u v
    simp only [muAffineMapTwo, muLinearTwo]
    field_simp [(E.modularParameter.tau z).ne_zero]
    ring
  affineOne_cycle := by
    intro z mu
    rw [muAffineMapOne, muAffineMapOne, muAffineMapOne,
      tau_one_coe E, tau_one_sq_coe E]
    exact muAffineOne_closes E z mu
  affineTwo_cycle := by
    intro z mu
    rw [muAffineMapTwo, muAffineMapTwo, muAffineMapTwo,
      muAffineMapTwo, tau_two_coe E, tau_two_sq_coe E, tau_two_cube_coe E]
    exact muAffineTwo_closes E z mu
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
    simp only [ModularNegOneFrame.frame]
    rw [F.frame_one]
    simp only [muLinearOne]
    ring
  frameZero_two := by
    intro z
    simp only [ModularNegOneFrame.frame]
    rw [F.frame_two]
    simp only [muLinearTwo]
    ring
  frameInfinity_one := by
    intro z _
    rw [liftedNegOneInfinityFrame_one E F]
    simp only [muLinearOne]
    ring
  frameInfinity_two := by
    intro z _
    rw [liftedNegOneInfinityFrame_two E F]
    simp only [muLinearTwo]
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
      simpa [ModularNegOneFrame.frame] using F.frame_branch_one.factorization }
  frameZero_branch_two := {
    uniformizer := F.frame_branch_two.uniformizer
    uniformizer_center := F.frame_branch_two.uniformizer_center
    uniformizer_isLocalDiffeomorph := F.frame_branch_two.uniformizer_isLocalDiffeomorph
    unit := F.frame_branch_two.unit
    unit_holomorphic := F.frame_branch_two.unit_holomorphic
    unit_ne_zero := F.frame_branch_two.unit_ne_zero
    factorization := by
      simpa [ModularNegOneFrame.frame] using F.frame_branch_two.factorization }
  frameZero_zero_iff := by
    intro z
    simpa [ModularNegOneFrame.frame] using F.frame_zero_iff z
  frameTransition := fun q ↦ q⁻¹
  frame_transition := fun _ _ ↦ rfl
  cuspFrameUnit := F.cuspUnit
  cuspFrameRadius := F.cuspRadius
  cuspFrameRadius_pos := F.cuspRadius_pos
  cuspFrameUnit_holomorphic := F.cuspUnit_holomorphic
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
  affineCusp_sub := fun _ _ _ ↦ rfl

@[expose] public def betaParameter
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : Parameters :=
  ⟨E.modularParameter.tau z, mu z, 0⟩

@[expose] public def betaAffineMapOne
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) (beta : ℂ) : ℂ :=
  beta + betaCocycleOne (betaParameter E mu z)

@[expose] public def betaAffineMapTwo
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) (beta : ℂ) : ℂ :=
  beta + betaCocycleTwo (betaParameter E mu z)

@[expose] public def ellipticBetaOne
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  localBetaOne (betaParameter E mu z)

@[expose] public def ellipticBetaTwo
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  localBetaTwo (betaParameter E mu z)

private theorem fuchsianBetaParameter_one_tau
    {mu : UpperHalfPlane → ℂ} (z : UpperHalfPlane) :
    (betaParameter E mu (fuchsianSourceAction g₁ • z)).tau =
      (transformOne (betaParameter E mu z)).tau := by
  rw [betaParameter, betaParameter, transformOne_tau]
  exact tau_one_coe E z

private theorem fuchsianBetaParameter_two_tau
    {mu : UpperHalfPlane → ℂ} (z : UpperHalfPlane) :
    (betaParameter E mu (fuchsianSourceAction g₂ • z)).tau =
      (transformTwo (betaParameter E mu z)).tau := by
  rw [betaParameter, betaParameter, transformTwo_tau]
  exact tau_two_coe E z

private theorem fuchsianBetaParameter_one_mu
    {mu : UpperHalfPlane → ℂ}
    (hmuOne : ∀ z, mu (fuchsianSourceAction g₁ • z) =
      (1 - mu z) / E.modularParameter.tau z) (z : UpperHalfPlane) :
    (betaParameter E mu (fuchsianSourceAction g₁ • z)).mu =
      (transformOne (betaParameter E mu z)).mu := by
  rw [betaParameter, betaParameter, transformOne_mu]
  exact hmuOne z

private theorem fuchsianBetaParameter_two_mu
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    (betaParameter E mu (fuchsianSourceAction g₂ • z)).mu =
      (transformTwo (betaParameter E mu z)).mu := by
  rw [betaParameter, betaParameter, transformTwo_mu]
  exact hmuTwo z

private theorem betaCocycleOne_fuchsian_step
    {mu : UpperHalfPlane → ℂ}
    (hmuOne : ∀ z, mu (fuchsianSourceAction g₁ • z) =
      (1 - mu z) / E.modularParameter.tau z) (z : UpperHalfPlane) :
    betaCocycleOne (betaParameter E mu (fuchsianSourceAction g₁ • z)) =
      betaCocycleOne (transformOne (betaParameter E mu z)) := by
  rw [betaCocycleOne, fuchsianBetaParameter_one_mu E hmuOne z,
    fuchsianBetaParameter_one_tau E z]
  rfl

private theorem betaCocycleTwo_fuchsian_step
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    betaCocycleTwo (betaParameter E mu (fuchsianSourceAction g₂ • z)) =
      betaCocycleTwo (transformTwo (betaParameter E mu z)) := by
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
    betaCocycleOne (betaParameter E mu (fuchsianSourceAction (g₁ ^ 2) • z)) =
      betaCocycleOne (transformOne (transformOne (betaParameter E mu z))) := by
  rw [map_pow, pow_two, mul_smul, betaCocycleOne_fuchsian_step E hmuOne]
  exact betaCocycleOne_transform_congr_tau_mu _ _
    (fuchsianBetaParameter_one_tau E z) (fuchsianBetaParameter_one_mu E hmuOne z)

private theorem betaCocycleTwo_fuchsian_sq
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    betaCocycleTwo (betaParameter E mu (fuchsianSourceAction (g₂ ^ 2) • z)) =
      betaCocycleTwo (transformTwo (transformTwo (betaParameter E mu z))) := by
  rw [map_pow, pow_two, mul_smul, betaCocycleTwo_fuchsian_step E hmuTwo]
  exact betaCocycleTwo_transform_congr_tau_mu _ _
    (fuchsianBetaParameter_two_tau E z) (fuchsianBetaParameter_two_mu E hmuTwo z)

private theorem fuchsianBetaParameter_two_sq_tau
    {mu : UpperHalfPlane → ℂ} (z : UpperHalfPlane) :
    (betaParameter E mu (fuchsianSourceAction (g₂ ^ 2) • z)).tau =
      (transformTwo (transformTwo (betaParameter E mu z))).tau := by
  rw [map_pow, pow_two, mul_smul, fuchsianBetaParameter_two_tau E,
    transformTwo_tau, fuchsianBetaParameter_two_tau E, transformTwo_tau]
  rw [transformTwo_tau, transformTwo_tau]

private theorem fuchsianBetaParameter_two_sq_mu
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    (betaParameter E mu (fuchsianSourceAction (g₂ ^ 2) • z)).mu =
      (transformTwo (transformTwo (betaParameter E mu z))).mu := by
  rw [map_pow, pow_two, mul_smul, fuchsianBetaParameter_two_mu E hmuTwo,
    transformTwo_mu, fuchsianBetaParameter_two_tau E,
    fuchsianBetaParameter_two_mu E hmuTwo, transformTwo_mu]
  rw [← transformTwo_mu, ← transformTwo_mu]

private theorem betaCocycleTwo_fuchsian_cube
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    betaCocycleTwo (betaParameter E mu (fuchsianSourceAction (g₂ ^ 3) • z)) =
      betaCocycleTwo
        (transformTwo (transformTwo (transformTwo (betaParameter E mu z)))) := by
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
      betaAffineMapOne E mu z (ellipticBetaOne E mu z) := by
  have hcongr :
      localBetaOne (betaParameter E mu (fuchsianSourceAction g₁ • z)) =
        localBetaOne (transformOne (betaParameter E mu z)) :=
    localBetaOne_congr_tau_mu _ _ (fuchsianBetaParameter_one_tau E z)
      (fuchsianBetaParameter_one_mu E hmuOne z)
  rw [ellipticBetaOne, ellipticBetaOne, hcongr, betaAffineMapOne]
  exact localBetaOne_transform _ (E.modularParameter.tau z).ne_zero (tau_coe_ne_one E z)

public theorem ellipticBetaTwo_equivariant
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) :
    ellipticBetaTwo E mu (fuchsianSourceAction g₂ • z) =
      betaAffineMapTwo E mu z (ellipticBetaTwo E mu z) := by
  have hcongr :
      localBetaTwo (betaParameter E mu (fuchsianSourceAction g₂ • z)) =
        localBetaTwo (transformTwo (betaParameter E mu z)) :=
    localBetaTwo_congr_tau_mu _ _ (fuchsianBetaParameter_two_tau E z)
      (fuchsianBetaParameter_two_mu E hmuTwo z)
  rw [ellipticBetaTwo, ellipticBetaTwo, hcongr, betaAffineMapTwo]
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
    betaParameter
  dsimp only [transformOne]
  have hsub : (E.modularParameter.tau z : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (tau_coe_ne_one E z)
  field_simp [(E.modularParameter.tau z).ne_zero, hsub]
  ring

private theorem ellipticBetaTwo_eq_formula
    (mu : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ellipticBetaTwo E mu z = ellipticBetaTwoFormula E mu z := by
  unfold ellipticBetaTwo ellipticBetaTwoFormula localBetaTwo betaCocycleTwo
    betaParameter
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
    betaAffineMapOne E mu (fuchsianSourceAction (g₁ ^ 2) • z)
        (betaAffineMapOne E mu (fuchsianSourceAction g₁ • z)
          (betaAffineMapOne E mu z beta)) = beta := by
  simp only [betaAffineMapOne]
  rw [betaCocycleOne_fuchsian_step E hmuOne z,
    betaCocycleOne_fuchsian_sq E hmuOne z]
  have hcycle := betaCocycleOne_cycle (⟨E.modularParameter.tau z, mu z, 0⟩ : Parameters)
    (E.modularParameter.tau z).ne_zero (tau_coe_ne_one E z)
  have hcycle' :
      betaCocycleOne (betaParameter E mu z) +
          betaCocycleOne (transformOne (betaParameter E mu z)) +
        betaCocycleOne (transformOne (transformOne (betaParameter E mu z))) = 0 := by
    simpa only [betaParameter] using hcycle
  linear_combination hcycle'

public theorem fuchsianBetaAffineTwo_cycle
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) (beta : ℂ) :
    betaAffineMapTwo E mu (fuchsianSourceAction (g₂ ^ 3) • z)
        (betaAffineMapTwo E mu (fuchsianSourceAction (g₂ ^ 2) • z)
          (betaAffineMapTwo E mu (fuchsianSourceAction g₂ • z)
            (betaAffineMapTwo E mu z beta))) = beta := by
  simp only [betaAffineMapTwo]
  rw [betaCocycleTwo_fuchsian_step E hmuTwo z,
    betaCocycleTwo_fuchsian_sq E hmuTwo z,
    betaCocycleTwo_fuchsian_cube E hmuTwo z]
  have hcycle := betaCocycleTwo_cycle (⟨E.modularParameter.tau z, mu z, 0⟩ : Parameters)
    (E.modularParameter.tau z).ne_zero
  have hcycle' :
      betaCocycleTwo (betaParameter E mu z) +
            betaCocycleTwo (transformTwo (betaParameter E mu z)) +
          betaCocycleTwo (transformTwo (transformTwo (betaParameter E mu z))) +
        betaCocycleTwo
          (transformTwo (transformTwo (transformTwo (betaParameter E mu z)))) = 0 := by
    simpa only [betaParameter] using hcycle
  linear_combination hcycle'

public theorem fuchsianBetaAffine_product
    {mu : UpperHalfPlane → ℂ}
    (hmuTwo : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) (z : UpperHalfPlane) (beta : ℂ) :
    betaAffineMapOne E mu (fuchsianSourceAction g₂ • z)
        (betaAffineMapTwo E mu z beta) = beta - 1 := by
  unfold betaAffineMapOne betaAffineMapTwo betaParameter
    betaCocycleOne betaCocycleTwo
  rw [tau_two_coe E, hmuTwo]
  simp only [tauTwoStep]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- The selected descended `mu` supplies an exact structure-sheaf affine torsor for `beta`; all
paper-specific algebra and local primitives are discharged before the general descent theorem is
invoked. -/
@[expose] public noncomputable def betaDescentData
    (F : ModularNegOneFrame E) (mu : UpperHalfPlane → ℂ)
    (hmu : MDiff mu ∧
      (∀ z, mu (fuchsianSourceAction g₁ • z) =
        (1 - mu z) / E.modularParameter.tau z) ∧
      (∀ z, mu (fuchsianSourceAction g₂ • z) =
        1 + mu z / E.modularParameter.tau z) ∧ BoundedOn mu fuchsianCuspRegion) :
    OrbifoldAffineDescentData := by
  exact {
    quotient := E.sourceCoordinate
    affineOne := betaAffineMapOne E mu
    affineTwo := betaAffineMapTwo E mu
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
    linearOne := fun _ ↦ 1
    linearTwo := fun _ ↦ 1
    affineOne_sub := by
      intro z u v
      simp only [betaAffineMapOne]
      ring
    affineTwo_sub := by
      intro z u v
      simp only [betaAffineMapTwo]
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
    frame_transition := fun _ _ ↦ by simp
    cuspFrameUnit := fun _ ↦ 1
    cuspFrameRadius := F.cuspRadius
    cuspFrameRadius_pos := F.cuspRadius_pos
    cuspFrameUnit_holomorphic := fun _ _ ↦ mdifferentiableAt_const
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
    affineCusp_sub := by
      intro z u v
      ring }


/-- The global torsor sections directly supply a coherent pair of additive period coordinates. -/
public theorem nonempty_fuchsianPeriodData (F : ModularNegOneFrame E) :
    Nonempty (FuchsianPeriodData E) := by
  obtain ⟨mu, hmuHol, hmuOne, hmuTwo, hmuCusp⟩ :=
    (muDescentData E F).hasCuspBoundedSection_of_standard_transition (Or.inl rfl)
  have hmu : MDiff mu ∧
      (∀ z, mu (fuchsianSourceAction g₁ • z) =
        (1 - mu z) / E.modularParameter.tau z) ∧
      (∀ z, mu (fuchsianSourceAction g₂ • z) =
        1 + mu z / E.modularParameter.tau z) ∧ BoundedOn mu fuchsianCuspRegion := by
    refine ⟨hmuHol, hmuOne, hmuTwo, ?_⟩
    simpa only [muDescentData, cuspLocalMu, sub_zero] using hmuCusp
  obtain ⟨beta, hbetaHol, hbetaOne, hbetaTwo, hbetaCusp⟩ :=
    (betaDescentData E F mu hmu).hasCuspBoundedSection_of_standard_transition (Or.inr rfl)
  refine ⟨{
    mu := mu
    beta := beta
    mu_holomorphic := hmu.1
    beta_holomorphic := hbetaHol
    mu_transform_one := hmu.2.1
    mu_transform_two := hmu.2.2.1
    beta_transform_one := ?_
    beta_transform_two := ?_
    mu_cusp_bounded := hmu.2.2.2
    beta_add_tau_cusp_bounded := ?_ }⟩
  · intro z
    convert hbetaOne z using 1
    simp [betaDescentData, betaAffineMapOne, betaParameter, betaCocycleOne]
    ring
  · intro z
    convert hbetaTwo z using 1
    simp [betaDescentData, betaAffineMapTwo, betaParameter, betaCocycleTwo]
    ring
  · simpa only [betaDescentData, cuspLocalBeta, sub_neg_eq_add] using hbetaCusp

end SphereSixComplex.Periods.FuchsianAffineDescent
