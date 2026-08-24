module

public import SphereSixComplex.Periods.FuchsianPeriodAssembly
import all SphereSixComplex.Periods.Functions
import all SphereSixComplex.Periods.FuchsianModularParameterExistence

/-!
# Exact modular-form input for the additive Fuchsian torsors

The paper's identification of the homogeneous `mu` sheaf with `O(-1)` is not a formal consequence
of cyclic consistency.  It uses the divisor and cusp behavior of
`E4^2 * sqrt(E6) / Delta` after pullback by the modular parameter.  This file isolates exactly
that classical modular-form input, derives the required two-chart frame, and identifies the
remaining affine-torsor local-triviality obligation without assuming a global `mu` or `beta`.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

variable (E : EstablishedFuchsianModularParameter)

/-- Pullback of the normalized weight-four Eisenstein series by the established modular
parameter. -/
@[expose] public def liftedEisensteinFour (z : UpperHalfPlane) : ℂ :=
  ModularForm.E₄ (E.modularParameter.tau z)

/-- Pullback of the normalized weight-six Eisenstein series by the established modular
parameter. -/
@[expose] public def liftedEisensteinSix (z : UpperHalfPlane) : ℂ :=
  ModularForm.E₆ (E.modularParameter.tau z)

/-- Pullback of the modular discriminant by the established modular parameter. -/
@[expose] public def liftedModularDiscriminant (z : UpperHalfPlane) : ℂ :=
  ModularForm.discriminant (E.modularParameter.tau z)

/-- Exact classical modular-form data used in Lemma 3.10 of the paper.

The square root is included together with its square identity and exact divisor data: no assertion
is made that an arbitrary nowhere-zero or arbitrary holomorphic function has a global square root.
The final cusp identity says that `coordinate⁻¹ * frame` extends as a holomorphic unit in the
completed cusp coordinate. -/
public structure ExactLiftedModularNegOneFrame where
  /-- The chosen holomorphic square root of the pulled-back weight-six Eisenstein series. -/
  sqrtEisensteinSix : UpperHalfPlane → ℂ
  /-- Holomorphicity of the chosen square root. -/
  sqrtEisensteinSix_holomorphic : MDiff sqrtEisensteinSix
  /-- The chosen function really is a square root. -/
  sqrtEisensteinSix_sq : ∀ z,
    sqrtEisensteinSix z ^ 2 = liftedEisensteinSix E z
  /-- The meromorphic modular expression, holomorphic on the source because the discriminant never
  vanishes there. -/
  frame : UpperHalfPlane → ℂ
  /-- Identification with the normalized modular-form expression. -/
  frame_eq : ∀ z,
    frame z = liftedEisensteinFour E z ^ 2 * sqrtEisensteinSix z /
      liftedModularDiscriminant E z
  /-- Holomorphicity of the pulled-back frame. -/
  frame_holomorphic : MDiff frame
  /-- Exact order-two zero over the order-three orbifold point. -/
  frame_branch_one : HasExactHolomorphicBranchAt frame fuchsianOneFixedPoint 0 2
  /-- Exact order-one zero over the order-four orbifold point. -/
  frame_branch_two : HasExactHolomorphicBranchAt frame fuchsianTwoFixedPoint 0 1
  /-- There are no further zeros. -/
  frame_zero_iff : ∀ z, frame z = 0 ↔
    (∃ g : Delta, fuchsianSourceAction g • fuchsianOneFixedPoint = z) ∨
      ∃ g : Delta, fuchsianSourceAction g • fuchsianTwoFixedPoint = z
  /-- The order-three homogeneous automorphy factor. -/
  frame_one : ∀ z, frame (fuchsianSourceAction g₁ • z) =
    -frame z / E.modularParameter.tau z
  /-- The order-four homogeneous automorphy factor. -/
  frame_two : ∀ z, frame (fuchsianSourceAction g₂ • z) =
    frame z / E.modularParameter.tau z
  /-- The affine quotient coordinate does not vanish on the distinguished cusp component. -/
  coordinate_ne_zero_on_cusp : ∀ z, z ∈ fuchsianCuspRegion →
    E.sourceCoordinate.coordinate z ≠ 0
  /-- The holomorphic unit after removing the simple pole at the completed cusp. -/
  cuspUnit : ℂ → ℂ
  /-- Radius of a completed cusp-coordinate neighbourhood. -/
  cuspRadius : ℝ
  /-- The completed cusp-coordinate neighbourhood is nontrivial. -/
  cuspRadius_pos : 0 < cuspRadius
  /-- The cusp unit is holomorphic on a neighbourhood of zero. -/
  cuspUnit_holomorphic : ∀ q, q ∈ Metric.ball 0 cuspRadius → MDiffAt cuspUnit q
  /-- The cusp unit is nonzero at the completed point. -/
  cuspUnit_zero_ne : cuspUnit 0 ≠ 0
  /-- The chosen distinguished cusp component maps into a compact subdisc of the unit's domain. -/
  inverse_coordinate_mem_closedBall : ∀ z, z ∈ fuchsianCuspRegion →
    (E.sourceCoordinate.coordinate z)⁻¹ ∈ Metric.closedBall 0 (cuspRadius / 2)
  /-- Exact simple-pole normalization on the distinguished cusp component. -/
  cusp_factorization : ∀ z, z ∈ fuchsianCuspRegion →
    (E.sourceCoordinate.coordinate z)⁻¹ * frame z =
      cuspUnit ((E.sourceCoordinate.coordinate z)⁻¹)

/-- Classical divisor, automorphy, and cusp theorem for the normalized modular-form expression in
Lemma 3.10.  It is independent of the affine `mu` and `beta` problems and of the six-sphere
construction. -/
public axiom establishedExactLiftedModularNegOneFrame
    (E : EstablishedFuchsianModularParameter) :
    Nonempty (ExactLiftedModularNegOneFrame E)

variable (F : ExactLiftedModularNegOneFrame E)

/-- The local cusp-unit theorem implies boundedness of every entire Cech correction on the fixed
distinguished cusp component. -/
public theorem ExactLiftedModularNegOneFrame.cusp_correction_bounded
    (f : ℂ → ℂ) (hf : MDiff f) :
    BoundedOn
      (fun z ↦ f ((E.sourceCoordinate.coordinate z)⁻¹) *
        ((E.sourceCoordinate.coordinate z)⁻¹ * F.frame z))
      fuchsianCuspRegion := by
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
  have hproduct : ContinuousOn (fun q ↦ f q * F.cuspUnit q) K :=
    hf.continuous.continuousOn.mul hunit
  obtain ⟨C, hC⟩ := hK.bddAbove_image hproduct.norm
  rw [SphereSixComplex.Periods.BoundedOn.eq_def]
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro z hz
  have hq := F.inverse_coordinate_mem_closedBall z hz
  rw [F.cusp_factorization z hz]
  exact (hC ⟨_, hq, rfl⟩).trans (le_max_left C 0)

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
    (F : ExactLiftedModularNegOneFrame E) :
    fuchsianCuspRegion ⊆ liftedInfinityRegion E := by
  intro z hz
  exact F.coordinate_ne_zero_on_cusp z hz

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

/-- Conditional construction of the sole period-specific local-data package from the independent
modular frame and the two affine local-triviality inputs. -/
@[expose] public noncomputable def exactFuchsianPeriodLocalData
    (Smu : MuAffineCechSections E F)
    (Sbeta : BetaAffineCechSections E
      (descendedFuchsianMu E (Smu.toLocalData E F))) :
    FuchsianPeriodLocalData E where
  muLocal := Smu.toLocalData E F
  betaLocal := Sbeta.data

/-- The remaining affine local-triviality statement after the modular `O(-1)` frame and every
finite cyclic consistency check have been supplied.  This is a proposition, not an axiom. -/
@[expose] public def FuchsianAffineTorsorLocalTriviality : Prop :=
  ∃ Smu : MuAffineCechSections E F,
    Nonempty (BetaAffineCechSections E
      (descendedFuchsianMu E (Smu.toLocalData E F)))

/-- A general affine-torsor local-triviality theorem, once supplied, completes the exact local
period package. -/
public theorem exists_fuchsianPeriodLocalData_of_affineTorsorLocalTriviality
    (hdescent : ∀ F : ExactLiftedModularNegOneFrame E,
      FuchsianAffineTorsorLocalTriviality E F) :
    Nonempty (FuchsianPeriodLocalData E) := by
  obtain ⟨F⟩ := establishedExactLiftedModularNegOneFrame E
  obtain ⟨Smu, ⟨Sbeta⟩⟩ := hdescent F
  exact ⟨exactFuchsianPeriodLocalData E F Smu Sbeta⟩

end SphereSixComplex.Periods
