module

public import SphereSixComplex.Periods.ExactFuchsianModularFrameData
import SphereSixComplex.Periods.ExactFuchsianRamification
import SphereSixComplex.Periods.AnalyticSquareRoot

/-!
# Global square root of the pulled-back weight-six Eisenstein series

The derivative of the established modular lift has a simple zero precisely above the order-two
modular elliptic orbit, while the pulled-back `E₆` has order two there.  Consequently
`E₆ / (tau')²` has a nowhere-zero analytic normal form.  Its square root on the simply connected
upper half-plane produces the required global square root of the pulled-back `E₆`.
-/

open scoped Manifold Topology

noncomputable section

namespace SphereSixComplex.Periods

open Filter Set
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods.AnalyticSquareRoot

private def ambientLiftedEisensteinSix
    (E : EstablishedFuchsianModularParameter) (w : ℂ) : ℂ :=
  liftedEisensteinSix E (UpperHalfPlane.ofComplex w)

private def rawEisensteinSixDerivativeQuotient
    (E : EstablishedFuchsianModularParameter) (w : ℂ) : ℂ :=
  ambientLiftedEisensteinSix E w / ambientEstablishedTauDeriv E w ^ 2

private lemma ambientLiftedEisensteinSix_analyticAt
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    AnalyticAt ℂ (ambientLiftedEisensteinSix E) z := by
  have hE6 : MDiff (liftedEisensteinSix E) :=
    (ModularFormClass.holo ModularForm.E₆).comp E.modularParameter.tau_holomorphic
  exact MDifferentiable.analyticAt_comp_ofComplex hE6 z

private lemma sourceCoordinate_eq_liftedEisensteinFour_cube_div
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    E.sourceCoordinate.coordinate z =
      liftedEisensteinFour E z ^ 3 /
        (1728 * liftedModularDiscriminant E z) := by
  rw [← E.induced_coordinate z]
  simp only [FuchsianModularParameter.coordinate, normalizedJ,
    liftedEisensteinFour, liftedModularDiscriminant]
  field_simp [ModularForm.discriminant_ne_zero]

private lemma liftedEisensteinSix_sq_eq_sourceCoordinate
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    liftedEisensteinSix E z ^ 2 =
      1728 * liftedModularDiscriminant E z *
        (E.sourceCoordinate.coordinate z - 1) := by
  have hdisc := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq
    (E.modularParameter.tau z)
  have hcoord := sourceCoordinate_eq_liftedEisensteinFour_cube_div E z
  simp only [liftedEisensteinFour, liftedEisensteinSix,
    liftedModularDiscriminant] at hcoord ⊢
  field_simp [ModularForm.discriminant_ne_zero] at hcoord
  have hdisc' :
      1728 * ModularForm.discriminant (E.modularParameter.tau z) =
        ModularForm.E₄ (E.modularParameter.tau z) ^ 3 -
          ModularForm.E₆ (E.modularParameter.tau z) ^ 2 := by
    calc
      _ = 1728 * ((ModularForm.E₄ (E.modularParameter.tau z) ^ 3 -
          ModularForm.E₆ (E.modularParameter.tau z) ^ 2) / 1728) := by rw [hdisc]
      _ = _ := by field_simp
  calc
    ModularForm.E₆ (E.modularParameter.tau z) ^ 2 =
        ModularForm.E₄ (E.modularParameter.tau z) ^ 3 -
          1728 * ModularForm.discriminant (E.modularParameter.tau z) := by
      linear_combination hdisc'
    _ = 1728 * ModularForm.discriminant (E.modularParameter.tau z) *
        (E.sourceCoordinate.coordinate z - 1) := by
      rw [← hcoord]
      ring

private lemma ambientLiftedEisensteinSix_zero_iff
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    ambientLiftedEisensteinSix E z = 0 ↔
      E.sourceCoordinate.coordinate z = 1 := by
  have hdisc : liftedModularDiscriminant E z ≠ 0 :=
    ModularForm.discriminant_ne_zero _
  rw [show ambientLiftedEisensteinSix E z = liftedEisensteinSix E z by
    simp only [ambientLiftedEisensteinSix, UpperHalfPlane.ofComplex_apply]]
  rw [← sq_eq_zero_iff, liftedEisensteinSix_sq_eq_sourceCoordinate E z]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, hdisc, false_or, sub_eq_zero]

private lemma ambientLiftedEisensteinSix_analyticOrderAt_of_coordinate_eq_one
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz : E.sourceCoordinate.coordinate z = 1) :
    analyticOrderAt (ambientLiftedEisensteinSix E) z = (2 : ℕ∞) := by
  let C1 : ℂ → ℂ := fun w ↦
    E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) - 1
  let F6 : ℂ → ℂ := ambientLiftedEisensteinSix E
  let Δ : ℂ → ℂ := fun w ↦
    liftedModularDiscriminant E (UpperHalfPlane.ofComplex w)
  have hC1 : AnalyticAt ℂ C1 z :=
    (MDifferentiable.analyticAt_comp_ofComplex
      E.sourceCoordinate.coordinate_holomorphic z).sub analyticAt_const
  have hF6 : AnalyticAt ℂ F6 z := by
    simpa only [F6] using ambientLiftedEisensteinSix_analyticAt E z
  have hΔ : AnalyticAt ℂ Δ z := by
    exact MDifferentiable.analyticAt_comp_ofComplex
      (discriminant_mdifferentiable.comp E.modularParameter.tau_holomorphic) z
  have hΔne : Δ z ≠ 0 := ModularForm.discriminant_ne_zero _
  have heq : F6 ^ 2 = (fun w ↦ 1728 * Δ w) * C1 := by
    funext w
    simpa only [F6, Δ, C1, ambientLiftedEisensteinSix, Function.comp_apply,
      Pi.mul_apply, Pi.pow_apply] using
      liftedEisensteinSix_sq_eq_sourceCoordinate E (UpperHalfPlane.ofComplex w)
  have hord : analyticOrderAt (F6 ^ 2) (z : ℂ) =
      analyticOrderAt ((fun w ↦ 1728 * Δ w) * C1) (z : ℂ) :=
    analyticOrderAt_congr (Eventually.of_forall (congrFun heq))
  have hconstΔ : AnalyticAt ℂ (fun w ↦ 1728 * Δ w) z :=
    analyticAt_const.mul hΔ
  have hconstΔorder : analyticOrderAt (fun w ↦ 1728 * Δ w) z = 0 := by
    apply hconstΔ.analyticOrderAt_eq_zero.mpr
    exact mul_ne_zero (by norm_num) hΔne
  rw [analyticOrderAt_pow hF6, analyticOrderAt_mul hconstΔ hC1,
    hconstΔorder,
    show analyticOrderAt C1 z = (4 : ℕ∞) by
      simpa only [C1] using
        sourceCoordinate_sub_one_analyticOrderAt_of_eq_one E z hz] at hord
  change analyticOrderAt F6 (z : ℂ) = (2 : ℕ∞)
  apply (ENat.mul_right_strictMono (a := (2 : ℕ∞)) (by norm_num) (by simp)).injective
  convert hord using 1 <;> norm_num

private lemma ambientLiftedEisensteinSix_analyticOrderAt
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    analyticOrderAt (ambientLiftedEisensteinSix E) z =
      if E.sourceCoordinate.coordinate z = 1 then (2 : ℕ∞) else 0 := by
  by_cases hz : E.sourceCoordinate.coordinate z = 1
  · simp only [hz, if_pos]
    exact ambientLiftedEisensteinSix_analyticOrderAt_of_coordinate_eq_one E z hz
  · simp only [hz]
    exact (ambientLiftedEisensteinSix_analyticAt E z).analyticOrderAt_eq_zero.mpr
      ((ambientLiftedEisensteinSix_zero_iff E z).not.mpr hz)

private lemma rawEisensteinSixDerivativeQuotient_meromorphicOn
    (E : EstablishedFuchsianModularParameter) :
    MeromorphicOn (rawEisensteinSixDerivativeQuotient E)
      UpperHalfPlane.upperHalfPlaneSet := by
  intro w hw
  let z : UpperHalfPlane := ⟨w, hw⟩
  have hF : AnalyticAt ℂ (ambientLiftedEisensteinSix E) w := by
    simpa only [z] using ambientLiftedEisensteinSix_analyticAt E z
  have hD : AnalyticAt ℂ (ambientEstablishedTauDeriv E) w := by
    simpa only [z] using ambientEstablishedTauDeriv_analyticAt E z
  exact hF.meromorphicAt.div (hD.pow 2).meromorphicAt

private lemma rawEisensteinSixDerivativeQuotient_order_zero
    (E : EstablishedFuchsianModularParameter) (w : ℂ)
    (hw : w ∈ UpperHalfPlane.upperHalfPlaneSet) :
    meromorphicOrderAt (rawEisensteinSixDerivativeQuotient E) w = 0 := by
  let z : UpperHalfPlane := ⟨w, hw⟩
  have hF : AnalyticAt ℂ (ambientLiftedEisensteinSix E) w := by
    simpa only [z] using ambientLiftedEisensteinSix_analyticAt E z
  have hD : AnalyticAt ℂ (ambientEstablishedTauDeriv E) w := by
    simpa only [z] using ambientEstablishedTauDeriv_analyticAt E z
  rw [show rawEisensteinSixDerivativeQuotient E =
      ambientLiftedEisensteinSix E / (ambientEstablishedTauDeriv E) ^ 2 by rfl,
    meromorphicOrderAt_div hF.meromorphicAt (hD.pow 2).meromorphicAt,
    hF.meromorphicOrderAt_eq, (hD.pow 2).meromorphicOrderAt_eq,
    analyticOrderAt_pow hD]
  rw [show analyticOrderAt (ambientLiftedEisensteinSix E) w =
      if E.sourceCoordinate.coordinate z = 1 then (2 : ℕ∞) else 0 by
        simpa only [z] using ambientLiftedEisensteinSix_analyticOrderAt E z]
  rw [show analyticOrderAt (ambientEstablishedTauDeriv E) w =
      if E.sourceCoordinate.coordinate z = 1 then (1 : ℕ∞) else 0 by
        simpa only [z] using ambientEstablishedTauDeriv_analyticOrderAt E z]
  by_cases hz : E.sourceCoordinate.coordinate z = 1 <;> simp [hz]

/-- A global holomorphic square root of the weight-six Eisenstein series pulled back by the
established Fuchsian modular parameter. -/
public structure ExactFuchsianEisensteinSixRoot
    (E : EstablishedFuchsianModularParameter) where
  /-- The selected global square root. -/
  root : UpperHalfPlane → ℂ
  /-- Holomorphicity of the selected root. -/
  root_holomorphic : MDiff root
  /-- The defining square identity. -/
  root_sq : ∀ z, root z ^ 2 = liftedEisensteinSix E z

/-- The pulled-back weight-six Eisenstein series has a global holomorphic square root on the
Fuchsian upper half-plane. -/
public theorem exists_exactFuchsianEisensteinSixRoot
    (E : EstablishedFuchsianModularParameter) :
    Nonempty (ExactFuchsianEisensteinSixRoot E) := by
  let U : Set ℂ := UpperHalfPlane.upperHalfPlaneSet
  let raw : ℂ → ℂ := rawEisensteinSixDerivativeQuotient E
  let Q : ℂ → ℂ := toMeromorphicNFOn raw U
  have hraw : MeromorphicOn raw U := by
    simpa only [raw, U] using rawEisensteinSixDerivativeQuotient_meromorphicOn E
  have hrawOrder : ∀ w ∈ U, meromorphicOrderAt raw w = 0 := by
    intro w hw
    simpa only [raw, U] using
      rawEisensteinSixDerivativeQuotient_order_zero E w hw
  obtain ⟨hQanalytic, hQne, hQraw⟩ :=
    toMeromorphicNFOn_analytic_ne_zero_of_order_zero hraw hrawOrder
  obtain ⟨r, hr_analytic, hr_sq⟩ := exists_analyticOnNhd_sq_eq
    upperHalfPlaneSet_isSimplyConnected UpperHalfPlane.isOpen_upperHalfPlaneSet
    hQanalytic hQne
  let s : UpperHalfPlane → ℂ := fun z ↦ ambientEstablishedTauDeriv E z * r z
  have hD_mdiff : MDiff (fun z : UpperHalfPlane ↦ ambientEstablishedTauDeriv E z) := by
    intro z
    exact (ambientEstablishedTauDeriv_analyticAt E z).differentiableAt.mdifferentiableAt.comp z
      UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt
  have hr_mdiff : MDiff (fun z : UpperHalfPlane ↦ r z) := by
    intro z
    exact (hr_analytic z z.im_pos).differentiableAt.mdifferentiableAt.comp z
      UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt
  refine ⟨⟨s, hD_mdiff.mul hr_mdiff, ?_⟩⟩
  intro z
  have hF : AnalyticAt ℂ (ambientLiftedEisensteinSix E) z :=
    ambientLiftedEisensteinSix_analyticAt E z
  have hD : AnalyticAt ℂ (ambientEstablishedTauDeriv E) z :=
    ambientEstablishedTauDeriv_analyticAt E z
  have hQ : AnalyticAt ℂ Q z := hQanalytic z z.im_pos
  have hDorder : analyticOrderAt (ambientEstablishedTauDeriv E) z ≠ ⊤ := by
    rw [ambientEstablishedTauDeriv_analyticOrderAt E z]
    split <;> simp
  have hDne : ∀ᶠ w in 𝓝[≠] (z : ℂ), ambientEstablishedTauDeriv E w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hD.meromorphicAt).mp <| by
      rw [hD.meromorphicOrderAt_eq]
      intro htop
      exact hDorder (ENat.map_eq_top_iff.mp htop)
  have hQrawz : Q =ᶠ[𝓝[≠] (z : ℂ)] raw := hQraw z z.im_pos
  have hproductNE :
      (fun w ↦ ambientEstablishedTauDeriv E w ^ 2 * Q w) =ᶠ[𝓝[≠] (z : ℂ)]
        ambientLiftedEisensteinSix E := by
    filter_upwards [hQrawz, hDne] with w hqw hdw
    rw [hqw]
    simp only [raw, rawEisensteinSixDerivativeQuotient]
    field_simp [hdw]
  have hproduct :
      (fun w ↦ ambientEstablishedTauDeriv E w ^ 2 * Q w) =ᶠ[nhds (z : ℂ)]
        ambientLiftedEisensteinSix E :=
    ((hD.pow 2).mul hQ).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      hF.continuousAt |>.mp hproductNE
  change (ambientEstablishedTauDeriv E z * r z) ^ 2 = liftedEisensteinSix E z
  rw [mul_pow, hr_sq]
  have hzprod := hproduct.eq_of_nhds
  simpa only [Q, U, UpperHalfPlane.ofComplex_apply,
    ambientLiftedEisensteinSix] using hzprod

/-- Existential form of `exists_exactFuchsianEisensteinSixRoot`. -/
public theorem exists_globalEisensteinSixRoot
    (E : EstablishedFuchsianModularParameter) :
    ∃ s : UpperHalfPlane → ℂ,
      MDiff s ∧ ∀ z, s z ^ 2 = liftedEisensteinSix E z := by
  obtain ⟨S⟩ := exists_exactFuchsianEisensteinSixRoot E
  exact ⟨S.root, S.root_holomorphic, S.root_sq⟩

end SphereSixComplex.Periods
