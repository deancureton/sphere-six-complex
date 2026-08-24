module

public import SphereSixComplex.Periods.Uniformization.AnalyticPowerGermUniqueness
import all SphereSixComplex.Periods.Uniformization.AnalyticPowerGermUniqueness

@[expose] public section

/-!
# Local equivariance from a branched power equation

The theorem below is a reusable local labeling criterion.  A source action with multiplier
`lambda`, a target action with multiplier `mu`, and a lift of local degree `k` must intertwine
when `lambda^k = mu`.  Equality after the target branch map gives equality of `m`-th powers;
the common leading coefficient then selects the marked root.
-/

noncomputable section

namespace TauCeti

open Complex Filter Set Topology

/-- A branched power equation plus matching rotation multipliers forces the marked local
equivariance germ. -/
theorem eventuallyEq_of_branched_power_action
    {A B τ φ : ℂ → ℂ} {a b lambda mu : ℂ} {k m : ℕ}
    (hA : AnalyticAt ℂ A a) (hAfix : A a = a)
    (hAderiv : deriv A a = lambda) (hAderiv0 : deriv A a ≠ 0)
    (hB : AnalyticAt ℂ B b) (hBfix : B b = b)
    (hBderiv : deriv B b = mu) (hBderiv0 : deriv B b ≠ 0)
    (hτ : AnalyticAt ℂ τ a) (hτab : τ a = b)
    (hφ : AnalyticAt ℂ φ b) (hφ0 : φ b = 0) (hφderiv0 : deriv φ b ≠ 0)
    (hTorder : analyticOrderAt (φ ∘ τ) a = k)
    (hresonance : lambda ^ k = mu) (hm : m ≠ 0)
    (hpow : (fun z ↦ φ (τ (A z)) ^ m) =ᶠ[nhds a]
      fun z ↦ φ (B (τ z)) ^ m) :
    (fun z ↦ τ (A z)) =ᶠ[nhds a] fun z ↦ B (τ z) := by
  let T : ℂ → ℂ := φ ∘ τ
  let R : ℂ → ℂ := φ ∘ B
  let X : ℂ → ℂ := T ∘ A
  let Y : ℂ → ℂ := R ∘ τ
  have hTat : AnalyticAt ℂ T a := by
    exact (hτab ▸ hφ).comp hτ
  have hT0 : T a = 0 := by simp only [T, Function.comp_apply, hτab, hφ0]
  obtain ⟨h, hh, hh0, hTfactor⟩ :=
    hTat.analyticOrderAt_eq_natCast.mp hTorder
  have hTfactor' : T =ᶠ[nhds a] fun z ↦ (z - a) ^ k * h z := by
    filter_upwards [hTfactor] with z hz
    simpa only [smul_eq_mul] using hz
  obtain ⟨s, hs, hsderiv, hs0, hAfactor⟩ :=
    AnalyticAt.exists_linear_normalForm_of_deriv_ne_zero hA hAderiv0
  have hsvalue : s a = lambda := hsderiv.trans hAderiv
  have hlambda0 : lambda ≠ 0 := hAderiv ▸ hAderiv0
  have hRan : AnalyticAt ℂ R b := by
    exact (hBfix ▸ hφ).comp hB
  have hR0 : R b = 0 := by simp only [R, Function.comp_apply, hBfix, hφ0]
  have hRderiv : deriv R b = deriv φ b * deriv B b := by
    have hcomp := ((hBfix ▸ hφ).differentiableAt.hasDerivAt.comp b
      hB.differentiableAt.hasDerivAt).deriv
    rw [hBfix] at hcomp
    simpa only [R] using hcomp
  have hRderiv0 : deriv R b ≠ 0 := by
    rw [hRderiv]
    exact mul_ne_zero hφderiv0 hBderiv0
  obtain ⟨q, hq, hqvalue, hq0, hRfactor⟩ :=
    exists_mul_normalForm_of_common_simple_zero hφ hRan hφ0 hR0
      hφderiv0 hRderiv0
  have hqmu : q b = mu := by
    rw [hqvalue, hRderiv, hBderiv]
    field_simp
  have hTfactorA : (fun z ↦ T (A z)) =ᶠ[nhds a]
      fun z ↦ (A z - a) ^ k * h (A z) := by
    have hAtend : Tendsto A (nhds a) (nhds a) := by
      have hc := hA.continuousAt
      change Tendsto A (nhds a) (nhds (A a)) at hc
      rw [hAfix] at hc
      exact hc
    exact hTfactor'.comp_tendsto hAtend
  have hAfactor' : (fun z ↦ A z - a) =ᶠ[nhds a]
      fun z ↦ (z - a) * s z := by
    filter_upwards [hAfactor] with z hz
    simpa only [hAfix] using hz
  let u : ℂ → ℂ := fun z ↦ s z ^ k * h (A z)
  have hu : AnalyticAt ℂ u a := by
    have hhA : AnalyticAt ℂ (h ∘ A) a := by
      exact (hAfix ▸ hh).comp hA
    exact (hs.pow k).mul hhA
  have huvalue : u a = mu * h a := by
    simp only [u, hAfix, hsvalue, hresonance]
  have hu0 : u a ≠ 0 := by
    have hmu0 : mu ≠ 0 := hBderiv ▸ hBderiv0
    rw [huvalue]
    exact mul_ne_zero hmu0 hh0
  have hXfactor : X =ᶠ[nhds a] fun z ↦ (z - a) ^ k * u z := by
    filter_upwards [hTfactorA, hAfactor'] with z hTz hAz
    simp only [X, Function.comp_apply]
    rw [hTz, hAz]
    simp only [u, mul_pow]
    ring
  have hRfactorτ : (fun z ↦ R (τ z)) =ᶠ[nhds a]
      fun z ↦ φ (τ z) * q (τ z) := by
    have hτtend : Tendsto τ (nhds a) (nhds b) := by
      have hc := hτ.continuousAt
      change Tendsto τ (nhds a) (nhds (τ a)) at hc
      rw [hτab] at hc
      exact hc
    exact hRfactor.comp_tendsto hτtend
  let v : ℂ → ℂ := fun z ↦ h z * q (τ z)
  have hv : AnalyticAt ℂ v a := by
    have hqτ : AnalyticAt ℂ (q ∘ τ) a := (hτab ▸ hq).comp hτ
    exact hh.mul hqτ
  have hvvalue : v a = mu * h a := by
    simp only [v, hτab, hqmu]
    ring
  have hv0 : v a ≠ 0 := by
    rw [hvvalue, ← huvalue]
    exact hu0
  have hYfactor : Y =ᶠ[nhds a] fun z ↦ (z - a) ^ k * v z := by
    filter_upwards [hRfactorτ, hTfactor'] with z hRz hTz
    simp only [Y, Function.comp_apply]
    rw [hRz]
    change T z * q (τ z) = _
    rw [hTz]
    simp only [v]
    ring
  have hXYpow : (fun z ↦ X z ^ m) =ᶠ[nhds a] fun z ↦ Y z ^ m := by
    simpa only [X, Y, T, R, Function.comp_apply] using hpow
  have hXY : X =ᶠ[nhds a] Y :=
    eventuallyEq_of_pow_eq_of_same_normalForm hu hv (huvalue.trans hvvalue.symm) hu0 hm
      hXfactor hYfactor hXYpow
  obtain ⟨S, hS, hφinj⟩ :=
    (exists_injOn_nhds_iff_deriv_ne_zero hφ).mpr hφderiv0
  have hleftS : ∀ᶠ z in nhds a, τ (A z) ∈ S := by
    have hleft : Tendsto (fun z ↦ τ (A z)) (nhds a) (nhds b) := by
      have hτAt : ContinuousAt τ (A a) := by rw [hAfix]; exact hτ.continuousAt
      have hcomp := hτAt.comp hA.continuousAt
      change Tendsto (fun z ↦ τ (A z)) (nhds a) (nhds (τ (A a))) at hcomp
      rw [hAfix, hτab] at hcomp
      exact hcomp
    exact hleft hS
  have hrightS : ∀ᶠ z in nhds a, B (τ z) ∈ S := by
    have hright : Tendsto (fun z ↦ B (τ z)) (nhds a) (nhds b) := by
      have hBAt : ContinuousAt B (τ a) := by rw [hτab]; exact hB.continuousAt
      have hcomp := hBAt.comp hτ.continuousAt
      change Tendsto (fun z ↦ B (τ z)) (nhds a) (nhds (B (τ a))) at hcomp
      rw [hτab, hBfix] at hcomp
      exact hcomp
    exact hright hS
  filter_upwards [hXY, hleftS, hrightS] with z hφeq hleft hright
  exact hφinj hleft hright hφeq


end TauCeti
