module

public import SphereSixComplex.Periods.Uniformization.PowerNormalFormCurrent
import all SphereSixComplex.Periods.Uniformization.PowerNormalFormCurrent
public import TauCeti.Analysis.Complex.Conformal.Biholomorph
import all TauCeti.Analysis.Complex.Conformal.Biholomorph

@[expose] public section

noncomputable section

namespace TauCeti

open Complex Filter Function Metric Set Topology

/-- Local lifting between two exact holomorphic power branches.  If `A` has order `m * k` and
`B` has order `m`, then locally `B ∘ L = A`; in normal-form coordinates the lift is simply the
`k`-th power followed by the inverse target chart. -/
theorem exists_local_branchedLift_of_analyticOrderAt
    {A B : ℂ → ℂ} {a b : ℂ} {m k : ℕ}
    (hA : AnalyticAt ℂ A a) (hB : AnalyticAt ℂ B b)
    (hordA : analyticOrderAt A a = m * k)
    (hordB : analyticOrderAt B b = m) (hm : m ≠ 0) (hk : k ≠ 0) :
    ∃ r > 0, ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (ball a r) ∧ L a = b ∧
        ∀ z ∈ ball a r, B (L z) = A z := by
  have hmk : m * k ≠ 0 := Nat.mul_ne_zero hm hk
  obtain ⟨rA, hrA, φA, hφAd, hφAi, hφA0, -, hAeq⟩ :=
    exists_powerChart_of_analyticOrderAt hA hordA hmk
  obtain ⟨rB, hrB, φB, hφBd, hφBi, hφB0, -, hBeq⟩ :=
    exists_powerChart_of_analyticOrderAt hB hordB hm
  let eB : OpenPartialHomeomorph ℂ ℂ :=
    TauCeti.DifferentiableOn.toOpenPartialHomeomorph hφBd isOpen_ball hφBi
  let Ψ : ℂ → ℂ := φA ^ k
  have hzero_target : 0 ∈ eB.target := by
    simpa [eB] using (show 0 ∈ φB '' ball b rB from
      ⟨b, mem_ball_self hrB, hφB0⟩)
  have hΨa : Ψ a = 0 := by simp [Ψ, hφA0, hk]
  have hΨcont : ContinuousAt Ψ a := by
    exact ((hφAd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrA))).pow k).continuousAt
  have hgood : ball a rA ∩ Ψ ⁻¹' eB.target ∈ 𝓝 a := by
    exact Filter.inter_mem (isOpen_ball.mem_nhds (mem_ball_self hrA))
      (hΨcont (hΨa.symm ▸ eB.open_target.mem_nhds hzero_target))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hgood
  let L : ℂ → ℂ := fun z ↦ eB.symm (Ψ z)
  have hballA : ball a r ⊆ ball a rA := fun z hz ↦ (hrsub hz).1
  have hΨmap : MapsTo Ψ (ball a r) eB.target := fun z hz ↦ (hrsub hz).2
  have hΨdiff : DifferentiableOn ℂ Ψ (ball a r) := by
    exact (hφAd.pow k).mono hballA
  have hBinv : DifferentiableOn ℂ eB.symm eB.target := by
    apply OpenPartialHomeomorph.differentiableOn_symm
    simpa [eB] using hφBd
  have hLdiff : DifferentiableOn ℂ L (ball a r) := by
    simpa only [L, Function.comp_def] using hBinv.comp hΨdiff hΨmap
  refine ⟨r, hr, L, hLdiff.analyticOnNhd isOpen_ball, ?_, fun z hz ↦ ?_⟩
  · change eB.symm (Ψ a) = b
    rw [hΨa]
    have hbsource : b ∈ eB.source := by
      have hb : b ∈ ball b rB := Metric.mem_ball_self (x := b) hrB
      simpa [eB] using hb
    rw [← hφB0]
    simpa [eB] using eB.left_inv hbsource
  · have hΨz : Ψ z ∈ eB.target := hΨmap hz
    have hLsource : L z ∈ eB.source := by
      exact eB.map_target hΨz
    have hchart : φB (L z) = Ψ z := by
      simpa [L, eB] using eB.right_inv hΨz
    calc
      B (L z) = φB (L z) ^ m := hBeq (L z) (by simpa [eB] using hLsource)
      _ = Ψ z ^ m := congrArg (fun w : ℂ ↦ w ^ m) hchart
      _ = φA z ^ (m * k) := by
        simp only [Ψ, Pi.pow_apply]
        rw [← pow_mul, Nat.mul_comm]
      _ = A z := (hAeq z (hballA hz)).symm

/-- The equal-order local lift needed at the order-three elliptic point. -/
theorem exists_local_branchedLift_order_three
    {A B : ℂ → ℂ} {a b : ℂ}
    (hA : AnalyticAt ℂ A a) (hB : AnalyticAt ℂ B b)
    (hordA : analyticOrderAt A a = 3) (hordB : analyticOrderAt B b = 3) :
    ∃ r > 0, ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (ball a r) ∧ L a = b ∧
        ∀ z ∈ ball a r, B (L z) = A z := by
  exact exists_local_branchedLift_of_analyticOrderAt
    (m := 3) (k := 1) hA hB (by simpa using hordA) hordB (by norm_num) (by norm_num)

/-- The degree-two local lift needed at the order-four source / order-two target elliptic point. -/
theorem exists_local_branchedLift_order_four_two
    {A B : ℂ → ℂ} {a b : ℂ}
    (hA : AnalyticAt ℂ A a) (hB : AnalyticAt ℂ B b)
    (hordA : analyticOrderAt A a = 4) (hordB : analyticOrderAt B b = 2) :
    ∃ r > 0, ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (ball a r) ∧ L a = b ∧
        ∀ z ∈ ball a r, B (L z) = A z := by
  exact exists_local_branchedLift_of_analyticOrderAt
    (m := 2) (k := 2) hA hB
      (by calc
        analyticOrderAt A a = 4 := hordA
        _ = (2 : ℕ∞) * 2 := by norm_num)
      hordB (by norm_num) (by norm_num)


end TauCeti
