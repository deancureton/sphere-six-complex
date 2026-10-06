module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.Notation

@[expose] public section

set_option autoImplicit false

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology RealInnerProductSpace

noncomputable section

namespace CrossField

section BandAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ea Eb F G : Type*} [NormedAddCommGroup Ea] [InnerProductSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  [NormedAddCommGroup Eb] [InnerProductSpace ℝ Eb] [FiniteDimensional ℝ Eb]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

theorem exists_uniform_taylor {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {φ : E → F'} {W : Set E} (hW : IsOpen W) (hφ : ContDiffOn ℝ 2 φ W) {K : Set E}
    (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ y ∈ K, ∀ z : E, ‖z - y‖ ≤ r →
      z ∈ W ∧ ‖φ z - φ y - fderiv ℝ φ y (z - y)‖ ≤ C * ‖z - y‖ ^ 2 ∧
        ‖fderiv ℝ φ z - fderiv ℝ φ y‖ ≤ C * ‖z - y‖ := by
  obtain ⟨r, hr, hrW⟩ := hK.exists_cthickening_subset_open hW hKW
  set T : Set E := Metric.cthickening r K with hTdef
  have hTc : IsCompact T := hK.cthickening
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ φ) W := hφ.fderiv_of_isOpen hW (by norm_num)
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) W :=
    hD1.continuousOn_fderiv_of_isOpen hW le_rfl
  obtain ⟨M, hM⟩ := hTc.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ φ)) (hD2c.mono hrW)
  have hφd : ∀ x ∈ W, DifferentiableAt ℝ φ x := fun x hx =>
    ((hφ.differentiableOn (by norm_num)) x hx).differentiableAt (hW.mem_nhds hx)
  have hDd : ∀ x ∈ W, DifferentiableAt ℝ (fderiv ℝ φ) x := fun x hx =>
    ((hD1.differentiableOn one_ne_zero) x hx).differentiableAt (hW.mem_nhds hx)
  refine ⟨r, max M 0, hr, le_max_right _ _, ?_⟩
  intro y hy z hz
  have hball : Metric.closedBall y r ⊆ W :=
    (Metric.closedBall_subset_cthickening hy r).trans hrW
  have hballT : Metric.closedBall y r ⊆ T := Metric.closedBall_subset_cthickening hy r
  have hyB : y ∈ Metric.closedBall y r := Metric.mem_closedBall_self hr.le
  have hzB : z ∈ Metric.closedBall y r := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hz
  have hDlip : ∀ x ∈ Metric.closedBall y r,
      ‖fderiv ℝ φ x - fderiv ℝ φ y‖ ≤ max M 0 * ‖x - y‖ := by
    intro x hx
    exact (convex_closedBall y r).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => hDd w (hball hw))
      (fun w hw => (hM w (hballT hw)).trans (le_max_left _ _)) hyB hx
  refine ⟨hball hzB, ?_, hDlip z hzB⟩
  set ρ : ℝ := ‖z - y‖ with hρ
  have hsub : Metric.closedBall y ρ ⊆ Metric.closedBall y r :=
    Metric.closedBall_subset_closedBall hz
  have hyρ : y ∈ Metric.closedBall y ρ := Metric.mem_closedBall_self (norm_nonneg _)
  have hzρ : z ∈ Metric.closedBall y ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
  have key := (convex_closedBall y ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun x => φ x - fderiv ℝ φ y x) (f' := fun x => fderiv ℝ φ x - fderiv ℝ φ y)
    (C := max M 0 * ρ)
    (fun x hx => (((hφd x (hball (hsub hx))).hasFDerivAt).sub
      (fderiv ℝ φ y).hasFDerivAt).hasFDerivWithinAt)
    (fun x hx => by
      refine (hDlip x (hsub hx)).trans ?_
      have : ‖x - y‖ ≤ ρ := by
        have := hx; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
      exact mul_le_mul_of_nonneg_left this (le_max_right _ _))
    hyρ hzρ
  have heq : (φ z - fderiv ℝ φ y z) - (φ y - fderiv ℝ φ y y)
      = φ z - φ y - fderiv ℝ φ y (z - y) := by
    rw [map_sub]; abel
  rw [heq] at key
  calc ‖φ z - φ y - fderiv ℝ φ y (z - y)‖ ≤ max M 0 * ρ * ‖z - y‖ := key
    _ = max M 0 * ‖z - y‖ ^ 2 := by rw [hρ]; ring

theorem exists_transverse_bound {N : E → ℝ} {a : E → Ea} {b : E → Eb} {σ : ℝ → E} {s₁ s₂ : ℝ}
    {W : Set E} (hW : IsOpen W) (hσc : ContinuousOn σ (Icc s₁ s₂))
    (hσW : ∀ s ∈ Icc s₁ s₂, σ s ∈ W) (hN : ContDiffOn ℝ 2 N W) (ha : ContDiffOn ℝ 2 a W)
    (hb : ContDiffOn ℝ 2 b W)
    (hσ : ∀ s ∈ Icc s₁ s₂, N (σ s) = s ∧ a (σ s) = 0 ∧ b (σ s) = 0)
    (hΦ : ∀ s ∈ Icc s₁ s₂, ∀ w : E, fderiv ℝ N (σ s) w = 0 → fderiv ℝ a (σ s) w = 0 →
      fderiv ℝ b (σ s) w = 0 → w = 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ y : E, N y ∈ Icc s₁ s₂ → ‖y - σ (N y)‖ ≤ r →
      y ∈ W ∧ ‖y - σ (N y)‖ ≤ C * (‖a y‖ + ‖b y‖) := by
  classical
  have _hEa : FiniteDimensional ℝ Ea := inferInstance
  have _hEb : FiniteDimensional ℝ Eb := inferInstance
  set K : Set E := σ '' Icc s₁ s₂ with hKdef
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hσc
  have hKW : K ⊆ W := by
    rintro _ ⟨s, hs, rfl⟩
    exact hσW s hs
  obtain ⟨rN, CN, hrN, hCN, hTN⟩ := exists_uniform_taylor hW hN hK hKW
  obtain ⟨ra, Ca, hra, hCa, hTa⟩ := exists_uniform_taylor hW ha hK hKW
  obtain ⟨rb, Cb, hrb, hCb, hTb⟩ := exists_uniform_taylor hW hb hK hKW
  have hmaps : MapsTo σ (Icc s₁ s₂) W := fun s hs => hσW s hs
  have hcN : ContinuousOn (fun s => fderiv ℝ N (σ s)) (Icc s₁ s₂) :=
    (hN.continuousOn_fderiv_of_isOpen hW (by norm_num)).comp hσc hmaps
  have hca : ContinuousOn (fun s => fderiv ℝ a (σ s)) (Icc s₁ s₂) :=
    (ha.continuousOn_fderiv_of_isOpen hW (by norm_num)).comp hσc hmaps
  have hcb : ContinuousOn (fun s => fderiv ℝ b (σ s)) (Icc s₁ s₂) :=
    (hb.continuousOn_fderiv_of_isOpen hW (by norm_num)).comp hσc hmaps
  let f : ℝ × E → ℝ := fun p =>
    ‖fderiv ℝ N (σ p.1) p.2‖ + ‖fderiv ℝ a (σ p.1) p.2‖ + ‖fderiv ℝ b (σ p.1) p.2‖
  set S : Set (ℝ × E) := Icc s₁ s₂ ×ˢ Metric.sphere (0 : E) 1 with hSdef
  have hfst : MapsTo Prod.fst S (Icc s₁ s₂) := fun p hp => hp.1
  have hcont : ContinuousOn f S := by
    have h1 := (hcN.comp continuousOn_fst hfst).clm_apply continuousOn_snd
    have h2 := (hca.comp continuousOn_fst hfst).clm_apply continuousOn_snd
    have h3 := (hcb.comp continuousOn_fst hfst).clm_apply continuousOn_snd
    exact (h1.norm.add h2.norm).add h3.norm
  have hscale : ∀ s : ℝ, ∀ w : E, w ≠ 0 → f (s, ‖w‖⁻¹ • w) = ‖w‖⁻¹ * f (s, w) := by
    intro s w _
    simp only [f, map_smul, norm_smul, norm_inv, norm_norm]
    ring
  have hsph : ∀ w : E, w ≠ 0 → ‖w‖⁻¹ • w ∈ Metric.sphere (0 : E) 1 := by
    intro w hw
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)
  have hfnn : ∀ p : ℝ × E, 0 ≤ f p := fun p => by positivity
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ s ∈ Icc s₁ s₂, ∀ w : E, m * ‖w‖ ≤ f (s, w) := by
    by_cases hne : S.Nonempty
    · obtain ⟨p, hp, hmin⟩ :=
        (isCompact_Icc.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn hne hcont
      have hp2 : p.2 ≠ 0 := by
        intro h0
        have := hp.2
        rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
        exact zero_ne_one this
      refine ⟨f p, ?_, ?_⟩
      · by_contra hle
        have h0 : f p = 0 := le_antisymm (not_lt.mp hle) (hfnn p)
        have n1 := norm_nonneg (fderiv ℝ N (σ p.1) p.2)
        have n2 := norm_nonneg (fderiv ℝ a (σ p.1) p.2)
        have n3 := norm_nonneg (fderiv ℝ b (σ p.1) p.2)
        have e : ‖fderiv ℝ N (σ p.1) p.2‖ + ‖fderiv ℝ a (σ p.1) p.2‖
            + ‖fderiv ℝ b (σ p.1) p.2‖ = 0 := h0
        apply hp2
        apply hΦ p.1 hp.1 p.2
        · exact norm_eq_zero.mp (by linarith)
        · exact norm_eq_zero.mp (by linarith)
        · exact norm_eq_zero.mp (by linarith)
      · intro s hs w
        by_cases hw : w = 0
        · subst hw
          simp only [norm_zero, mul_zero]
          exact hfnn _
        · have hmem : (s, ‖w‖⁻¹ • w) ∈ S := ⟨hs, hsph w hw⟩
          have h1 : f p ≤ f (s, ‖w‖⁻¹ • w) := hmin hmem
          rw [hscale s w hw] at h1
          have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
          calc f p * ‖w‖ ≤ (‖w‖⁻¹ * f (s, w)) * ‖w‖ :=
                mul_le_mul_of_nonneg_right h1 hwpos.le
            _ = f (s, w) := by field_simp
    · refine ⟨1, one_pos, ?_⟩
      intro s hs w
      by_cases hw : w = 0
      · subst hw
        simp only [norm_zero, mul_zero]
        exact hfnn _
      · exact absurd ⟨(s, ‖w‖⁻¹ • w), hs, hsph w hw⟩ hne
  obtain ⟨m, hm0, hmf⟩ := hm
  set D : ℝ := CN + Ca + Cb with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨min (min rN ra) (min rb (m / (2 * (D + 1)))), 2 / m, ?_, by positivity, ?_⟩
  · have : 0 < m / (2 * (D + 1)) := by positivity
    exact lt_min (lt_min hrN hra) (lt_min hrb this)
  intro y hy hyr
  set s := N y with hs
  set x := σ s with hx
  have hxK : x ∈ K := ⟨s, hy, rfl⟩
  obtain ⟨hNx, hax, hbx⟩ := hσ s hy
  have hr1 : ‖y - x‖ ≤ rN := hyr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr2 : ‖y - x‖ ≤ ra := hyr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr3 : ‖y - x‖ ≤ rb := hyr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr4 : ‖y - x‖ ≤ m / (2 * (D + 1)) :=
    hyr.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hyW, hN1, -⟩ := hTN x hxK y hr1
  obtain ⟨-, ha1, -⟩ := hTa x hxK y hr2
  obtain ⟨-, hb1, -⟩ := hTb x hxK y hr3
  refine ⟨hyW, ?_⟩
  set z := y - x with hz
  have eN : N y - N x = 0 := by rw [hNx]; exact sub_self _
  rw [eN, zero_sub, norm_neg] at hN1
  rw [hax, sub_zero] at ha1
  rw [hbx, sub_zero] at hb1
  have ha2 : ‖fderiv ℝ a x z‖ ≤ ‖a y‖ + Ca * ‖z‖ ^ 2 := by
    have : fderiv ℝ a x z = a y - (a y - fderiv ℝ a x z) := by abel
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith)
  have hb2 : ‖fderiv ℝ b x z‖ ≤ ‖b y‖ + Cb * ‖z‖ ^ 2 := by
    have : fderiv ℝ b x z = b y - (b y - fderiv ℝ b x z) := by abel
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith)
  have hmz : m * ‖z‖ ≤ f (s, z) := hmf s hy z
  have hfz : f (s, z) = ‖fderiv ℝ N x z‖ + ‖fderiv ℝ a x z‖ + ‖fderiv ℝ b x z‖ := rfl
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hDz : D * ‖z‖ ≤ m / 2 := by
    have h1 : D * ‖z‖ ≤ (D + 1) * ‖z‖ := by nlinarith
    have h2 : (D + 1) * ‖z‖ ≤ (D + 1) * (m / (2 * (D + 1))) :=
      mul_le_mul_of_nonneg_left hr4 (by linarith)
    have h3 : (D + 1) * (m / (2 * (D + 1))) = m / 2 := by
      field_simp
    linarith
  have hDz2 : D * ‖z‖ ^ 2 ≤ m / 2 * ‖z‖ := by
    have := mul_le_mul_of_nonneg_right hDz hz0
    nlinarith
  have hmain : m / 2 * ‖z‖ ≤ ‖a y‖ + ‖b y‖ := by
    have : m * ‖z‖ ≤ ‖a y‖ + ‖b y‖ + D * ‖z‖ ^ 2 := by
      rw [hD]; nlinarith
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
  nlinarith

theorem exists_reflection_ascent {N : E → ℝ} {a : E → Ea} {b : E → Eb} {g : E → F} {h : E → G}
    {A₁ A₂ : E → ℝ} {σ : ℝ → E} {s₁ s₂ : ℝ} {W : Set E} (hW : IsOpen W)
    (hσc : ContinuousOn σ (Icc s₁ s₂)) (hσW : ∀ s ∈ Icc s₁ s₂, σ s ∈ W)
    (hdim : Module.finrank ℝ E = 1 + Module.finrank ℝ Ea + Module.finrank ℝ Eb)
    (hN : ContDiffOn ℝ 2 N W) (ha : ContDiffOn ℝ 2 a W) (hb : ContDiffOn ℝ 2 b W)
    (hg : ContDiffOn ℝ 2 g W) (hh : ContDiffOn ℝ 2 h W) (hA₁ : ContDiffOn ℝ 2 A₁ W)
    (hA₂ : ContDiffOn ℝ 2 A₂ W)
    (hσ : ∀ s ∈ Icc s₁ s₂, N (σ s) = s ∧ a (σ s) = 0 ∧ b (σ s) = 0 ∧ g (σ s) = 0 ∧ h (σ s) = 0)
    (hΦ : ∀ s ∈ Icc s₁ s₂, ∀ w : E, fderiv ℝ N (σ s) w = 0 → fderiv ℝ a (σ s) w = 0 →
      fderiv ℝ b (σ s) w = 0 → w = 0)
    (hgi : ∀ s ∈ Icc s₁ s₂, ∀ w : E, fderiv ℝ N (σ s) w = 0 → fderiv ℝ a (σ s) w = 0 →
      fderiv ℝ g (σ s) w = 0 → w = 0)
    (hhi : ∀ s ∈ Icc s₁ s₂, ∀ w : E, fderiv ℝ N (σ s) w = 0 → fderiv ℝ b (σ s) w = 0 →
      fderiv ℝ h (σ s) w = 0 → w = 0)
    (hA : ∀ s ∈ Icc s₁ s₂, ∀ w : E, fderiv ℝ N (σ s) w = 0 →
      fderiv ℝ A₁ (σ s) w = 0 ∧ fderiv ℝ A₂ (σ s) w = 0) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc 0 η₀, ∃ r μ₀ : ℝ, 0 < r ∧ 0 < μ₀ ∧
      ∀ μ ∈ Ioc 0 μ₀, ∀ y : E, N y ∈ Icc s₁ s₂ → ‖y - σ (N y)‖ ≤ r → (a y ≠ 0 ∨ b y ≠ 0) →
        ∃ w : E, fderiv ℝ N y w = 0 ∧
          0 < fderiv ℝ (fun z => ‖a z‖ ^ 2 - η * ‖g z‖ ^ 2 + μ * A₁ z) y w ∧
          0 < fderiv ℝ (fun z => η * ‖h z‖ ^ 2 - ‖b z‖ ^ 2 + μ * A₂ z) y w := by
  classical
  have _hF : FiniteDimensional ℝ F := inferInstance
  have _hG : FiniteDimensional ℝ G := inferInstance
  have key : ∀ η Q κ D Ee G H m ε μ₀ A B δ tα tβ err dv X μ : ℝ, 0 < η → 2 * η * Q ^ 2 ≤ 1 →
      0 < κ → 0 ≤ D → 0 ≤ G → 0 ≤ H →
      H = Q ^ 2 * (6 * D + 9 * D ^ 2) + 2 * κ * (κ + 2) * D + Ee → 0 < m → m ≤ 1 →
      m ≤ 2 * η * κ ^ 2 → ε ≤ 1 → ε * (16 * η * H + 1) ≤ m → μ₀ * (8 * (G + 1)) = m →
      0 ≤ A → 0 ≤ B → 0 < A + B → A + B ≤ ε → 0 ≤ δ →
      δ ≤ D * (A + B) ^ 2 → 0 ≤ tα → tα ≤ Q * (A + 3 * δ) → 0 ≤ tβ →
      κ * B - (κ + 2) * δ ≤ tβ → err ≤ Ee * (A + B) ^ 3 → |dv| ≤ G * (A + B) ^ 2 →
      X ≤ tα ^ 2 - tβ ^ 2 + err → 0 < μ → μ ≤ μ₀ → 0 < 2 * A ^ 2 - 2 * η * X + μ * dv := by
    intro η Q κ D Ee G H m ε μ₀ A B δ tα tβ err dv X μ hη0 hηQ hκ hD0 hG0 hH0 hH hm0 hm1 hmκ hε1 hεH
      hμ₀G hA hB hρ hρε hδ hδD htα htαQ htβ htβκ herr hdv hX hμ hμμ
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = A + B := ⟨_, rfl⟩
    rw [← hρdef] at hρ hρε hδD herr hdv
    have hρ1 : ρ ≤ 1 := hρε.trans hε1
    have hAρ : A ≤ ρ := by linarith only [hρdef, hB]
    have hBρ : B ≤ ρ := by linarith only [hρdef, hA]
    have hρ4 : ρ ^ 4 ≤ ρ ^ 3 := by
      have : ρ ^ 4 = ρ * ρ ^ 3 := by ring
      rw [this]
      exact mul_le_of_le_one_left (by positivity) hρ1
    have hAδ : A * δ ≤ D * ρ ^ 3 := by
      calc A * δ ≤ ρ * (D * ρ ^ 2) := mul_le_mul hAρ hδD hδ hρ.le
        _ = D * ρ ^ 3 := by ring
    have hBδ : B * δ ≤ D * ρ ^ 3 := by
      calc B * δ ≤ ρ * (D * ρ ^ 2) := mul_le_mul hBρ hδD hδ hρ.le
        _ = D * ρ ^ 3 := by ring
    have hδ2 : δ ^ 2 ≤ D ^ 2 * ρ ^ 3 := by
      calc δ ^ 2 ≤ (D * ρ ^ 2) ^ 2 := pow_le_pow_left₀ hδ hδD 2
        _ = D ^ 2 * ρ ^ 4 := by ring
        _ ≤ D ^ 2 * ρ ^ 3 := mul_le_mul_of_nonneg_left hρ4 (sq_nonneg D)
    have hα : tα ^ 2 ≤ Q ^ 2 * A ^ 2 + Q ^ 2 * (6 * D + 9 * D ^ 2) * ρ ^ 3 := by
      have h1 : A ^ 2 + 6 * (A * δ) + 9 * δ ^ 2 ≤ A ^ 2 + 6 * (D * ρ ^ 3) + 9 * (D ^ 2 * ρ ^ 3) := by
        linarith only [hAδ, hδ2]
      calc tα ^ 2 ≤ (Q * (A + 3 * δ)) ^ 2 := pow_le_pow_left₀ htα htαQ 2
        _ = Q ^ 2 * (A ^ 2 + 6 * (A * δ) + 9 * δ ^ 2) := by ring
        _ ≤ Q ^ 2 * (A ^ 2 + 6 * (D * ρ ^ 3) + 9 * (D ^ 2 * ρ ^ 3)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg Q)
        _ = Q ^ 2 * A ^ 2 + Q ^ 2 * (6 * D + 9 * D ^ 2) * ρ ^ 3 := by ring
    have hβ : κ ^ 2 * B ^ 2 - 2 * κ * (κ + 2) * (D * ρ ^ 3) ≤ tβ ^ 2 := by
      have hk : 0 ≤ 2 * κ * (κ + 2) := by positivity
      have h1 : κ ^ 2 * B ^ 2 - 2 * κ * (κ + 2) * (B * δ) ≤ tβ ^ 2 := by
        rcases le_or_gt (κ * B - (κ + 2) * δ) 0 with hc | hc
        · have h2 : κ * B * (κ * B) ≤ κ * B * ((κ + 2) * δ) :=
            mul_le_mul_of_nonneg_left (by linarith only [hc]) (by positivity)
          have h3 : 0 ≤ κ * B * ((κ + 2) * δ) := by positivity
          have h4 : κ ^ 2 * B ^ 2 - 2 * κ * (κ + 2) * (B * δ) =
              κ * B * (κ * B) - 2 * (κ * B * ((κ + 2) * δ)) := by ring
          rw [h4]
          linarith only [h2, h3, sq_nonneg tβ]
        · have h2 : (κ * B - (κ + 2) * δ) ^ 2 ≤ tβ ^ 2 := pow_le_pow_left₀ hc.le htβκ 2
          have h4 : (κ * B - (κ + 2) * δ) ^ 2 =
              κ ^ 2 * B ^ 2 - 2 * κ * (κ + 2) * (B * δ) + ((κ + 2) * δ) ^ 2 := by ring
          linarith only [h2, h4, sq_nonneg ((κ + 2) * δ)]
      have h2 : 2 * κ * (κ + 2) * (B * δ) ≤ 2 * κ * (κ + 2) * (D * ρ ^ 3) :=
        mul_le_mul_of_nonneg_left hBδ hk
      linarith only [h1, h2]
    have hdv' : -(G * ρ ^ 2) ≤ dv := by linarith only [neg_abs_le dv, hdv]
    have hμdv : μ * (-(G * ρ ^ 2)) ≤ μ * dv := mul_le_mul_of_nonneg_left hdv' hμ.le
    have hμG : μ * (G * ρ ^ 2) ≤ m / 8 * ρ ^ 2 := by
      have h1 : μ * G ≤ m / 8 := by
        have h2 : μ * G ≤ μ₀ * G := mul_le_mul_of_nonneg_right hμμ hG0
        have h3 : μ₀ * G ≤ μ₀ * (G + 1) := by linarith only [hμ, hμμ]
        linarith only [h2, h3, hμ₀G]
      calc μ * (G * ρ ^ 2) = (μ * G) * ρ ^ 2 := by ring
        _ ≤ m / 8 * ρ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ρ)
    have hηH : 2 * η * H * ρ ^ 3 ≤ m / 8 * ρ ^ 2 := by
      have h1 : ρ * (16 * η * H + 1) ≤ m := by
        have hc : 0 ≤ 16 * η * H + 1 := by positivity
        exact (mul_le_mul_of_nonneg_right hρε hc).trans hεH
      have h2 : 2 * η * H * ρ ≤ m / 8 := by linarith only [h1, hρ]
      calc 2 * η * H * ρ ^ 3 = (2 * η * H * ρ) * ρ ^ 2 := by ring
        _ ≤ m / 8 * ρ ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ρ)
    have hηX : 2 * η * X ≤ 2 * η * (tα ^ 2 - tβ ^ 2 + err) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    have herr' : 2 * η * err ≤ 2 * η * (Ee * ρ ^ 3) :=
      mul_le_mul_of_nonneg_left herr (by positivity)
    have hα' : 2 * η * tα ^ 2 ≤
        2 * η * (Q ^ 2 * A ^ 2 + Q ^ 2 * (6 * D + 9 * D ^ 2) * ρ ^ 3) :=
      mul_le_mul_of_nonneg_left hα (by positivity)
    have hβ' : 2 * η * (κ ^ 2 * B ^ 2 - 2 * κ * (κ + 2) * (D * ρ ^ 3)) ≤ 2 * η * tβ ^ 2 :=
      mul_le_mul_of_nonneg_left hβ (by positivity)
    have hQA : 2 * η * Q ^ 2 * A ^ 2 ≤ A ^ 2 := by
      have := mul_le_mul_of_nonneg_right hηQ (sq_nonneg A)
      linarith only [this]
    have hmA : m * A ^ 2 ≤ A ^ 2 := by
      have := mul_le_mul_of_nonneg_right hm1 (sq_nonneg A)
      linarith only [this]
    have hmB : m * B ^ 2 ≤ 2 * η * κ ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_right hmκ (sq_nonneg B)
    have hsq : m * ρ ^ 2 ≤ 2 * (m * A ^ 2 + m * B ^ 2) := by
      have h1 : m * ρ ^ 2 + m * (A - B) ^ 2 = 2 * (m * A ^ 2 + m * B ^ 2) := by rw [hρdef]; ring
      have h2 : 0 ≤ m * (A - B) ^ 2 := by positivity
      linarith only [h1, h2]
    have hmρ : 0 < m * ρ ^ 2 := by positivity
    have hHexp : 2 * η * H * ρ ^ 3 = 2 * η * (Q ^ 2 * (6 * D + 9 * D ^ 2) * ρ ^ 3) +
        2 * η * (2 * κ * (κ + 2) * (D * ρ ^ 3)) + 2 * η * (Ee * ρ ^ 3) := by
      rw [hH]; ring
    have e1 : 2 * η * (Q ^ 2 * A ^ 2 + Q ^ 2 * (6 * D + 9 * D ^ 2) * ρ ^ 3) =
      2 * η * Q ^ 2 * A ^ 2 + 2 * η * (Q ^ 2 * (6 * D + 9 * D ^ 2) * ρ ^ 3) := by ring
    have e2 : 2 * η * (κ ^ 2 * B ^ 2 - 2 * κ * (κ + 2) * (D * ρ ^ 3)) =
      2 * η * κ ^ 2 * B ^ 2 - 2 * η * (2 * κ * (κ + 2) * (D * ρ ^ 3)) := by ring
    have e3 : 2 * η * (tα ^ 2 - tβ ^ 2 + err) = 2 * η * tα ^ 2 - 2 * η * tβ ^ 2 + 2 * η * err := by
      ring
    have e4 : μ * (-(G * ρ ^ 2)) = -(μ * (G * ρ ^ 2)) := by ring
    linarith only [hηX, herr', hα', hβ', hQA, hmA, hmB, hsq, hmρ, hHexp, e1, e2, e3, e4, hμdv,
      hμG, hηH]
  have hIc : IsCompact (Icc s₁ s₂) := isCompact_Icc
  have hKc : IsCompact (σ '' Icc s₁ s₂) := hIc.image_of_continuousOn hσc
  have hKW : σ '' Icc s₁ s₂ ⊆ W := by
    rintro _ ⟨s, hs, rfl⟩
    exact hσW s hs
  have h12 : (1 : WithTop ℕ∞) ≤ 2 := by norm_num
  have hmaps : MapsTo σ (Icc s₁ s₂) W := fun s hs => hσW s hs
  have cN : ContinuousOn (fun s => fderiv ℝ N (σ s)) (Icc s₁ s₂) :=
    (hN.continuousOn_fderiv_of_isOpen hW h12).comp hσc hmaps
  have ca : ContinuousOn (fun s => fderiv ℝ a (σ s)) (Icc s₁ s₂) :=
    (ha.continuousOn_fderiv_of_isOpen hW h12).comp hσc hmaps
  have cb : ContinuousOn (fun s => fderiv ℝ b (σ s)) (Icc s₁ s₂) :=
    (hb.continuousOn_fderiv_of_isOpen hW h12).comp hσc hmaps
  have cg : ContinuousOn (fun s => fderiv ℝ g (σ s)) (Icc s₁ s₂) :=
    (hg.continuousOn_fderiv_of_isOpen hW h12).comp hσc hmaps
  have ch : ContinuousOn (fun s => fderiv ℝ h (σ s)) (Icc s₁ s₂) :=
    (hh.continuousOn_fderiv_of_isOpen hW h12).comp hσc hmaps
  have c₁ : ContinuousOn (fun s => fderiv ℝ A₁ (σ s)) (Icc s₁ s₂) :=
    (hA₁.continuousOn_fderiv_of_isOpen hW h12).comp hσc hmaps
  have c₂ : ContinuousOn (fun s => fderiv ℝ A₂ (σ s)) (Icc s₁ s₂) :=
    (hA₂.continuousOn_fderiv_of_isOpen hW h12).comp hσc hmaps
  obtain ⟨Ma, hMa⟩ := hIc.exists_bound_of_continuousOn ca
  obtain ⟨Mb, hMb⟩ := hIc.exists_bound_of_continuousOn cb
  obtain ⟨Mg, hMg⟩ := hIc.exists_bound_of_continuousOn cg
  obtain ⟨Mh, hMh⟩ := hIc.exists_bound_of_continuousOn ch
  obtain ⟨M₁, hM₁⟩ := hIc.exists_bound_of_continuousOn c₁
  obtain ⟨M₂, hM₂⟩ := hIc.exists_bound_of_continuousOn c₂
  obtain ⟨M, hM1, bda, bdb, bdg, bdh, bd₁, bd₂⟩ : ∃ M : ℝ, 1 ≤ M ∧
      (∀ s ∈ Icc s₁ s₂, ‖fderiv ℝ a (σ s)‖ ≤ M) ∧ (∀ s ∈ Icc s₁ s₂, ‖fderiv ℝ b (σ s)‖ ≤ M) ∧
      (∀ s ∈ Icc s₁ s₂, ‖fderiv ℝ g (σ s)‖ ≤ M) ∧ (∀ s ∈ Icc s₁ s₂, ‖fderiv ℝ h (σ s)‖ ≤ M) ∧
      (∀ s ∈ Icc s₁ s₂, ‖fderiv ℝ A₁ (σ s)‖ ≤ M) ∧
      (∀ s ∈ Icc s₁ s₂, ‖fderiv ℝ A₂ (σ s)‖ ≤ M) := by
    refine ⟨1 + |Ma| + |Mb| + |Mg| + |Mh| + |M₁| + |M₂|, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith only [abs_nonneg Ma, abs_nonneg Mb, abs_nonneg Mg, abs_nonneg Mh, abs_nonneg M₁,
        abs_nonneg M₂]
    · intro s hs
      linarith only [hMa s hs, le_abs_self Ma, abs_nonneg Mb, abs_nonneg Mg, abs_nonneg Mh,
        abs_nonneg M₁, abs_nonneg M₂]
    · intro s hs
      linarith only [hMb s hs, le_abs_self Mb, abs_nonneg Ma, abs_nonneg Mg, abs_nonneg Mh,
        abs_nonneg M₁, abs_nonneg M₂]
    · intro s hs
      linarith only [hMg s hs, le_abs_self Mg, abs_nonneg Mb, abs_nonneg Ma, abs_nonneg Mh,
        abs_nonneg M₁, abs_nonneg M₂]
    · intro s hs
      linarith only [hMh s hs, le_abs_self Mh, abs_nonneg Mb, abs_nonneg Mg, abs_nonneg Ma,
        abs_nonneg M₁, abs_nonneg M₂]
    · intro s hs
      linarith only [hM₁ s hs, le_abs_self M₁, abs_nonneg Mb, abs_nonneg Mg, abs_nonneg Mh,
        abs_nonneg Ma, abs_nonneg M₂]
    · intro s hs
      linarith only [hM₂ s hs, le_abs_self M₂, abs_nonneg Mb, abs_nonneg Mg, abs_nonneg Mh,
        abs_nonneg M₁, abs_nonneg Ma]
  have lowb : ∀ f : ℝ → E → ℝ, ContinuousOn (fun q : ℝ × E => f q.1 q.2) (Icc s₁ s₂ ×ˢ univ) →
      (∀ s ∈ Icc s₁ s₂, ∀ (t : ℝ) (u : E), f s (t • u) = ‖t‖ * f s u) →
      (∀ s ∈ Icc s₁ s₂, ∀ u : E, u ≠ 0 → 0 < f s u) →
      ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Icc s₁ s₂, ∀ u : E, c * ‖u‖ ≤ f s u := by
    intro f hf hhom hpos
    have hzero : ∀ s ∈ Icc s₁ s₂, f s 0 = 0 := by
      intro s hs
      have := hhom s hs 0 0
      simpa using this
    have hscale : ∀ s ∈ Icc s₁ s₂, ∀ u : E, u ≠ 0 → f s u = ‖u‖ * f s (‖u‖⁻¹ • u) := by
      intro s hs u hu
      have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
      have := hhom s hs ‖u‖ (‖u‖⁻¹ • u)
      rwa [smul_smul, mul_inv_cancel₀ hnu.ne', one_smul, norm_norm] at this
    have hsph : ∀ u : E, u ≠ 0 → ‖u‖⁻¹ • u ∈ Metric.sphere (0 : E) 1 := by
      intro u hu
      have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnu.ne']
    by_cases hne : (Icc s₁ s₂ ×ˢ Metric.sphere (0 : E) 1).Nonempty
    · obtain ⟨q, hq, hmin⟩ := (hIc.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn hne
        (hf.mono (prod_mono le_rfl (subset_univ _)))
      have hq2 : q.2 ≠ 0 := by
        intro h0
        have := hq.2
        rw [h0, mem_sphere_zero_iff_norm, norm_zero] at this
        norm_num at this
      refine ⟨f q.1 q.2, hpos q.1 hq.1 q.2 hq2, ?_⟩
      intro s hs u
      by_cases hu : u = 0
      · rw [hu, hzero s hs, norm_zero, mul_zero]
      · have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
        have h1 : f q.1 q.2 ≤ f s (‖u‖⁻¹ • u) :=
          isMinOn_iff.1 hmin (s, ‖u‖⁻¹ • u) ⟨hs, hsph u hu⟩
        rw [hscale s hs u hu, mul_comm]
        exact mul_le_mul_of_nonneg_left h1 hnu.le
    · refine ⟨1, one_pos, ?_⟩
      intro s hs u
      by_cases hu : u = 0
      · rw [hu, hzero s hs, norm_zero, mul_zero]
      · exact absurd ⟨(s, ‖u‖⁻¹ • u), hs, hsph u hu⟩ hne
  have hfst : MapsTo (Prod.fst : ℝ × E → ℝ) (Icc s₁ s₂ ×ˢ univ) (Icc s₁ s₂) := fun q hq => hq.1
  have cN' : ContinuousOn (fun q : ℝ × E => fderiv ℝ N (σ q.1) q.2) (Icc s₁ s₂ ×ˢ univ) :=
    (cN.comp continuousOn_fst hfst).clm_apply continuousOn_snd
  have ca' : ContinuousOn (fun q : ℝ × E => fderiv ℝ a (σ q.1) q.2) (Icc s₁ s₂ ×ˢ univ) :=
    (ca.comp continuousOn_fst hfst).clm_apply continuousOn_snd
  have cb' : ContinuousOn (fun q : ℝ × E => fderiv ℝ b (σ q.1) q.2) (Icc s₁ s₂ ×ˢ univ) :=
    (cb.comp continuousOn_fst hfst).clm_apply continuousOn_snd
  have cg' : ContinuousOn (fun q : ℝ × E => fderiv ℝ g (σ q.1) q.2) (Icc s₁ s₂ ×ˢ univ) :=
    (cg.comp continuousOn_fst hfst).clm_apply continuousOn_snd
  have ch' : ContinuousOn (fun q : ℝ × E => fderiv ℝ h (σ q.1) q.2) (Icc s₁ s₂ ×ˢ univ) :=
    (ch.comp continuousOn_fst hfst).clm_apply continuousOn_snd
  obtain ⟨cΦ, hcΦ, lbΦ⟩ := lowb
    (fun s u => ‖fderiv ℝ N (σ s) u‖ + ‖fderiv ℝ a (σ s) u‖ + ‖fderiv ℝ b (σ s) u‖)
    ((cN'.norm.add ca'.norm).add cb'.norm)
    (fun s hs t u => by rw [map_smul, map_smul, map_smul, norm_smul, norm_smul, norm_smul]; ring)
    (fun s hs u hu => by
      by_cases h1 : fderiv ℝ N (σ s) u = 0
      · by_cases h2 : fderiv ℝ a (σ s) u = 0
        · exact add_pos_of_nonneg_of_pos (add_nonneg (norm_nonneg _) (norm_nonneg _))
            (norm_pos_iff.2 (fun h3 => hu (hΦ s hs u h1 h2 h3)))
        · exact add_pos_of_pos_of_nonneg
            (add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.2 h2)) (norm_nonneg _)
      · exact add_pos_of_pos_of_nonneg
          (add_pos_of_pos_of_nonneg (norm_pos_iff.2 h1) (norm_nonneg _)) (norm_nonneg _))
  obtain ⟨cG, hcG, lbG⟩ := lowb
    (fun s u => ‖fderiv ℝ N (σ s) u‖ + ‖fderiv ℝ a (σ s) u‖ + ‖fderiv ℝ g (σ s) u‖)
    ((cN'.norm.add ca'.norm).add cg'.norm)
    (fun s hs t u => by rw [map_smul, map_smul, map_smul, norm_smul, norm_smul, norm_smul]; ring)
    (fun s hs u hu => by
      by_cases h1 : fderiv ℝ N (σ s) u = 0
      · by_cases h2 : fderiv ℝ a (σ s) u = 0
        · exact add_pos_of_nonneg_of_pos (add_nonneg (norm_nonneg _) (norm_nonneg _))
            (norm_pos_iff.2 (fun h3 => hu (hgi s hs u h1 h2 h3)))
        · exact add_pos_of_pos_of_nonneg
            (add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.2 h2)) (norm_nonneg _)
      · exact add_pos_of_pos_of_nonneg
          (add_pos_of_pos_of_nonneg (norm_pos_iff.2 h1) (norm_nonneg _)) (norm_nonneg _))
  obtain ⟨cH, hcH, lbH⟩ := lowb
    (fun s u => ‖fderiv ℝ N (σ s) u‖ + ‖fderiv ℝ b (σ s) u‖ + ‖fderiv ℝ h (σ s) u‖)
    ((cN'.norm.add cb'.norm).add ch'.norm)
    (fun s hs t u => by rw [map_smul, map_smul, map_smul, norm_smul, norm_smul, norm_smul]; ring)
    (fun s hs u hu => by
      by_cases h1 : fderiv ℝ N (σ s) u = 0
      · by_cases h2 : fderiv ℝ b (σ s) u = 0
        · exact add_pos_of_nonneg_of_pos (add_nonneg (norm_nonneg _) (norm_nonneg _))
            (norm_pos_iff.2 (fun h3 => hu (hhi s hs u h1 h2 h3)))
        · exact add_pos_of_pos_of_nonneg
            (add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.2 h2)) (norm_nonneg _)
      · exact add_pos_of_pos_of_nonneg
          (add_pos_of_pos_of_nonneg (norm_pos_iff.2 h1) (norm_nonneg _)) (norm_nonneg _))
  have surj : ∀ x : E, (∀ u : E, fderiv ℝ N x u = 0 → fderiv ℝ a x u = 0 →
      fderiv ℝ b x u = 0 → u = 0) → ∀ (t : ℝ) (α : Ea) (β : Eb),
      ∃ u : E, fderiv ℝ N x u = t ∧ fderiv ℝ a x u = α ∧ fderiv ℝ b x u = β := by
    intro x hinj t α β
    let L : E →ₗ[ℝ] ℝ × Ea × Eb :=
      (((fderiv ℝ N x).prod ((fderiv ℝ a x).prod (fderiv ℝ b x)) : E →L[ℝ] ℝ × Ea × Eb) :
        E →ₗ[ℝ] ℝ × Ea × Eb)
    have hL : Function.Injective L := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      have hu' : (fderiv ℝ N x u, fderiv ℝ a x u, fderiv ℝ b x u) = 0 := hu
      simp only [Prod.mk_eq_zero] at hu'
      exact hinj u hu'.1 hu'.2.1 hu'.2.2
    have hfr : Module.finrank ℝ E = Module.finrank ℝ (ℝ × Ea × Eb) := by
      rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
      omega
    obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hL (t, α, β)
    have hu' : (fderiv ℝ N x u, fderiv ℝ a x u, fderiv ℝ b x u) = (t, α, β) := hu
    simp only [Prod.mk.injEq] at hu'
    exact ⟨u, hu'.1, hu'.2.1, hu'.2.2⟩
  obtain ⟨rN, CN, hrN, hCN, TN⟩ := exists_uniform_taylor hW hN hKc hKW
  obtain ⟨ra, Ca, hra, hCa, Ta⟩ := exists_uniform_taylor hW ha hKc hKW
  obtain ⟨rb, Cb, hrb, hCb, Tb⟩ := exists_uniform_taylor hW hb hKc hKW
  obtain ⟨rg, Cg, hrg, hCg, Tg⟩ := exists_uniform_taylor hW hg hKc hKW
  obtain ⟨rh, Ch, hrh, hCh, Th⟩ := exists_uniform_taylor hW hh hKc hKW
  obtain ⟨r₁, C₁, hr₁, hC₁, T₁⟩ := exists_uniform_taylor hW hA₁ hKc hKW
  obtain ⟨r₂, C₂, hr₂, hC₂, T₂⟩ := exists_uniform_taylor hW hA₂ hKc hKW
  obtain ⟨rT, CT, hrT, hCT, TT⟩ := exists_transverse_bound hW hσc hσW hN ha hb
    (fun s hs => ⟨(hσ s hs).1, (hσ s hs).2.1, (hσ s hs).2.2.1⟩) hΦ
  obtain ⟨C₀, hC₀, hCN0, hCa0, hCb0, hCg0, hCh0, hC₁0, hC₂0⟩ : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ CN ≤ C₀ ∧
      Ca ≤ C₀ ∧ Cb ≤ C₀ ∧ Cg ≤ C₀ ∧ Ch ≤ C₀ ∧ C₁ ≤ C₀ ∧ C₂ ≤ C₀ :=
    ⟨max CN (max Ca (max Cb (max Cg (max Ch (max C₁ C₂))))), hCN.trans (le_max_left _ _),
      le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _),
      ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _),
      (((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _),
      (((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)⟩
  obtain ⟨r₀, hr₀, hr₀N, hr₀a, hr₀b, hr₀g, hr₀h, hr₀₁, hr₀₂, hr₀T⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ rN ∧
      r₀ ≤ ra ∧ r₀ ≤ rb ∧ r₀ ≤ rg ∧ r₀ ≤ rh ∧ r₀ ≤ r₁ ∧ r₀ ≤ r₂ ∧ r₀ ≤ rT := by
    refine ⟨min rN (min ra (min rb (min rg (min rh (min r₁ (min r₂ rT)))))), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · simp only [lt_min_iff]
      exact ⟨hrN, hra, hrb, hrg, hrh, hr₁, hr₂, hrT⟩
    all_goals simp only [min_le_iff, le_refl, true_or, or_true]
  have hM0 : 0 ≤ M := by linarith only [hM1]
  obtain ⟨κ, hκ, hκG, hκH⟩ : ∃ κ : ℝ, 0 < κ ∧ κ * M ≤ cG ∧ κ * M ≤ cH := by
    refine ⟨min cG cH / M, by positivity, ?_, ?_⟩
    · rw [div_mul_cancel₀ _ (by linarith only [hM1] : M ≠ 0)]
      exact min_le_left _ _
    · rw [div_mul_cancel₀ _ (by linarith only [hM1] : M ≠ 0)]
      exact min_le_right _ _
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = M / cΦ := ⟨_, rfl⟩
  obtain ⟨Cw, hCw⟩ : ∃ Cw : ℝ, Cw = 2 / cΦ := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hCw0 : 0 ≤ Cw := by rw [hCw]; positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C₀ * (CT ^ 2 + CT * Cw) := ⟨_, rfl⟩
  obtain ⟨Ee, hEe⟩ : ∃ Ee : ℝ, Ee = 2 * M * C₀ * CT ^ 2 * Cw + C₀ ^ 2 * CT ^ 3 * Cw := ⟨_, rfl⟩
  obtain ⟨Gc, hGc⟩ : ∃ Gc : ℝ, Gc = C₀ * (1 + M / cΦ) * CT * Cw := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = Q ^ 2 * (6 * D + 9 * D ^ 2) + 2 * κ * (κ + 2) * D + Ee :=
    ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ mul_nonneg hC₀ (add_nonneg (sq_nonneg _) (mul_nonneg hCT hCw0))
  have hEe0 : 0 ≤ Ee := hEe ▸ add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hM0) hC₀) (sq_nonneg _)) hCw0)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hCT 3)) hCw0)
  have hGc0 : 0 ≤ Gc := hGc ▸ mul_nonneg (mul_nonneg (mul_nonneg hC₀
    (add_nonneg zero_le_one (div_nonneg hM0 hcΦ.le))) hCT) hCw0
  have hH0 : 0 ≤ H := hH ▸ add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _)
    (add_nonneg (mul_nonneg (by norm_num) hD0) (mul_nonneg (by norm_num) (sq_nonneg _))))
    (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hκ.le) (by linarith only [hκ])) hD0)) hEe0
  have hQ1 : 0 < 2 * Q ^ 2 + 1 := add_pos_of_nonneg_of_pos (mul_nonneg zero_le_two (sq_nonneg Q)) one_pos
  refine ⟨1 / (2 * Q ^ 2 + 1), one_div_pos.2 hQ1, ?_⟩
  intro η hη
  obtain ⟨hη0, hη1⟩ := hη
  have hηQ : 2 * η * Q ^ 2 ≤ 1 := by
    have h1 : η * (2 * Q ^ 2 + 1) ≤ 1 :=
      (le_div_iff₀ hQ1).1 (by simpa only [one_div] using hη1)
    have h2 : η * (2 * Q ^ 2 + 1) = 2 * η * Q ^ 2 + η := by ring
    linarith only [h1, h2, hη0]
  have hηκ : 0 < 2 * η * κ ^ 2 := mul_pos (mul_pos two_pos hη0) (pow_pos hκ 2)
  obtain ⟨m, hm0, hm1, hmκ⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ 2 * η * κ ^ 2 :=
    ⟨min 1 (2 * η * κ ^ 2), lt_min one_pos hηκ, min_le_left _ _, min_le_right _ _⟩
  have hηH : 0 < 16 * η * H + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg (by norm_num) hη0.le) hH0) one_pos
  obtain ⟨ε, hε0, hε1, hεH⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * (16 * η * H + 1) ≤ m :=
    ⟨min 1 (m / (16 * η * H + 1)), lt_min one_pos (div_pos hm0 hηH), min_le_left _ _,
      (le_div_iff₀ hηH).1 (min_le_right _ _)⟩
  have hG8 : 0 < 8 * (Gc + 1) := mul_pos (by norm_num) (add_pos_of_nonneg_of_pos hGc0 one_pos)
  obtain ⟨μ₀, hμ₀, hμ₀G⟩ : ∃ μ₀ : ℝ, 0 < μ₀ ∧ μ₀ * (8 * (Gc + 1)) = m :=
    ⟨m / (8 * (Gc + 1)), div_pos hm0 hG8, div_mul_cancel₀ m hG8.ne'⟩
  have hC6 : 0 < 6 * (C₀ + 1) := mul_pos (by norm_num) (add_pos_of_nonneg_of_pos hC₀ one_pos)
  have hMC : 0 < 2 * (M + C₀) := mul_pos two_pos (add_pos_of_pos_of_nonneg (by linarith only [hM1]) hC₀)
  obtain ⟨r, hr, hrr₀, hr1, hrc, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧ r ≤ 1 ∧
      r * (6 * (C₀ + 1)) ≤ cΦ ∧ r * (2 * (M + C₀)) ≤ ε :=
    ⟨min r₀ (min 1 (min (cΦ / (6 * (C₀ + 1))) (ε / (2 * (M + C₀))))),
      lt_min hr₀ (lt_min one_pos (lt_min (div_pos hcΦ hC6) (div_pos hε0 hMC))),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (le_div_iff₀ hC6).1 ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
      (le_div_iff₀ hMC).1 ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  refine ⟨r, μ₀, hr, hμ₀, ?_⟩
  intro μ hμ y hy hyr hab
  obtain ⟨hμ0, hμ1⟩ := hμ
  have hpK : σ (N y) ∈ σ '' Icc s₁ s₂ := ⟨N y, hy, rfl⟩
  obtain ⟨hNp, hap, hbp, hgp, hhp⟩ := hσ (N y) hy
  have hV₀ : ‖y - σ (N y)‖ ≤ r₀ := hyr.trans hrr₀
  obtain ⟨hyW, hVT⟩ := TT y hy (hV₀.trans hr₀T)
  obtain ⟨-, tN, dNd⟩ := TN _ hpK y (hV₀.trans hr₀N)
  obtain ⟨-, ta, dad⟩ := Ta _ hpK y (hV₀.trans hr₀a)
  obtain ⟨-, tb, dbd⟩ := Tb _ hpK y (hV₀.trans hr₀b)
  obtain ⟨-, tg, dgd⟩ := Tg _ hpK y (hV₀.trans hr₀g)
  obtain ⟨-, th, dhd⟩ := Th _ hpK y (hV₀.trans hr₀h)
  obtain ⟨-, -, d₁d⟩ := T₁ _ hpK y (hV₀.trans hr₀₁)
  obtain ⟨-, -, d₂d⟩ := T₂ _ hpK y (hV₀.trans hr₀₂)
  have hAp := hA (N y) hy
  have hMa' := bda (N y) hy
  have hMb' := bdb (N y) hy
  have hMg' := bdg (N y) hy
  have hMh' := bdh (N y) hy
  have hM₁' := bd₁ (N y) hy
  have hM₂' := bd₂ (N y) hy
  have lbΦ' := lbΦ (N y) hy
  have lbG' := lbG (N y) hy
  have lbH' := lbH (N y) hy
  have hΦp := hΦ (N y) hy
  clear TN Ta Tb Tg Th T₁ T₂ TT hA bda bdb bdg bdh bd₁ bd₂ lbΦ lbG lbH hσ hΦ hgi hhi cN ca cb cg ch
    c₁ c₂ cN' ca' cb' cg' ch' hMa hMb hMg hMh hM₁ hM₂ lowb hfst hmaps hKc hKW hV₀ hpK
  generalize σ (N y) = p at hNp hap hbp hgp hhp hyr hVT tN ta tb tg th dNd dad dbd dgd dhd d₁d d₂d hAp hMa' hMb' hMg' hMh' hM₁' hM₂' lbΦ' lbG' lbH' hΦp
  generalize y - p = v at hyr hVT tN ta tb tg th dNd dad dbd dgd dhd d₁d d₂d
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have hv1 : ‖v‖ ≤ 1 := hyr.trans hr1
  have dN' : ∀ u : E, ‖fderiv ℝ N y u - fderiv ℝ N p u‖ ≤ C₀ * ‖v‖ * ‖u‖ := fun u => by
    rw [← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (dNd.trans (mul_le_mul_of_nonneg_right hCN0 hv0)) (norm_nonneg u))
  have da' : ∀ u : E, ‖fderiv ℝ a y u - fderiv ℝ a p u‖ ≤ C₀ * ‖v‖ * ‖u‖ := fun u => by
    rw [← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (dad.trans (mul_le_mul_of_nonneg_right hCa0 hv0)) (norm_nonneg u))
  have db' : ∀ u : E, ‖fderiv ℝ b y u - fderiv ℝ b p u‖ ≤ C₀ * ‖v‖ * ‖u‖ := fun u => by
    rw [← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (dbd.trans (mul_le_mul_of_nonneg_right hCb0 hv0)) (norm_nonneg u))
  have dg' : ∀ u : E, ‖fderiv ℝ g y u - fderiv ℝ g p u‖ ≤ C₀ * ‖v‖ * ‖u‖ := fun u => by
    rw [← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (dgd.trans (mul_le_mul_of_nonneg_right hCg0 hv0)) (norm_nonneg u))
  have dh' : ∀ u : E, ‖fderiv ℝ h y u - fderiv ℝ h p u‖ ≤ C₀ * ‖v‖ * ‖u‖ := fun u => by
    rw [← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (dhd.trans (mul_le_mul_of_nonneg_right hCh0 hv0)) (norm_nonneg u))
  have d₁' : ∀ u : E, ‖fderiv ℝ A₁ y u - fderiv ℝ A₁ p u‖ ≤ C₀ * ‖v‖ * ‖u‖ := fun u => by
    rw [← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (d₁d.trans (mul_le_mul_of_nonneg_right hC₁0 hv0)) (norm_nonneg u))
  have d₂' : ∀ u : E, ‖fderiv ℝ A₂ y u - fderiv ℝ A₂ p u‖ ≤ C₀ * ‖v‖ * ‖u‖ := fun u => by
    rw [← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (d₂d.trans (mul_le_mul_of_nonneg_right hC₂0 hv0)) (norm_nonneg u))
  have tN' : ‖fderiv ℝ N p v‖ ≤ C₀ * ‖v‖ ^ 2 := by
    rw [hNp, sub_self, zero_sub, norm_neg] at tN
    exact tN.trans (mul_le_mul_of_nonneg_right hCN0 (sq_nonneg _))
  have ta' : ‖a y - fderiv ℝ a p v‖ ≤ C₀ * ‖v‖ ^ 2 := by
    rw [hap, sub_zero] at ta
    exact ta.trans (mul_le_mul_of_nonneg_right hCa0 (sq_nonneg _))
  have tb' : ‖b y - fderiv ℝ b p v‖ ≤ C₀ * ‖v‖ ^ 2 := by
    rw [hbp, sub_zero] at tb
    exact tb.trans (mul_le_mul_of_nonneg_right hCb0 (sq_nonneg _))
  have tg' : ‖g y - fderiv ℝ g p v‖ ≤ C₀ * ‖v‖ ^ 2 := by
    rw [hgp, sub_zero] at tg
    exact tg.trans (mul_le_mul_of_nonneg_right hCg0 (sq_nonneg _))
  have th' : ‖h y - fderiv ℝ h p v‖ ≤ C₀ * ‖v‖ ^ 2 := by
    rw [hhp, sub_zero] at th
    exact th.trans (mul_le_mul_of_nonneg_right hCh0 (sq_nonneg _))
  clear dNd dad dbd dgd dhd d₁d d₂d tN ta tb tg th
  have hVc : C₀ * ‖v‖ * 6 ≤ cΦ := by
    have h1 : C₀ * ‖v‖ ≤ r * (C₀ + 1) := by
      have := mul_le_mul hyr (by linarith only : C₀ ≤ C₀ + 1) hC₀ hr.le
      linarith only [this]
    linarith only [h1, hrc]
  have hinjy : ∀ u : E, cΦ / 2 * ‖u‖ ≤
      ‖fderiv ℝ N y u‖ + ‖fderiv ℝ a y u‖ + ‖fderiv ℝ b y u‖ := by
    intro u
    have h0 : cΦ * ‖u‖ ≤ ‖fderiv ℝ N p u‖ + ‖fderiv ℝ a p u‖ + ‖fderiv ℝ b p u‖ := lbΦ' u
    have h1 := norm_le_insert (fderiv ℝ N y u) (fderiv ℝ N p u)
    have h2 := norm_le_insert (fderiv ℝ a y u) (fderiv ℝ a p u)
    have h3 := norm_le_insert (fderiv ℝ b y u) (fderiv ℝ b p u)
    have h7 : C₀ * ‖v‖ * ‖u‖ * 6 ≤ cΦ * ‖u‖ := by
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right hVc (norm_nonneg u)
    linarith only [h0, h1, h2, h3, dN' u, da' u, db' u, h7]
  have hinj' : ∀ u : E, fderiv ℝ N y u = 0 → fderiv ℝ a y u = 0 → fderiv ℝ b y u = 0 →
      u = 0 := by
    intro u h1 h2 h3
    have h0 := hinjy u
    rw [h1, h2, h3] at h0
    simp only [norm_zero, add_zero] at h0
    by_contra hu
    have h4 : 0 < cΦ / 2 * ‖u‖ := mul_pos (half_pos hcΦ) (norm_pos_iff.2 hu)
    linarith only [h0, h4]
  obtain ⟨w, hwN, hwa, hwb⟩ := surj y hinj' 0 (a y) (-b y)
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hρ0 : 0 < ‖a y‖ + ‖b y‖ := by
    rcases hab with h0 | h0
    · linarith only [norm_pos_iff.2 h0, norm_nonneg (b y)]
    · linarith only [norm_pos_iff.2 h0, norm_nonneg (a y)]
  have hwρ : ‖w‖ ≤ Cw * (‖a y‖ + ‖b y‖) := by
    have h0 := hinjy w
    rw [hwN, hwa, hwb, norm_zero, norm_neg, zero_add] at h0
    rw [hCw, div_mul_eq_mul_div, le_div_iff₀ hcΦ]
    linarith only [h0]
  have hvρ : ‖v‖ ≤ CT * (‖a y‖ + ‖b y‖) := hVT
  have hρε : ‖a y‖ + ‖b y‖ ≤ ε := by
    have hvv : C₀ * ‖v‖ ^ 2 ≤ C₀ * ‖v‖ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hv0 hv1) hC₀
    have h1 := norm_le_insert' (a y) (fderiv ℝ a p v)
    have h2 := norm_le_insert' (b y) (fderiv ℝ b p v)
    have h3 : ‖fderiv ℝ a p v‖ ≤ M * ‖v‖ := (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hMa' hv0)
    have h4 : ‖fderiv ℝ b p v‖ ≤ M * ‖v‖ := (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hMb' hv0)
    have h5 : ‖v‖ * (2 * (M + C₀)) ≤ r * (2 * (M + C₀)) :=
      mul_le_mul_of_nonneg_right hyr (by linarith only [hM0, hC₀])
    linarith only [h1, h2, h3, h4, h5, hvv, ta', tb', hrε]
  have wN : ‖fderiv ℝ N p w‖ ≤ C₀ * ‖v‖ * ‖w‖ := by
    have h0 := dN' w
    rwa [hwN, zero_sub, norm_neg] at h0
  have wa : ‖fderiv ℝ a p w - a y‖ ≤ C₀ * ‖v‖ * ‖w‖ := by
    have h0 := da' w
    rwa [hwa, norm_sub_rev] at h0
  have wb : ‖fderiv ℝ b p w + b y‖ ≤ C₀ * ‖v‖ * ‖w‖ := by
    have h0 := db' w
    rw [hwb] at h0
    have e : fderiv ℝ b p w + b y = -(-b y - fderiv ℝ b p w) := by abel
    rwa [e, norm_neg]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = C₀ * ‖v‖ ^ 2 + C₀ * ‖v‖ * ‖w‖ := ⟨_, rfl⟩
  have hδ1 : 0 ≤ C₀ * ‖v‖ ^ 2 := mul_nonneg hC₀ (sq_nonneg _)
  have hδ2 : 0 ≤ C₀ * ‖v‖ * ‖w‖ := mul_nonneg (mul_nonneg hC₀ hv0) hw0
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact add_nonneg hδ1 hδ2
  have hαN : ‖fderiv ℝ N p (v + w)‖ ≤ δ := by
    rw [map_add]
    have := norm_add_le (fderiv ℝ N p v) (fderiv ℝ N p w)
    linarith only [this, tN', wN, hδ]
  have hβN : ‖fderiv ℝ N p (v - w)‖ ≤ δ := by
    rw [map_sub]
    have := norm_sub_le (fderiv ℝ N p v) (fderiv ℝ N p w)
    linarith only [this, tN', wN, hδ]
  have hαb : ‖fderiv ℝ b p (v + w)‖ ≤ δ := by
    rw [map_add, ← sub_add_add_cancel (fderiv ℝ b p v) (fderiv ℝ b p w) (b y)]
    have := norm_add_le (fderiv ℝ b p v - b y) (fderiv ℝ b p w + b y)
    rw [norm_sub_rev] at this
    linarith only [this, tb', wb, hδ]
  have hβa : ‖fderiv ℝ a p (v - w)‖ ≤ δ := by
    rw [map_sub, ← sub_sub_sub_cancel_right (fderiv ℝ a p v) (fderiv ℝ a p w) (a y)]
    have := norm_sub_le (fderiv ℝ a p v - a y) (fderiv ℝ a p w - a y)
    rw [norm_sub_rev (fderiv ℝ a p v)] at this
    linarith only [this, ta', wa, hδ]
  obtain ⟨hαa, hαa'⟩ : ‖fderiv ℝ a p (v + w)‖ ≤ 2 * ‖a y‖ + δ ∧
      2 * ‖a y‖ - δ ≤ ‖fderiv ℝ a p (v + w)‖ := by
    rw [map_add]
    have h1 := norm_add_le (fderiv ℝ a p v) (fderiv ℝ a p w)
    have h2 := norm_le_insert' (fderiv ℝ a p v) (a y)
    rw [norm_sub_rev] at h2
    have h3 := norm_le_insert' (fderiv ℝ a p w) (a y)
    have h4 := norm_le_insert' (a y + a y) (fderiv ℝ a p v + fderiv ℝ a p w)
    rw [add_sub_add_comm] at h4
    have h5 := norm_add_le (a y - fderiv ℝ a p v) (a y - fderiv ℝ a p w)
    rw [norm_sub_rev (a y) (fderiv ℝ a p w)] at h5
    have h6 : ‖a y + a y‖ = 2 * ‖a y‖ := by
      rw [← two_smul ℝ (a y), norm_smul_of_nonneg zero_le_two]
    exact ⟨by linarith only [h1, h2, h3, ta', wa, hδ], by linarith only [h4, h5, h6, ta', wa, hδ]⟩
  obtain ⟨hβb, hβb'⟩ : ‖fderiv ℝ b p (v - w)‖ ≤ 2 * ‖b y‖ + δ ∧
      2 * ‖b y‖ - δ ≤ ‖fderiv ℝ b p (v - w)‖ := by
    rw [map_sub]
    have h1 := norm_sub_le (fderiv ℝ b p v) (fderiv ℝ b p w)
    have h2 := norm_le_insert' (fderiv ℝ b p v) (b y)
    rw [norm_sub_rev] at h2
    have h3 := norm_le_insert' (fderiv ℝ b p w) (-b y)
    rw [norm_neg, sub_neg_eq_add] at h3
    have h4 := norm_le_insert' (b y + b y) (fderiv ℝ b p v - fderiv ℝ b p w)
    have e : b y + b y - (fderiv ℝ b p v - fderiv ℝ b p w) =
        (b y - fderiv ℝ b p v) + (fderiv ℝ b p w + b y) := by abel
    rw [e] at h4
    have h5 := norm_add_le (b y - fderiv ℝ b p v) (fderiv ℝ b p w + b y)
    have h6 : ‖b y + b y‖ = 2 * ‖b y‖ := by
      rw [← two_smul ℝ (b y), norm_smul_of_nonneg zero_le_two]
    exact ⟨by linarith only [h1, h2, h3, tb', wb, hδ], by linarith only [h4, h5, h6, tb', wb, hδ]⟩
  have hαn : cΦ * ‖v + w‖ ≤ 2 * ‖a y‖ + 3 * δ := by
    have h0 : cΦ * ‖v + w‖ ≤ ‖fderiv ℝ N p (v + w)‖ + ‖fderiv ℝ a p (v + w)‖ +
      ‖fderiv ℝ b p (v + w)‖ := lbΦ' (v + w)
    linarith only [h0, hαN, hαa, hαb]
  have hβn : cΦ * ‖v - w‖ ≤ 2 * ‖b y‖ + 3 * δ := by
    have h0 : cΦ * ‖v - w‖ ≤ ‖fderiv ℝ N p (v - w)‖ + ‖fderiv ℝ a p (v - w)‖ +
      ‖fderiv ℝ b p (v - w)‖ := lbΦ' (v - w)
    linarith only [h0, hβN, hβa, hβb]
  have hQM : ∀ t : ℝ, 0 ≤ t → M * t ≤ Q * (cΦ * t) := by
    intro t ht
    rw [hQ, ← mul_assoc, div_mul_cancel₀ _ hcΦ.ne']
  have hQδ : 0 ≤ Q * δ := mul_nonneg hQ0 hδ0
  have hκδ : 0 ≤ (κ + 2) * δ := mul_nonneg (by linarith only [hκ]) hδ0
  have tαg : ‖fderiv ℝ g p (v + w)‖ / 2 ≤ Q * (‖a y‖ + 3 * δ) := by
    have h1 := ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hMg'
      (norm_nonneg _))).trans ((hQM _ (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hαn hQ0))
    linarith only [h1, hQδ]
  have tβh : ‖fderiv ℝ h p (v - w)‖ / 2 ≤ Q * (‖b y‖ + 3 * δ) := by
    have h1 := ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hMh'
      (norm_nonneg _))).trans ((hQM _ (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hβn hQ0))
    linarith only [h1, hQδ]
  have tβg : κ * ‖b y‖ - (κ + 2) * δ ≤ ‖fderiv ℝ g p (v - w)‖ / 2 := by
    have h0 : cG * ‖v - w‖ ≤ ‖fderiv ℝ N p (v - w)‖ + ‖fderiv ℝ a p (v - w)‖ +
      ‖fderiv ℝ g p (v - w)‖ := lbG' (v - w)
    have h1 : ‖fderiv ℝ b p (v - w)‖ ≤ M * ‖v - w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hMb' (norm_nonneg _))
    have h2 : κ * (2 * ‖b y‖ - δ) ≤ κ * (M * ‖v - w‖) :=
      mul_le_mul_of_nonneg_left (hβb'.trans h1) hκ.le
    have h3 : κ * M * ‖v - w‖ ≤ cG * ‖v - w‖ := mul_le_mul_of_nonneg_right hκG (norm_nonneg _)
    have h4 : κ * (M * ‖v - w‖) = κ * M * ‖v - w‖ := by ring
    linarith only [h0, h2, h3, h4, hβN, hβa, hκδ]
  have tαh : κ * ‖a y‖ - (κ + 2) * δ ≤ ‖fderiv ℝ h p (v + w)‖ / 2 := by
    have h0 : cH * ‖v + w‖ ≤ ‖fderiv ℝ N p (v + w)‖ + ‖fderiv ℝ b p (v + w)‖ +
      ‖fderiv ℝ h p (v + w)‖ := lbH' (v + w)
    have h1 : ‖fderiv ℝ a p (v + w)‖ ≤ M * ‖v + w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hMa' (norm_nonneg _))
    have h2 : κ * (2 * ‖a y‖ - δ) ≤ κ * (M * ‖v + w‖) :=
      mul_le_mul_of_nonneg_left (hαa'.trans h1) hκ.le
    have h3 : κ * M * ‖v + w‖ ≤ cH * ‖v + w‖ := mul_le_mul_of_nonneg_right hκH (norm_nonneg _)
    have h4 : κ * (M * ‖v + w‖) = κ * M * ‖v + w‖ := by ring
    linarith only [h0, h2, h3, h4, hαN, hαb, hκδ]
  have tαg0 : 0 ≤ ‖fderiv ℝ g p (v + w)‖ / 2 := div_nonneg (norm_nonneg _) zero_le_two
  have tβg0 : 0 ≤ ‖fderiv ℝ g p (v - w)‖ / 2 := div_nonneg (norm_nonneg _) zero_le_two
  have tαh0 : 0 ≤ ‖fderiv ℝ h p (v + w)‖ / 2 := div_nonneg (norm_nonneg _) zero_le_two
  have tβh0 : 0 ≤ ‖fderiv ℝ h p (v - w)‖ / 2 := div_nonneg (norm_nonneg _) zero_le_two
  obtain ⟨err, herr⟩ : ∃ err : ℝ, err = M * ‖v‖ * (C₀ * ‖v‖ * ‖w‖) +
      C₀ * ‖v‖ ^ 2 * (M * ‖w‖) + C₀ * ‖v‖ ^ 2 * (C₀ * ‖v‖ * ‖w‖) := ⟨_, rfl⟩
  have hρ1 : ‖a y‖ + ‖b y‖ ≤ 1 := hρε.trans hε1
  have herrE : err ≤ Ee * (‖a y‖ + ‖b y‖) ^ 3 := by
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ‖a y‖ + ‖b y‖ := ⟨_, rfl⟩
    rw [← hρ] at hρ1 hwρ hvρ hρ0 ⊢
    have h1 : ‖v‖ ^ 2 * ‖w‖ ≤ (CT * ρ) ^ 2 * (Cw * ρ) :=
      mul_le_mul (pow_le_pow_left₀ hv0 hvρ 2) hwρ hw0 (sq_nonneg _)
    have h2 : ‖v‖ ^ 3 * ‖w‖ ≤ (CT * ρ) ^ 3 * (Cw * ρ) :=
      mul_le_mul (pow_le_pow_left₀ hv0 hvρ 3) hwρ hw0 (pow_nonneg (mul_nonneg hCT hρ0.le) 3)
    have h3 : ρ ^ 4 ≤ ρ ^ 3 := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hρ0.le 3) hρ1
    have h4 : C₀ ^ 2 * CT ^ 3 * Cw * ρ ^ 4 ≤ C₀ ^ 2 * CT ^ 3 * Cw * ρ ^ 3 :=
      mul_le_mul_of_nonneg_left h3
        (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hCT 3)) hCw0)
    have h5 : 2 * M * C₀ * (‖v‖ ^ 2 * ‖w‖) ≤ 2 * M * C₀ * ((CT * ρ) ^ 2 * (Cw * ρ)) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg zero_le_two hM0) hC₀)
    have h6 : C₀ ^ 2 * (‖v‖ ^ 3 * ‖w‖) ≤ C₀ ^ 2 * ((CT * ρ) ^ 3 * (Cw * ρ)) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have e1 : err = 2 * M * C₀ * (‖v‖ ^ 2 * ‖w‖) + C₀ ^ 2 * (‖v‖ ^ 3 * ‖w‖) := by
      rw [herr]; ring
    have e2 : 2 * M * C₀ * ((CT * ρ) ^ 2 * (Cw * ρ)) + C₀ ^ 2 * ((CT * ρ) ^ 3 * (Cw * ρ)) =
        (2 * M * C₀ * CT ^ 2 * Cw) * ρ ^ 3 + C₀ ^ 2 * CT ^ 3 * Cw * ρ ^ 4 := by ring
    have e3 : Ee * ρ ^ 3 = (2 * M * C₀ * CT ^ 2 * Cw) * ρ ^ 3 + C₀ ^ 2 * CT ^ 3 * Cw * ρ ^ 3 := by
      rw [hEe]; ring
    linarith only [h4, h5, h6, e1, e2, e3]
  have hδD : δ ≤ D * (‖a y‖ + ‖b y‖) ^ 2 := by
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ‖a y‖ + ‖b y‖ := ⟨_, rfl⟩
    rw [← hρ] at hwρ hvρ hρ0 ⊢
    have h1 : ‖v‖ ^ 2 ≤ (CT * ρ) ^ 2 := pow_le_pow_left₀ hv0 hvρ 2
    have h2 : ‖v‖ * ‖w‖ ≤ (CT * ρ) * (Cw * ρ) := mul_le_mul hvρ hwρ hw0 (mul_nonneg hCT hρ0.le)
    have h3 : C₀ * ‖v‖ ^ 2 ≤ C₀ * (CT * ρ) ^ 2 := mul_le_mul_of_nonneg_left h1 hC₀
    have h4 : C₀ * (‖v‖ * ‖w‖) ≤ C₀ * ((CT * ρ) * (Cw * ρ)) := mul_le_mul_of_nonneg_left h2 hC₀
    have e1 : D * ρ ^ 2 = C₀ * (CT * ρ) ^ 2 + C₀ * ((CT * ρ) * (Cw * ρ)) := by rw [hD]; ring
    have e2 : C₀ * ‖v‖ * ‖w‖ = C₀ * (‖v‖ * ‖w‖) := by ring
    linarith only [h3, h4, e1, e2, hδ]
  obtain ⟨e, he1, he2, he3⟩ := surj p hΦp 1 0 0
  have hen : cΦ * ‖e‖ ≤ 1 := by
    have h0 : cΦ * ‖e‖ ≤ ‖fderiv ℝ N p e‖ + ‖fderiv ℝ a p e‖ + ‖fderiv ℝ b p e‖ := lbΦ' e
    rw [he1, he2, he3] at h0
    simpa using h0
  have hAw : ∀ A' : E → ℝ, (∀ u : E, fderiv ℝ N p u = 0 → fderiv ℝ A' p u = 0) →
      ‖fderiv ℝ A' p‖ ≤ M → (∀ u : E, ‖fderiv ℝ A' y u - fderiv ℝ A' p u‖ ≤ C₀ * ‖v‖ * ‖u‖) →
      |fderiv ℝ A' y w| ≤ Gc * (‖a y‖ + ‖b y‖) ^ 2 := by
    intro A' hker hM' hd
    have h1 : fderiv ℝ N p (w - fderiv ℝ N p w • e) = 0 := by
      rw [map_sub, map_smul, he1, smul_eq_mul, mul_one, sub_self]
    have h2 := hker _ h1
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h2
    have h3 : ‖fderiv ℝ A' p e‖ * cΦ ≤ M := by
      have h4 : ‖fderiv ℝ A' p e‖ ≤ M * ‖e‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hM' (norm_nonneg _))
      have h5 : M * ‖e‖ * cΦ ≤ M * 1 := by
        rw [mul_assoc, mul_comm ‖e‖]
        exact mul_le_mul_of_nonneg_left hen hM0
      have h6 := mul_le_mul_of_nonneg_right h4 hcΦ.le
      linarith only [h5, h6]
    have h7 : ‖fderiv ℝ A' p w‖ * cΦ ≤ M * (C₀ * ‖v‖ * ‖w‖) := by
      rw [h2, norm_mul, mul_assoc, mul_comm]
      exact mul_le_mul h3 wN (norm_nonneg _) hM0
    have h8 : ‖fderiv ℝ A' p w‖ ≤ M / cΦ * (C₀ * ‖v‖ * ‖w‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hcΦ]
      exact h7
    have h9 := norm_le_insert' (fderiv ℝ A' y w) (fderiv ℝ A' p w)
    rw [← Real.norm_eq_abs]
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ‖a y‖ + ‖b y‖ := ⟨_, rfl⟩
    rw [← hρ] at hwρ hvρ hρ0 ⊢
    have h10 : ‖v‖ * ‖w‖ ≤ (CT * ρ) * (Cw * ρ) := mul_le_mul hvρ hwρ hw0 (mul_nonneg hCT hρ0.le)
    have h11 : C₀ * (1 + M / cΦ) * (‖v‖ * ‖w‖) ≤ C₀ * (1 + M / cΦ) * ((CT * ρ) * (Cw * ρ)) :=
      mul_le_mul_of_nonneg_left h10 (mul_nonneg hC₀ (add_nonneg zero_le_one (div_nonneg hM0 hcΦ.le)))
    have e1 : Gc * ρ ^ 2 = C₀ * (1 + M / cΦ) * ((CT * ρ) * (Cw * ρ)) := by rw [hGc]; ring
    have e2 : M / cΦ * (C₀ * ‖v‖ * ‖w‖) + C₀ * ‖v‖ * ‖w‖ =
        C₀ * (1 + M / cΦ) * (‖v‖ * ‖w‖) := by ring
    linarith only [h8, h9, hd w, h11, e1, e2]
  have hA₁w := hAw A₁ (fun u hu => (hAp u hu).1) hM₁' d₁'
  have hA₂w := hAw A₂ (fun u hu => (hAp u hu).2) hM₂' d₂'
  have hgvM : ‖fderiv ℝ g p v‖ ≤ M * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hMg' hv0)
  have hgwM : ‖fderiv ℝ g p w‖ ≤ M * ‖w‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hMg' hw0)
  have hhvM : ‖fderiv ℝ h p v‖ ≤ M * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hMh' hv0)
  have hhwM : ‖fderiv ℝ h p w‖ ≤ M * ‖w‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hMh' hw0)
  have ig : ⟪g y, fderiv ℝ g y w⟫ ≤
      (‖fderiv ℝ g p (v + w)‖ / 2) ^ 2 - (‖fderiv ℝ g p (v - w)‖ / 2) ^ 2 + err := by
    obtain ⟨e1, he1⟩ : ∃ e1 : F, e1 = g y - fderiv ℝ g p v := ⟨_, rfl⟩
    obtain ⟨e2, he2⟩ : ∃ e2 : F, e2 = fderiv ℝ g y w - fderiv ℝ g p w := ⟨_, rfl⟩
    have hgy : g y = fderiv ℝ g p v + e1 := by rw [he1]; abel
    have hgw : fderiv ℝ g y w = fderiv ℝ g p w + e2 := by rw [he2]; abel
    have n1 : ‖e1‖ ≤ C₀ * ‖v‖ ^ 2 := he1 ▸ tg'
    have n2 : ‖e2‖ ≤ C₀ * ‖v‖ * ‖w‖ := he2 ▸ dg' w
    have i0 : ⟪fderiv ℝ g p v, fderiv ℝ g p w⟫ =
        (‖fderiv ℝ g p (v + w)‖ / 2) ^ 2 - (‖fderiv ℝ g p (v - w)‖ / 2) ^ 2 := by
      rw [map_add, map_sub]
      have j1 := norm_add_sq_real (fderiv ℝ g p v) (fderiv ℝ g p w)
      have j2 := norm_sub_sq_real (fderiv ℝ g p v) (fderiv ℝ g p w)
      linarith only [j1, j2]
    have i1 := (real_inner_le_norm (fderiv ℝ g p v) e2).trans
      (mul_le_mul hgvM n2 (norm_nonneg _) (mul_nonneg hM0 hv0))
    have i2 := (real_inner_le_norm e1 (fderiv ℝ g p w)).trans
      (mul_le_mul n1 hgwM (norm_nonneg _) hδ1)
    have i3 := (real_inner_le_norm e1 e2).trans (mul_le_mul n1 n2 (norm_nonneg _) hδ1)
    rw [hgy, hgw, inner_add_left, inner_add_right, inner_add_right]
    linarith only [i0, i1, i2, i3, herr]
  have ih : (‖fderiv ℝ h p (v + w)‖ / 2) ^ 2 - (‖fderiv ℝ h p (v - w)‖ / 2) ^ 2 - err ≤
      ⟪h y, fderiv ℝ h y w⟫ := by
    obtain ⟨e1, he1⟩ : ∃ e1 : G, e1 = h y - fderiv ℝ h p v := ⟨_, rfl⟩
    obtain ⟨e2, he2⟩ : ∃ e2 : G, e2 = fderiv ℝ h y w - fderiv ℝ h p w := ⟨_, rfl⟩
    have hhy : h y = fderiv ℝ h p v + e1 := by rw [he1]; abel
    have hhw : fderiv ℝ h y w = fderiv ℝ h p w + e2 := by rw [he2]; abel
    have n1 : ‖e1‖ ≤ C₀ * ‖v‖ ^ 2 := he1 ▸ th'
    have n2 : ‖e2‖ ≤ C₀ * ‖v‖ * ‖w‖ := he2 ▸ dh' w
    have i0 : ⟪fderiv ℝ h p v, fderiv ℝ h p w⟫ =
        (‖fderiv ℝ h p (v + w)‖ / 2) ^ 2 - (‖fderiv ℝ h p (v - w)‖ / 2) ^ 2 := by
      rw [map_add, map_sub]
      have j1 := norm_add_sq_real (fderiv ℝ h p v) (fderiv ℝ h p w)
      have j2 := norm_sub_sq_real (fderiv ℝ h p v) (fderiv ℝ h p w)
      linarith only [j1, j2]
    have i1 := (abs_real_inner_le_norm (fderiv ℝ h p v) e2).trans
      (mul_le_mul hhvM n2 (norm_nonneg _) (mul_nonneg hM0 hv0))
    have i2 := (abs_real_inner_le_norm e1 (fderiv ℝ h p w)).trans
      (mul_le_mul n1 hhwM (norm_nonneg _) hδ1)
    have i3 := (abs_real_inner_le_norm e1 e2).trans (mul_le_mul n1 n2 (norm_nonneg _) hδ1)
    rw [hhy, hhw, inner_add_left, inner_add_right, inner_add_right]
    linarith only [i0, i1, i2, i3, herr, neg_abs_le ⟪fderiv ℝ h p v, e2⟫,
      neg_abs_le ⟪e1, fderiv ℝ h p w⟫, neg_abs_le ⟪e1, e2⟫]
  have hyn : W ∈ 𝓝 y := hW.mem_nhds hyW
  have h20 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have dfa : DifferentiableAt ℝ a y := (ha.differentiableOn h20).differentiableAt hyn
  have dfb : DifferentiableAt ℝ b y := (hb.differentiableOn h20).differentiableAt hyn
  have dfg : DifferentiableAt ℝ g y := (hg.differentiableOn h20).differentiableAt hyn
  have dfh : DifferentiableAt ℝ h y := (hh.differentiableOn h20).differentiableAt hyn
  have df₁ : DifferentiableAt ℝ A₁ y := (hA₁.differentiableOn h20).differentiableAt hyn
  have df₂ : DifferentiableAt ℝ A₂ y := (hA₂.differentiableOn h20).differentiableAt hyn
  have hd₁ : HasFDerivAt (fun z => ‖a z‖ ^ 2 - η * ‖g z‖ ^ 2 + μ * A₁ z) _ y :=
    (dfa.hasFDerivAt.norm_sq.sub (dfg.hasFDerivAt.norm_sq.const_mul η)).add
      (df₁.hasFDerivAt.const_mul μ)
  have hd₂ : HasFDerivAt (fun z => η * ‖h z‖ ^ 2 - ‖b z‖ ^ 2 + μ * A₂ z) _ y :=
    ((dfh.hasFDerivAt.norm_sq.const_mul η).sub dfb.hasFDerivAt.norm_sq).add
      (df₂.hasFDerivAt.const_mul μ)
  refine ⟨w, hwN, ?_, ?_⟩
  · rw [hd₁.fderiv]
    simp only [add_apply, sub_apply,
      smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, hwa, real_inner_self_eq_norm_sq]
    have K := key η Q κ D Ee Gc H m ε μ₀ ‖a y‖ ‖b y‖ δ _ _ err _ _ μ hη0 hηQ hκ hD0 hGc0 hH0 hH hm0
      hm1 hmκ hε1 hεH hμ₀G (norm_nonneg _) (norm_nonneg _) hρ0 hρε hδ0 hδD tαg0 tαg tβg0 tβg
      herrE hA₁w ig hμ0 hμ1
    linarith only [K]
  · rw [hd₂.fderiv]
    simp only [add_apply, sub_apply,
      smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, hwb, inner_neg_right,
      real_inner_self_eq_norm_sq]
    have hρ0' : 0 < ‖b y‖ + ‖a y‖ := by rwa [add_comm]
    have hρε' : ‖b y‖ + ‖a y‖ ≤ ε := by rwa [add_comm]
    have hδD' : δ ≤ D * (‖b y‖ + ‖a y‖) ^ 2 := by rwa [add_comm (‖b y‖)]
    have herrE' : err ≤ Ee * (‖b y‖ + ‖a y‖) ^ 3 := by rwa [add_comm (‖b y‖)]
    have hA₂w' : |fderiv ℝ A₂ y w| ≤ Gc * (‖b y‖ + ‖a y‖) ^ 2 := by rwa [add_comm (‖b y‖)]
    have ih' : -⟪h y, fderiv ℝ h y w⟫ ≤ (‖fderiv ℝ h p (v - w)‖ / 2) ^ 2 -
        (‖fderiv ℝ h p (v + w)‖ / 2) ^ 2 + err := by linarith only [ih]
    have K := key η Q κ D Ee Gc H m ε μ₀ ‖b y‖ ‖a y‖ δ _ _ err _ _ μ hη0 hηQ hκ hD0 hGc0 hH0 hH hm0
      hm1 hmκ hε1 hεH hμ₀G (norm_nonneg _) (norm_nonneg _) hρ0' hρε' hδ0 hδD' tβh0 tβh tαh0 tαh
      herrE' hA₂w' ih' hμ0 hμ1
    linarith only [K]

end BandAnalysis

end CrossField

end

end DifferentialGeometry.Topology
