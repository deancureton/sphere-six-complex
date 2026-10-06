module

public import DifferentialGeometry.Topology.Morse.Strip.Foundations.RelativePerturbation
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter

namespace MonotoneShift

section Shift

theorem contDiff_iterate {n : WithTop ℕ∞} {T : ℝ → ℝ} (hT : ContDiff ℝ n T) :
    ∀ k : ℕ, ContDiff ℝ n T^[k]
  | 0 => by simpa using contDiff_id
  | k + 1 => by
    rw [Function.iterate_succ']
    exact hT.comp (contDiff_iterate hT k)

theorem exists_pos_hasDerivAt_iterate {T : ℝ → ℝ} {T' : ℝ → ℝ}
    (hT : ∀ t, HasDerivAt T (T' t) t) (hpos : ∀ t, 0 < T' t) :
    ∀ (k : ℕ) (t : ℝ), ∃ d, 0 < d ∧ HasDerivAt T^[k] d t
  | 0, t => ⟨1, one_pos, by simpa using hasDerivAt_id t⟩
  | k + 1, t => by
    obtain ⟨d, hd, hdiff⟩ := exists_pos_hasDerivAt_iterate hT hpos k t
    refine ⟨T' (T^[k] t) * d, mul_pos (hpos _) hd, ?_⟩
    rw [Function.iterate_succ']
    exact (hT (T^[k] t)).comp t hdiff

theorem exists_monotoneShift {c₀ x₀ y₀ c₁ : ℝ} (hx : x₀ ∈ Ioo c₀ c₁) (hy : y₀ ∈ Ioo c₀ c₁) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ t, 0 < deriv ρ t) ∧ StrictMono ρ ∧
      (∀ t, t ∉ Ioo c₀ c₁ → ρ t = t) ∧ MapsTo ρ (Ioo c₀ c₁) (Ioo c₀ c₁) ∧ ρ x₀ = y₀ ∧
      (∀ᶠ t in 𝓝 x₀, ρ t = t + (y₀ - x₀)) := by
  set lo := min x₀ y₀ with hlo
  set hi := max x₀ y₀ with hhi
  have hlo_x : lo ≤ x₀ := min_le_left _ _
  have hlo_y : lo ≤ y₀ := min_le_right _ _
  have hx_hi : x₀ ≤ hi := le_max_left _ _
  have hy_hi : y₀ ≤ hi := le_max_right _ _
  have hlo_c : c₀ < lo := lt_min hx.1 hy.1
  have hhi_c : hi < c₁ := max_lt hx.2 hy.2
  set δ := min (lo - c₀) (c₁ - hi) / 3 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    have : 0 < min (lo - c₀) (c₁ - hi) := lt_min (by linarith) (by linarith)
    linarith
  have hδlo : 3 * δ ≤ lo - c₀ := by
    rw [hδ]; have := min_le_left (lo - c₀) (c₁ - hi); linarith
  have hδhi : 3 * δ ≤ c₁ - hi := by
    rw [hδ]; have := min_le_right (lo - c₀) (c₁ - hi); linarith
  set m := (lo + hi) / 2 with hm
  set r := (hi - lo) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  let b : ContDiffBump m := ⟨r + δ, r + 2 * δ, by linarith, by linarith⟩
  have hb_one : ∀ t, lo - δ ≤ t → t ≤ hi + δ → b t = 1 := by
    intro t h1 h2
    apply b.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    constructor
    · change m - (r + δ) ≤ t
      rw [hm, hr]; linarith
    · change t ≤ m + (r + δ)
      rw [hm, hr]; linarith
  have hb_zero : ∀ t, t ∉ Ioo c₀ c₁ → b t = 0 := by
    intro t ht
    apply b.zero_of_le_dist
    change r + 2 * δ ≤ dist t m
    rw [Real.dist_eq]
    by_contra hcon
    rw [not_le, abs_lt] at hcon
    apply ht
    constructor
    · rw [hm, hr] at hcon; linarith [hcon.1]
    · rw [hm, hr] at hcon; linarith [hcon.2]
  have hb_smooth : ContDiff ℝ ∞ b := b.contDiff
  have hb_diff : ∀ t, HasDerivAt b (deriv b t) t := fun t =>
    ((hb_smooth.differentiable (by simp)) t).hasDerivAt
  obtain ⟨C, hC⟩ := (hb_smooth.continuous_deriv (by simp)).bounded_above_of_compact_support
    b.hasCompactSupport.deriv
  obtain ⟨k, hk⟩ := exists_nat_gt (max (|y₀ - x₀| * C) 0)
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hkC : |y₀ - x₀| * C < k := lt_of_le_of_lt (le_max_left _ _) hk
  set s := (y₀ - x₀) / k with hs
  have hks : (k : ℝ) * s = y₀ - x₀ := by rw [hs]; field_simp
  set T : ℝ → ℝ := fun t => t + s * b t with hT
  have hT_deriv : ∀ t, HasDerivAt T (1 + s * deriv b t) t := fun t =>
    (hasDerivAt_id t).add ((hb_diff t).const_mul s)
  have hT_pos : ∀ t, 0 < 1 + s * deriv b t := by
    intro t
    have h1 : |s * deriv b t| < 1 := by
      rw [abs_mul, hs, abs_div, abs_of_pos hkpos, div_mul_eq_mul_div, div_lt_one hkpos]
      calc |y₀ - x₀| * |deriv b t| ≤ |y₀ - x₀| * C :=
            mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC t) (abs_nonneg _)
        _ < k := hkC
    have := (abs_lt.1 h1).1
    linarith
  have hT_smooth : ContDiff ℝ ∞ T := contDiff_id.add (contDiff_const.mul hb_smooth)
  have hT_id : ∀ t, t ∉ Ioo c₀ c₁ → T t = t := by
    intro t ht
    simp [hT, hb_zero t ht]
  have hplateau : ∀ j : ℕ, j ≤ k → lo ≤ x₀ + j * s ∧ x₀ + j * s ≤ hi := by
    intro j hj
    have hθ0 : 0 ≤ (j : ℝ) / k := div_nonneg (Nat.cast_nonneg j) hkpos.le
    have hθ1 : (j : ℝ) / k ≤ 1 := by
      rw [div_le_one hkpos]; exact_mod_cast hj
    have hjs : (j : ℝ) * s = (j / k) * (y₀ - x₀) := by rw [hs]; ring
    rw [hjs]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hlo_x),
        mul_nonneg hθ0 (sub_nonneg.2 hlo_y)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hx_hi),
        mul_nonneg hθ0 (sub_nonneg.2 hy_hi)]
  have hstep : ∀ t ∈ Metric.ball x₀ δ, ∀ j : ℕ, j ≤ k → T^[j] t = t + j * s := by
    intro t ht j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hj' : j ≤ k := Nat.le_of_succ_le hj
      rw [Function.iterate_succ_apply', ih hj']
      have hb1 : b (t + j * s) = 1 := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
        obtain ⟨h1, h2⟩ := hplateau j hj'
        exact hb_one _ (by linarith) (by linarith)
      simp only [hT, hb1, mul_one, Nat.cast_succ]
      ring
  refine ⟨T^[k], contDiff_iterate hT_smooth k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨d, hd, hdiff⟩ := exists_pos_hasDerivAt_iterate hT_deriv hT_pos k t
    rw [hdiff.deriv]; exact hd
  · exact strictMono_of_deriv_pos (fun t => by
      obtain ⟨d, hd, hdiff⟩ := exists_pos_hasDerivAt_iterate hT_deriv hT_pos k t
      rw [hdiff.deriv]; exact hd)
  · intro t ht
    exact Function.iterate_fixed (hT_id t ht) k
  · have hmono : StrictMono T^[k] := strictMono_of_deriv_pos (fun t => by
      obtain ⟨d, hd, hdiff⟩ := exists_pos_hasDerivAt_iterate hT_deriv hT_pos k t
      rw [hdiff.deriv]; exact hd)
    intro t ht
    have h0 : T^[k] c₀ = c₀ := Function.iterate_fixed (hT_id c₀ (by simp)) k
    have h1 : T^[k] c₁ = c₁ := Function.iterate_fixed (hT_id c₁ (by simp)) k
    exact ⟨h0 ▸ hmono ht.1, h1 ▸ hmono ht.2⟩
  · exact hstep x₀ (Metric.mem_ball_self hδpos) k le_rfl |>.trans (by rw [hks]; ring)
  · filter_upwards [Metric.ball_mem_nhds x₀ hδpos] with t ht
    rw [hstep t ht k le_rfl, hks]

end Shift

section Affine

theorem contDiff_affineComb {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (m : ℝ) :
    ContDiff ℝ ∞ (fun t => t + m * (ρ t - t)) :=
  contDiff_id.add (contDiff_const.mul (hρ.sub contDiff_id))

theorem hasDerivAt_affineComb {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (m t : ℝ) :
    HasDerivAt (fun t => t + m * (ρ t - t)) (1 + m * (deriv ρ t - 1)) t :=
  (hasDerivAt_id t).add
    (((hρ.differentiable (by simp) t).hasDerivAt.sub (hasDerivAt_id t)).const_mul m)

theorem deriv_affineComb {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (m t : ℝ) :
    deriv (fun t => t + m * (ρ t - t)) t = 1 + m * (deriv ρ t - 1) :=
  (hasDerivAt_affineComb hρ m t).deriv

theorem affineComb_deriv_pos {m d : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hd : 0 < d) :
    0 < 1 + m * (d - 1) := by
  rcases hm0.eq_or_lt with rfl | hm
  · simp
  · nlinarith [mul_pos hm hd]

end Affine

section Signature

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem negDef_restrict_smul_iff (Q : QuadraticForm ℝ V) {c : ℝ} (hc : 0 < c)
    (W : Submodule ℝ V) :
    ((-(c • Q)).restrict W).PosDef ↔ ((-Q).restrict W).PosDef := by
  constructor
  · intro h x hx
    have := h x hx
    simp only [QuadraticMap.restrict_apply, neg_apply, smul_apply, smul_eq_mul] at this ⊢
    nlinarith
  · intro h x hx
    have := h x hx
    simp only [QuadraticMap.restrict_apply, neg_apply, smul_apply, smul_eq_mul] at this ⊢
    nlinarith

theorem sigNeg_smul_of_pos [Module.Finite ℝ V] (Q : QuadraticForm ℝ V) {c : ℝ} (hc : 0 < c) :
    sigNeg (c • Q) = sigNeg Q := by
  have hset : {r | ∃ W : Submodule ℝ V, Module.finrank ℝ W = r ∧ ((-(c • Q)).restrict W).PosDef}
      = {r | ∃ W : Submodule ℝ V, Module.finrank ℝ W = r ∧ ((-Q).restrict W).PosDef} := by
    ext r
    simp only [mem_ofPred_eq, negDef_restrict_smul_iff Q hc]
  have h1 := sigNeg_isGreatest (c • Q)
  rw [hset] at h1
  exact h1.unique (sigNeg_isGreatest Q)

theorem associated_smul_apply (Q : QuadraticForm ℝ V) (c : ℝ) (u v : V) :
    QuadraticMap.associated (R := ℝ) (c • Q) u v = c * QuadraticMap.associated (R := ℝ) Q u v := by
  rw [map_smul]
  rfl

theorem separatingLeft_associated_smul_iff (Q : QuadraticForm ℝ V) {c : ℝ} (hc : c ≠ 0) :
    (QuadraticMap.associated (R := ℝ) (c • Q)).SeparatingLeft ↔
      (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft := by
  simp only [LinearMap.SeparatingLeft, associated_smul_apply, mul_eq_zero, hc, false_or]

end Signature

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chartHessianAt_apply (g : E → ℝ) (x v : E) :
    DifferentialGeometry.Topology.Morse.chartHessianAt g x v = fderiv ℝ (fderiv ℝ g) x v v := rfl

theorem chartHessianAt_eq_of_fderiv_fderiv_eq {g₁ g₂ : E → ℝ} {x : E}
    (h : fderiv ℝ (fderiv ℝ g₁) x = fderiv ℝ (fderiv ℝ g₂) x) :
    DifferentialGeometry.Topology.Morse.chartHessianAt g₁ x = DifferentialGeometry.Topology.Morse.chartHessianAt g₂ x := by
  unfold DifferentialGeometry.Topology.Morse.chartHessianAt DifferentialGeometry.Topology.Morse.chartHessianBilinAt
  simp only [h]

theorem chartHessianAt_add_const (g : E → ℝ) (x : E) (c : ℝ) :
    DifferentialGeometry.Topology.Morse.chartHessianAt (fun y => g y + c) x = DifferentialGeometry.Topology.Morse.chartHessianAt g x := by
  apply chartHessianAt_eq_of_fderiv_fderiv_eq
  have : fderiv ℝ (fun y => g y + c) = fderiv ℝ g := funext fun _ => fderiv_add_const c
  rw [this]

theorem chartHessianAt_const (x : E) (c : ℝ) : DifferentialGeometry.Topology.Morse.chartHessianAt (fun _ : E => c) x = 0 := by
  ext v
  rw [chartHessianAt_apply]
  have : fderiv ℝ (fun _ : E => c) = fun _ => 0 := funext fun _ => fderiv_const_apply c
  simp [this]

theorem hasFDerivAt_fderiv_of_contDiffAt {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
  ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt

theorem eventually_differentiableAt_of_contDiffAt {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
  (hg.eventually MorseExistence.two_ne_infty).mono fun _ hy => hy.differentiableAt (by norm_num)

theorem chartHessianAt_add {g h : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x)
    (hh : ContDiffAt ℝ 2 h x) :
    DifferentialGeometry.Topology.Morse.chartHessianAt (fun y => g y + h y) x = DifferentialGeometry.Topology.Morse.chartHessianAt g x + DifferentialGeometry.Topology.Morse.chartHessianAt h x := by
  have hfd : fderiv ℝ (fun y => g y + h y) =ᶠ[𝓝 x] fun y => fderiv ℝ g y + fderiv ℝ h y := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hg,
      eventually_differentiableAt_of_contDiffAt hh] with y hgy hhy
    exact fderiv_add hgy hhy
  have hsum : HasFDerivAt (fun y => fderiv ℝ g y + fderiv ℝ h y)
      (fderiv ℝ (fderiv ℝ g) x + fderiv ℝ (fderiv ℝ h) x) x :=
    (hasFDerivAt_fderiv_of_contDiffAt hg).add (hasFDerivAt_fderiv_of_contDiffAt hh)
  ext v
  rw [add_apply, chartHessianAt_apply, chartHessianAt_apply, chartHessianAt_apply, hfd.fderiv_eq,
    hsum.fderiv]
  simp

theorem chartHessianAt_const_mul {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) (c : ℝ) :
    DifferentialGeometry.Topology.Morse.chartHessianAt (fun y => c * g y) x = c • DifferentialGeometry.Topology.Morse.chartHessianAt g x := by
  have hfd : fderiv ℝ (fun y => c * g y) =ᶠ[𝓝 x] fun y => c • fderiv ℝ g y := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hg] with y hgy
    exact fderiv_const_mul hgy c
  have hsm : HasFDerivAt (fun y => c • fderiv ℝ g y) (c • fderiv ℝ (fderiv ℝ g) x) x :=
    (hasFDerivAt_fderiv_of_contDiffAt hg).const_smul c
  ext v
  rw [smul_apply, chartHessianAt_apply, chartHessianAt_apply, hfd.fderiv_eq, hsm.fderiv]
  simp

theorem chartHessianAt_sub {g h : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x)
    (hh : ContDiffAt ℝ 2 h x) :
    DifferentialGeometry.Topology.Morse.chartHessianAt (fun y => g y - h y) x = DifferentialGeometry.Topology.Morse.chartHessianAt g x - DifferentialGeometry.Topology.Morse.chartHessianAt h x := by
  have h1 : (fun y => g y - h y) = fun y => g y + (-1 : ℝ) * h y := by
    funext y; ring
  rw [h1, chartHessianAt_add hg (contDiffAt_const.mul hh), chartHessianAt_const_mul hh]
  ext v
  simp [sub_eq_add_neg]

theorem chartHessianAt_comp_of_fderiv_eq_zero {g : E → ℝ} {ρ : ℝ → ℝ} {x : E}
    (hg : ContDiffAt ℝ 2 g x) (hρ : ContDiffAt ℝ 2 ρ (g x)) (h0 : fderiv ℝ g x = 0) :
    DifferentialGeometry.Topology.Morse.chartHessianAt (ρ ∘ g) x = deriv ρ (g x) • DifferentialGeometry.Topology.Morse.chartHessianAt g x := by
  have hρev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ρ (g y) :=
    (hg.continuousAt.tendsto.eventually (hρ.eventually MorseExistence.two_ne_infty)).mono
      fun _ hy => hy.differentiableAt (by norm_num)
  have hfd : fderiv ℝ (ρ ∘ g) =ᶠ[𝓝 x] fun y => (fderiv ℝ ρ (g y)).comp (fderiv ℝ g y) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hg, hρev] with y hgy hρy
    exact fderiv_comp y hρy hgy
  have hc : HasFDerivAt (fun y => fderiv ℝ ρ (g y))
      ((fderiv ℝ (fderiv ℝ ρ) (g x)).comp (fderiv ℝ g x)) x :=
    (hasFDerivAt_fderiv_of_contDiffAt hρ).comp x (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd := hasFDerivAt_fderiv_of_contDiffAt hg
  have hcomp := hc.clm_comp hd
  ext v
  rw [smul_apply, chartHessianAt_apply, chartHessianAt_apply, hfd.fderiv_eq, hcomp.fderiv]
  simp [h0, fderiv_eq_smul_deriv, mul_comm]

end Hessian

section Congr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}

theorem isCriticalPointAt_congr_nhds {g₁ g₂ : M → ℝ} {p : M} (h : g₁ =ᶠ[𝓝 p] g₂) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₁ p ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ p := by
  unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt
  rw [h.mfderiv_eq]
  constructor
  · intro h1
    ext v
    exact DFunLike.congr_fun h1 v
  · intro h2
    rw [h2, ContinuousLinearMap.comp_zero]

theorem hessianAt_congr_nhds {g₁ g₂ : M → ℝ} {p : M} (h : g₁ =ᶠ[𝓝 p] g₂) :
    hessianAt I g₁ p = hessianAt I g₂ p := by
  apply MorseExistence.chartHessianAt_congr
  have ht : Tendsto (extChartAt I p).symm (𝓝 (extChartAt I p p)) (𝓝 p) := by
    have := (continuousAt_extChartAt_symm (I := I) p).tendsto
    rwa [extChartAt_to_inv] at this
  exact ht.eventually h

theorem isNondegenerateCriticalPointAt_congr_nhds {g₁ g₂ : M → ℝ} {p : M} (h : g₁ =ᶠ[𝓝 p] g₂) :
    DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g₁ p ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g₂ p := by
  change (Morse.IsCriticalPointAt I g₁ p ∧
    (QuadraticMap.associated (R := ℝ) (hessianAt I g₁ p)).SeparatingLeft) ↔
    (Morse.IsCriticalPointAt I g₂ p ∧
      (QuadraticMap.associated (R := ℝ) (hessianAt I g₂ p)).SeparatingLeft)
  rw [isCriticalPointAt_congr_nhds h, hessianAt_congr_nhds h]

theorem morseIndex_congr_nhds {g₁ g₂ : M → ℝ} {p : M} (h : g₁ =ᶠ[𝓝 p] g₂) :
    morseIndex I g₁ p = morseIndex I g₂ p := by
  unfold morseIndex
  rw [hessianAt_congr_nhds h]

theorem mfderiv_comp_eq_smul {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (p : M) :
    mfderiv I 𝓘(ℝ, ℝ) (ρ ∘ g) p = deriv ρ (g p) • mfderiv I 𝓘(ℝ, ℝ) g p := by
  have hρm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ρ (g p) :=
    (hρ.contMDiff (g p)).mdifferentiableAt (by simp)
  have hgm : MDifferentiableAt I 𝓘(ℝ, ℝ) g p := (hg p).mdifferentiableAt (by simp)
  rw [mfderiv_comp p hρm hgm, mfderiv_eq_fderiv]
  ext v
  have key : ∀ w : ℝ, fderiv ℝ ρ (g p) w = deriv ρ (g p) • w := fun w =>
    (fderiv_eq_smul_deriv w).trans (mul_comm _ _)
  exact key _

end Congr

section Manifold

open MorseExistence

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M]

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem chartRep_comp (ρ : ℝ → ℝ) (g : M → ℝ) (p : M) :
    chartRep I (ρ ∘ g) p = ρ ∘ chartRep I g p := rfl

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem chartRep_apply_self (g : M → ℝ) (p : M) :
    chartRep I g p (extChartAt I p p) = g p := by
  simp [chartRep]

theorem fderiv_chartRep_comp {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (p : M) :
    fderiv ℝ (chartRep I (ρ ∘ g) p) (extChartAt I p p) =
      deriv ρ (g p) • fderiv ℝ (chartRep I g p) (extChartAt I p p) := by
  rw [chartRep_comp]
  have hgd : DifferentiableAt ℝ (chartRep I g p) (extChartAt I p p) :=
    (contDiffAt_chartRep hg (mem_extChartAt_target p)).differentiableAt (by simp)
  have hρd : HasDerivAt ρ (deriv ρ (chartRep I g p (extChartAt I p p)))
      (chartRep I g p (extChartAt I p p)) :=
    (hρ.differentiable (by simp) _).hasDerivAt
  rw [(hρd.comp_hasFDerivAt _ hgd.hasFDerivAt).fderiv, chartRep_apply_self]

theorem isCriticalPointAt_comp_iff {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) {p : M} (hρ' : deriv ρ (g p) ≠ 0) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (ρ ∘ g) p ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p := by
  have hg' : ContMDiff I 𝓘(ℝ, ℝ) ∞ (ρ ∘ g) := hρ.contMDiff.comp hg
  rw [isCriticalPointAt_iff_chart hg' (mem_extChartAt_source p),
    isCriticalPointAt_iff_chart hg (mem_extChartAt_source p), fderiv_chartRep_comp hg hρ p,
    smul_eq_zero, or_iff_right hρ']

theorem hessianAt_comp {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) {p : M} (hp : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p) :
    hessianAt I (ρ ∘ g) p = deriv ρ (g p) • hessianAt I g p := by
  rw [hessianAt_eq, hessianAt_eq, chartRep_comp]
  have h0 := (isCriticalPointAt_iff_chart hg (mem_extChartAt_source p)).1 hp
  rw [chartHessianAt_comp_of_fderiv_eq_zero
    ((contDiffAt_chartRep hg (mem_extChartAt_target p)).of_le two_le_infty)
    (hρ.contDiffAt.of_le two_le_infty) h0, chartRep_apply_self]

theorem morseIndex_comp_of_isCriticalPointAt {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) {p : M} (hρ' : 0 < deriv ρ (g p)) (hp : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (ρ ∘ g) p ∧
      (DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I (ρ ∘ g) p ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g p) ∧
      morseIndex I (ρ ∘ g) p = morseIndex I g p := by
  refine ⟨(isCriticalPointAt_comp_iff hg hρ hρ'.ne').2 hp, ?_, ?_⟩
  · change (Morse.IsCriticalPointAt I (ρ ∘ g) p ∧
      (QuadraticMap.associated (R := ℝ) (hessianAt I (ρ ∘ g) p)).SeparatingLeft) ↔
      (Morse.IsCriticalPointAt I g p ∧
        (QuadraticMap.associated (R := ℝ) (hessianAt I g p)).SeparatingLeft)
    rw [isCriticalPointAt_comp_iff hg hρ hρ'.ne', hessianAt_comp hg hρ hp,
      separatingLeft_associated_smul_iff _ hρ'.ne']
  · unfold morseIndex
    rw [hessianAt_comp hg hρ hp, sigNeg_smul_of_pos _ hρ']

theorem isCriticalPointAt_affineComb_iff {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) {m : ℝ} {p : M} (hcoef : 1 + m * (deriv ρ (g p) - 1) ≠ 0)
    {g' : M → ℝ} (hg' : g' =ᶠ[𝓝 p] fun x => g x + m * (ρ (g x) - g x)) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g' p ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p := by
  have hΨ' : deriv (fun t => t + m * (ρ t - t)) (g p) ≠ 0 := by
    rw [deriv_affineComb hρ]; exact hcoef
  have hcomp : (fun t => t + m * (ρ t - t)) ∘ g = fun x => g x + m * (ρ (g x) - g x) := rfl
  rw [isCriticalPointAt_congr_nhds hg', ← hcomp]
  exact isCriticalPointAt_comp_iff hg (contDiff_affineComb hρ m) hΨ'

theorem morseIndex_affineComb_of_isCriticalPointAt {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) {p : M}
    (hρ' : 0 < deriv ρ (g p)) (hp : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p) {g' : M → ℝ}
    (hg' : g' =ᶠ[𝓝 p] fun x => g x + m * (ρ (g x) - g x)) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g' p ∧ (DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g' p ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g p) ∧
      morseIndex I g' p = morseIndex I g p := by
  have hΨ' : 0 < deriv (fun t => t + m * (ρ t - t)) (g p) := by
    rw [deriv_affineComb hρ]; exact affineComb_deriv_pos hm0 hm1 hρ'
  have hcomp : (fun t => t + m * (ρ t - t)) ∘ g = fun x => g x + m * (ρ (g x) - g x) := rfl
  obtain ⟨h1, h2, h3⟩ := morseIndex_comp_of_isCriticalPointAt hg (contDiff_affineComb hρ m) hΨ' hp
  rw [hcomp] at h1 h2 h3
  exact ⟨(isCriticalPointAt_congr_nhds hg').2 h1, (isNondegenerateCriticalPointAt_congr_nhds hg').trans h2,
    (morseIndex_congr_nhds hg').trans h3⟩

end Manifold

end MonotoneShift

end DifferentialGeometry.Topology
