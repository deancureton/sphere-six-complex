module

public import DifferentialGeometry.Topology.Morse.Cancellation.Setup.Bridge
public import DifferentialGeometry.Topology.Morse.Rearrangement.Rearrange
public import DifferentialGeometry.Topology.Morse.Rearrangement.Swap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

namespace MonotoneShift

theorem exists_translationShift {c₀ c₁ lo hi d : ℝ} (hlo : c₀ < min lo (lo + d))
    (hhi : max hi (hi + d) < c₁) (hlohi : lo ≤ hi) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ t, 0 < deriv ρ t) ∧ StrictMono ρ ∧
      (∀ t, t ∉ Ioo c₀ c₁ → ρ t = t) ∧ MapsTo ρ (Ioo c₀ c₁) (Ioo c₀ c₁) ∧
      ∀ t ∈ Icc lo hi, ρ t = t + d := by
  set lo' := min lo (lo + d) with hlo'
  set hi' := max hi (hi + d) with hhi'
  have hlo'lo : lo' ≤ lo := min_le_left _ _
  have hlo'd : lo' ≤ lo + d := min_le_right _ _
  have hhihi' : hi ≤ hi' := le_max_left _ _
  have hdhi' : hi + d ≤ hi' := le_max_right _ _
  have hlohi' : lo' ≤ hi' := by linarith
  set δ := min (lo' - c₀) (c₁ - hi') / 3 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    have : 0 < min (lo' - c₀) (c₁ - hi') := lt_min (by linarith) (by linarith)
    linarith
  have hδlo : 3 * δ ≤ lo' - c₀ := by
    rw [hδ]; have := min_le_left (lo' - c₀) (c₁ - hi'); linarith
  have hδhi : 3 * δ ≤ c₁ - hi' := by
    rw [hδ]; have := min_le_right (lo' - c₀) (c₁ - hi'); linarith
  set m := (lo' + hi') / 2 with hm
  set r := (hi' - lo') / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  let b : ContDiffBump m := ⟨r + δ, r + 2 * δ, by linarith, by linarith⟩
  have hb_one : ∀ t, lo' - δ ≤ t → t ≤ hi' + δ → b t = 1 := by
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
  obtain ⟨k, hk⟩ := exists_nat_gt (max (|d| * C) 0)
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hkC : |d| * C < k := lt_of_le_of_lt (le_max_left _ _) hk
  set s := d / k with hs
  have hks : (k : ℝ) * s = d := by rw [hs]; field_simp
  set T : ℝ → ℝ := fun t => t + s * b t with hT
  have hT_deriv : ∀ t, HasDerivAt T (1 + s * deriv b t) t := fun t =>
    (hasDerivAt_id t).add ((hb_diff t).const_mul s)
  have hT_pos : ∀ t, 0 < 1 + s * deriv b t := by
    intro t
    have h1 : |s * deriv b t| < 1 := by
      rw [abs_mul, hs, abs_div, abs_of_pos hkpos, div_mul_eq_mul_div, div_lt_one hkpos]
      calc |d| * |deriv b t| ≤ |d| * C :=
            mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC t) (abs_nonneg _)
        _ < k := hkC
    have := (abs_lt.1 h1).1
    linarith
  have hT_smooth : ContDiff ℝ ∞ T := contDiff_id.add (contDiff_const.mul hb_smooth)
  have hT_id : ∀ t, t ∉ Ioo c₀ c₁ → T t = t := by
    intro t ht
    simp [hT, hb_zero t ht]
  have hplateau : ∀ t ∈ Icc lo hi, ∀ j : ℕ, j ≤ k → lo' ≤ t + j * s ∧ t + j * s ≤ hi' := by
    intro t ht j hj
    have hθ0 : 0 ≤ (j : ℝ) / k := div_nonneg (Nat.cast_nonneg j) hkpos.le
    have hθ1 : (j : ℝ) / k ≤ 1 := by
      rw [div_le_one hkpos]; exact_mod_cast hj
    have hjs : (j : ℝ) * s = (j / k) * d := by rw [hs]; ring
    rw [hjs]
    rcases le_or_gt 0 d with hd | hd
    · constructor
      · nlinarith [ht.1]
      · nlinarith [ht.2]
    · constructor
      · nlinarith [ht.1]
      · nlinarith [ht.2]
  have hstep : ∀ t ∈ Icc lo hi, ∀ j : ℕ, j ≤ k → T^[j] t = t + j * s := by
    intro t ht j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hj' : j ≤ k := Nat.le_of_succ_le hj
      rw [Function.iterate_succ_apply', ih hj']
      have hb1 : b (t + j * s) = 1 := by
        obtain ⟨h1, h2⟩ := hplateau t ht j hj'
        exact hb_one _ (by linarith) (by linarith)
      simp only [hT, hb1, mul_one, Nat.cast_succ]
      ring
  have hderiv : ∀ t, ∃ d', 0 < d' ∧ HasDerivAt T^[k] d' t :=
    fun t => exists_pos_hasDerivAt_iterate hT_deriv hT_pos k t
  have hmono : StrictMono T^[k] := strictMono_of_deriv_pos (fun t => by
    obtain ⟨d', hd, hdiff⟩ := hderiv t
    rw [hdiff.deriv]; exact hd)
  refine ⟨T^[k], contDiff_iterate hT_smooth k, ?_, hmono, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨d', hd, hdiff⟩ := hderiv t
    rw [hdiff.deriv]; exact hd
  · intro t ht
    exact Function.iterate_fixed (hT_id t ht) k
  · intro t ht
    have h0 : T^[k] c₀ = c₀ := Function.iterate_fixed (hT_id c₀ (by simp)) k
    have h1 : T^[k] c₁ = c₁ := Function.iterate_fixed (hT_id c₁ (by simp)) k
    exact ⟨h0 ▸ hmono ht.1, h1 ▸ hmono ht.2⟩
  · intro t ht
    rw [hstep t ht k le_rfl, hks]

end MonotoneShift

section Rearrange'

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M]
  {f : M → ℝ} {a b : ℝ}

open Rearrange MonotoneShift

theorem rearrange' (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a') (hab' : a' < b')
    (hb : b' ≤ b) (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {crit : Finset M}
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) (μ : M → ℝ)
    (hμ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ μ (f ⁻¹' Ioo a' b')) (hμ01 : ∀ x, μ x ∈ Icc 0 1)
    (hμV : ∀ x ∈ f ⁻¹' Ioo a' b', (mfderiv I 𝓘(ℝ, ℝ) μ x) (D.V x) = 0)
    (hμcrit : ∀ p ∈ crit, f p ∈ Ioo a' b' → ∀ᶠ x in 𝓝 p, μ x = μ p) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρ' : ∀ t, 0 < deriv ρ t) {a₃ b₃ : ℝ}
    (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) (h₃ : a' < a₃ ∧ b₃ < b')
    (hρmaps : MapsTo ρ (Ioo a' b') (Ioo a' b')) :
    ModifiedWithin f a' b' (rearranged f μ ρ) ∧ MorseStrip I (rearranged f μ ρ) a' b' ∧
      ModifiedWithin f a b (rearranged f μ ρ) ∧ MorseStrip I (rearranged f μ ρ) a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (rearranged f μ ρ) x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I (rearranged f μ ρ) x = morseIndex I f x) ∧
      (∀ p, rearranged f μ ρ p = f p + μ p * (ρ (f p) - f p)) ∧
      EqOn (rearranged f μ ρ) f {x | f x ≤ a₃ ∨ b₃ ≤ f x} := by
  set g := rearranged f μ ρ with hg
  have hfc : Continuous f := hf.smooth.continuous
  have hmod : ModifiedWithin f a' b' g := modifiedWithin_rearranged hμ01 hρid h₃ hρmaps
  have hmod' : ModifiedWithin f a b g := hmod.mono ha hb
  have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := contMDiff_rearranged hf.smooth hμ hρ hρid h₃
  have hout : ∀ x, f x ∉ Ioo a' b' → g =ᶠ[𝓝 x] f := fun x hx =>
    rearranged_eventuallyEq_of_notMem hfc hρid h₃ hx
  have hnear : ∀ p ∈ crit, f p ∈ Ioo a' b' →
      g =ᶠ[𝓝 p] fun x => f x + μ p * (ρ (f x) - f x) := by
    intro p hp hp'
    filter_upwards [hμcrit p hp hp'] with x hx
    rw [hg, rearranged_apply, hx]
  have hcritIff : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x
    by_cases hx : f x ∈ Ioo a' b'
    · by_cases hxf : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x
      · have hxc : x ∈ crit := (hcrit x).2 ⟨⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩, hxf⟩
        exact isCriticalPointAt_affineComb_iff hf.smooth hρ
          (affineComb_deriv_pos (hμ01 x).1 (hμ01 x).2 (hρ' (f x))).ne' (hnear x hxc hx)
      · have hxc : x ∉ crit := fun h => hxf ((hcrit x).1 h).2
        refine ⟨fun h => absurd h ?_, fun h => absurd h hxf⟩
        have hμx : MDifferentiableAt I 𝓘(ℝ, ℝ) μ x :=
          (hμ.contMDiffAt ((isOpen_Ioo.preimage hfc).mem_nhds hx)).mdifferentiableAt (by simp)
        exact not_isCriticalPointAt_rearranged hf.smooth hμx hρ (hμ01 x) (hρ' (f x)) (hμV x hx)
          (D.neg x ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩ hxc)
    · exact isCriticalPointAt_congr_nhds (hout x hx)
  have hidx : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x →
      (DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f x) ∧
        morseIndex I g x = morseIndex I f x := by
    intro x hxf
    by_cases hx : f x ∈ Ioo a' b'
    · have hxc : x ∈ crit := (hcrit x).2 ⟨⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩, hxf⟩
      obtain ⟨_, h2, h3⟩ := morseIndex_affineComb_of_isCriticalPointAt hf.smooth hρ (hμ01 x).1
        (hμ01 x).2 (hρ' (f x)) hxf (hnear x hxc hx)
      exact ⟨h2, h3⟩
    · exact ⟨isNondegenerateCriticalPointAt_congr_nhds (hout x hx), morseIndex_congr_nhds (hout x hx)⟩
  have hcompact : IsCompact (g ⁻¹' Icc a' b') := by
    rw [hmod.preimage_Icc]
    exact hf.compact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc ha hb))
  have hstrip' : MorseStrip I g a' b' := by
    refine ⟨hsmooth, hab', hcompact, fun x hx => ?_, fun x hx hxc => ?_⟩
    · have hfx : f x = a' ∨ f x = b' := by
        rcases hx with hx | hx
        · left
          have : x ∈ g ⁻¹' {a'} := hx
          rw [hmod.preimage_singleton_left] at this
          exact this
        · right
          have : x ∈ g ⁻¹' {b'} := hx
          rw [hmod.preimage_singleton_right] at this
          exact this
      rw [hcritIff]
      exact hreg x hfx
    · have hfx : f x ∈ Ioo a' b' := by
        have : x ∈ g ⁻¹' Ioo a' b' := hx
        rwa [hmod.preimage_Ioo] at this
      have hxf : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := (hcritIff x).1 hxc
      exact (hidx x hxf).1.2 (hf.nondegenerate x ⟨ha.trans_lt hfx.1, hfx.2.trans_le hb⟩ hxf)
  have hcompact' : IsCompact (g ⁻¹' Icc a b) := by
    rw [hmod'.preimage_Icc]
    exact hf.compact
  have hstrip : MorseStrip I g a b := by
    refine ⟨hsmooth, hf.lt, hcompact', fun x hx => ?_, fun x hx hxc => ?_⟩
    · have hfx : f x = a ∨ f x = b := by
        rcases hx with hx | hx
        · left
          have : x ∈ g ⁻¹' {a} := hx
          rw [hmod'.preimage_singleton_left] at this
          exact this
        · right
          have : x ∈ g ⁻¹' {b} := hx
          rw [hmod'.preimage_singleton_right] at this
          exact this
      rw [hcritIff]
      exact hf.regular x hfx
    · have hfx : f x ∈ Ioo a b := by
        have : x ∈ g ⁻¹' Ioo a b := hx
        rwa [hmod'.preimage_Ioo] at this
      have hxf : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := (hcritIff x).1 hxc
      exact (hidx x hxf).1.2 (hf.nondegenerate x hfx hxf)
  exact ⟨hmod, hstrip', hmod', hstrip, hcritIff, fun x hx => (hidx x hx).2, fun p => rfl,
    eqOn_rearranged hρid⟩

end Rearrange'

open DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split morseNorm_piNorm_le recombine)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless]

theorem morseNormalForm_add_const {k : ℕ} (hk : k ≤ n) (c d : ℝ) (y : Fin n → ℝ) :
    morseNormalForm hk (c + d) y = morseNormalForm hk c y + d := by
  unfold morseNormalForm; ring

theorem exists_reparam {g : M → ℝ} (D : GradientLikeStrip I f a b crit)
    (D' : GradientLikeStrip I g a b crit) {φ : M → ℝ} (hφ : Continuous φ) {m M₀ : ℝ}
    (hm : 0 < m) (hφb : ∀ x, m ≤ φ x ∧ φ x ≤ M₀) (hV : ∀ x, D'.V x = φ x • D.V x) (x : M) :
    ∃ σ : ℝ → ℝ, StrictMono σ ∧ σ 0 = 0 ∧ Function.Surjective σ ∧
      ∀ s, D'.flow s x = D.flow (σ s) x := by
  set γ : ℝ → M := fun t => D.flow t x with hγdef
  have hγ : IsMIntegralCurve γ D.V := D.isMIntegralCurve_flow x
  have hγc : Continuous γ := D.continuous_flow_curve x
  have hφpos : ∀ y, 0 < φ y := fun y => hm.trans_le (hφb y).1
  have hM₀ : 0 < M₀ := hm.trans_le ((hφb x).1.trans (hφb x).2)
  set ψ : ℝ → ℝ := fun u => (φ (γ u))⁻¹ with hψdef
  have hψc : Continuous ψ := (hφ.comp hγc).inv₀ fun u => (hφpos _).ne'
  have hψpos : ∀ u, 0 < ψ u := fun u => inv_pos.2 (hφpos _)
  have hψlow : ∀ u, M₀⁻¹ ≤ ψ u := fun u => inv_anti₀ (hφpos _) (hφb _).2
  set θ : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, ψ v with hθdef
  have hθ : ∀ u, HasDerivAt θ (ψ u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hψc.intervalIntegrable _ _)
      (hψc.stronglyMeasurableAtFilter _ _) hψc.continuousAt
  have hθ0 : θ 0 = 0 := by simp [hθdef]
  have hθmono : StrictMono θ := strictMono_of_deriv_pos fun u => by
    rw [(hθ u).deriv]; exact hψpos u
  have hθc : Continuous θ := continuous_iff_continuousAt.2 fun u => (hθ u).continuousAt
  have hθdiff : Differentiable ℝ θ := fun u => (hθ u).differentiableAt
  have hlow : ∀ u v, u ≤ v → M₀⁻¹ * (v - u) ≤ θ v - θ u := fun u v huv =>
    Convex.mul_sub_le_image_sub_of_le_deriv convex_univ hθc.continuousOn
      hθdiff.differentiableOn (fun w _ => by rw [(hθ w).deriv]; exact hψlow w) u (mem_univ _)
      v (mem_univ _) huv
  have hM₀inv : 0 < M₀⁻¹ := inv_pos.2 hM₀
  have htop : Tendsto θ atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hM₀inv)
    filter_upwards [eventually_ge_atTop 0] with u hu
    have := hlow 0 u hu
    rw [hθ0] at this
    simpa using this
  have hbot : Tendsto θ atBot atBot := by
    refine tendsto_atBot_mono' atBot ?_ (tendsto_id.const_mul_atBot hM₀inv)
    filter_upwards [eventually_le_atBot 0] with u hu
    have := hlow u 0 hu
    rw [hθ0] at this
    simp only [id]
    linarith
  have hsurj : Function.Surjective θ := hθc.surjective htop hbot
  set e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective θ hθmono hsurj with he
  have he_apply : ∀ u, e u = θ u := fun u => rfl
  set σ : ℝ → ℝ := fun s => e.symm s with hσdef
  have hσθ : ∀ s, θ (σ s) = s := fun s => by
    rw [← he_apply]; exact e.apply_symm_apply s
  have hσ0 : σ 0 = 0 := hθmono.injective (by rw [hσθ 0, hθ0])
  have hσmono : StrictMono σ := e.symm.strictMono
  have hσsurj : Function.Surjective σ := e.symm.surjective
  have hσc : Continuous σ := e.symm.continuous
  have hσderiv : ∀ s, HasDerivAt σ (φ (γ (σ s))) s := by
    intro s
    have h := HasDerivAt.of_local_left_inverse hσc.continuousAt (hθ (σ s)) (hψpos _).ne'
      (Eventually.of_forall hσθ)
    simpa [hψdef] using h
  set δ : ℝ → M := fun s => γ (σ s) with hδdef
  have hδ : IsMIntegralCurve δ D'.V := by
    intro s
    have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) I γ (σ s)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (D.V (γ (σ s)))) := hγ (σ s)
    have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (φ (γ (σ s)))) :=
      (hasDerivAt_iff_hasFDerivAt.1 (hσderiv s)).hasMFDerivAt
    have h3 := h1.comp s h2
    have heq : ((1 : ℝ →L[ℝ] ℝ).smulRight (D.V (γ (σ s)))).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (φ (γ (σ s)))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (D'.V (δ s)) := by
      apply ContinuousLinearMap.ext
      intro r
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        one_apply_eq_self, hδdef, hV, smul_smul]
      rfl
    rw [← heq]
    exact h3
  have hflow : (fun s => D'.flow s x) = δ :=
    integralCurve_eq_of_agree D'.V D'.smooth_one (D'.isMIntegralCurve_flow x) hδ (t₀ := 0)
      (by simp [hδdef, hγdef, hσ0])
  exact ⟨σ, hσmono, hσ0, hσsurj, fun s => congrFun hflow s⟩

theorem exists_nonneg_flow_mem_iff {g : M → ℝ} (D : GradientLikeStrip I f a b crit)
    (D' : GradientLikeStrip I g a b crit) {φ : M → ℝ} (hφ : Continuous φ) {m M₀ : ℝ}
    (hm : 0 < m) (hφb : ∀ x, m ≤ φ x ∧ φ x ≤ M₀) (hV : ∀ x, D'.V x = φ x • D.V x) (x : M)
    (S : Set M) : (∃ t, 0 ≤ t ∧ D'.flow t x ∈ S) ↔ ∃ t, 0 ≤ t ∧ D.flow t x ∈ S := by
  obtain ⟨σ, hσmono, hσ0, hσsurj, hflow⟩ := exists_reparam D D' hφ hm hφb hV x
  constructor
  · rintro ⟨t, ht, hmem⟩
    refine ⟨σ t, ?_, by rwa [hflow] at hmem⟩
    rw [← hσ0]; exact hσmono.monotone ht
  · rintro ⟨t, ht, hmem⟩
    obtain ⟨s, rfl⟩ := hσsurj t
    refine ⟨s, ?_, by rwa [hflow]⟩
    rw [← hσ0] at ht
    exact hσmono.le_iff_le.1 ht

theorem exists_flow_mem_iff {g : M → ℝ} (D : GradientLikeStrip I f a b crit)
    (D' : GradientLikeStrip I g a b crit) {φ : M → ℝ} (hφ : Continuous φ) {m M₀ : ℝ}
    (hm : 0 < m) (hφb : ∀ x, m ≤ φ x ∧ φ x ≤ M₀) (hV : ∀ x, D'.V x = φ x • D.V x) (x : M)
    (S : Set M) : (∃ t, D'.flow t x ∈ S) ↔ ∃ t, D.flow t x ∈ S := by
  obtain ⟨σ, -, -, hσsurj, hflow⟩ := exists_reparam D D' hφ hm hφb hV x
  constructor
  · rintro ⟨t, hmem⟩
    exact ⟨σ t, by rwa [hflow] at hmem⟩
  · rintro ⟨t, hmem⟩
    obtain ⟨s, rfl⟩ := hσsurj t
    exact ⟨s, by rwa [hflow]⟩

end GradientLikeStrip

section Rescale

variable [I.Boundaryless]

open Rearrange MonotoneShift

theorem deriv_eq_one_of_notMem {ρ : ℝ → ℝ} {a₃ b₃ : ℝ} (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t)
    {t : ℝ} (ht : t < a₃ ∨ b₃ < t) : deriv ρ t = 1 := by
  have hev : ρ =ᶠ[𝓝 t] id := by
    rcases ht with ht | ht
    · filter_upwards [Iio_mem_nhds ht] with s hs
      exact hρid s fun h => absurd hs (not_lt.2 h.1.le)
    · filter_upwards [Ioi_mem_nhds ht] with s hs
      exact hρid s fun h => absurd hs (not_lt.2 h.2.le)
  rw [hev.deriv_eq, deriv_id]

theorem exists_rescaled (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a') (hab' : a' < b')
    (hb : b' ≤ b) (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) (μ : M → ℝ)
    (hμ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ μ (f ⁻¹' Ioo a' b')) (hμ01 : ∀ x, μ x ∈ Icc 0 1)
    (hμV : ∀ x ∈ f ⁻¹' Ioo a' b', (mfderiv I 𝓘(ℝ, ℝ) μ x) (D.V x) = 0)
    (hμcrit : ∀ p ∈ crit, f p ∈ Ioo a' b' → ∀ᶠ x in 𝓝 p, μ x = μ p) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρ' : ∀ t, 0 < deriv ρ t) {a₃ b₃ : ℝ}
    (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) (h₃ : a' < a₃ ∧ b₃ < b')
    (hρmaps : MapsTo ρ (Ioo a' b') (Ioo a' b')) (Rn rmn : ∀ p ∈ crit, ℝ)
    (hRn : ∀ p hp, 4 * (D.chart p hp).r₀ < Rn p hp ∧ Rn p hp ≤ (D.chart p hp).R)
    (hrmn : ∀ p hp, 2 * (D.chart p hp).r₀ < rmn p hp ∧ rmn p hp ≤ D.rm p hp ∧
      rmn p hp ≤ Rn p hp)
    (hconst : ∀ p hp, ∀ y, morseNorm n y ≤ Rn p hp →
      μ ((D.chart p hp).χ y) * (ρ (f ((D.chart p hp).χ y)) - f ((D.chart p hp).χ y)) =
        μ p * (ρ (f p) - f p) ∧
      μ ((D.chart p hp).χ y) * (deriv ρ (f ((D.chart p hp).χ y)) - 1) = 0) :
    ∃ D' : GradientLikeStrip I (rearranged f μ ρ) a b crit,
      (∀ p hp, (D'.chart p hp).χ = (D.chart p hp).χ ∧ (D'.chart p hp).k = (D.chart p hp).k ∧
        (D'.chart p hp).r₀ = (D.chart p hp).r₀ ∧ (D'.chart p hp).R = Rn p hp ∧
        (D'.chart p hp).R' = (D.chart p hp).R') ∧
      (∀ p hp, D'.rm p hp = rmn p hp) ∧
      ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ x, D'.V x = φ x • D.V x := by
  obtain ⟨hmod, -, hmod', hstrip, hcritIff, hidx, hval, -⟩ :=
    rearrange' hf ha hab' hb hreg D hcrit μ hμ hμ01 hμV hμcrit ρ hρ hρ' hρid h₃ hρmaps
  set g := rearranged f μ ρ with hgdef
  have hfc : Continuous f := hf.smooth.continuous
  set ψ : M → ℝ := fun x => 1 + μ x * (deriv ρ (f x) - 1) with hψdef
  have hψpos : ∀ x, 0 < ψ x := fun x =>
    affineComb_deriv_pos (hμ01 x).1 (hμ01 x).2 (hρ' (f x))
  have hψone : ∀ x, f x ∈ Iio a₃ ∪ Ioi b₃ → ψ x = 1 := by
    intro x hx
    have : deriv ρ (f x) = 1 := deriv_eq_one_of_notMem hρid (by
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr h)
    simp [hψdef, this]
  have houter : ∀ x, f x ∉ Ioo a' b' → f x ∈ Iio a₃ ∪ Ioi b₃ := fun x hx =>
    mem_outer_of_notMem h₃ hx
  have hψsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ := by
    intro x
    by_cases hx : f x ∈ Ioo a' b'
    · have hμx : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ μ x :=
        hμ.contMDiffAt ((isOpen_Ioo.preimage hfc).mem_nhds hx)
      have hρ'c : ContDiff ℝ ∞ (deriv ρ) := (contDiff_infty_iff_deriv.1 hρ).2
      have hd : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => deriv ρ (f y)) x :=
        (hρ'c.contMDiff.comp hf.smooth) x
      exact contMDiffAt_const.add (hμx.mul (hd.sub contMDiffAt_const))
    · refine (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_outer hfc a₃ b₃).mem_nhds (houter x hx)] with y hy
      exact hψone y hy
  set φ : M → ℝ := fun x => (ψ x)⁻¹ with hφdef
  have hφsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ := hψsmooth.inv₀ fun x => (hψpos x).ne'
  have hφc : Continuous φ := hφsmooth.continuous
  have hφpos : ∀ x, 0 < φ x := fun x => inv_pos.2 (hψpos x)
  have hφone : ∀ x, f x ∉ Ioo a' b' → φ x = 1 := fun x hx => by
    simp [hφdef, hψone x (houter x hx)]
  have hbounds : ∃ m M₀, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀ := by
    have hK : IsCompact (f ⁻¹' Icc a' b') :=
      hf.compact.of_isClosed_subset (isClosed_Icc.preimage hfc)
        (preimage_mono (Icc_subset_Icc ha hb))
    rcases (f ⁻¹' Icc a' b').eq_empty_or_nonempty with hemp | hne
    · refine ⟨1, 1, one_pos, fun x => ?_⟩
      have hx : f x ∉ Ioo a' b' := fun h => by
        have : x ∈ f ⁻¹' Icc a' b' := Ioo_subset_Icc_self h
        rw [hemp] at this; exact this
      rw [hφone x hx]; exact ⟨le_rfl, le_rfl⟩
    · obtain ⟨x₁, -, hmin⟩ := hK.exists_isMinOn hne hφc.continuousOn
      obtain ⟨x₂, -, hmax⟩ := hK.exists_isMaxOn hne hφc.continuousOn
      refine ⟨min (φ x₁) 1, max (φ x₂) 1, lt_min (hφpos x₁) one_pos, fun x => ?_⟩
      by_cases hx : f x ∈ Ioo a' b'
      · have hx' : x ∈ f ⁻¹' Icc a' b' := Ioo_subset_Icc_self hx
        exact ⟨(min_le_left _ _).trans (hmin hx'), (hmax hx').trans (le_max_left _ _)⟩
      · rw [hφone x hx]; exact ⟨min_le_right _ _, le_max_right _ _⟩
  set V' : (x : M) → TangentSpace I x := fun x => φ x • D.V x with hV'def
  have hV'smooth : ContMDiff I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, V' x⟩ : TangentBundle I M)) :=
    hφsmooth.smul_section D.smooth
  have hV'supp : tsupport V' ⊆ tsupport D.V := by
    apply closure_mono
    intro x hx h
    apply hx
    change φ x • D.V x = 0
    rw [h]
    change φ x • (0 : Fin n → ℝ) = (0 : Fin n → ℝ)
    exact smul_zero _
  have hV'compact : IsCompact (tsupport V') :=
    D.compact.of_isClosed_subset (isClosed_tsupport _) hV'supp
  have hdf : ∀ x, dfV I g V' x = dfV I f D.V x := by
    intro x
    by_cases hx : f x ∈ Ioo a' b'
    · have hμx : MDifferentiableAt I 𝓘(ℝ, ℝ) μ x :=
        (hμ.contMDiffAt ((isOpen_Ioo.preimage hfc).mem_nhds hx)).mdifferentiableAt (by simp)
      have h := mfderiv_rearranged_apply hf.smooth hμx hρ (V' x)
      unfold dfV
      rw [h]
      simp only [hV'def, map_smul, smul_eq_mul, hμV x hx, map_zero, mul_zero, add_zero]
      have hψφ : ψ x * φ x = 1 := by
        rw [hφdef]; exact mul_inv_cancel₀ (hψpos x).ne'
      change ψ x * (φ x * _) = _
      rw [← mul_assoc, hψφ, one_mul]
    · have hev : g =ᶠ[𝓝 x] f := rearranged_eventuallyEq_of_notMem hfc hρid h₃ hx
      unfold dfV
      rw [hev.mfderiv_eq]
      simp only [hV'def, map_smul, smul_eq_mul, hφone x hx, one_mul]
      rfl
  have hpre : g ⁻¹' Icc a b = f ⁻¹' Icc a b := hmod'.preimage_Icc
  have hpreo : g ⁻¹' Ioo a b = f ⁻¹' Ioo a b := hmod'.preimage_Ioo
  have hV'eq : ∀ p hp, ∀ y, morseNorm n y < rmn p hp → V' ((D.chart p hp).χ y) =
      D.V ((D.chart p hp).χ y) := by
    intro p hp y hy
    have h2 := (hconst p hp y (hy.le.trans (hrmn p hp).2.2)).2
    have hψ1 : ψ ((D.chart p hp).χ y) = 1 := by simp [hψdef, h2]
    simp [hV'def, hφdef, hψ1]
  have hnorm' : ∀ p (hp : p ∈ crit), ∀ y, morseNorm n y ≤ Rn p hp →
      g ((D.chart p hp).χ y) = morseNormalForm (D.chart p hp).hk (g p) y := by
    intro p hp y hy
    have h1 := (hconst p hp y hy).1
    have h2 := (D.chart p hp).hnorm y (hy.trans (hRn p hp).2)
    rw [hval p, hgdef, rearranged_apply, h1, h2, GradientLikeStrip.morseNormalForm_add_const]
  refine ⟨{ V := V'
            smooth := hV'smooth
            compact := hV'compact
            rate := fun x => by
              change -1 ≤ dfV I g V' x ∧ dfV I g V' x ≤ 0
              rw [hdf x]; exact D.rate x
            chart := fun p hp =>
              { k := (D.chart p hp).k
                hk := (D.chart p hp).hk
                hkidx := by rw [hidx p ((hcrit p).1 hp).2]; exact (D.chart p hp).hkidx
                χ := (D.chart p hp).χ
                R := Rn p hp
                R' := (D.chart p hp).R'
                r₀ := (D.chart p hp).r₀
                hr₀ := (D.chart p hp).hr₀
                hr₀R := (hRn p hp).1
                hRR' := (hRn p hp).2.trans_lt (D.chart p hp).hRR'
                hχ0 := (D.chart p hp).hχ0
                hball := (D.chart p hp).hball
                hsrc := fun y hy => (D.chart p hp).hsrc y (hy.trans (hRn p hp).2)
                hnorm := hnorm' p hp
                hχ := (D.chart p hp).hχ
                hχsymm := (D.chart p hp).hχsymm }
            disjoint := fun p hp q hq hpq => D.disjoint p hp q hq hpq
            inStrip := fun p hp => by
              change (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' ⊆ g ⁻¹' Ioo a b
              rw [hpreo]
              exact D.inStrip p hp
            unit := fun x hx hxB => by
              change dfV I g V' x = -1
              rw [hdf x]
              exact D.unit x (by rwa [← hpre]) fun p hp hmem => hxB p hp hmem
            neg := fun x hx hxc => by
              change dfV I g V' x < 0
              rw [hdf x]
              exact D.neg x (by rwa [← hpre]) hxc
            rm := rmn
            hrm := fun p hp => ⟨(hrmn p hp).1, (hrmn p hp).2.2⟩
            model := fun p hp y hy => by
              have hy' : morseNorm n y < D.rm p hp := hy.trans_le (hrmn p hp).2.1
              change mfderiv I 𝓘(ℝ, Fin n → ℝ) (D.chart p hp).χ.symm ((D.chart p hp).χ y)
                (V' ((D.chart p hp).χ y)) = _
              rw [hV'eq p hp y hy]
              exact D.model p hp y hy' }, fun p hp => ⟨rfl, rfl, rfl, rfl, rfl⟩,
    fun p hp => rfl, φ, hφc, hbounds, fun x => rfl⟩

end Rescale

theorem exists_trajectoryCutoff' [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit) {a₂ b₂ : ℝ}
    (ha₂ : a ≤ a₂) (hb₂ : b₂ ≤ b) (P₀ P₁ : Set M)
    (hP : ∀ p ∈ crit, f p ∈ Ioo a₂ b₂ → p ∈ P₀ ∨ p ∈ P₁)
    (hdisj : ∀ p, p ∈ P₀ → p ∈ P₁ → False) {c ε : ℝ} (hc : c ∈ Ioo a₂ b₂) (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (hsep : ∀ p ∈ crit, f p ∉ Ioo a₂ b₂ → f p + ε ≤ a₂ ∨ b₂ ≤ f p - ε)
    (hcε : ∀ p ∈ crit, f p ∈ Ioo a₂ b₂ → (f p < c → f p + ε < c) ∧ (c < f p → c < f p - ε))
    (hcne : ∀ p ∈ crit, f p ∈ Ioo a₂ b₂ → f p ≠ c)
    (r' : ∀ p ∈ crit, ℝ) (hr' : ∀ p hp, (D.chart p hp).r₀ < r' p hp)
    (hnocommon : ∀ p hp q hq, p ∈ P₀ → q ∈ P₁ → f p ∈ Ioo a₂ b₂ → f q ∈ Ioo a₂ b₂ →
      ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r' p hp}, ∀ t,
        D.flow t x ∉ (D.chart q hq).χ '' {y | morseNorm n y < r' q hq}) :
    ∃ μ : M → ℝ, ∃ ρ : ∀ p ∈ crit, ℝ,
      (∀ p hp, (D.chart p hp).r₀ < ρ p hp ∧ ρ p hp ≤ r' p hp ∧ ρ p hp ^ 2 ≤ 2 * ε) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ μ (f ⁻¹' Ioo a₂ b₂) ∧ (∀ x, μ x ∈ Icc 0 1) ∧
      (∀ x ∈ f ⁻¹' Ioo a₂ b₂, (mfderiv I 𝓘(ℝ, ℝ) μ x) (D.V x) = 0) ∧
      (∀ p hp, p ∈ P₀ → f p ∈ Ioo a₂ b₂ →
        ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < ρ p hp}, μ x = 0) ∧
      (∀ p hp, p ∈ P₁ → f p ∈ Ioo a₂ b₂ →
        ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < ρ p hp}, μ x = 1) := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : NormalSpace M := inferInstance
  have hfc : Continuous f := hf.continuous
  have hcab : c ∈ Ioo a b := ⟨ha₂.trans_lt hc.1, hc.2.trans_le hb₂⟩
  have hcI : c ∈ Icc a b := ⟨hcab.1.le, hcab.2.le⟩
  have hr₀ε : ∀ p hp, (D.chart p hp).r₀ ^ 2 ≤ 2 * ε := fun p hp => (hεr p hp).1.le
  have h3R : ∀ p hp, 3 * ε ≤ (D.chart p hp).R ^ 2 := fun p hp => by
    have h1 := (hεr p hp).2
    have h2 : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos p hp).le (D.hrm p hp).2 2
    linarith
  have h6 : ∀ p hp, 6 * ε < D.rm p hp ^ 2 := fun p hp => by linarith [(hεr p hp).2]
  have hsmall : ∀ p hp, ∀ y ∈ D.smallBall p hp, |f y - f p| < ε := by
    intro p hp y hy
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hp hy
    linarith [(hεr p hp).1]
  have hcU : ∀ p hp, ∀ y ∈ D.smallBall p hp, f y ≠ c := by
    intro p hp y hy hyc
    have h1 := hsmall p hp y hy
    rw [hyc, abs_lt] at h1
    by_cases hp' : f p ∈ Ioo a₂ b₂
    · obtain ⟨h2, h3⟩ := hcε p hp hp'
      rcases lt_trichotomy (f p) c with h | h | h
      · linarith [h2 h]
      · exact hcne p hp hp' h
      · linarith [h3 h]
    · rcases hsep p hp hp' with h | h
      · linarith [hc.1]
      · linarith [hc.2]
  have hcε' : ∀ p (_ : p ∈ crit), (f p < c → f p + ε < c) ∧ (c < f p → c < f p - ε) := by
    intro p hp
    by_cases hp' : f p ∈ Ioo a₂ b₂
    · exact hcε p hp hp'
    · rcases hsep p hp hp' with h | h
      · exact ⟨fun _ => by linarith [hc.1], fun h' => by linarith [hc.1]⟩
      · exact ⟨fun h' => by linarith [hc.2], fun _ => by linarith [hc.2]⟩
  set K₀ : Set M := ⋃ q : {q // q ∈ crit}, ⋃ (_ : q.1 ∈ P₀ ∧ f q.1 ∈ Ioo a₂ b₂),
    D.thick q.1 q.2 ε c (D.chart q.1 q.2).r₀ with hK₀
  set K₁ : Set M := ⋃ q : {q // q ∈ crit}, ⋃ (_ : q.1 ∈ P₁ ∧ f q.1 ∈ Ioo a₂ b₂),
    D.thick q.1 q.2 ε c (D.chart q.1 q.2).r₀ with hK₁
  have hK₀c : IsCompact K₀ := isCompact_iUnion fun q => isCompact_iUnion fun _ =>
    D.isCompact_thick q.1 q.2 hε (hr₀ε q.1 q.2) (h3R q.1 q.2) c
  have hK₁c : IsCompact K₁ := isCompact_iUnion fun q => isCompact_iUnion fun _ =>
    D.isCompact_thick q.1 q.2 hε (hr₀ε q.1 q.2) (h3R q.1 q.2) c
  have hKdisj : Disjoint K₀ K₁ := by
    rw [Set.disjoint_left]
    intro x hx₀ hx₁
    simp only [hK₀, hK₁, mem_iUnion, Subtype.exists, exists_prop] at hx₀ hx₁
    obtain ⟨p, hp, ⟨hpP, hpI⟩, hxp⟩ := hx₀
    obtain ⟨q, hq, ⟨hqP, hqI⟩, hxq⟩ := hx₁
    obtain ⟨t, ht⟩ := GradientLikeStrip.exists_flow_mem_closedSmallBall_of_mem_thick hf hp hε
      (hεr p hp).1 (hεr p hp).2 hxp
    obtain ⟨t', ht'⟩ := GradientLikeStrip.exists_flow_mem_closedSmallBall_of_mem_thick hf hq hε
      (hεr q hq).1 (hεr q hq).2 hxq
    have hmemp : D.flow t x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r' p hp} :=
      image_mono (fun y (hy : morseNorm n y ≤ _) => lt_of_le_of_lt hy (hr' p hp)) ht
    have hmemq : D.flow t' x ∈ (D.chart q hq).χ '' {y | morseNorm n y < r' q hq} :=
      image_mono (fun y (hy : morseNorm n y ≤ _) => lt_of_le_of_lt hy (hr' q hq)) ht'
    refine hnocommon p hp q hq hpP hqP hpI hqI _ hmemp (t' - t) ?_
    rw [GradientLikeStrip.flow_flow, add_sub_cancel]
    exact hmemq
  obtain ⟨ν, hν0, hν1, hν01⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := ⊤) hK₀c.isClosed hK₁c.isClosed hKdisj
  obtain ⟨N₀, hN₀, hKN₀, hνN₀⟩ := eventually_nhdsSet_iff_exists.1 hν0
  obtain ⟨N₁, hN₁, hKN₁, hνN₁⟩ := eventually_nhdsSet_iff_exists.1 hν1
  have hρ : ∀ p hp, ∃ ρ : ℝ, (D.chart p hp).r₀ < ρ ∧ ρ ≤ r' p hp ∧ ρ ^ 2 ≤ 2 * ε ∧
      (p ∈ P₀ → f p ∈ Ioo a₂ b₂ → D.thick p hp ε c ρ ⊆ N₀) ∧
      (p ∈ P₁ → f p ∈ Ioo a₂ b₂ → D.thick p hp ε c ρ ⊆ N₁) := by
    intro p hp
    set r₁ := min (r' p hp) (Real.sqrt (2 * ε)) with hr₁
    have hr₀r₁ : (D.chart p hp).r₀ < r₁ := by
      refine lt_min (hr' p hp) ?_
      exact (Real.lt_sqrt (D.chart p hp).hr₀.le).2 (hεr p hp).1
    have hr₁sq : r₁ ^ 2 ≤ 2 * ε := by
      have h1 : r₁ ≤ Real.sqrt (2 * ε) := min_le_right _ _
      have h2 : 0 ≤ r₁ := (D.chart p hp).hr₀.le.trans hr₀r₁.le
      calc r₁ ^ 2 ≤ Real.sqrt (2 * ε) ^ 2 := pow_le_pow_left₀ h2 h1 2
        _ = 2 * ε := Real.sq_sqrt (by positivity)
    by_cases hpI : f p ∈ Ioo a₂ b₂
    · set U : Set M := if p ∈ P₀ then N₀ else N₁ with hU
      have hUopen : IsOpen U := by
        rw [hU]; split_ifs
        · exact hN₀
        · exact hN₁
      have hsub : D.thick p hp ε c (D.chart p hp).r₀ ⊆ U := by
        rw [hU]
        split_ifs with hpP
        · refine subset_trans ?_ hKN₀
          exact subset_iUnion₂_of_subset (⟨p, hp⟩ : {q // q ∈ crit}) ⟨hpP, hpI⟩ subset_rfl
        · have hpP' : p ∈ P₁ := (hP p hp hpI).resolve_left hpP
          refine subset_trans ?_ hKN₁
          exact subset_iUnion₂_of_subset (⟨p, hp⟩ : {q // q ∈ crit}) ⟨hpP', hpI⟩ subset_rfl
      obtain ⟨ρ, hρ, hρU⟩ := D.exists_thick_subset p hp hε (D.chart p hp).hr₀.le hr₀r₁ hr₁sq
        (h3R p hp) c hUopen hsub
      have hρ0 : 0 ≤ ρ := (D.chart p hp).hr₀.le.trans hρ.1.le
      refine ⟨ρ, hρ.1, hρ.2.trans (min_le_left _ _), (pow_le_pow_left₀ hρ0 hρ.2 2).trans hr₁sq,
        fun hpP _ => ?_, fun hpP _ => ?_⟩
      · rw [hU, ite_eq_left hpP] at hρU; exact hρU
      · have hpP' : p ∉ P₀ := fun h => hdisj p h hpP
        rw [hU, ite_eq_right hpP'] at hρU; exact hρU
    · exact ⟨r₁, hr₀r₁, min_le_left _ _, hr₁sq, fun _ h => absurd h hpI, fun _ h => absurd h hpI⟩
  choose ρ hρ₀ hρr' hρε hρN₀ hρN₁ using hρ
  have hρR' : ∀ p hp, ρ p hp ≤ (D.chart p hp).R' := fun p hp => by
    have h1 : ρ p hp ^ 2 < D.rm p hp ^ 2 := by linarith [hρε p hp, (hεr p hp).2]
    have h2 : ρ p hp < D.rm p hp :=
      lt_of_pow_lt_pow_left₀ 2 (D.rm_pos p hp).le h1
    exact (h2.trans (D.rm_lt_R' p hp)).le
  have hρR : ∀ p hp, ρ p hp ≤ (D.chart p hp).R := fun p hp => by
    have h1 : ρ p hp ^ 2 < D.rm p hp ^ 2 := by linarith [hρε p hp, (hεr p hp).2]
    have h2 : ρ p hp < D.rm p hp :=
      lt_of_pow_lt_pow_left₀ 2 (D.rm_pos p hp).le h1
    exact (h2.trans_le (D.hrm p hp).2).le
  set A₀ : Set M := ⋃ q : {q // q ∈ crit}, ⋃ (_ : q.1 ∈ P₀ ∧ f q.1 ∈ Ioo a₂ b₂),
    D.throughBall q.1 q.2 (ρ q.1 q.2) c with hA₀
  set A₁ : Set M := ⋃ q : {q // q ∈ crit}, ⋃ (_ : q.1 ∈ P₁ ∧ f q.1 ∈ Ioo a₂ b₂),
    D.throughBall q.1 q.2 (ρ q.1 q.2) c with hA₁
  have hA₀open : IsOpen A₀ := isOpen_iUnion fun q => isOpen_iUnion fun _ =>
    D.isOpen_throughBall hfc q.1 q.2 (hρR' q.1 q.2) c
  have hA₁open : IsOpen A₁ := isOpen_iUnion fun q => isOpen_iUnion fun _ =>
    D.isOpen_throughBall hfc q.1 q.2 (hρR' q.1 q.2) c
  have hΩopen : IsOpen (D.regularFlowDomain c) := D.isOpen_regularFlowDomain hfc c
  have hmemA₀ : ∀ x, x ∈ A₀ ↔ ∃ p hp, (p ∈ P₀ ∧ f p ∈ Ioo a₂ b₂) ∧
      x ∈ D.throughBall p hp (ρ p hp) c := fun x => by
    simp only [hA₀, mem_iUnion, Subtype.exists, exists_prop]
  have hmemA₁ : ∀ x, x ∈ A₁ ↔ ∃ p hp, (p ∈ P₁ ∧ f p ∈ Ioo a₂ b₂) ∧
      x ∈ D.throughBall p hp (ρ p hp) c := fun x => by
    simp only [hA₁, mem_iUnion, Subtype.exists, exists_prop]
  have hA01 : ∀ x, x ∈ A₀ → x ∈ A₁ → False := by
    intro x hx₀ hx₁
    obtain ⟨p, hp, ⟨hpP, hpI⟩, -, s, -, hs⟩ := (hmemA₀ x).1 hx₀
    obtain ⟨q, hq, ⟨hqP, hqI⟩, -, s', -, hs'⟩ := (hmemA₁ x).1 hx₁
    have hmemp : D.flow s x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r' p hp} :=
      image_mono (fun y (hy : morseNorm n y < _) => lt_of_lt_of_le hy (hρr' p hp)) hs
    have hmemq : D.flow s' x ∈ (D.chart q hq).χ '' {y | morseNorm n y < r' q hq} :=
      image_mono (fun y (hy : morseNorm n y < _) => lt_of_lt_of_le hy (hρr' q hq)) hs'
    refine hnocommon p hp q hq hpP hqP hpI hqI _ hmemp (s' - s) ?_
    rw [GradientLikeStrip.flow_flow, add_sub_cancel]
    exact hmemq
  have hΩA₀ : ∀ x, x ∈ D.regularFlowDomain c → x ∈ A₀ → ν (D.π c x) = 0 := by
    intro x hx hx₀
    obtain ⟨p, hp, ⟨hpP, hpI⟩, hmem⟩ := (hmemA₀ x).1 hx₀
    exact hνN₀ _ (hρN₀ p hp hpP hpI (GradientLikeStrip.π_mem_thick hf hp hε (hρε p hp) (h6 p hp)
      hcI (hcU p hp) (hcε' p hp) hx hmem))
  have hΩA₁ : ∀ x, x ∈ D.regularFlowDomain c → x ∈ A₁ → ν (D.π c x) = 1 := by
    intro x hx hx₁
    obtain ⟨p, hp, ⟨hpP, hpI⟩, hmem⟩ := (hmemA₁ x).1 hx₁
    exact hνN₁ _ (hρN₁ p hp hpP hpI (GradientLikeStrip.π_mem_thick hf hp hε (hρε p hp) (h6 p hp)
      hcI (hcU p hp) (hcε' p hp) hx hmem))
  set μ : M → ℝ := fun x => if x ∈ A₀ then 0 else if x ∈ A₁ then 1 else
    if x ∈ D.regularFlowDomain c then ν (D.π c x) else 0 with hμ
  have hμA₀ : ∀ x ∈ A₀, μ x = 0 := fun x hx => by simp only [hμ, ite_eq_left hx]
  have hμA₁ : ∀ x ∈ A₁, μ x = 1 := fun x hx => by
    have hx₀ : x ∉ A₀ := fun h => hA01 x h hx
    simp only [hμ, ite_eq_right hx₀, ite_eq_left hx]
  have hμΩ : ∀ x ∈ D.regularFlowDomain c, μ x = ν (D.π c x) := fun x hx => by
    by_cases hx₀ : x ∈ A₀
    · rw [hμA₀ x hx₀, hΩA₀ x hx hx₀]
    by_cases hx₁ : x ∈ A₁
    · rw [hμA₁ x hx₁, hΩA₁ x hx hx₁]
    simp only [hμ, ite_eq_right hx₀, ite_eq_right hx₁, ite_eq_left hx]
  have hcover : ∀ x ∈ f ⁻¹' Ioo a₂ b₂, x ∈ A₀ ∨ x ∈ A₁ ∨ x ∈ D.regularFlowDomain c := by
    intro x hx
    have hxab : f x ∈ Ioo a b := ⟨ha₂.trans_lt hx.1, hx.2.trans_le hb₂⟩
    rcases D.mem_regularFlowDomain_or_exists_throughBall ρ hρ₀ hxab with h | ⟨p, hp, hmem⟩
    · exact Or.inr (Or.inr h)
    · have hpI : f p ∈ Ioo a₂ b₂ := by
        obtain ⟨-, s, hs, hsmem⟩ := hmem
        have hlev : f (D.flow s x) ∈ Icc (f p - ρ p hp ^ 2 / 2) (f p + ρ p hp ^ 2 / 2) :=
          (D.chart p hp).f_mem_Icc_of_mem_image_lt (hρR p hp) hsmem
        have hρε' : ρ p hp ^ 2 / 2 ≤ ε := by linarith [hρε p hp]
        have hbetween : f (D.flow s x) ∈ Ioo a₂ b₂ := by
          rw [mem_uIcc] at hs
          rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
          · have h1 := GradientLikeStrip.f_flow_le (D := D) hf x hs1
            have h2 := GradientLikeStrip.sub_le_f_flow (D := D) hf x hs1
            exact ⟨by linarith [hc.1], by linarith [hx.2]⟩
          · have h1 := GradientLikeStrip.le_f_flow_of_nonpos (D := D) hf x hs2
            have h2 := GradientLikeStrip.f_flow_le_sub_of_nonpos (D := D) hf x hs2
            exact ⟨by linarith [hx.1], by linarith [hc.2]⟩
        by_contra hnot
        rcases hsep p hp hnot with h | h
        · linarith [hlev.2, hbetween.1]
        · linarith [hlev.1, hbetween.2]
      rcases hP p hp hpI with hpP | hpP
      · exact Or.inl ((hmemA₀ x).2 ⟨p, hp, ⟨hpP, hpI⟩, hmem⟩)
      · exact Or.inr (Or.inl ((hmemA₁ x).2 ⟨p, hp, ⟨hpP, hpI⟩, hmem⟩))
  have hνπ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ν (D.π c x)) :=
    ν.contMDiff.comp (D.contMDiff_π hf c)
  have hsmooth : ∀ x ∈ f ⁻¹' Ioo a₂ b₂, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ μ x := by
    intro x hx
    rcases hcover x hx with hx₀ | hx₁ | hxΩ
    · refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hA₀open.mem_nhds hx₀] with y hy
      exact hμA₀ y hy
    · refine (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hA₁open.mem_nhds hx₁] with y hy
      exact hμA₁ y hy
    · refine (hνπ x).congr_of_eventuallyEq ?_
      filter_upwards [hΩopen.mem_nhds hxΩ] with y hy
      exact hμΩ y hy
  refine ⟨μ, ρ, fun p hp => ⟨hρ₀ p hp, hρr' p hp, hρε p hp⟩,
    fun x hx => (hsmooth x hx).contMDiffWithinAt, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [hμ]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hν01 _
    · exact ⟨le_rfl, zero_le_one⟩
  · intro x hx
    refine GradientLikeStrip.mfderiv_V_eq_zero_of_eventually_const
      ((hsmooth x hx).mdifferentiableAt (by simp)) ?_
    have hflow0 : ∀ O : Set M, IsOpen O → x ∈ O → ∀ᶠ s in 𝓝 (0 : ℝ), D.flow s x ∈ O := by
      intro O hO hxO
      have : {s : ℝ | D.flow s x ∈ O} ∈ 𝓝 (0 : ℝ) :=
        (D.continuous_flow_curve x).continuousAt.preimage_mem_nhds
          (by rw [GradientLikeStrip.flow_zero]; exact hO.mem_nhds hxO)
      exact this
    rcases hcover x hx with hx₀ | hx₁ | hxΩ
    · filter_upwards [hflow0 A₀ hA₀open hx₀] with s hs
      rw [hμA₀ _ hs, hμA₀ x hx₀]
    · filter_upwards [hflow0 A₁ hA₁open hx₁] with s hs
      rw [hμA₁ _ hs, hμA₁ x hx₁]
    · filter_upwards [hflow0 (D.regularFlowDomain c) hΩopen hxΩ] with s hs
      rw [hμΩ _ hs, hμΩ x hxΩ, GradientLikeStrip.π_flow hf hcI hcU hxΩ hs]
  · intro p hp hpP hpI x hx
    exact hμA₀ x ((hmemA₀ x).2 ⟨p, hp, ⟨hpP, hpI⟩,
      D.mem_throughBall_of_mem_ball p hp (hρR' p hp) hx⟩)
  · intro p hp hpP hpI x hx
    exact hμA₁ x ((hmemA₁ x).2 ⟨p, hp, ⟨hpP, hpI⟩,
      D.mem_throughBall_of_mem_ball p hp (hρR' p hp) hx⟩)

theorem morseNorm_le_succ_mul_norm (y : Fin n → ℝ) : morseNorm n y ≤ (n + 1) * ‖y‖ := by
  have hsq : morseNorm n y ^ 2 = ∑ i, y i ^ 2 := by
    unfold morseNorm
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have hle : ∀ i, y i ^ 2 ≤ ‖y‖ ^ 2 := fun i => by
    have := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (y i), sq_abs (y i)]
  have h1 : morseNorm n y ^ 2 ≤ n * ‖y‖ ^ 2 := by
    rw [hsq]
    calc ∑ i, y i ^ 2 ≤ ∑ _i : Fin n, ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => hle i
      _ = n * ‖y‖ ^ 2 := by simp
  have h2 : morseNorm n y ^ 2 ≤ ((n + 1) * ‖y‖) ^ 2 := by
    have : (n : ℝ) ≤ (n + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [sq_nonneg ‖y‖]
  exact (pow_le_pow_iff_left₀ (ModelField.morseNorm_nonneg y)
    (by positivity) two_ne_zero).1 h2

theorem deriv_eq_one_of_translation {ρ : ℝ → ℝ} {lo hi d : ℝ}
    (h : ∀ t ∈ Icc lo hi, ρ t = t + d) {t : ℝ} (ht : t ∈ Ioo lo hi) : deriv ρ t = 1 := by
  have hev : ρ =ᶠ[𝓝 t] fun s => s + d := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact h s (Ioo_subset_Icc_self hs)
  rw [hev.deriv_eq, deriv_add_const, deriv_id'']

theorem morseNormalForm_index_zero {k : ℕ} (hk : k ≤ n) (hk0 : k = 0) (c : ℝ) (y : Fin n → ℝ) :
    morseNormalForm hk c y = c + morseNorm n y ^ 2 / 2 := by
  have hneg : negPart hk y = 0 := by
    ext i
    have := i.isLt
    omega
  rw [morseNormalForm_split, morseNorm_sq_eq_negPart_add_posPart hk, hneg, norm_zero]
  ring

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless] {D : GradientLikeStrip I f a b crit}

omit [T2Space M] [I.Boundaryless] in
theorem f_p_le_of_mem_modelBall_index_zero {p : M} {hp : p ∈ crit} (hk : (D.chart p hp).k = 0)
    {x : M} (hx : x ∈ (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp}) : f p ≤ f x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [(D.chart p hp).hnorm y ((le_of_lt hy).trans (D.hrm p hp).2),
    morseNormalForm_index_zero _ hk]
  nlinarith [sq_nonneg (morseNorm n y)]

theorem basin_eq_of_le {p : M} {hp : p ∈ crit} (hk : (D.chart p hp).k = 0) {ρ : ℝ}
    (hρ : 0 < ρ) (hρrm : ρ ≤ D.rm p hp) :
    D.basin p hp = {x | ∃ t, 0 ≤ t ∧ D.flow t x ∈ (D.chart p hp).χ '' {y | morseNorm n y < ρ}} := by
  ext x
  constructor
  · intro hx
    rw [← captured_index_zero_eq_basin hk] at hx
    obtain ⟨T, hT⟩ := captured_eventually_small hx hρ
    refine ⟨max T 0, le_max_right _ _, ?_⟩
    exact image_mono (fun z hz => hz.1) (hT _ (le_max_left _ _))
  · rintro ⟨t, ht, hmem⟩
    exact ⟨t, ht, image_mono (fun z (hz : morseNorm n z < ρ) => hz.trans_le hρrm) hmem⟩

def bottomAt (D : GradientLikeStrip I f a b crit) (a₁ : ℝ) : Set M :=
  {x | ∃ t, 0 ≤ t ∧ f (D.flow t x) < a₁}

theorem isOpen_bottomAt (hf : Continuous f) (a₁ : ℝ) : IsOpen (D.bottomAt a₁) := by
  have : D.bottomAt a₁ = ⋃ t ∈ Ici (0 : ℝ), D.flow t ⁻¹' (f ⁻¹' Iio a₁) := by
    ext x
    simp only [bottomAt, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_Iio, mem_Ici, exists_prop]
  rw [this]
  exact isOpen_biUnion fun t _ => (isOpen_Iio.preimage hf).preimage (D.continuous_flow t)

theorem disjoint_bottomAt_basin (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a₁ : ℝ} {p : M} {hp : p ∈ crit}
    (hk : (D.chart p hp).k = 0) (hpa : a₁ ≤ f p) : Disjoint (D.bottomAt a₁) (D.basin p hp) := by
  rw [Set.disjoint_left]
  rintro x ⟨s, hs, hlt⟩ hxb
  obtain ⟨t, ht, hmem⟩ := flow_mem_basin_of_mem hk hxb s
  have h1 : f p ≤ f (D.flow t (D.flow s x)) := f_p_le_of_mem_modelBall_index_zero hk hmem
  have h2 : f (D.flow t (D.flow s x)) ≤ f (D.flow s x) := f_flow_le hf _ ht
  linarith

theorem mem_bottomAt_or_exists_basin (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a₁ b₁ : ℝ}
    (ha₁ : a ≤ a₁) (hb₁ : b₁ ≤ b)
    (hsep : ∀ p hp, f p ∉ Ioo a₁ b₁ → f p + D.rm p hp ^ 2 / 2 < a₁ ∨ b₁ < f p - D.rm p hp ^ 2 / 2)
    {x : M} (hx : f x ∈ Ioo a₁ b₁) :
    x ∈ D.bottomAt a₁ ∨ ∃ p hp, f p ∈ Ioo a₁ b₁ ∧ x ∈ D.basin p hp := by
  have hxab : f x ∈ Ioo a b := ⟨ha₁.trans_lt hx.1, hx.2.trans_le hb₁⟩
  have hcI : a₁ ∈ Icc a b := ⟨ha₁, hx.1.le.trans (hx.2.le.trans hb₁)⟩
  rcases D.mem_regularFlowDomain_or_exists_throughBall (c := a₁) (fun p hp => D.rm p hp)
    (fun p hp => D.r₀_lt_rm p hp) hxab with hΩ | ⟨p, hp, hmem⟩
  · left
    have hlev := f_flow_eq_sub_of_mem_regularFlowDomain hf hcI hΩ _ right_mem_uIcc
    have hfy : f (D.flow (f x - a₁) x) = a₁ := by rw [hlev]; ring
    have hunit : dfV I f D.V (D.flow (f x - a₁) x) = -1 := by
      refine D.unit _ (by rw [mem_preimage, hfy]; exact hcI) fun p hp hmem => ?_
      exact π_notMem_closedSmallBall hΩ p hp (D.smallBall_subset_closedSmallBall p hp hmem)
    obtain ⟨t, ht, ht0⟩ := ((eventually_f_flow_lt hf hunit).and self_mem_nhdsWithin).exists
    have ht0' : (0 : ℝ) < t := ht0
    refine ⟨f x - a₁ + t, by linarith [hx.1], ?_⟩
    rw [← flow_flow]
    rw [hfy] at ht
    exact ht
  · right
    obtain ⟨-, s, hs, hsmem⟩ := hmem
    rw [uIcc_of_le (by linarith [hx.1])] at hs
    obtain ⟨y, hy, hyx⟩ := hsmem
    have hy' : morseNorm n y < D.rm p hp := hy
    have hlev : f (D.flow s x) < f p + D.rm p hp ^ 2 / 2 ∧
        f p - D.rm p hp ^ 2 / 2 < f (D.flow s x) := by
      rw [← hyx, (D.chart p hp).hnorm y (hy'.le.trans (D.hrm p hp).2), morseNormalForm_split]
      have h1 := morseNorm_sq_eq_negPart_add_posPart (D.chart p hp).hk y
      have h2 : morseNorm n y ^ 2 < D.rm p hp ^ 2 :=
        pow_lt_pow_left₀ hy' (ModelField.morseNorm_nonneg y) two_ne_zero
      constructor <;> nlinarith [sq_nonneg ‖negPart (D.chart p hp).hk y‖,
        sq_nonneg ‖posPart (D.chart p hp).hk y‖]
    have h1 := f_flow_le (D := D) hf x hs.1
    have h2 := sub_le_f_flow (D := D) hf x hs.1
    have hpI : f p ∈ Ioo a₁ b₁ := by
      by_contra hnot
      rcases hsep p hp hnot with h | h
      · linarith [hlev.1, hs.2]
      · linarith [hlev.2, hx.2]
    exact ⟨p, hp, hpI, s, hs.1, y, hy, hyx⟩

theorem exists_basinCutoff (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a₁ b₁ : ℝ} (ha₁ : a ≤ a₁)
    (hb₁ : b₁ ≤ b)
    (hsep : ∀ p hp, f p ∉ Ioo a₁ b₁ → f p + D.rm p hp ^ 2 / 2 < a₁ ∨ b₁ < f p - D.rm p hp ^ 2 / 2)
    (hidx0 : ∀ p hp, f p ∈ Ioo a₁ b₁ → (D.chart p hp).k = 0) {p : M} (hp : p ∈ crit)
    (hpI : f p ∈ Ioo a₁ b₁) :
    ∃ μ : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ μ (f ⁻¹' Ioo a₁ b₁) ∧ (∀ x, μ x ∈ Icc 0 1) ∧
      (∀ x ∈ f ⁻¹' Ioo a₁ b₁, (mfderiv I 𝓘(ℝ, ℝ) μ x) (D.V x) = 0) ∧
      (∀ x ∈ D.basin p hp, μ x = 1) ∧
      (∀ p' hp', p' ≠ p → f p' ∈ Ioo a₁ b₁ → ∀ x ∈ D.basin p' hp', μ x = 0) ∧
      (∀ x ∈ D.bottomAt a₁, μ x = 0) := by
  classical
  have hk : (D.chart p hp).k = 0 := hidx0 p hp hpI
  set μ : M → ℝ := fun x => if x ∈ D.basin p hp then 1 else 0 with hμ
  have hμ1 : ∀ x ∈ D.basin p hp, μ x = 1 := fun x hx => by simp only [hμ, ite_eq_left hx]
  have hμ0 : ∀ x, x ∉ D.basin p hp → μ x = 0 := fun x hx => by simp only [hμ, ite_eq_right hx]
  have hbot : ∀ x ∈ D.bottomAt a₁, μ x = 0 := fun x hx =>
    hμ0 x (Set.disjoint_left.1 (disjoint_bottomAt_basin hf hk hpI.1.le) hx)
  have hother : ∀ p' hp', p' ≠ p → f p' ∈ Ioo a₁ b₁ → ∀ x ∈ D.basin p' hp', μ x = 0 := by
    intro p' hp' hne hp'I x hx
    exact hμ0 x (Set.disjoint_left.1 (disjoint_basin_basin (hidx0 p' hp' hp'I) hk hne) hx)
  have hloc : ∀ x ∈ f ⁻¹' Ioo a₁ b₁, ∀ᶠ y in 𝓝 x, μ y = μ x := by
    intro x hx
    by_cases hxb : x ∈ D.basin p hp
    · filter_upwards [(D.isOpen_basin p hp).mem_nhds hxb] with y hy
      rw [hμ1 y hy, hμ1 x hxb]
    · rcases mem_bottomAt_or_exists_basin hf ha₁ hb₁ hsep hx with hb | ⟨p', hp', hp'I, hxb'⟩
      · filter_upwards [(D.isOpen_bottomAt hf.continuous a₁).mem_nhds hb] with y hy
        rw [hbot y hy, hbot x hb]
      · have hne : p' ≠ p := fun h => hxb (h ▸ hxb')
        filter_upwards [(D.isOpen_basin p' hp').mem_nhds hxb'] with y hy
        rw [hother p' hp' hne hp'I y hy, hother p' hp' hne hp'I x hxb']
  refine ⟨μ, fun x hx => ?_, fun x => ?_, fun x hx => ?_, hμ1, hother, hbot⟩
  · exact ((contMDiffAt_const (c := μ x)).congr_of_eventuallyEq (hloc x hx)).contMDiffWithinAt
  · simp only [hμ]
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · have hev : μ =ᶠ[𝓝 x] fun _ => μ x := hloc x hx
    rw [hev.mfderiv_eq, mfderiv_const]
    rfl

end GradientLikeStrip

theorem exists_first_time {K : Set M} (hK : IsClosed K) {γ : ℝ → M} (hγ : Continuous γ)
    {t : ℝ} (h : ∃ s ∈ Icc 0 t, γ s ∈ K) :
    ∃ s₀ ∈ Icc 0 t, γ s₀ ∈ K ∧ ∀ s ∈ Ico 0 s₀, γ s ∉ K := by
  have hc : IsCompact {s | s ∈ Icc 0 t ∧ γ s ∈ K} :=
    isCompact_Icc.inter_right (hK.preimage hγ)
  obtain ⟨s₀, ⟨hs₀I, hs₀K⟩, hmin⟩ := hc.exists_isLeast h
  refine ⟨s₀, hs₀I, hs₀K, fun s hs hsK => ?_⟩
  have := hmin ⟨⟨hs.1, hs.2.le.trans hs₀I.2⟩, hsK⟩
  linarith [hs.2]

namespace MorseNormalChart

omit [IsManifold I ∞ M] in
theorem armPt_negPart_coord {q : M} (d : MorseNormalChart I f q) (hk : d.k = 1) (ε : ℝ) (i : Fin 2) :
    negPart d.hk (d.armPt hk ε i) ⟨0, by omega⟩ =
      (if i = 0 then 1 else -1) * Real.sqrt (2 * ε) := by
  unfold MorseNormalChart.armPt
  rw [ModelField.negPart_recombine, PiLp.smul_apply, PiLp.single_apply,
    ite_eq_left rfl, smul_eq_mul, mul_one]

end MorseNormalChart

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless]

theorem flow_eq_of_avoid_halfBalls {D E : GradientLikeStrip I f a b crit}
    (hV : ∀ x, x ∉ D.halfBalls → E.V x = D.V x) {x : M} {T : ℝ}
    (hmem : ∀ s ∈ Ico 0 T, D.flow s x ∉ D.halfBalls) : ∀ s ∈ Icc 0 T, E.flow s x = D.flow s x :=
  flow_eq_of_agree D.isClosed_halfBalls.isOpen_compl (fun y hy => (hV y hy).symm) hmem

theorem flow_eq_of_avoid_halfBalls' {D E : GradientLikeStrip I f a b crit}
    (hV : ∀ x, x ∉ D.halfBalls → E.V x = D.V x) {x : M} {T : ℝ}
    (hmem : ∀ s ∈ Ico 0 T, E.flow s x ∉ D.halfBalls) : ∀ s ∈ Icc 0 T, D.flow s x = E.flow s x :=
  flow_eq_of_agree D.isClosed_halfBalls.isOpen_compl (fun y hy => hV y hy) hmem

omit [T2Space M] [I.Boundaryless] in
theorem halfBall_subset_lt {D : GradientLikeStrip I f a b crit} (r : M) (hr : r ∈ crit) {ρ : ℝ}
    (hρ : (D.chart r hr).r₀ / 2 < ρ) :
    (D.chart r hr).χ '' {z | morseNorm n z ≤ (D.chart r hr).r₀ / 2} ⊆
      (D.chart r hr).χ '' {z | morseNorm n z < ρ} :=
  image_mono fun z (hz : morseNorm n z ≤ _) => hz.trans_lt hρ

theorem arm_halfBall_aux (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {D : GradientLikeStrip I f a b crit}
    {ε r' : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (hr₀r' : ∀ p hp, (D.chart p hp).r₀ < r')
    (hidx : ∀ p hp q hq, (D.chart p hp).k < (D.chart q hq).k → f p < f q)
    (harm : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
        D.flow t x ∉ (D.chart p hp).χ '' {y | morseNorm n y < r'})
    {q : M} (hq : q ∈ crit) (hkq : (D.chart q hq).k = 1) {y : Fin n → ℝ}
    (hy : y ∈ (D.chart q hq).leftModelSphere ε) {r : M} (hr : r ∈ crit)
    (hkr : (D.chart r hr).k ≠ 0) {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (hz : D.flow s₀ ((D.chart q hq).χ y) ∈
      (D.chart r hr).χ '' {z | morseNorm n z ≤ (D.chart r hr).r₀ / 2}) : False := by
  have hfx : f ((D.chart q hq).χ y) = f q - ε := f_chart_of_mem_leftModelSphere' hq (hεr q hq).2 hy
  have hfz : f (D.flow s₀ ((D.chart q hq).χ y)) ≤ f q - ε := by
    rw [← hfx]; exact f_flow_le hf _ hs₀
  have hr₀ := (D.chart r hr).hr₀
  have hlev := (D.chart r hr).f_mem_Icc_of_mem_image_le
    (by linarith [D.r₀_lt_R r hr]) hz
  have hr₀sq : (D.chart r hr).r₀ ^ 2 / 8 < ε / 4 := by linarith [(hεr r hr).1]
  have hhalf : ((D.chart r hr).r₀ / 2) ^ 2 / 2 = (D.chart r hr).r₀ ^ 2 / 8 := by ring
  rw [hhalf] at hlev
  have hfr : f r < f q := by linarith [hlev.1]
  rcases Nat.lt_or_ge (D.chart r hr).k 2 with hk1 | hk2
  · have hk1' : (D.chart r hr).k = 1 := by omega
    exact harm r hr q hq hk1' hkq hfr _ ⟨y, hy, rfl⟩ s₀ hs₀
      (halfBall_subset_lt r hr (by linarith [hr₀r' r hr]) hz)
  · have := hidx q hq r hr (by rw [hkq]; exact hk2)
    linarith

theorem mem_basin_iff_of_shrink (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {D E : GradientLikeStrip I f a b crit}
    (hχ : ∀ r hr, (E.chart r hr).χ = (D.chart r hr).χ)
    (hk : ∀ r hr, (E.chart r hr).k = (D.chart r hr).k) (hrm : ∀ r hr, E.rm r hr = D.rm r hr)
    (hV : ∀ x, x ∉ D.halfBalls → E.V x = D.V x) {ε r' : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (hr₀r' : ∀ p hp, (D.chart p hp).r₀ < r')
    (hidx : ∀ p hp q hq, (D.chart p hp).k < (D.chart q hq).k → f p < f q)
    (harm : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
        D.flow t x ∉ (D.chart p hp).χ '' {y | morseNorm n y < r'})
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hkp : (D.chart p hp).k = 0)
    (hkq : (D.chart q hq).k = 1) {y : Fin n → ℝ} (hy : y ∈ (D.chart q hq).leftModelSphere ε) :
    (D.chart q hq).χ y ∈ D.basin p hp ↔ (D.chart q hq).χ y ∈ E.basin p hp := by
  set x := (D.chart q hq).χ y with hxdef
  set B := (D.chart p hp).χ '' {z | morseNorm n z < D.rm p hp} with hB
  have hEB : (E.chart p hp).χ '' {z | morseNorm n z < E.rm p hp} = B := by
    rw [hB, hχ, hrm]
  have hEkp : (E.chart p hp).k = 0 := by rw [hk]; exact hkp
  have hhalf : ∀ r hr, (D.chart r hr).r₀ / 2 < D.rm r hr := fun r hr => by
    linarith [D.r₀_lt_rm r hr, (D.chart r hr).hr₀]
  have hfBp : ∀ w ∈ B, f p ≤ f w := fun w hw => f_p_le_of_mem_modelBall_index_zero hkp hw
  have hmodel : ∀ r hr, ∀ w ∈ (D.chart r hr).χ '' {z | morseNorm n z ≤ (D.chart r hr).r₀ / 2},
      w ∈ (D.chart r hr).χ '' {z | morseNorm n z < D.rm r hr} :=
    fun r hr w hw => halfBall_subset_lt r hr (hhalf r hr) hw
  have hdisjB : ∀ r hr, r ≠ p → ∀ w ∈ (D.chart r hr).χ '' {z | morseNorm n z < D.rm r hr},
      w ∉ B := by
    intro r hr hrp w hw hwB
    exact Set.disjoint_left.1 (D.disjoint r hr p hp hrp) (D.modelBall_subset_image_ball r hr hw)
      (D.modelBall_subset_image_ball p hp hwB)
  constructor
  · rintro ⟨t, ht, htB⟩
    change ∃ t', 0 ≤ t' ∧ E.flow t' x ∈ (E.chart p hp).χ '' {z | morseNorm n z < E.rm p hp}
    rw [hEB]
    by_cases hK : ∃ s ∈ Icc 0 t, D.flow s x ∈ D.halfBalls
    · obtain ⟨s₀, hs₀I, hs₀K, hfirst⟩ :=
        exists_first_time D.isClosed_halfBalls (D.continuous_flow_curve x) hK
      have hEq : E.flow s₀ x = D.flow s₀ x :=
        flow_eq_of_avoid_halfBalls hV (fun s hs => hfirst s hs) s₀ (right_mem_Icc.2 hs₀I.1)
      obtain ⟨r, hr, hzr⟩ := D.mem_halfBalls_iff.1 hs₀K
      by_cases hrp : r = p
      · subst hrp
        exact ⟨s₀, hs₀I.1, by rw [hEq]; exact hmodel r hr _ hzr⟩
      · exfalso
        rcases Nat.eq_zero_or_pos (D.chart r hr).k with hk0 | hkpos
        · have h1 := flow_mem_modelBall_of_index_zero hk0 (hmodel r hr _ hzr) (t := t - s₀)
            (by linarith [hs₀I.2])
          rw [flow_flow, add_sub_cancel] at h1
          exact hdisjB r hr hrp _ h1 htB
        · exact arm_halfBall_aux hf hε hεr hr₀r' hidx harm hq hkq hy hr (by omega) hs₀I.1 hzr
    · push Not at hK
      have hEq : E.flow t x = D.flow t x :=
        flow_eq_of_avoid_halfBalls hV (fun s hs => hK s (Ico_subset_Icc_self hs)) t
          (right_mem_Icc.2 ht)
      exact ⟨t, ht, by rw [hEq]; exact htB⟩
  · rintro ⟨t, ht, htB⟩
    rw [hEB] at htB
    by_cases hK : ∃ s ∈ Icc 0 t, E.flow s x ∈ D.halfBalls
    · obtain ⟨s₀, hs₀I, hs₀K, hfirst⟩ :=
        exists_first_time D.isClosed_halfBalls (E.continuous_flow_curve x) hK
      have hEq : D.flow s₀ x = E.flow s₀ x :=
        flow_eq_of_avoid_halfBalls' hV (fun s hs => hfirst s hs) s₀ (right_mem_Icc.2 hs₀I.1)
      obtain ⟨r, hr, hzr⟩ := D.mem_halfBalls_iff.1 hs₀K
      by_cases hrp : r = p
      · subst hrp
        exact ⟨s₀, hs₀I.1, by rw [hEq]; exact hmodel r hr _ hzr⟩
      · exfalso
        rcases Nat.eq_zero_or_pos (D.chart r hr).k with hk0 | hkpos
        · have hEk : (E.chart r hr).k = 0 := by rw [hk]; exact hk0
          have hzE : E.flow s₀ x ∈ (E.chart r hr).χ '' {z | morseNorm n z < E.rm r hr} := by
            rw [hχ, hrm]; exact hmodel r hr _ hzr
          have h1 := flow_mem_modelBall_of_index_zero hEk hzE (t := t - s₀) (by linarith [hs₀I.2])
          rw [flow_flow, add_sub_cancel, hχ, hrm] at h1
          exact hdisjB r hr hrp _ h1 htB
        · exact arm_halfBall_aux hf hε hεr hr₀r' hidx harm hq hkq hy hr (by omega) hs₀I.1
            (by rw [hEq]; exact hzr)
    · push Not at hK
      have hEq : D.flow t x = E.flow t x :=
        flow_eq_of_avoid_halfBalls' hV (fun s hs => hK s (Ico_subset_Icc_self hs)) t
          (right_mem_Icc.2 ht)
      exact ⟨t, ht, by rw [hEq]; exact htB⟩

omit [T2Space M] [I.Boundaryless] in
theorem mfderiv_V_eq_zero_of_shrink {D E : GradientLikeStrip I f a b crit}
    (hV : ∀ x, x ∉ D.halfBalls → E.V x = D.V x) {μ : M → ℝ} {a₂ b₂ : ℝ}
    (hμV : ∀ x ∈ f ⁻¹' Ioo a₂ b₂, (mfderiv I 𝓘(ℝ, ℝ) μ x) (D.V x) = 0)
    (hloc : ∀ r hr, f r ∈ Ioo a₂ b₂ →
      ∀ x ∈ (D.chart r hr).χ '' {z | morseNorm n z ≤ (D.chart r hr).r₀ / 2},
        ∀ᶠ y in 𝓝 x, μ y = μ x)
    (hout : ∀ r hr, f r ∉ Ioo a₂ b₂ →
      ∀ x ∈ (D.chart r hr).χ '' {z | morseNorm n z ≤ (D.chart r hr).r₀ / 2}, f x ∉ Ioo a₂ b₂) :
    ∀ x ∈ f ⁻¹' Ioo a₂ b₂, (mfderiv I 𝓘(ℝ, ℝ) μ x) (E.V x) = 0 := by
  intro x hx
  by_cases hxK : x ∈ D.halfBalls
  · obtain ⟨r, hr, hxr⟩ := D.mem_halfBalls_iff.1 hxK
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · have hev : μ =ᶠ[𝓝 x] fun _ => μ x := hloc r hr hrI x hxr
      rw [hev.mfderiv_eq, mfderiv_const]
      rfl
    · exact absurd hx (hout r hr hrI x hxr)
  · rw [hV x hxK]
    exact hμV x hx

theorem exists_flow_armPt_eq (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {D : GradientLikeStrip I f a b crit}
    {q : M} (hq : q ∈ crit) (hk : (D.chart q hq).k = 1) {ε ε' : ℝ} (hε' : 0 < ε')
    (hε'ε : ε' ≤ ε) (hrm : 2 * ε < D.rm q hq ^ 2) (i : Fin 2) :
    ∃ t, 0 ≤ t ∧ D.flow t ((D.chart q hq).χ ((D.chart q hq).armPt hk ε' i)) =
      (D.chart q hq).χ ((D.chart q hq).armPt hk ε i) := by
  set d := D.chart q hq with hd
  have hε : 0 < ε := hε'.trans_le hε'ε
  set y := d.armPt hk ε' i with hy
  have hymem : y ∈ d.leftModelSphere ε' := d.armPt_mem_leftModelSphere hk hε'.le i
  have hyv : posPart d.hk y = 0 := hymem.1
  have hyu : ‖negPart d.hk y‖ ^ 2 = 2 * ε' := hymem.2
  have hu0 : negPart d.hk y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hyu
    linarith
  have hrm0 := D.rm_pos q hq
  have hball : 2 * ε + 2 * ‖posPart d.hk y‖ ^ 2 < D.rm q hq ^ 2 := by
    rw [hyv, norm_zero]; linarith
  have hlevel : f q - ε ≤ morseNormalForm d.hk (f q) y := by
    rw [d.nf_of_mem_leftModelSphere hymem]; linarith
  obtain ⟨t, ht0, hft, hstay, -⟩ := exists_exit_desc hf hq hε hball hu0 hlevel
  rw [hyv, norm_zero] at hstay
  set x := d.χ y with hx
  have hSsub : {z : Fin n → ℝ | morseNorm n z ^ 2 ≤ 2 * ε + 2 * 0 ^ 2} ⊆
      {z | morseNorm n z < D.rm q hq} := fun z hz => by
    have hz' : morseNorm n z ^ 2 ≤ 2 * ε + 2 * 0 ^ 2 := hz
    exact lt_of_pow_lt_pow_left₀ 2 hrm0.le (by linarith)
  have hODE : ∀ s ∈ Icc 0 t, D.flow s x ∈ d.χ '' {z | morseNorm n z < D.rm q hq} :=
    fun s hs => image_mono hSsub (hstay s hs)
  have hγ := hasDerivAt_symm_flow_Icc hq hODE
  have hyrm : morseNorm n y < D.rm q hq := by
    apply lt_of_pow_lt_pow_left₀ 2 hrm0.le
    rw [morseNorm_sq_eq_negPart_add_posPart d.hk, hyu, hyv, norm_zero]
    linarith
  have hyR : morseNorm n y ≤ d.R := hyrm.le.trans (D.hrm q hq).2
  have hγ0 : d.χ.symm (D.flow 0 x) = y := by
    rw [flow_zero, hx, d.χ.left_inv (d.hsrc y hyR)]
  set z := d.χ.symm (D.flow t x) with hz
  have htO := hODE t (right_mem_Icc.2 ht0)
  have hzrm : morseNorm n z < D.rm q hq :=
    d.symm_mem (d.lt_subset_ball (D.rm_lt_R' q hq).le) htO
  have hzR : morseNorm n z ≤ d.R := hzrm.le.trans (D.hrm q hq).2
  have hzx : d.χ z = D.flow t x := d.symm_image_eq (D.modelBall_subset_image_ball q hq htO)
  have hzv : posPart d.hk z = 0 := by
    have hanti := ModelField.normSq_posPart_antitoneOn d.hk d.hr₀ hγ (left_mem_Icc.2 ht0)
      (right_mem_Icc.2 ht0) ht0
    beta_reduce at hanti
    rw [hγ0, hyv, norm_zero] at hanti
    have h0 : ‖posPart d.hk z‖ = 0 := by nlinarith [norm_nonneg (posPart d.hk z)]
    exact norm_eq_zero.1 h0
  have hzu : ‖negPart d.hk z‖ ^ 2 = 2 * ε := by
    have hfe : f (D.flow t x) = morseNormalForm d.hk (f q) z :=
      d.f_eq_nf_symm (D.modelBall_subset_image_le q hq htO)
    rw [hft, morseNormalForm_split, hzv, norm_zero] at hfe
    linarith
  have hzS : z ∈ d.leftModelSphere ε := ⟨hzv, hzu⟩
  have hi : ∀ j : Fin d.k, j = ⟨0, by omega⟩ := fun j => Fin.ext (by have := j.isLt; omega)
  set u : ℝ → ℝ := fun s => negPart d.hk (d.χ.symm (D.flow s x)) ⟨0, by omega⟩ with hu
  have huc : ContinuousOn u (Icc 0 t) := by
    have h1 : ContinuousOn (fun s => d.χ.symm (D.flow s x)) (Icc 0 t) := by
      refine ContinuousOn.comp (g := d.χ.symm) (d.hχsymm.continuousOn) ?_ ?_
      · exact (D.continuous_flow_curve x).continuousOn
      · intro s hs
        exact D.modelBall_subset_image_ball q hq (hODE s hs)
    have h2 : Continuous fun w : Fin n → ℝ => negPart d.hk w ⟨0, by omega⟩ :=
      (continuous_apply _).comp ((PiLp.continuous_ofLp (p := 2)
        (β := fun _ : Fin d.k => ℝ)).comp d.continuous_negPart)
    exact h2.comp_continuousOn h1
  have hnz : ∀ s ∈ Icc 0 t, u s ≠ 0 := by
    intro s hs hus
    have hneg : negPart d.hk (d.χ.symm (D.flow s x)) = 0 := by
      ext j
      rw [hi j]
      exact hus
    have hγ' : ∀ s' ∈ Icc s t, HasDerivAt (fun s => d.χ.symm (D.flow s x))
        (ModelField.modelField d.k d.r₀ (d.χ.symm (D.flow s' x))) s' :=
      fun s' hs' => hγ s' ⟨hs.1.trans hs'.1, hs'.2⟩
    have := ModelField.negPart_eq_zero_of_left d.hk d.hr₀ hγ' hneg hs.2 t (right_mem_Icc.2 hs.2)
    rw [← hz] at this
    rw [this, norm_zero] at hzu
    linarith
  have hu0' : u 0 = (if i = 0 then 1 else -1) * Real.sqrt (2 * ε') := by
    change negPart d.hk (d.χ.symm (D.flow 0 x)) ⟨0, by omega⟩ = _
    rw [hγ0]
    exact d.armPt_negPart_coord hk ε' i
  have hs' : 0 < Real.sqrt (2 * ε') := Real.sqrt_pos.2 (by linarith)
  have hs : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.2 (by linarith)
  rcases d.eq_armPt_of_mem_leftModelSphere hk hε hzS with hz0 | hz1
  · have hut : u t = Real.sqrt (2 * ε) := by
      change negPart d.hk z ⟨0, by omega⟩ = _
      rw [hz0, d.armPt_negPart_coord hk ε 0, ite_eq_left rfl, one_mul]
    have hi0 : i = 0 := by
      by_contra hi
      have hi1 : i = 1 := by fin_cases i <;> first | rfl | exact absurd rfl hi
      have hu0neg : u 0 < 0 := by
        rw [hu0', hi1, ite_eq_right (by decide), neg_one_mul]
        exact neg_lt_zero.2 hs'
      have hutpos : 0 < u t := by rw [hut]; exact hs
      obtain ⟨s, hsI, hs0⟩ := intermediate_value_Icc ht0 huc ⟨hu0neg.le, hutpos.le⟩
      exact hnz s hsI hs0
    refine ⟨t, ht0, ?_⟩
    rw [← hzx, hz0, hi0]
  · have hut : u t = -Real.sqrt (2 * ε) := by
      change negPart d.hk z ⟨0, by omega⟩ = _
      rw [hz1, d.armPt_negPart_coord hk ε 1, ite_eq_right (by decide), neg_one_mul]
    have hi1 : i = 1 := by
      by_contra hi
      have hi0 : i = 0 := by fin_cases i <;> first | rfl | exact absurd rfl hi
      have hu0pos : 0 < u 0 := by
        rw [hu0', hi0, ite_eq_left rfl, one_mul]
        exact hs'
      have hutneg : u t < 0 := by rw [hut]; exact neg_lt_zero.2 hs
      obtain ⟨s, hsI, hs0⟩ := intermediate_value_Icc' ht0 huc ⟨hutneg.le, hu0pos.le⟩
      exact hnz s hsI hs0
    refine ⟨t, ht0, ?_⟩
    rw [← hzx, hz1, hi1]

theorem goodPair_of_le (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {D : GradientLikeStrip I f a b crit}
    {ε ε' : ℝ} (hε' : 0 < ε') (hε'ε : ε' ≤ ε) {p q : M} {hp : p ∈ crit} {hq : q ∈ crit}
    (hrm : 2 * ε < D.rm q hq ^ 2) (h : goodPair D ε p q hp hq) : goodPair D ε' p q hp hq := by
  obtain ⟨hkp, hk, i, hi, hi'⟩ := h
  refine ⟨hkp, hk, i, ?_, ?_⟩
  · obtain ⟨t, -, ht⟩ := exists_flow_armPt_eq hf hq hk hε' hε'ε hrm i
    rw [← flow_mem_basin_iff hkp t, ht]
    exact hi
  · obtain ⟨t, -, ht⟩ := exists_flow_armPt_eq hf hq hk hε' hε'ε hrm (i + 1)
    rw [← flow_mem_basin_iff hkp t, ht]
    exact hi'

end GradientLikeStrip

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless]

theorem flow_eq_of_V_eq {g : M → ℝ} {crit' : Finset M} {a' b' : ℝ}
    (D : GradientLikeStrip I f a b crit) (D' : GradientLikeStrip I g a' b' crit')
    (hV : ∀ x, D'.V x = D.V x) (t : ℝ) (x : M) : D'.flow t x = D.flow t x := by
  have hV' : D'.V = D.V := funext hV
  have hγ : IsMIntegralCurve (fun s => D'.flow s x) D.V := by
    rw [← hV']; exact D'.isMIntegralCurve_flow x
  have := integralCurve_eq_of_agree D.V D.smooth_one hγ (D.isMIntegralCurve_flow x) (t₀ := 0)
    (by simp)
  exact congrFun this t

omit [T2Space M] [I.Boundaryless] in
theorem exists_restrict (D : GradientLikeStrip I f a b crit) {a' b' : ℝ} (ha : a ≤ a')
    (hb : b' ≤ b) (crit' : Finset M) (hsub : ∀ r ∈ crit', r ∈ crit)
    (hother : ∀ r hr, r ∉ crit' → ∀ y ∈ D.smallBall r hr, f y ∉ Icc a' b')
    (Rn R'n rmn : ∀ r ∈ crit', ℝ)
    (hRn : ∀ r hr, 4 * (D.chart r (hsub r hr)).r₀ < Rn r hr ∧ Rn r hr ≤ (D.chart r (hsub r hr)).R)
    (hR'n : ∀ r hr, Rn r hr < R'n r hr ∧ R'n r hr ≤ (D.chart r (hsub r hr)).R')
    (hrmn : ∀ r hr, 2 * (D.chart r (hsub r hr)).r₀ < rmn r hr ∧ rmn r hr ≤ D.rm r (hsub r hr) ∧
      rmn r hr ≤ Rn r hr)
    (hinStrip : ∀ r hr, (D.chart r (hsub r hr)).χ '' Metric.ball 0 (R'n r hr) ⊆ f ⁻¹' Ioo a' b')
    (hnotcrit : ∀ x, f x ∈ Icc a' b' → x ∉ crit' → x ∉ crit) :
    ∃ D' : GradientLikeStrip I f a' b' crit',
      (∀ r hr, (D'.chart r hr).χ = (D.chart r (hsub r hr)).χ ∧
        (D'.chart r hr).k = (D.chart r (hsub r hr)).k ∧
        (D'.chart r hr).r₀ = (D.chart r (hsub r hr)).r₀ ∧ (D'.chart r hr).R = Rn r hr ∧
        (D'.chart r hr).R' = R'n r hr) ∧
      (∀ r hr, D'.rm r hr = rmn r hr) ∧ (∀ x, D'.V x = D.V x) := by
  refine ⟨{ V := D.V
            smooth := D.smooth
            compact := D.compact
            rate := D.rate
            chart := fun r hr =>
              { k := (D.chart r (hsub r hr)).k
                hk := (D.chart r (hsub r hr)).hk
                hkidx := (D.chart r (hsub r hr)).hkidx
                χ := (D.chart r (hsub r hr)).χ
                R := Rn r hr
                R' := R'n r hr
                r₀ := (D.chart r (hsub r hr)).r₀
                hr₀ := (D.chart r (hsub r hr)).hr₀
                hr₀R := (hRn r hr).1
                hRR' := (hR'n r hr).1
                hχ0 := (D.chart r (hsub r hr)).hχ0
                hball := (Metric.ball_subset_ball (hR'n r hr).2).trans (D.chart r (hsub r hr)).hball
                hsrc := fun y hy => (D.chart r (hsub r hr)).hsrc y (hy.trans (hRn r hr).2)
                hnorm := fun y hy => (D.chart r (hsub r hr)).hnorm y (hy.trans (hRn r hr).2)
                hχ := (D.chart r (hsub r hr)).hχ.mono (Metric.ball_subset_ball (hR'n r hr).2)
                hχsymm := (D.chart r (hsub r hr)).hχsymm.mono
                  (image_mono (Metric.ball_subset_ball (hR'n r hr).2)) }
            disjoint := fun r hr s hs hrs => by
              refine (D.disjoint r (hsub r hr) s (hsub s hs) hrs).mono ?_ ?_
              · exact image_mono (Metric.ball_subset_ball (hR'n r hr).2)
              · exact image_mono (Metric.ball_subset_ball (hR'n s hs).2)
            inStrip := fun r hr => hinStrip r hr
            unit := fun x hx hxB => by
              refine D.unit x ⟨ha.trans hx.1, hx.2.trans hb⟩ fun r hr hmem => ?_
              by_cases hr' : r ∈ crit'
              · exact hxB r hr' hmem
              · exact hother r hr hr' x hmem hx
            neg := fun x hx hxc =>
              D.neg x ⟨ha.trans hx.1, hx.2.trans hb⟩ (hnotcrit x hx hxc)
            rm := rmn
            hrm := fun r hr => ⟨(hrmn r hr).1, (hrmn r hr).2.2⟩
            model := fun r hr y hy =>
              D.model r (hsub r hr) y (hy.trans_le (hrmn r hr).2.1) },
    fun r hr => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr => rfl, fun x => rfl⟩

end GradientLikeStrip

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless]

theorem goodPair_congr {g : M → ℝ} {a' b' : ℝ} {crit' : Finset M}
    {D : GradientLikeStrip I f a b crit} {D' : GradientLikeStrip I g a' b' crit'} {ε : ℝ}
    {p q : M} {hp : p ∈ crit} {hq : q ∈ crit} {hp' : p ∈ crit'} {hq' : q ∈ crit'}
    (hχq : (D'.chart q hq').χ = (D.chart q hq).χ) (hkp : (D'.chart p hp').k = (D.chart p hp).k)
    (hkq : (D'.chart q hq').k = (D.chart q hq).k) (hbasin : D'.basin p hp' = D.basin p hp)
    (h : goodPair D ε p q hp hq) : goodPair D' ε p q hp' hq' := by
  obtain ⟨hk0, hk, i, h1, h2⟩ := h
  refine ⟨by rw [hkp]; exact hk0, by rw [hkq]; exact hk, i, ?_, ?_⟩
  · rw [hχq, (D'.chart q hq').armPt_eq_ite, ← (D.chart q hq).armPt_eq_ite hk, hbasin]
    exact h1
  · rw [hχq, (D'.chart q hq').armPt_eq_ite, ← (D.chart q hq).armPt_eq_ite hk, hbasin]
    exact h2

theorem portPrivate_12a41ca5_exists_small_cancellation_scale (n : ℕ) {ε a b : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      128 * (n + 1) ^ 2 * ε' < a ^ 2 ∧
      32 * (n + 1) ^ 2 * ε' < (b / 2) ^ 2 := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  set Ap : ℝ := a / (4 * (n + 1)) with hAp
  set Aq : ℝ := b / (4 * (n + 1)) with hAq
  have hAp0 : 0 < Ap := div_pos ha (by positivity)
  have hAq0 : 0 < Aq := div_pos hb (by positivity)
  let ε' : ℝ := min ε (min (Ap ^ 2 / 16) (Aq ^ 2 / 16))
  have hε'0 : 0 < ε' := lt_min hε (lt_min (by positivity) (by positivity))
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'p : ε' ≤ Ap ^ 2 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hε'q : ε' ≤ Aq ^ 2 / 16 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε', hε'0, hε'ε, ?_, ?_⟩
  · have h1 : Ap ^ 2 * (16 * (n + 1) ^ 2) = a ^ 2 := by
      rw [hAp]; field_simp; ring
    nlinarith [pow_pos ha 2, pow_pos hn1 2]
  · have h1 : Aq ^ 2 * (16 * (n + 1) ^ 2) = b ^ 2 := by
      rw [hAq]; field_simp; ring
    nlinarith [pow_pos hb 2, pow_pos hn1 2]

theorem exists_lower_q [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {ε r' : ℝ} (hε : 0 < ε) (hr'ε : r' ^ 2 < ε)
    (hD : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 24 * ε < D.rm p hp ^ 2 ∧
      (D.chart p hp).r₀ < r')
    (hE2 : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r'}, ∀ t,
        D.flow t x ∉ (D.chart q hq).χ '' {y | morseNorm n y < r'})
    (hE3 : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
        D.flow t x ∉ (D.chart p hp).χ '' {y | morseNorm n y < r'})
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hkp : (D.chart p hp).k = 0)
    (hkq : (D.chart q hq).k = 1) (hgood : goodPair D ε p q hp hq)
    {a₂ b₂ a₃ b₃ y₂ : ℝ} (ha₂ : a ≤ a₂) (hb₂ : b₂ ≤ b) (h₃ : a₂ < a₃ ∧ b₃ < b₂)
    (hidx1 : ∀ r hr, f r ∈ Ioo a₂ b₂ → (D.chart r hr).k = 1)
    (hsep : ∀ r hr, f r ∉ Ioo a₂ b₂ →
      f r + (D.chart r hr).R ^ 2 / 2 + ε < a₂ ∨ b₂ + ε < f r - (D.chart r hr).R ^ 2 / 2)
    (hqI : f q ∈ Ioo a₂ b₂) (hy₂ : a₃ + ε < y₂ ∧ y₂ < f q) (hq₃ : f q + ε < b₃)
    (hreg : ∀ x, f x = a₂ ∨ f x = b₂ → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    {c : ℝ} (hc : c ∈ Ioo a₂ b₂) (hcr : ∀ r ∈ crit, f r ∈ Ioo a₂ b₂ → c < f r - ε)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ g₁ : M → ℝ, ∃ D₂ : GradientLikeStrip I g₁ a b crit, ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ModifiedWithin f a b g₁ ∧ MorseStrip I g₁ a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₁ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g₁ x = morseIndex I f x) ∧
      g₁ q = y₂ ∧ (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ q → g₁ x = f x) ∧
      (∀ r hr, (D₂.chart r hr).χ = (D.chart r hr).χ ∧ (D₂.chart r hr).k = (D.chart r hr).k ∧
        (D₂.chart r hr).R ≤ (D.chart r hr).R ∧ (D₂.chart r hr).R' = (D.chart r hr).R') ∧
      (∀ r hr, (D₂.chart r hr).r₀ ≤ σ ∧ (D₂.chart r hr).r₀ ^ 2 < 2 * ε' ∧
        16 * (n + 1) * (D₂.chart r hr).r₀ < D₂.rm r hr) ∧
      (∀ r hr, f r ∉ Ioo a₂ b₂ → D₂.rm r hr = D.rm r hr) ∧
      (∀ r hr, D₂.rm r hr ≤ D.rm r hr) ∧
      128 * (n + 1) ^ 2 * ε' < D.rm p hp ^ 2 ∧ 32 * (n + 1) ^ 2 * ε' < D₂.rm q hq ^ 2 ∧
      (D₂.chart q hq).R ≤ D₂.rm q hq ∧ goodPair D₂ ε' p q hp hq := by
  classical
  have hfs := hf.smooth
  have hidx : ∀ r hr s hs, (D.chart r hr).k < (D.chart s hs).k → f r < f s :=
    k_lt_imp_f_lt_of_selfIndexing D hsi hcrit
  have hεr : ∀ r hr, (D.chart r hr).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm r hr ^ 2 := fun r hr =>
    ⟨(hD r hr).1, by linarith [(hD r hr).2.1]⟩
  have hr'0 : 0 < r' := (D.chart p hp).hr₀.trans (hD p hp).2.2
  have hr'rm : ∀ r hr, r' < D.rm r hr := fun r hr => by
    apply lt_of_pow_lt_pow_left₀ 2 (D.rm_pos r hr).le
    linarith [(hD r hr).2.1]
  have hpI : f p ∉ Ioo a₂ b₂ := fun h => by
    have := hidx1 p hp h; rw [hkp] at this; exact zero_ne_one this
  have hnocommon : ∀ r hr q' hq', r ∈ {x : M | x ≠ q} → q' ∈ ({q} : Set M) →
      f r ∈ Ioo a₂ b₂ → f q' ∈ Ioo a₂ b₂ →
      ∀ x ∈ (D.chart r hr).χ '' {y | morseNorm n y < r'}, ∀ t,
        D.flow t x ∉ (D.chart q' hq').χ '' {y | morseNorm n y < r'} := by
    intro r hr q' hq' hrq hq'q hrI hq'I x hx t hmem
    rw [mem_singleton_iff] at hq'q
    subst hq'q
    have hrq' : r ≠ q' := hrq
    have hkr := hidx1 r hr hrI
    have hkq' := hidx1 q' hq' hq'I
    rcases lt_or_gt_of_ne (fun h : f r = f q' =>
        hrq' (hinj ((hcrit r).1 hr) ((hcrit q').1 hq') h)) with hlt | hlt
    · exact hE2 r hr q' hq' hkr hkq' hlt x hx t hmem
    · refine hE2 q' hq' r hr hkq' hkr hlt _ hmem (-t) ?_
      rw [flow_neg_flow]
      exact hx
  obtain ⟨μ, ρ, hρ, hμ, hμ01, hμV, hμ0, hμ1⟩ := exists_trajectoryCutoff' hfs D ha₂ hb₂
    {x | x ≠ q} {q} (fun r _ _ => by by_cases h : r = q <;> simp [h])
    (fun r h1 h2 => h1 (mem_singleton_iff.1 h2)) hc hε hεr
    (fun r hr hrI => by
      rcases hsep r hr hrI with h | h
      · left; nlinarith [sq_nonneg (D.chart r hr).R]
      · right; nlinarith [sq_nonneg (D.chart r hr).R])
    (fun r hr hrI => ⟨fun h => by linarith [hcr r hr hrI], fun _ => hcr r hr hrI⟩)
    (fun r hr hrI => by linarith [hcr r hr hrI]) (fun _ _ => r') (fun r hr => (hD r hr).2.2)
    hnocommon
  have hρq : (D.chart q hq).r₀ < ρ q hq ∧ ρ q hq ≤ r' ∧ ρ q hq ^ 2 ≤ 2 * ε := hρ q hq
  have hρpos : ∀ r hr, 0 < ρ r hr := fun r hr => (D.chart r hr).hr₀.trans (hρ r hr).1
  have hρrm : ∀ r hr, ρ r hr < D.rm r hr := fun r hr => (hρ r hr).2.1.trans_lt (hr'rm r hr)
  have hρR : ∀ r hr, ρ r hr ≤ (D.chart r hr).R := fun r hr =>
    (hρrm r hr).le.trans (D.hrm r hr).2
  have hρR' : ∀ r hr, ρ r hr ≤ (D.chart r hr).R' := fun r hr =>
    (hρrm r hr).le.trans (D.rm_lt_R' r hr).le
  obtain ⟨ε', hε'0, hε'ε, hε'p', hε'q'⟩ :=
    portPrivate_12a41ca5_exists_small_cancellation_scale n hε (D.rm_pos p hp) (hρpos q hq)
  obtain ⟨ρ₁, hρ₁, hρ₁le⟩ := exists_pos_le_forall_finset crit.attach
    (fun r => min (D.chart r.1 r.2).r₀ (min (ρ r.1 r.2 / (64 * (n + 1)))
      (D.rm r.1 r.2 / (64 * (n + 1))))) (fun r _ => lt_min (D.chart r.1 r.2).hr₀
      (lt_min (by have := hρpos r.1 r.2; positivity) (by have := D.rm_pos r.1 r.2; positivity)))
  set ρs : ℝ := min ρ₁ (min σ (Real.sqrt ε')) with hρsdef
  have hρs : 0 < ρs := lt_min hρ₁ (lt_min hσ (Real.sqrt_pos.2 hε'0))
  have hρsr₀ : ∀ r hr, ρs ≤ (D.chart r hr).r₀ := fun r hr =>
    (min_le_left _ _).trans ((hρ₁le ⟨r, hr⟩ (Finset.mem_attach _ _)).trans (min_le_left _ _))
  have hρsρ : ∀ r hr, ρs ≤ ρ r hr / (64 * (n + 1)) := fun r hr =>
    (min_le_left _ _).trans ((hρ₁le ⟨r, hr⟩ (Finset.mem_attach _ _)).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hρsrm : ∀ r hr, ρs ≤ D.rm r hr / (64 * (n + 1)) := fun r hr =>
    (min_le_left _ _).trans ((hρ₁le ⟨r, hr⟩ (Finset.mem_attach _ _)).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hρsσ : ρs ≤ σ := (min_le_right _ _).trans (min_le_left _ _)
  have hρsε' : ρs ^ 2 ≤ ε' := by
    have h1 : ρs ≤ Real.sqrt ε' := (min_le_right _ _).trans (min_le_right _ _)
    calc ρs ^ 2 ≤ Real.sqrt ε' ^ 2 := pow_le_pow_left₀ hρs.le h1 2
      _ = ε' := Real.sq_sqrt hε'0.le
  obtain ⟨E, hE1, hE2', hE3', hEV⟩ := exists_shrinkAll hfs D hρs hρsr₀
  have hEχ : ∀ r hr, (E.chart r hr).χ = (D.chart r hr).χ := fun r hr => (hE1 r hr).1
  have hEk : ∀ r hr, (E.chart r hr).k = (D.chart r hr).k := fun r hr => (hE1 r hr).2.1
  have hER : ∀ r hr, (E.chart r hr).R = (D.chart r hr).R := fun r hr => (hE1 r hr).2.2.1
  have hER' : ∀ r hr, (E.chart r hr).R' = (D.chart r hr).R' := fun r hr => (hE1 r hr).2.2.2
  have hEV' : ∀ x, x ∉ D.halfBalls → E.V x = D.V x := fun x hx =>
    hEV x fun r hr h => hx (D.mem_halfBalls_iff.2 ⟨r, hr, h⟩)
  obtain ⟨ρ₂, hρ₂, hρ₂', -, hρ₂id, hρ₂maps₃, hρ₂tr⟩ :=
    MonotoneShift.exists_translationShift (c₀ := a₃) (c₁ := b₃) (lo := f q - ε) (hi := f q + ε)
      (d := y₂ - f q) (lt_min (by linarith [hy₂.1, hy₂.2]) (by linarith [hy₂.1]))
      (max_lt hq₃ (by linarith [hy₂.2, hq₃])) (by linarith)
  have hρ₂maps : MapsTo ρ₂ (Ioo a₂ b₂) (Ioo a₂ b₂) := by
    intro t ht
    by_cases ht' : t ∈ Ioo a₃ b₃
    · have := hρ₂maps₃ ht'
      exact ⟨h₃.1.trans this.1, this.2.trans h₃.2⟩
    · rw [hρ₂id t ht']
      exact ht
  have hρ₂q : ρ₂ (f q) = y₂ := by
    rw [hρ₂tr (f q) ⟨by linarith, by linarith⟩]; ring
  have hhalf_sub : ∀ r hr, (D.chart r hr).χ '' {z | morseNorm n z ≤ (D.chart r hr).r₀ / 2} ⊆
      (D.chart r hr).χ '' {z | morseNorm n z < ρ r hr} := fun r hr =>
    halfBall_subset_lt r hr (by linarith [(hρ r hr).1, (D.chart r hr).hr₀])
  have hμconst : ∀ r hr, f r ∈ Ioo a₂ b₂ →
      ∀ x ∈ (D.chart r hr).χ '' {z | morseNorm n z < ρ r hr}, μ x = if r = q then 1 else 0 := by
    intro r hr hrI x hx
    by_cases hrq : r = q
    · subst hrq
      rw [ite_eq_left rfl]
      exact hμ1 r hr rfl hrI x hx
    · rw [ite_eq_right hrq]
      exact hμ0 r hr hrq hrI x hx
  have hμVE : ∀ x ∈ f ⁻¹' Ioo a₂ b₂, (mfderiv I 𝓘(ℝ, ℝ) μ x) (E.V x) = 0 := by
    refine mfderiv_V_eq_zero_of_shrink hEV' hμV ?_ ?_
    · intro r hr hrI x hx
      have hO : IsOpen ((D.chart r hr).χ '' {z | morseNorm n z < ρ r hr}) :=
        (D.chart r hr).isOpen_image_of_lt (hρR' r hr)
      filter_upwards [hO.mem_nhds (hhalf_sub r hr hx)] with y hy
      rw [hμconst r hr hrI y hy, hμconst r hr hrI x (hhalf_sub r hr hx)]
    · intro r hr hrI x hx hxI
      have hlev := (D.chart r hr).f_mem_Icc_of_mem_image_le
        (by linarith [D.r₀_lt_R r hr, (D.chart r hr).hr₀]) hx
      have hr₀ε : ((D.chart r hr).r₀ / 2) ^ 2 / 2 < ε := by
        have : ((D.chart r hr).r₀ / 2) ^ 2 / 2 = (D.chart r hr).r₀ ^ 2 / 8 := by ring
        rw [this]; linarith [(hD r hr).1]
      rcases hsep r hr hrI with h | h
      · linarith [hlev.2, hxI.1, sq_nonneg (D.chart r hr).R]
      · linarith [hlev.1, hxI.2, sq_nonneg (D.chart r hr).R]
  have hμcrit : ∀ r ∈ crit, f r ∈ Ioo a₂ b₂ → ∀ᶠ x in 𝓝 r, μ x = μ r := by
    intro r hr hrI
    have hO : IsOpen ((D.chart r hr).χ '' {z | morseNorm n z < ρ r hr}) :=
      (D.chart r hr).isOpen_image_of_lt (hρR' r hr)
    filter_upwards [hO.mem_nhds ((D.chart r hr).p_mem_image_lt (hρpos r hr))] with y hy
    rw [hμconst r hr hrI y hy, hμconst r hr hrI r ((D.chart r hr).p_mem_image_lt (hρpos r hr))]
  have hab₂ : a₂ < b₂ := hqI.1.trans hqI.2
  set g₁ := Rearrange.rearranged f μ ρ₂ with hg₁
  obtain ⟨-, -, hmod, hstrip, hcritIff, hidxEq, hval, -⟩ :=
    rearrange' hf ha₂ hab₂ hb₂ hreg E hcrit μ hμ hμ01 hμVE hμcrit ρ₂ hρ₂ hρ₂' hρ₂id h₃ hρ₂maps
  set Rn : ∀ r ∈ crit, ℝ := fun r hr => if f r ∈ Ioo a₂ b₂ then ρ r hr / 2 else (D.chart r hr).R
    with hRndef
  set rmn : ∀ r ∈ crit, ℝ := fun r hr => if f r ∈ Ioo a₂ b₂ then ρ r hr / 2 else D.rm r hr
    with hrmndef
  have hRnI : ∀ r hr, f r ∈ Ioo a₂ b₂ → Rn r hr = ρ r hr / 2 := fun r hr h => by
    simp only [hRndef, ite_eq_left h]
  have hRnO : ∀ r hr, f r ∉ Ioo a₂ b₂ → Rn r hr = (D.chart r hr).R := fun r hr h => by
    simp only [hRndef, ite_eq_right h]
  have hrmnI : ∀ r hr, f r ∈ Ioo a₂ b₂ → rmn r hr = ρ r hr / 2 := fun r hr h => by
    simp only [hrmndef, ite_eq_left h]
  have hrmnO : ∀ r hr, f r ∉ Ioo a₂ b₂ → rmn r hr = D.rm r hr := fun r hr h => by
    simp only [hrmndef, ite_eq_right h]
  have hρsρ' : ∀ r hr, 64 * ρs ≤ ρ r hr := fun r hr => by
    have h1 := hρsρ r hr
    have h2 : ρ r hr / (64 * (n + 1)) ≤ ρ r hr / 64 := by
      apply div_le_div_of_nonneg_left (hρpos r hr).le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have hρsrm' : ∀ r hr, 64 * ρs ≤ D.rm r hr := fun r hr => by
    have h1 := hρsrm r hr
    have h2 : D.rm r hr / (64 * (n + 1)) ≤ D.rm r hr / 64 := by
      apply div_le_div_of_nonneg_left (D.rm_pos r hr).le (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have hRn : ∀ r hr, 4 * (E.chart r hr).r₀ < Rn r hr ∧ Rn r hr ≤ (E.chart r hr).R := by
    intro r hr
    rw [hE2' r hr, hER r hr]
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · rw [hRnI r hr hrI]
      exact ⟨by linarith [hρsρ' r hr], by linarith [hρR r hr, hρpos r hr]⟩
    · rw [hRnO r hr hrI]
      exact ⟨by linarith [hρsrm' r hr, (D.hrm r hr).2], le_rfl⟩
  have hrmn : ∀ r hr, 2 * (E.chart r hr).r₀ < rmn r hr ∧ rmn r hr ≤ E.rm r hr ∧
      rmn r hr ≤ Rn r hr := by
    intro r hr
    rw [hE2' r hr, hE3' r hr]
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · rw [hrmnI r hr hrI, hRnI r hr hrI]
      exact ⟨by linarith [hρsρ' r hr], by linarith [hρrm r hr, hρpos r hr], le_rfl⟩
    · rw [hrmnO r hr hrI, hRnO r hr hrI]
      exact ⟨by linarith [hρsrm' r hr], le_rfl, (D.hrm r hr).2⟩
  have hconst : ∀ r hr, ∀ y, morseNorm n y ≤ Rn r hr →
      μ ((E.chart r hr).χ y) * (ρ₂ (f ((E.chart r hr).χ y)) - f ((E.chart r hr).χ y)) =
        μ r * (ρ₂ (f r) - f r) ∧
      μ ((E.chart r hr).χ y) * (deriv ρ₂ (f ((E.chart r hr).χ y)) - 1) = 0 := by
    intro r hr y hy
    rw [hEχ r hr]
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · rw [hRnI r hr hrI] at hy
      have hyρ : (D.chart r hr).χ y ∈ (D.chart r hr).χ '' {z | morseNorm n z < ρ r hr} :=
        ⟨y, by change morseNorm n y < ρ r hr; linarith [hρpos r hr], rfl⟩
      have hrρ : r ∈ (D.chart r hr).χ '' {z | morseNorm n z < ρ r hr} :=
        (D.chart r hr).p_mem_image_lt (hρpos r hr)
      rw [hμconst r hr hrI _ hyρ, hμconst r hr hrI r hrρ]
      by_cases hrq : r = q
      · subst hrq
        rw [ite_eq_left rfl]
        have hlev := (D.chart r hr).f_mem_Icc_of_mem_image_le (hρR r hr)
          (⟨y, by change morseNorm n y ≤ ρ r hr; linarith [hρpos r hr], rfl⟩ :
            (D.chart r hr).χ y ∈ (D.chart r hr).χ '' {z | morseNorm n z ≤ ρ r hr})
        have hlev' : f ((D.chart r hr).χ y) ∈ Ioo (f r - ε) (f r + ε) := by
          have h2 : ρ r hr ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ (hρpos r hr).le (hρ r hr).2.1 2
          have h1 : ρ r hr ^ 2 / 2 < ε := by linarith
          exact ⟨by linarith [hlev.1], by linarith [hlev.2]⟩
        have e1 := hρ₂tr (f ((D.chart r hr).χ y)) (Ioo_subset_Icc_self hlev')
        have e2 := hρ₂tr (f r) ⟨by linarith, by linarith⟩
        have e3 := deriv_eq_one_of_translation hρ₂tr hlev'
        rw [e1, e2, e3]
        exact ⟨by rw [one_mul, one_mul, add_sub_cancel_left, add_sub_cancel_left],
          by rw [sub_self, mul_zero]⟩
      · rw [ite_eq_right hrq]
        exact ⟨by rw [zero_mul, zero_mul], zero_mul _⟩
    · rw [hRnO r hr hrI] at hy
      have hlev := (D.chart r hr).f_mem_Icc_of_morseNorm_le le_rfl hy
      have hout : f ((D.chart r hr).χ y) < a₃ ∨ b₃ < f ((D.chart r hr).χ y) := by
        rcases hsep r hr hrI with h | h
        · left; linarith only [hlev.2, h, h₃.1, hε]
        · right; linarith only [hlev.1, h, h₃.2, hε]
      have hrout : f r ∉ Ioo a₃ b₃ := by
        rcases hsep r hr hrI with h | h
        · exact fun h' => by linarith only [h'.1, h, h₃.1, hε, sq_nonneg (D.chart r hr).R]
        · exact fun h' => by linarith only [h'.2, h, h₃.2, hε, sq_nonneg (D.chart r hr).R]
      have e1 : ρ₂ (f ((D.chart r hr).χ y)) = f ((D.chart r hr).χ y) := hρ₂id _ (by
        rcases hout with h | h
        · exact fun h' => absurd h'.1 (not_lt.2 h.le)
        · exact fun h' => absurd h'.2 (not_lt.2 h.le))
      have e2 : ρ₂ (f r) = f r := hρ₂id _ hrout
      have e3 := deriv_eq_one_of_notMem hρ₂id hout
      rw [e1, e2, e3]
      exact ⟨by rw [sub_self, sub_self, mul_zero, mul_zero], by rw [sub_self, mul_zero]⟩
  obtain ⟨D₂, hD₂c, hD₂rm, φ, hφc, ⟨m, M₀, hm, hφb⟩, hφV⟩ :=
    exists_rescaled hf ha₂ hab₂ hb₂ hreg E hcrit μ hμ hμ01 hμVE hμcrit ρ₂ hρ₂ hρ₂' hρ₂id h₃
      hρ₂maps Rn rmn hRn hrmn hconst
  have hgoodE : goodPair E ε p q hp hq := by
    obtain ⟨hk0, hk, i, h1, h2⟩ := hgood
    have hkE : (E.chart q hq).k = 1 := by rw [hEk]; exact hk
    refine ⟨by rw [hEk]; exact hk0, hkE, i, ?_, ?_⟩
    · rw [hEχ, (E.chart q hq).armPt_eq_ite, ← (D.chart q hq).armPt_eq_ite hk]
      exact (mem_basin_iff_of_shrink hfs hEχ hEk hE3' hEV' hε hεr (fun r hr => (hD r hr).2.2)
        hidx hE3 hp hq hkp hkq ((D.chart q hq).armPt_mem_leftModelSphere hk hε.le i)).1 h1
    · rw [hEχ, (E.chart q hq).armPt_eq_ite, ← (D.chart q hq).armPt_eq_ite hk]
      exact fun h => h2 ((mem_basin_iff_of_shrink hfs hEχ hEk hE3' hEV' hε hεr
        (fun r hr => (hD r hr).2.2) hidx hE3 hp hq hkp hkq
        ((D.chart q hq).armPt_mem_leftModelSphere hk hε.le (i + 1))).2 h)
  have hgoodE' : goodPair E ε' p q hp hq :=
    goodPair_of_le hfs hε'0 hε'ε (by rw [hE3' q hq]; linarith [(hD q hq).2.1]) hgoodE
  have hbasin : D₂.basin p hp = E.basin p hp := by
    ext x
    unfold basin
    rw [(hD₂c p hp).1, hD₂rm p hp, hrmnO p hp hpI, hE3' p hp]
    exact exists_nonneg_flow_mem_iff E D₂ hφc hm hφb hφV x _
  have hgood₂ : goodPair D₂ ε' p q hp hq :=
    goodPair_congr (hD₂c q hq).1 (hD₂c p hp).2.1 (hD₂c q hq).2.1 hbasin hgoodE'
  have hg₁q : g₁ q = y₂ := by
    rw [hg₁, hval q, hμ1 q hq rfl hqI q ((D.chart q hq).p_mem_image_lt (hρpos q hq)), hρ₂q]
    ring
  have hg₁other : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ q → g₁ x = f x := by
    intro x hx hxq
    rw [hg₁]
    by_cases hxab : f x ∈ Ioo a b
    · have hxc : x ∈ crit := (hcrit x).2 ⟨hxab, hx⟩
      rw [hval x]
      by_cases hxI : f x ∈ Ioo a₂ b₂
      · rw [hμ0 x hxc hxq hxI x ((D.chart x hxc).p_mem_image_lt (hρpos x hxc))]; ring
      · have hrout : f x ∉ Ioo a₃ b₃ := by
          rcases hsep x hxc hxI with h | h
          · exact fun h' => by nlinarith [h'.1, sq_nonneg (D.chart x hxc).R, h₃.1]
          · exact fun h' => by nlinarith [h'.2, sq_nonneg (D.chart x hxc).R, h₃.2]
        rw [hρ₂id _ hrout]; ring
    · exact hmod.eqOn hxab
  refine ⟨g₁, D₂, ε', hε'0, hε'ε, hmod, hstrip, hcritIff, hidxEq, hg₁q, hg₁other, ?_, ?_, ?_, ?_,
    hε'p', ?_, ?_, hgood₂⟩
  · intro r hr
    refine ⟨(hD₂c r hr).1.trans (hEχ r hr), (hD₂c r hr).2.1.trans (hEk r hr), ?_,
      (hD₂c r hr).2.2.2.2.trans (hER' r hr)⟩
    rw [(hD₂c r hr).2.2.2.1]
    have := (hRn r hr).2
    rwa [hER r hr] at this
  · intro r hr
    rw [(hD₂c r hr).2.2.1, hE2' r hr, hD₂rm r hr]
    refine ⟨by linarith, ?_, ?_⟩
    · have : (ρs / 2) ^ 2 = ρs ^ 2 / 4 := by ring
      rw [this]; linarith
    · by_cases hrI : f r ∈ Ioo a₂ b₂
      · rw [hrmnI r hr hrI]
        have h1 := hρsρ r hr
        have h2 : 8 * (n + 1) * ρs ≤ ρ r hr / 8 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
          have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * (n + 1) * 8)
          have h3 : 8 * (n + 1) * 8 * (ρ r hr / (64 * (n + 1))) = ρ r hr := by
            field_simp; ring
          linarith
        linarith [hρpos r hr]
      · rw [hrmnO r hr hrI]
        have h1 := hρsrm r hr
        have h2 : 8 * (n + 1) * ρs ≤ D.rm r hr / 8 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
          have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * (n + 1) * 8)
          have h3 : 8 * (n + 1) * 8 * (D.rm r hr / (64 * (n + 1))) = D.rm r hr := by
            field_simp; ring
          linarith
        linarith [D.rm_pos r hr]
  · intro r hr hrI
    rw [hD₂rm r hr, hrmnO r hr hrI]
  · intro r hr
    rw [hD₂rm r hr]
    by_cases hrI : f r ∈ Ioo a₂ b₂
    · rw [hrmnI r hr hrI]; linarith [hρrm r hr, hρpos r hr]
    · rw [hrmnO r hr hrI]
  · rw [hD₂rm q hq, hrmnI q hq hqI]
    exact hε'q'
  · rw [(hD₂c q hq).2.2.2.1, hD₂rm q hq, hRnI q hq hqI, hrmnI q hq hqI]

end GradientLikeStrip

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless]

theorem exists_raise_p (hf : MorseStrip I f a b)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {p : M} (hp : p ∈ crit) (hkp : (D.chart p hp).k = 0)
    {a₁ b₁ a₃ b₃ y₁ : ℝ} (ha₁ : a ≤ a₁) (hb₁ : b₁ ≤ b) (h₃ : a₁ < a₃ ∧ b₃ < b₁)
    (hidx0 : ∀ r hr, f r ∈ Ioo a₁ b₁ → (D.chart r hr).k = 0)
    (hsep : ∀ r hr, f r ∉ Ioo a₁ b₁ →
      f r + (D.chart r hr).R ^ 2 / 2 < a₁ ∨ b₁ + (D.chart r hr).R ^ 2 / 2 < f r)
    (hpI : f p ∈ Ioo a₁ b₁) (hy₁ : f p < y₁)
    (hplat : a₃ < f p - D.rm p hp ^ 2 / 2 ∧ y₁ + D.rm p hp ^ 2 / 2 < b₃)
    (hreg : ∀ x, f x = a₁ ∨ f x = b₁ → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hr₀ : ∀ r hr, 4 * (D.chart r hr).r₀ < D.rm r hr) :
    ∃ g₂ : M → ℝ, ∃ D₁ : GradientLikeStrip I g₂ a b crit,
      ModifiedWithin f a b g₂ ∧ MorseStrip I g₂ a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g₂ x = morseIndex I f x) ∧
      g₂ p = y₁ ∧ (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ p → g₂ x = f x) ∧
      (∀ r hr, (D₁.chart r hr).χ = (D.chart r hr).χ ∧ (D₁.chart r hr).k = (D.chart r hr).k ∧
        (D₁.chart r hr).r₀ = (D.chart r hr).r₀ ∧ (D₁.chart r hr).R ≤ (D.chart r hr).R ∧
        (D₁.chart r hr).R' = (D.chart r hr).R') ∧
      (∀ r hr, D₁.rm r hr ≤ D.rm r hr) ∧ (∀ r hr, f r ∉ Ioo a₁ b₁ → D₁.rm r hr = D.rm r hr) ∧
      D.rm p hp / 2 ≤ D₁.rm p hp ∧ D₁.rm p hp = (D₁.chart p hp).R ∧
      D₁.basin p hp = D.basin p hp := by
  classical
  have hfs := hf.smooth
  have hab₁ : a₁ < b₁ := hpI.1.trans hpI.2
  have hsep' : ∀ r hr, f r ∉ Ioo a₁ b₁ →
      f r + D.rm r hr ^ 2 / 2 < a₁ ∨ b₁ < f r - D.rm r hr ^ 2 / 2 := by
    intro r hr hrI
    have hrmR : D.rm r hr ^ 2 ≤ (D.chart r hr).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos r hr).le (D.hrm r hr).2 2
    rcases hsep r hr hrI with h | h
    · left; linarith
    · right; linarith
  obtain ⟨μ, hμ, hμ01, hμV, hμ1, hμ0, -⟩ := exists_basinCutoff hfs ha₁ hb₁ hsep' hidx0 hp hpI
  obtain ⟨ρ₁, hρ₁, hρ₁', -, hρ₁id, hρ₁maps₃, hρ₁tr⟩ :=
    MonotoneShift.exists_translationShift (c₀ := a₃) (c₁ := b₃) (lo := f p - D.rm p hp ^ 2 / 2)
      (hi := f p + D.rm p hp ^ 2 / 2) (d := y₁ - f p) (lt_min hplat.1 (by linarith [hplat.1]))
      (max_lt (by linarith [hplat.2]) (by linarith [hplat.2])) (by linarith [sq_nonneg (D.rm p hp)])
  have hρ₁maps : MapsTo ρ₁ (Ioo a₁ b₁) (Ioo a₁ b₁) := by
    intro t ht
    by_cases ht' : t ∈ Ioo a₃ b₃
    · have := hρ₁maps₃ ht'
      exact ⟨h₃.1.trans this.1, this.2.trans h₃.2⟩
    · rw [hρ₁id t ht']
      exact ht
  have hρ₁p : ρ₁ (f p) = y₁ := by
    rw [hρ₁tr (f p) ⟨by linarith [sq_nonneg (D.rm p hp)], by linarith [sq_nonneg (D.rm p hp)]⟩]
    ring
  have hμcrit : ∀ r ∈ crit, f r ∈ Ioo a₁ b₁ → ∀ᶠ x in 𝓝 r, μ x = μ r := by
    intro r hr hrI
    by_cases hrp : r = p
    · subst hrp
      filter_upwards [(D.isOpen_basin r hr).mem_nhds (crit_mem_basin r hr)] with y hy
      rw [hμ1 y hy, hμ1 r (crit_mem_basin r hr)]
    · filter_upwards [(D.isOpen_basin r hr).mem_nhds (crit_mem_basin r hr)] with y hy
      rw [hμ0 r hr hrp hrI y hy, hμ0 r hr hrp hrI r (crit_mem_basin r hr)]
  set g₂ := Rearrange.rearranged f μ ρ₁ with hg₂
  obtain ⟨-, -, hmod, hstrip, hcritIff, hidxEq, hval, -⟩ :=
    rearrange' hf ha₁ hab₁ hb₁ hreg D hcrit μ hμ hμ01 hμV hμcrit ρ₁ hρ₁ hρ₁' hρ₁id h₃ hρ₁maps
  set Rn : ∀ r ∈ crit, ℝ := fun r hr =>
    if f r ∈ Ioo a₁ b₁ then (D.rm r hr + 4 * (D.chart r hr).r₀) / 2 else (D.chart r hr).R
    with hRndef
  set rmn : ∀ r ∈ crit, ℝ := fun r hr =>
    if f r ∈ Ioo a₁ b₁ then (D.rm r hr + 4 * (D.chart r hr).r₀) / 2 else D.rm r hr
    with hrmndef
  have hRnI : ∀ r hr, f r ∈ Ioo a₁ b₁ → Rn r hr = (D.rm r hr + 4 * (D.chart r hr).r₀) / 2 :=
    fun r hr h => by simp only [hRndef, ite_eq_left h]
  have hRnO : ∀ r hr, f r ∉ Ioo a₁ b₁ → Rn r hr = (D.chart r hr).R := fun r hr h => by
    simp only [hRndef, ite_eq_right h]
  have hrmnI : ∀ r hr, f r ∈ Ioo a₁ b₁ → rmn r hr = (D.rm r hr + 4 * (D.chart r hr).r₀) / 2 :=
    fun r hr h => by simp only [hrmndef, ite_eq_left h]
  have hrmnO : ∀ r hr, f r ∉ Ioo a₁ b₁ → rmn r hr = D.rm r hr := fun r hr h => by
    simp only [hrmndef, ite_eq_right h]
  have hRn : ∀ r hr, 4 * (D.chart r hr).r₀ < Rn r hr ∧ Rn r hr ≤ (D.chart r hr).R := by
    intro r hr
    by_cases hrI : f r ∈ Ioo a₁ b₁
    · rw [hRnI r hr hrI]
      exact ⟨by linarith [hr₀ r hr], by linarith [hr₀ r hr, (D.hrm r hr).2]⟩
    · rw [hRnO r hr hrI]
      exact ⟨(D.chart r hr).hr₀R, le_rfl⟩
  have hrmn : ∀ r hr, 2 * (D.chart r hr).r₀ < rmn r hr ∧ rmn r hr ≤ D.rm r hr ∧
      rmn r hr ≤ Rn r hr := by
    intro r hr
    by_cases hrI : f r ∈ Ioo a₁ b₁
    · rw [hrmnI r hr hrI, hRnI r hr hrI]
      exact ⟨by linarith [hr₀ r hr, (D.chart r hr).hr₀], by linarith [hr₀ r hr], le_rfl⟩
    · rw [hrmnO r hr hrI, hRnO r hr hrI]
      exact ⟨(D.hrm r hr).1, le_rfl, (D.hrm r hr).2⟩
  have hconst : ∀ r hr, ∀ y, morseNorm n y ≤ Rn r hr →
      μ ((D.chart r hr).χ y) * (ρ₁ (f ((D.chart r hr).χ y)) - f ((D.chart r hr).χ y)) =
        μ r * (ρ₁ (f r) - f r) ∧
      μ ((D.chart r hr).χ y) * (deriv ρ₁ (f ((D.chart r hr).χ y)) - 1) = 0 := by
    intro r hr y hy
    by_cases hrI : f r ∈ Ioo a₁ b₁
    · have hRnlt : Rn r hr < D.rm r hr := by rw [hRnI r hr hrI]; linarith [hr₀ r hr]
      have hymem : (D.chart r hr).χ y ∈ D.basin r hr :=
        modelBall_subset_basin r hr ⟨y, by change morseNorm n y < D.rm r hr; linarith, rfl⟩
      by_cases hrp : r = p
      · subst hrp
        have hlev := (D.chart r hr).f_mem_Icc_of_morseNorm_le (hRn r hr).2 hy
        have hRn2 : Rn r hr ^ 2 < D.rm r hr ^ 2 :=
          pow_lt_pow_left₀ hRnlt (by rw [hRnI r hr hrI]; linarith [hr₀ r hr, (D.chart r hr).hr₀])
            two_ne_zero
        have hlev' : f ((D.chart r hr).χ y) ∈
            Ioo (f r - D.rm r hr ^ 2 / 2) (f r + D.rm r hr ^ 2 / 2) :=
          ⟨by linarith [hlev.1], by linarith [hlev.2]⟩
        have e1 := hρ₁tr (f ((D.chart r hr).χ y)) (Ioo_subset_Icc_self hlev')
        have e2 := hρ₁tr (f r) ⟨by linarith [sq_nonneg (D.rm r hr)],
          by linarith [sq_nonneg (D.rm r hr)]⟩
        have e3 := deriv_eq_one_of_translation hρ₁tr hlev'
        rw [hμ1 _ hymem, hμ1 r (crit_mem_basin r hr), e1, e2, e3]
        exact ⟨by rw [one_mul, one_mul, add_sub_cancel_left, add_sub_cancel_left],
          by rw [sub_self, mul_zero]⟩
      · rw [hμ0 r hr hrp hrI _ hymem, hμ0 r hr hrp hrI r (crit_mem_basin r hr)]
        exact ⟨by rw [zero_mul, zero_mul], zero_mul _⟩
    · rw [hRnO r hr hrI] at hy
      have hlev := (D.chart r hr).f_mem_Icc_of_morseNorm_le le_rfl hy
      have hout : f ((D.chart r hr).χ y) < a₃ ∨ b₃ < f ((D.chart r hr).χ y) := by
        rcases hsep r hr hrI with h | h
        · left; linarith only [hlev.2, h, h₃.1]
        · right; linarith only [hlev.1, h, h₃.2]
      have hrout : f r ∉ Ioo a₃ b₃ := by
        rcases hsep r hr hrI with h | h
        · exact fun h' => by linarith only [h'.1, h, h₃.1, sq_nonneg (D.chart r hr).R]
        · exact fun h' => by linarith only [h'.2, h, h₃.2, sq_nonneg (D.chart r hr).R]
      have e1 : ρ₁ (f ((D.chart r hr).χ y)) = f ((D.chart r hr).χ y) := hρ₁id _ (by
        rcases hout with h | h
        · exact fun h' => absurd h'.1 (not_lt.2 h.le)
        · exact fun h' => absurd h'.2 (not_lt.2 h.le))
      have e2 : ρ₁ (f r) = f r := hρ₁id _ hrout
      have e3 := deriv_eq_one_of_notMem hρ₁id hout
      rw [e1, e2, e3]
      exact ⟨by rw [sub_self, sub_self, mul_zero, mul_zero], by rw [sub_self, mul_zero]⟩
  obtain ⟨D₁, hD₁c, hD₁rm, φ, hφc, ⟨m, M₀, hm, hφb⟩, hφV⟩ :=
    exists_rescaled hf ha₁ hab₁ hb₁ hreg D hcrit μ hμ hμ01 hμV hμcrit ρ₁ hρ₁ hρ₁' hρ₁id h₃
      hρ₁maps Rn rmn hRn hrmn hconst
  have hg₂p : g₂ p = y₁ := by
    rw [hg₂, hval p, hμ1 p (crit_mem_basin p hp), hρ₁p]; ring
  have hg₂other : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ p → g₂ x = f x := by
    intro x hx hxp
    rw [hg₂]
    by_cases hxab : f x ∈ Ioo a b
    · have hxc : x ∈ crit := (hcrit x).2 ⟨hxab, hx⟩
      rw [hval x]
      by_cases hxI : f x ∈ Ioo a₁ b₁
      · rw [hμ0 x hxc hxp hxI x (crit_mem_basin x hxc)]; ring
      · have hrout : f x ∉ Ioo a₃ b₃ := by
          rcases hsep x hxc hxI with h | h
          · exact fun h' => by linarith only [h'.1, h, h₃.1, sq_nonneg (D.chart x hxc).R]
          · exact fun h' => by linarith only [h'.2, h, h₃.2, sq_nonneg (D.chart x hxc).R]
        rw [hρ₁id _ hrout]; ring
    · exact hmod.eqOn hxab
  have hbasin : D₁.basin p hp = D.basin p hp := by
    have hRnp : Rn p hp = (D.rm p hp + 4 * (D.chart p hp).r₀) / 2 := hRnI p hp hpI
    have hρpos : 0 < Rn p hp := by rw [hRnp]; linarith [D.rm_pos p hp, (D.chart p hp).hr₀]
    have hρle : Rn p hp ≤ D.rm p hp := by rw [hRnp]; linarith [hr₀ p hp]
    rw [basin_eq_of_le hkp hρpos hρle]
    ext x
    unfold basin
    rw [(hD₁c p hp).1, hD₁rm p hp, hrmnI p hp hpI, ← hRnp]
    exact exists_nonneg_flow_mem_iff D D₁ hφc hm hφb hφV x _
  refine ⟨g₂, D₁, hmod, hstrip, hcritIff, hidxEq, hg₂p, hg₂other, ?_, ?_, ?_, ?_, ?_, hbasin⟩
  · intro r hr
    refine ⟨(hD₁c r hr).1, (hD₁c r hr).2.1, (hD₁c r hr).2.2.1, ?_, (hD₁c r hr).2.2.2.2⟩
    rw [(hD₁c r hr).2.2.2.1]
    exact (hRn r hr).2
  · intro r hr
    rw [hD₁rm r hr]
    exact (hrmn r hr).2.1
  · intro r hr hrI
    rw [hD₁rm r hr, hrmnO r hr hrI]
  · rw [hD₁rm p hp, hrmnI p hp hpI]
    linarith [(D.chart p hp).hr₀]
  · rw [hD₁rm p hp, hrmnI p hp hpI, (hD₁c p hp).2.2.2.1, hRnI p hp hpI]

end GradientLikeStrip

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless]

omit [T2Space M] [I.Boundaryless] in
theorem exists_value_levels (hsi : isSelfIndexing I f a b)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {G : ℝ} (hG : 0 < G)
    (hgap : ∀ r ∈ crit, ∀ s ∈ crit, f r < f s → f r + 16 * G < f s)
    (hab : ∀ r ∈ crit, a + 16 * G < f r ∧ f r + 16 * G < b) {p q : M} (hp : p ∈ crit)
    (hq : q ∈ crit) (hkp : (D.chart p hp).k = 0) (hkq : (D.chart q hq).k = 1) :
    ∃ v₀ u₁ w₂ : ℝ, (∀ r hr, (D.chart r hr).k = 0 → f r ≤ v₀) ∧ a + 16 * G < v₀ ∧
      (∀ r hr, 1 ≤ (D.chart r hr).k → v₀ + 16 * G < f r) ∧
      (∀ r hr, 1 ≤ (D.chart r hr).k → u₁ ≤ f r) ∧ v₀ + 16 * G < u₁ ∧ u₁ ≤ f q ∧
      (∀ r hr, 2 ≤ (D.chart r hr).k → w₂ ≤ f r) ∧
      (∀ r hr, (D.chart r hr).k ≤ 1 → f r + 16 * G < w₂) ∧ w₂ ≤ b := by
  classical
  have hidx : ∀ r hr s hs, (D.chart r hr).k < (D.chart s hs).k → f r < f s :=
    k_lt_imp_f_lt_of_selfIndexing D hsi hcrit
  have hkidx : ∀ r hr, (D.chart r hr).k = morseIndex I f r := fun r hr =>
    (D.chart r hr).hkidx.symm
  set S₀ := crit.filter fun r => morseIndex I f r = 0 with hS₀
  have hpS₀ : p ∈ S₀ := Finset.mem_filter.2 ⟨hp, by rw [← hkidx p hp]; exact hkp⟩
  obtain ⟨r₀, hr₀S, hr₀max⟩ := Finset.exists_max_image S₀ f ⟨p, hpS₀⟩
  obtain ⟨hr₀c, hr₀k⟩ := Finset.mem_filter.1 hr₀S
  have hr₀k' : (D.chart r₀ hr₀c).k = 0 := by rw [hkidx]; exact hr₀k
  set S₁ := crit.filter fun r => 1 ≤ morseIndex I f r with hS₁
  have hqS₁ : q ∈ S₁ := Finset.mem_filter.2 ⟨hq, by rw [← hkidx q hq, hkq]⟩
  obtain ⟨s₁, hs₁S, hs₁min⟩ := Finset.exists_min_image S₁ f ⟨q, hqS₁⟩
  obtain ⟨hs₁c, hs₁k⟩ := Finset.mem_filter.1 hs₁S
  have hs₁k' : 1 ≤ (D.chart s₁ hs₁c).k := by rw [hkidx]; exact hs₁k
  have hv₀ : ∀ r hr, (D.chart r hr).k = 0 → f r ≤ f r₀ := fun r hr hk =>
    hr₀max r (Finset.mem_filter.2 ⟨hr, by rw [← hkidx r hr]; exact hk⟩)
  have hu₁ : ∀ r hr, 1 ≤ (D.chart r hr).k → f s₁ ≤ f r := fun r hr hk =>
    hs₁min r (Finset.mem_filter.2 ⟨hr, by rw [← hkidx r hr]; exact hk⟩)
  have hv₀u : ∀ r hr, 1 ≤ (D.chart r hr).k → f r₀ + 16 * G < f r := fun r hr hk =>
    hgap r₀ hr₀c r hr (hidx r₀ hr₀c r hr (by rw [hr₀k']; exact hk))
  set S₂ := crit.filter fun r => 2 ≤ morseIndex I f r with hS₂
  rcases S₂.eq_empty_or_nonempty with hemp | hne
  · refine ⟨f r₀, f s₁, b, hv₀, (hab r₀ hr₀c).1, hv₀u, hu₁, hv₀u s₁ hs₁c hs₁k', hu₁ q hq (by
      rw [hkq]), fun r hr hk => ?_, fun r hr _ => (hab r hr).2, le_rfl⟩
    exfalso
    have : r ∈ S₂ := Finset.mem_filter.2 ⟨hr, by rw [← hkidx r hr]; exact hk⟩
    rw [hemp] at this
    exact Finset.notMem_empty r this
  · obtain ⟨t₂, ht₂S, ht₂min⟩ := Finset.exists_min_image S₂ f hne
    obtain ⟨ht₂c, ht₂k⟩ := Finset.mem_filter.1 ht₂S
    have ht₂k' : 2 ≤ (D.chart t₂ ht₂c).k := by rw [hkidx]; exact ht₂k
    refine ⟨f r₀, f s₁, f t₂, hv₀, (hab r₀ hr₀c).1, hv₀u, hu₁, hv₀u s₁ hs₁c hs₁k', hu₁ q hq (by
      rw [hkq]), fun r hr hk => ?_, fun r hr hk => ?_, by linarith [(hab t₂ ht₂c).2]⟩
    · exact ht₂min r (Finset.mem_filter.2 ⟨hr, by rw [← hkidx r hr]; exact hk⟩)
    · exact hgap r hr t₂ ht₂c (hidx r hr t₂ ht₂c (by omega))

theorem exists_moves [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {ε r' R₀ : ℝ} (hε : 0 < ε) (hr'ε : r' ^ 2 < ε)
    (hD : ∀ p hp, (D.chart p hp).R ≤ R₀ ∧ (D.chart p hp).r₀ ^ 2 < 2 * ε ∧
      24 * ε < D.rm p hp ^ 2 ∧ (D.chart p hp).r₀ < r')
    (hE2 : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r'}, ∀ t,
        D.flow t x ∉ (D.chart q hq).χ '' {y | morseNorm n y < r'})
    (hE3 : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
        D.flow t x ∉ (D.chart p hp).χ '' {y | morseNorm n y < r'})
    (hgap : ∀ r ∈ crit, ∀ s ∈ crit, f r < f s → f r + 16 * R₀ ^ 2 < f s)
    (hab : ∀ r ∈ crit, a + 16 * R₀ ^ 2 < f r ∧ f r + 16 * R₀ ^ 2 < b)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hgood : goodPair D ε p q hp hq) :
    ∃ g₂ : M → ℝ, ∃ D₁ : GradientLikeStrip I g₂ a b crit, ∃ ε' v₀ G : ℝ, 0 < G ∧ 24 * ε < G ∧
      0 < ε' ∧ ε' ≤ ε ∧ a + 16 * G < v₀ ∧ v₀ + 16 * G < b ∧
      ModifiedWithin f a b g₂ ∧ MorseStrip I g₂ a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g₂ x = morseIndex I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ p → x ≠ q → g₂ x = f x) ∧
      g₂ p = v₀ + 4 * G ∧ g₂ q = v₀ + 8 * G ∧
      (∀ r hr, r ≠ p → (D.chart r hr).k = 0 → g₂ r ≤ v₀) ∧
      (∀ r hr, r ≠ q → 1 ≤ (D.chart r hr).k → v₀ + 16 * G < g₂ r) ∧
      (∀ r hr, (D₁.chart r hr).χ = (D.chart r hr).χ ∧ (D₁.chart r hr).k = (D.chart r hr).k ∧
        (D₁.chart r hr).r₀ ^ 2 / 2 < ε' ∧ (D₁.chart r hr).R ^ 2 ≤ G) ∧
      (∀ r hr, r = p ∨ r = q → 8 * (n + 1) * (D₁.chart r hr).r₀ < (D₁.chart r hr).R ∧
        32 * (n + 1) ^ 2 * ε' < (D₁.chart r hr).R ^ 2 ∧ (D₁.chart r hr).R / 2 ≤ D₁.rm r hr) ∧
      goodPair D₁ ε' p q hp hq := by
  classical
  have hfs := hf.smooth
  have hkp : (D.chart p hp).k = 0 := hgood.1
  obtain ⟨hkq, -⟩ := hgood.2
  set G : ℝ := R₀ ^ 2 with hG
  have hR₀ : 0 < R₀ := (D.chart p hp).R_pos.trans_le (hD p hp).1
  have hG0 : 0 < G := by positivity
  have hRG : ∀ r hr, (D.chart r hr).R ^ 2 ≤ G := fun r hr =>
    pow_le_pow_left₀ (D.chart r hr).R_pos.le (hD r hr).1 2
  have hrmG : ∀ r hr, D.rm r hr ^ 2 ≤ G := fun r hr =>
    (pow_le_pow_left₀ (D.rm_pos r hr).le (D.hrm r hr).2 2).trans (hRG r hr)
  have hεG : 24 * ε < G := (hD p hp).2.2.1.trans_le (hrmG p hp)
  have hidx : ∀ r hr s hs, (D.chart r hr).k < (D.chart s hs).k → f r < f s :=
    k_lt_imp_f_lt_of_selfIndexing D hsi hcrit
  obtain ⟨v₀, u₁, w₂, hv₀, hav₀, hv₀u, hu₁, hv₀u₁, hu₁q, hw₂a, hw₂b, hw₂b'⟩ :=
    exists_value_levels hsi hcrit D hG0 hgap hab hp hq hkp hkq
  have hfp : f p ≤ v₀ := hv₀ p hp hkp
  have hfq : u₁ ≤ f q := hu₁q
  have hfq' : f q + 16 * G < w₂ := hw₂b q hq (by rw [hkq])
  have hpab := (hab p hp)
  have hkcases : ∀ r hr, (D.chart r hr).k = 0 ∨ (D.chart r hr).k = 1 ∨ 2 ≤ (D.chart r hr).k :=
    fun r hr => by omega
  set a₂ : ℝ := v₀ + G with ha₂def
  set b₂ : ℝ := w₂ - G with hb₂def
  set a₃ : ℝ := v₀ + 5 * G / 4 with ha₃def
  set b₃ : ℝ := w₂ - 5 * G / 4 with hb₃def
  set y₂ : ℝ := v₀ + 8 * G with hy₂def
  have hidx1 : ∀ r hr, f r ∈ Ioo a₂ b₂ → (D.chart r hr).k = 1 := by
    intro r hr hrI
    rcases hkcases r hr with h | h | h
    · exfalso; have := hv₀ r hr h; linarith [hrI.1]
    · exact h
    · exfalso; have := hw₂a r hr h; linarith [hrI.2]
  have hval1 : ∀ r hr, (D.chart r hr).k = 1 → f r ∈ Ioo a₂ b₂ := fun r hr hk =>
    ⟨by linarith [hv₀u r hr (by rw [hk])], by linarith [hw₂b r hr (by rw [hk])]⟩
  obtain ⟨g₁, D₂, ε', hε'0, hε'ε, hmod₁, hstrip₁, hcrit₁, hidx₁, hg₁q, hg₁other, hD₂c, hD₂r₀,
      hD₂rmO, hD₂rm, hε'p, hε'q, hD₂Rq, hgood₂⟩ :=
    exists_lower_q hf hsi hinj hcrit D hε hr'ε (fun r hr => ⟨(hD r hr).2.1, (hD r hr).2.2.1,
      (hD r hr).2.2.2⟩) hE2 hE3 hp hq hkp hkq hgood (a₂ := a₂) (b₂ := b₂)
      (a₃ := a₃) (b₃ := b₃) (y₂ := y₂) (by linarith) (by linarith)
      ⟨by linarith, by linarith⟩ hidx1
      (fun r hr hrI => by
        rcases hkcases r hr with h | h | h
        · left; have := hv₀ r hr h; have := hRG r hr; linarith
        · exact absurd (hval1 r hr h) hrI
        · right; have := hw₂a r hr h; have := hRG r hr; linarith)
      (hval1 q hq hkq) ⟨by linarith, by linarith⟩ (by linarith)
      (fun x hx hc => by
        have hxab : f x ∈ Ioo a b := by
          rcases hx with hx | hx <;> rw [hx] <;> constructor <;> linarith
        have hxc : x ∈ crit := (hcrit x).2 ⟨hxab, hc⟩
        rcases hkcases x hxc with h | h | h
        · have := hv₀ x hxc h; rcases hx with hx | hx <;> linarith
        · have := hval1 x hxc h; rcases hx with hx | hx <;> linarith [this.1, this.2]
        · have := hw₂a x hxc h; rcases hx with hx | hx <;> linarith)
      (c := u₁ - G / 2) ⟨by linarith, by linarith⟩
      (fun r hr hrI => by have := hu₁ r hr (by rw [hidx1 r hr hrI]); linarith) (σ := 1) one_pos
  have hne_q : ∀ r hr, (D.chart r hr).k = 0 → r ≠ q := fun r hr hk h => by
    subst h; exact one_ne_zero (hkq.symm.trans hk)
  have hne_p : ∀ r hr, 1 ≤ (D.chart r hr).k → r ≠ p := fun r hr hk h => by
    subst h
    have h2 : (D.chart r hr).k = 0 := hkp
    omega
  have hpq : p ≠ q := hne_q p hp hkp
  have hcritg₁ : ∀ x, x ∈ crit ↔ g₁ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₁ x := by
    intro x
    rw [hcrit x, hcrit₁ x]
    have : g₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := Set.ext_iff.1 hmod₁.preimage_Ioo x
    rw [this]
  have hg₁val : ∀ r hr, r ≠ q → g₁ r = f r := fun r hr h => hg₁other r ((hcrit r).1 hr).2 h
  set a₁ : ℝ := a + G with ha₁def
  set b₁ : ℝ := v₀ + 6 * G with hb₁def
  set a₃' : ℝ := a + 2 * G with ha₃'def
  set b₃' : ℝ := v₀ + 11 * G / 2 with hb₃'def
  set y₁ : ℝ := v₀ + 4 * G with hy₁def
  have hD₂k : ∀ r hr, (D₂.chart r hr).k = (D.chart r hr).k := fun r hr => (hD₂c r hr).2.1
  have hD₂R : ∀ r hr, (D₂.chart r hr).R ^ 2 ≤ G := fun r hr =>
    (pow_le_pow_left₀ (D₂.chart r hr).R_pos.le (hD₂c r hr).2.2.1 2).trans (hRG r hr)
  have hD₂rmG : ∀ r hr, D₂.rm r hr ^ 2 ≤ G := fun r hr =>
    (pow_le_pow_left₀ (D₂.rm_pos r hr).le (hD₂rm r hr) 2).trans (hrmG r hr)
  have hg₁lo : ∀ r hr, (D.chart r hr).k = 0 → g₁ r = f r := fun r hr hk =>
    hg₁val r hr (hne_q r hr hk)
  have hg₁hi : ∀ r hr, 1 ≤ (D.chart r hr).k → v₀ + 8 * G ≤ g₁ r := by
    intro r hr hk
    by_cases hrq : r = q
    · subst hrq; rw [hg₁q]
    · rw [hg₁val r hr hrq]; linarith [hu₁ r hr hk, hv₀u₁]
  obtain ⟨g₂, D₁, hmod₂, hstrip₂, hcrit₂, hidx₂, hg₂p, hg₂other, hD₁c, hD₁rm, hD₁rmO, hD₁rmp,
      hD₁Rp, hbasin₁⟩ :=
    exists_raise_p hstrip₁ hcritg₁ D₂ hp (by rw [hD₂k]; exact hkp) (a₁ := a₁) (b₁ := b₁)
      (a₃ := a₃') (b₃ := b₃') (y₁ := y₁) (by linarith) (by linarith [hpab.2, hfp])
      ⟨by linarith, by linarith⟩
      (fun r hr hrI => by
        rcases Nat.eq_zero_or_pos (D.chart r hr).k with h | h
        · rw [hD₂k]; exact h
        · exfalso; have := hg₁hi r hr h; linarith [hrI.2])
      (fun r hr hrI => by
        rcases Nat.eq_zero_or_pos (D.chart r hr).k with h | h
        · exfalso
          rw [hg₁lo r hr h] at hrI
          exact hrI ⟨by linarith [(hab r hr).1], by linarith [hv₀ r hr h]⟩
        · right; have := hg₁hi r hr h; have := hD₂R r hr; linarith)
      (by rw [hg₁lo p hp hkp]; exact ⟨by linarith [hpab.1], by linarith⟩)
      (by rw [hg₁lo p hp hkp]; linarith)
      ⟨by rw [hg₁lo p hp hkp]; have := hD₂rmG p hp; linarith [hpab.1],
        by have := hD₂rmG p hp; linarith⟩
      (fun x hx hc => by
        have hxab : g₁ x ∈ Ioo a b := by
          rcases hx with hx | hx <;> rw [hx] <;> constructor <;> linarith [hpab.2, hfp]
        have hxc : x ∈ crit := (hcritg₁ x).2 ⟨hxab, hc⟩
        rcases Nat.eq_zero_or_pos (D.chart x hxc).k with h | h
        · rw [hg₁lo x hxc h] at hx
          have := hv₀ x hxc h; have := (hab x hxc).1
          rcases hx with hx | hx <;> linarith
        · have := hg₁hi x hxc h; rcases hx with hx | hx <;> linarith)
      (fun r hr => by
        have := (hD₂r₀ r hr).2.2
        have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        nlinarith only [this, hn, (D₂.chart r hr).hr₀])
  set a' : ℝ := v₀ + 2 * G with ha'def
  set b' : ℝ := v₀ + 10 * G with hb'def
  have hcritg₂ : ∀ x, x ∈ crit ↔ g₂ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x := by
    intro x
    rw [hcritg₁ x, hcrit₂ x]
    have : g₂ x ∈ Ioo a b ↔ g₁ x ∈ Ioo a b := Set.ext_iff.1 hmod₂.preimage_Ioo x
    rw [this]
  have hg₂q : g₂ q = y₂ := by rw [hg₂other q ((hcritg₁ q).1 hq).2 (Ne.symm hpq), hg₁q]
  have hg₂val : ∀ r hr, r ≠ p → r ≠ q → g₂ r = f r := fun r hr hrp hrq => by
    rw [hg₂other r ((hcritg₁ r).1 hr).2 hrp, hg₁val r hr hrq]
  have hg₂lo : ∀ r hr, r ≠ p → (D.chart r hr).k = 0 → g₂ r ≤ v₀ := fun r hr hrp hk => by
    rw [hg₂val r hr hrp (hne_q r hr hk)]
    exact hv₀ r hr hk
  have hg₂hi : ∀ r hr, r ≠ q → 1 ≤ (D.chart r hr).k → v₀ + 16 * G < g₂ r := fun r hr hrq hk => by
    rw [hg₂val r hr (hne_p r hr hk) hrq]
    exact hv₀u r hr hk
  have hD₁k : ∀ r hr, (D₁.chart r hr).k = (D.chart r hr).k := fun r hr =>
    (hD₁c r hr).2.1.trans (hD₂k r hr)
  have hD₁χ : ∀ r hr, (D₁.chart r hr).χ = (D.chart r hr).χ := fun r hr =>
    (hD₁c r hr).1.trans (hD₂c r hr).1
  have hD₁r₀ : ∀ r hr, (D₁.chart r hr).r₀ = (D₂.chart r hr).r₀ := fun r hr => (hD₁c r hr).2.2.1
  have hD₁R : ∀ r hr, (D₁.chart r hr).R ≤ R₀ := fun r hr =>
    (hD₁c r hr).2.2.2.1.trans ((hD₂c r hr).2.2.1.trans (hD r hr).1)
  have hD₁RG : ∀ r hr, (D₁.chart r hr).R ^ 2 ≤ G := fun r hr =>
    pow_le_pow_left₀ (D₁.chart r hr).R_pos.le (hD₁R r hr) 2
  have hqI₁ : g₁ q ∉ Ioo a₁ b₁ := by rw [hg₁q]; exact fun h => by linarith [h.2]
  have hD₁rmq : D₁.rm q hq = D₂.rm q hq := hD₁rmO q hq hqI₁
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hR₁rm : ∀ r hr, D₁.rm r hr ≤ (D₁.chart r hr).R := fun r hr => (D₁.hrm r hr).2
  have hr₀ε' : ∀ r hr, (D₁.chart r hr).r₀ ^ 2 / 2 < ε' := fun r hr => by
    rw [hD₁r₀]; linarith [(hD₂r₀ r hr).2.1]
  have hpI₂ : f p ∉ Ioo a₂ b₂ := fun h => by have := hidx1 p hp h; omega
  have hrmp : D.rm p hp / 2 ≤ (D₁.chart p hp).R := by
    have h1 := hD₁rmp; have h2 := hD₂rmO p hp hpI₂; have h3 := hD₁Rp
    linarith
  have hrmq : D₂.rm q hq ≤ (D₁.chart q hq).R := by rw [← hD₁rmq]; exact hR₁rm q hq
  have hgood₁ : goodPair D₁ ε' p q hp hq :=
    goodPair_congr (hD₁c q hq).1 (hD₁c p hp).2.1 (hD₁c q hq).2.1 hbasin₁ hgood₂
  have hmod := hmod₁.trans hmod₂
  have hcritIff : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := fun x =>
    (hcrit₂ x).trans (hcrit₁ x)
  have hidxEq : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g₂ x = morseIndex I f x := fun x hx => by
    rw [hidx₂ x ((hcrit₁ x).2 hx), hidx₁ x hx]
  have hg₂other' : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ p → x ≠ q → g₂ x = f x := fun x hx hxp hxq => by
    rw [hg₂other x ((hcrit₁ x).2 hx) hxp, hg₁other x hx hxq]
  refine ⟨g₂, D₁, ε', v₀, G, hG0, hεG, hε'0, hε'ε, hav₀, by linarith, hmod, hstrip₂, hcritIff,
    hidxEq,
    hg₂other', hg₂p, hg₂q, hg₂lo, hg₂hi, fun r hr => ⟨hD₁χ r hr, hD₁k r hr, hr₀ε' r hr,
    hD₁RG r hr⟩, fun r hr hrpq => ?_, hgood₁⟩
  rcases hrpq with rfl | rfl
  · have h1 := (hD₂r₀ r hr).2.2
    rw [hD₂rmO r hr hpI₂] at h1
    refine ⟨?_, ?_, ?_⟩
    · rw [hD₁r₀]; linarith
    · have h2 : (D.rm r hr / 2) ^ 2 ≤ (D₁.chart r hr).R ^ 2 :=
        pow_le_pow_left₀ (by linarith [D.rm_pos r hr]) hrmp 2
      nlinarith only [h2, hε'p]
    · rw [hD₁Rp]; linarith [(D₁.chart r hr).R_pos]
  · have h1 := (hD₂r₀ r hr).2.2
    refine ⟨?_, ?_, ?_⟩
    · rw [hD₁r₀]; have := (D₂.chart r hr).hr₀; nlinarith only [h1, this, hn1, hrmq]
    · have h2 : D₂.rm r hr ^ 2 ≤ (D₁.chart r hr).R ^ 2 :=
        pow_le_pow_left₀ (D₂.rm_pos r hr).le hrmq 2
      linarith only [h2, hε'q]
    · rw [hD₁rmq]
      have := (hD₁c r hr).2.2.2.1
      linarith [hD₂Rq, (D₁.chart r hr).R_pos]

theorem exists_isolated_pair [SigmaCompactSpace M] [DecidableEq M] (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {ε r' R₀ : ℝ} (hε : 0 < ε) (hr'ε : r' ^ 2 < ε)
    (hD : ∀ p hp, (D.chart p hp).R ≤ R₀ ∧ (D.chart p hp).r₀ ^ 2 < 2 * ε ∧
      24 * ε < D.rm p hp ^ 2 ∧ (D.chart p hp).r₀ < r')
    (hE2 : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r'}, ∀ t,
        D.flow t x ∉ (D.chart q hq).χ '' {y | morseNorm n y < r'})
    (hE3 : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
        D.flow t x ∉ (D.chart p hp).χ '' {y | morseNorm n y < r'})
    (hgap : ∀ r ∈ crit, ∀ s ∈ crit, f r < f s → f r + 16 * R₀ ^ 2 < f s)
    (hab : ∀ r ∈ crit, a + 16 * R₀ ^ 2 < f r ∧ f r + 16 * R₀ ^ 2 < b)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hgood : goodPair D ε p q hp hq) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ isSelfIndexing I g a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ p → x ≠ q → g x = f x) ∧
      ∃ a' b' : ℝ, a < a' ∧ a' < g p ∧ g p < g q ∧ g q < b' ∧ b' < b ∧
        (∀ x, g x = a' ∨ g x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) ∧
        (∀ x, x ∈ ({p, q} : Finset M) ↔ g x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) ∧
        ∃ D' : GradientLikeStrip I g a' b' {p, q}, ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
          goodPair D' ε' p q (Finset.mem_insert_self p {q})
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self q)) ∧
          (∀ p' hp', (D'.chart p' hp').r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < D'.rm p' hp' ^ 2) ∧
          g p + 2 * ε' < g q ∧
          (∀ y, g y ∈ Icc (g p + ε') (g q - ε') → ∀ p' hp', y ∉ D'.smallBall p' hp') := by
  classical
  obtain ⟨g₂, D₁, ε', v₀, G, hG0, hεG, hε'0, hε'ε, hav₀, hv₀b, hmod, hstrip₂, hcritIff, hidxEq,
    hg₂other', hg₂p', hg₂q', hg₂lo, hg₂hi, hD₁c, hD₁pq, hgood₁⟩ :=
    exists_moves hf hsi hinj hcrit D hε hr'ε hD hE2 hE3 hgap hab hp hq hgood
  have hkp : (D.chart p hp).k = 0 := hgood.1
  obtain ⟨hkq, -⟩ := hgood.2
  have hpq : p ≠ q := fun h => by subst h; exact one_ne_zero (hkq.symm.trans hkp)
  have hcritg₂ : ∀ x, x ∈ crit ↔ g₂ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x := by
    intro x
    rw [hcrit x, hcritIff x]
    have : g₂ x ∈ Ioo a b ↔ f x ∈ Ioo a b := Set.ext_iff.1 hmod.preimage_Ioo x
    rw [this]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  set a' : ℝ := v₀ + 2 * G with ha'def
  set b' : ℝ := v₀ + 10 * G with hb'def
  have hpmem : p ∈ ({p, q} : Finset M) := Finset.mem_insert_self p {q}
  have hqmem : q ∈ ({p, q} : Finset M) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hsub : ∀ r ∈ ({p, q} : Finset M), r ∈ crit := by
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact hp
    · rw [Finset.mem_singleton.1 hr]; exact hq
  have hcases : ∀ r (hr : r ∈ ({p, q} : Finset M)), r = p ∨ r = q := fun r hr => by
    rcases Finset.mem_insert.1 hr with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.1 h)
  set R'n : ∀ r ∈ ({p, q} : Finset M), ℝ := fun r hr => (D₁.chart r (hsub r hr)).R / (n + 1)
    with hR'ndef
  set Rn : ∀ r ∈ ({p, q} : Finset M), ℝ := fun r hr => R'n r hr / 2 with hRndef
  have h2n : (0 : ℝ) < 2 * (n + 1) := by positivity
  have h2n' : (0 : ℝ) < (2 * (n + 1)) ^ 2 := by positivity
  have hRn_eq : ∀ r hr, Rn r hr = (D₁.chart r (hsub r hr)).R / (2 * (n + 1)) := fun r hr => by
    simp only [hRndef, hR'ndef]; rw [div_div, mul_comm]
  have hRnpos : ∀ r hr, 0 < Rn r hr := fun r hr => by
    rw [hRn_eq r hr]; exact div_pos (D₁.chart r (hsub r hr)).R_pos h2n
  have hRn_le : ∀ r hr, Rn r hr ≤ (D₁.chart r (hsub r hr)).R := fun r hr => by
    rw [hRn_eq r hr]
    exact div_le_self (D₁.chart r (hsub r hr)).R_pos.le (by linarith)
  have hr₀Rn : ∀ r hr, 4 * (D₁.chart r (hsub r hr)).r₀ < Rn r hr := fun r hr => by
    rw [hRn_eq r hr, lt_div_iff₀ h2n]
    have h1 := (hD₁pq r (hsub r hr) (hcases r hr)).1
    linarith
  have hε'Rn : ∀ r hr, 8 * ε' < Rn r hr ^ 2 := fun r hr => by
    rw [hRn_eq r hr, div_pow, lt_div_iff₀ h2n']
    have h1 := (hD₁pq r (hsub r hr) (hcases r hr)).2.1
    have h2 : (2 * ((n : ℝ) + 1)) ^ 2 = 4 * (n + 1) ^ 2 := by ring
    rw [h2]; linarith
  have hRnrm : ∀ r hr, Rn r hr ≤ D₁.rm r (hsub r hr) := fun r hr => by
    rw [hRn_eq r hr]
    have h1 := (hD₁pq r (hsub r hr) (hcases r hr)).2.2
    have h2 : (D₁.chart r (hsub r hr)).R / (2 * (n + 1)) ≤ (D₁.chart r (hsub r hr)).R / 2 :=
      div_le_div_of_nonneg_left (D₁.chart r (hsub r hr)).R_pos.le two_pos
        (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hother : ∀ r hr, r ∉ ({p, q} : Finset M) → ∀ y ∈ D₁.smallBall r hr, g₂ y ∉ Icc a' b' := by
    intro r hr hrpq y hy hyI
    have hrp : r ≠ p := fun h => hrpq (h ▸ hpmem)
    have hrq : r ≠ q := fun h => hrpq (h ▸ hqmem)
    have h1 := abs_f_sub_lt_of_mem_smallBall hr hy
    have h2 := (hD₁c r hr).2.2.1
    rw [abs_lt] at h1
    rcases Nat.eq_zero_or_pos (D.chart r hr).k with h | h
    · have := hg₂lo r hr hrp h; linarith [hyI.1]
    · have := hg₂hi r hr hrq h; linarith [hyI.2]
  obtain ⟨D', hD'c, hD'rm, hD'V⟩ := exists_restrict D₁ (a' := a') (b' := b') (by linarith)
    (by linarith) {p, q} hsub hother Rn R'n Rn
    (fun r hr => ⟨hr₀Rn r hr, hRn_le r hr⟩)
    (fun r hr => by
      refine ⟨?_, ?_⟩
      · rw [hRn_eq r hr]
        change (D₁.chart r (hsub r hr)).R / (2 * (n + 1)) < (D₁.chart r (hsub r hr)).R / (n + 1)
        rw [div_lt_div_iff₀ h2n hn1]
        nlinarith [(D₁.chart r (hsub r hr)).R_pos]
      · change (D₁.chart r (hsub r hr)).R / (n + 1) ≤ (D₁.chart r (hsub r hr)).R'
        have h1 : (D₁.chart r (hsub r hr)).R / (n + 1) ≤ (D₁.chart r (hsub r hr)).R :=
          div_le_self (D₁.chart r (hsub r hr)).R_pos.le (by linarith)
        exact h1.trans (D₁.chart r (hsub r hr)).hRR'.le)
    (fun r hr => ⟨by linarith [hr₀Rn r hr, (D₁.chart r (hsub r hr)).hr₀], hRnrm r hr, le_rfl⟩)
    (fun r hr => by
      rintro _ ⟨y, hy, rfl⟩
      have hyn : morseNorm n y < (D₁.chart r (hsub r hr)).R := by
        have h1 := morseNorm_le_succ_mul_norm y
        have h2 : ‖y‖ < R'n r hr := by simpa using hy
        simp only [hR'ndef] at h2
        rw [lt_div_iff₀ hn1] at h2
        linarith
      have hlev := (D₁.chart r (hsub r hr)).f_mem_Icc_of_morseNorm_le le_rfl hyn.le
      have hRG := (hD₁c r (hsub r hr)).2.2.2
      rcases hcases r hr with rfl | rfl
      · rw [hg₂p'] at hlev; exact ⟨by linarith [hlev.1], by linarith [hlev.2]⟩
      · rw [hg₂q'] at hlev; exact ⟨by linarith [hlev.1], by linarith [hlev.2]⟩)
    (fun x hx hxpq hxc => by
      have hxp : x ≠ p := fun h => hxpq (h ▸ hpmem)
      have hxq : x ≠ q := fun h => hxpq (h ▸ hqmem)
      rcases Nat.eq_zero_or_pos (D.chart x hxc).k with h | h
      · have := hg₂lo x hxc hxp h; linarith [hx.1]
      · have := hg₂hi x hxc hxq h; linarith [hx.2])
  have hbasin' : D'.basin p hpmem = D₁.basin p hp := by
    rw [basin_eq_of_le (D := D₁) (hp := hp) (by rw [(hD₁c p hp).2.1]; exact hkp) (hRnpos p hpmem)
      (hRnrm p hpmem)]
    ext x
    unfold basin
    rw [(hD'c p hpmem).1, hD'rm p hpmem]
    constructor
    · rintro ⟨t, ht, hmem⟩
      exact ⟨t, ht, by rwa [flow_eq_of_V_eq D₁ D' hD'V] at hmem⟩
    · rintro ⟨t, ht, hmem⟩
      exact ⟨t, ht, by rwa [flow_eq_of_V_eq D₁ D' hD'V]⟩
  have hgood' : goodPair D' ε' p q hpmem hqmem :=
    goodPair_congr (hD'c q hqmem).1 (hD'c p hpmem).2.1 (hD'c q hqmem).2.1 hbasin' hgood₁
  have hcritsub : ∀ x, x ∈ ({p, q} : Finset M) ↔ g₂ x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x := by
    intro x
    constructor
    · intro hx
      rcases hcases x hx with rfl | rfl
      · exact ⟨by rw [hg₂p']; constructor <;> linarith, (hcritIff x).2 ((hcrit x).1 hp).2⟩
      · exact ⟨by rw [hg₂q']; constructor <;> linarith, (hcritIff x).2 ((hcrit x).1 hq).2⟩
    · rintro ⟨hxI, hxc⟩
      have hxc' : x ∈ crit :=
        (hcritg₂ x).2 ⟨⟨by linarith [hxI.1], by linarith [hxI.2]⟩, hxc⟩
      by_contra hxpq
      have hxp : x ≠ p := fun h => hxpq (h ▸ hpmem)
      have hxq : x ≠ q := fun h => hxpq (h ▸ hqmem)
      rcases Nat.eq_zero_or_pos (D.chart x hxc').k with h | h
      · have := hg₂lo x hxc' hxp h; linarith [hxI.1]
      · have := hg₂hi x hxc' hxq h; linarith [hxI.2]
  have hreg' : ∀ x, g₂ x = a' ∨ g₂ x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x := by
    intro x hx hxc
    have hxab : g₂ x ∈ Ioo a b := by
      rcases hx with hx | hx <;> rw [hx] <;> constructor <;> linarith
    have hxc' : x ∈ crit := (hcritg₂ x).2 ⟨hxab, hxc⟩
    by_cases hxp : x = p
    · subst hxp; rw [hg₂p'] at hx; rcases hx with hx | hx <;> linarith
    by_cases hxq : x = q
    · subst hxq; rw [hg₂q'] at hx; rcases hx with hx | hx <;> linarith
    rcases Nat.eq_zero_or_pos (D.chart x hxc').k with h | h
    · have := hg₂lo x hxc' hxp h; rcases hx with hx | hx <;> linarith
    · have := hg₂hi x hxc' hxq h; rcases hx with hx | hx <;> linarith
  have hsi' : isSelfIndexing I g₂ a b := by
    intro r s hr hs hcr hcs hlt
    have hrc : r ∈ crit := (hcritg₂ r).2 ⟨hr, hcr⟩
    have hsc : s ∈ crit := (hcritg₂ s).2 ⟨hs, hcs⟩
    have hkr : (D.chart r hrc).k = morseIndex I g₂ r := by
      rw [hidxEq r ((hcrit r).1 hrc).2]; exact (D.chart r hrc).hkidx.symm
    have hks : (D.chart s hsc).k = morseIndex I g₂ s := by
      rw [hidxEq s ((hcrit s).1 hsc).2]; exact (D.chart s hsc).hkidx.symm
    rw [← hkr, ← hks] at hlt
    by_cases hsp : s = p
    · subst hsp
      have : (D.chart s hsc).k = 0 := hkp
      omega
    by_cases hsq : s = q
    · subst hsq
      rw [hg₂q']
      have hkr0 : (D.chart r hrc).k = 0 := by
        have : (D.chart s hsc).k = 1 := hkq
        omega
      by_cases hrp : r = p
      · subst hrp; rw [hg₂p']; linarith
      · linarith [hg₂lo r hrc hrp hkr0]
    have hs1 : 1 ≤ (D.chart s hsc).k := by omega
    have hgs := hg₂hi s hsc hsq hs1
    by_cases hrp : r = p
    · subst hrp; rw [hg₂p']; linarith
    by_cases hrq : r = q
    · subst hrq; rw [hg₂q']; linarith
    rcases Nat.eq_zero_or_pos (D.chart r hrc).k with hkr0 | hkr1
    · linarith [hg₂lo r hrc hrp hkr0]
    · rw [hg₂other' r ((hcrit r).1 hrc).2 hrp hrq, hg₂other' s ((hcrit s).1 hsc).2 hsp hsq]
      exact hsi r s ((hcrit r).1 hrc).1 ((hcrit s).1 hsc).1 ((hcrit r).1 hrc).2
        ((hcrit s).1 hsc).2 (by rwa [← (D.chart r hrc).hkidx, ← (D.chart s hsc).hkidx] at hlt)
  refine ⟨g₂, hmod, hstrip₂, hsi', hcritIff, hidxEq, hg₂other', a', b', by linarith,
    by rw [hg₂p']; linarith, by rw [hg₂p', hg₂q']; linarith, by rw [hg₂q']; linarith,
    by linarith, hreg', hcritsub, D', ε', hε'0, hε'ε, hgood', ?_, ?_, ?_⟩
  · intro r hr
    refine ⟨?_, ?_⟩
    · rw [(hD'c r hr).2.2.1]
      have := (hD₁c r (hsub r hr)).2.2.1
      linarith
    · rw [hD'rm r hr]
      exact hε'Rn r hr
  · rw [hg₂p', hg₂q']; linarith
  · intro y hy r hr hmem
    have hsmall : y ∈ D₁.smallBall r (hsub r hr) := by
      unfold smallBall at hmem ⊢
      rwa [(hD'c r hr).1, (hD'c r hr).2.2.1] at hmem
    have h1 := abs_f_sub_lt_of_mem_smallBall (hsub r hr) hsmall
    have h2 := (hD₁c r (hsub r hr)).2.2.1
    rw [abs_lt] at h1
    rcases hcases r hr with rfl | rfl
    · rw [hg₂p'] at h1; linarith [hy.1]
    · rw [hg₂q'] at h1; linarith [hy.2]

end GradientLikeStrip

end

end DifferentialGeometry.Topology
