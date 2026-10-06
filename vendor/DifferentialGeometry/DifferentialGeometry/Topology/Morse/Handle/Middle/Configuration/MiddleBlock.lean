module

public import DifferentialGeometry.Topology.Morse.Handle.Middle.Configuration.MiddleTransport

@[expose] public section

set_option autoImplicit false

open Set Filter
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem dimH_image_sardMap_lt (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) {ε c η : ℝ} (hε : 0 < ε)
    (hεR : 2 * ε ≤ (D.chart q hq).R ^ 2)
    (hle : (D.chart q hq).k ≤ (D.chart p hp).k) (hkp : 1 ≤ (D.chart p hp).k) :
    dimH (D.sardMap p hq ε c η hp '' D.sardDom p hq ε c η hp) < ((D.chart p hp).k : ENNReal) := by
  classical
  have _hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf
  have key : ∀ (k : ℕ) (S : (Fin k → ℝ) → EuclideanSpace ℝ (Fin (D.chart p hp).k))
      (U : Set (Fin k → ℝ)), (∀ w ∈ U, w ≠ 0) →
      (∀ w ∈ U, ∀ t : ℝ, 0 < t → t • w ∈ U ∧ S (t • w) = S w) →
      (∀ w ∈ U, ∃ C : NNReal, ∃ s ∈ 𝓝 w, LipschitzOnWith C S s) →
      dimH (S '' U) ≤ ((k - 1 : ℕ) : ENNReal) := by
    intro k S U hU0 hray hloc
    cases k with
    | zero =>
      have hUe : U = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro w hw
        exact hU0 w hw (Subsingleton.elim _ _)
      simp [hUe]
    | succ m =>
      have hsub : S '' U ⊆ ⋃ (i : Fin (m + 1)) (b : Bool),
          S '' (U ∩ {w | w i = if b then 1 else -1}) := by
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨i, hi⟩ := Function.ne_iff.1 (hU0 w hw)
        have hwi : w i ≠ 0 := hi
        have ht : 0 < |w i|⁻¹ := inv_pos.2 (abs_pos.2 hwi)
        obtain ⟨h1, h2⟩ := hray w hw _ ht
        refine Set.mem_iUnion₂.2 ⟨i, decide (0 < w i), |w i|⁻¹ • w, ⟨h1, ?_⟩, h2⟩
        change |w i|⁻¹ * w i = _
        rcases lt_or_gt_of_ne hwi with h | h
        · rw [abs_of_neg h]
          simp [not_lt.2 h.le, inv_neg, neg_mul, inv_mul_cancel₀ hwi]
        · rw [abs_of_pos h]
          simp [h, inv_mul_cancel₀ hwi]
      have hH : ∀ (i : Fin (m + 1)) (s : ℝ),
          dimH {w : Fin (m + 1) → ℝ | w i = s} ≤ (m : ENNReal) := by
        intro i s
        have hlip : LipschitzWith 1 (fun x : Fin m → ℝ => (Fin.insertNth i s x : Fin (m + 1) → ℝ)) := by
          refine LipschitzWith.of_dist_le_mul fun x y => ?_
          rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
          intro j
          refine Fin.succAboveCases i ?_ (fun j' => ?_) j
          · simp
          · simp only [Fin.insertNth_apply_succAbove]
            exact dist_le_pi_dist x y j'
        calc dimH {w : Fin (m + 1) → ℝ | w i = s}
            ≤ dimH (Set.range (fun x : Fin m → ℝ => (Fin.insertNth i s x : Fin (m + 1) → ℝ))) := by
              apply dimH_mono
              intro w hw
              have hw' : w i = s := hw
              subst hw'
              exact ⟨Fin.removeNth i w, Fin.insertNth_self_removeNth i w⟩
          _ ≤ dimH (Set.univ : Set (Fin m → ℝ)) := hlip.dimH_range_le
          _ = m := by rw [Real.dimH_univ_pi]; simp
      calc dimH (S '' U)
          ≤ dimH (⋃ (i : Fin (m + 1)) (b : Bool),
              S '' (U ∩ {w | w i = if b then 1 else -1})) := dimH_mono hsub
        _ = ⨆ (i : Fin (m + 1)) (b : Bool),
              dimH (S '' (U ∩ {w | w i = if b then 1 else -1})) := by
            simp only [dimH_iUnion]
        _ ≤ m := by
            refine iSup₂_le fun i b => ?_
            calc dimH (S '' (U ∩ {w | w i = if b then 1 else -1}))
                ≤ dimH (U ∩ {w | w i = if b then 1 else -1}) := by
                  apply dimH_image_le_of_locally_lipschitzOn
                  intro w hw
                  obtain ⟨C, s, hs, hL⟩ := hloc w hw.1
                  exact ⟨C, s, mem_nhdsWithin_of_mem_nhds hs, hL⟩
              _ ≤ dimH {w : Fin (m + 1) → ℝ | w i = if b then 1 else -1} :=
                  dimH_mono inter_subset_right
              _ ≤ m := hH i _
        _ = ((m + 1 - 1 : ℕ) : ENNReal) := by simp
  have hU0 : ∀ w ∈ D.sardDom p hq ε c η hp, w ≠ 0 := fun w hw => hw.1
  have hray : ∀ w ∈ D.sardDom p hq ε c η hp, ∀ t : ℝ, 0 < t →
      t • w ∈ D.sardDom p hq ε c η hp ∧
        D.sardMap p hq ε c η hp (t • w) = D.sardMap p hq ε c η hp w := by
    intro w hw t ht
    have hl := D.landing_smul p hq ε c η ht hw.1
    refine ⟨⟨smul_ne_zero ht.ne' hw.1, ?_⟩, ?_⟩
    · change D.landing p hq ε c η (t • w) ∈
        (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}
      rw [hl]
      exact hw.2
    · unfold sardMap
      rw [hl]
  have hloc : ∀ w ∈ D.sardDom p hq ε c η hp, ∃ C : NNReal, ∃ s ∈ 𝓝 w,
      LipschitzOnWith C (D.sardMap p hq ε c η hp) s := by
    rintro w ⟨hw0, hland⟩
    have hw0' : w ≠ 0 := hw0
    have hland' : D.landing p hq ε c η w ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
      (D.chart p hp).image_lt_subset_image_ball (D.chart p hp).hRR'.le hland
    have hsp : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        ((D.chart q hq).sphereParam ε) w :=
      contMDiffAt_iff_contDiffAt.2 ((D.chart q hq).contDiffAt_sphereParam ε hw0')
    have hχq : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (D.chart q hq).χ
        ((D.chart q hq).sphereParam ε w) :=
      (D.chart q hq).contMDiffAt_chart
        ((D.chart q hq).mem_ball_of_le ((D.chart q hq).morseNorm_sphereParam_le hε.le hεR hw0'))
    have hfl1 : ContMDiffAt I I ∞ (D.flow (f q - ε - c))
        ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) := (D.contMDiff_flow _).contMDiffAt
    have hfl2 : ContMDiffAt I I ∞ (D.flow (c - (f p + η)))
        (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) :=
      (D.contMDiff_flow _).contMDiffAt
    have hsymm : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (D.chart p hp).χ.symm
        (D.landing p hq ε c η w) :=
      (D.chart p hp).contMDiffAt_symm hland'
    have c1 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞
        (fun w => (D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) w := hχq.comp w hsp
    have c2 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞
        (fun w => D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) w :=
      hfl1.comp w c1
    have c3 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) I ∞
        (D.landing p hq ε c η) w :=
      hfl2.comp w c2
    have c4 : ContMDiffAt 𝓘(ℝ, Fin (D.chart q hq).k → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun w => (D.chart p hp).χ.symm (D.landing p hq ε c η w)) w :=
      hsymm.comp w c3
    have hg : ContDiffAt ℝ 1 (fun w => (D.chart p hp).χ.symm (D.landing p hq ε c η w)) w :=
      (contMDiffAt_iff_contDiffAt.1 c4).of_le (by exact_mod_cast le_top)
    obtain ⟨K, t, ht, hL⟩ := hg.exists_lipschitzOnWith
    set y₀ := (D.chart p hp).χ.symm (D.landing p hq ε c η w) with hy₀
    obtain ⟨K', hJ⟩ : ∃ K' : NNReal,
        LipschitzOnWith K' (ModelField.scaledNegativePart (D.chart p hp).hk) (Metric.ball y₀ 1) := by
      set P := ModelField.posPartL (D.chart p hp).hk with hP
      set N := ModelField.negPartL (D.chart p hp).hk with hN
      set R := ‖y₀‖ + 1 with hR
      have hR0 : 0 ≤ R := by positivity
      refine ⟨⟨2 * ‖P‖ * ‖N‖ * R, by positivity⟩,
        LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
      have hxR : ‖x‖ ≤ R := by
        have := norm_le_norm_add_norm_sub' x y₀
        have h2 : ‖x - y₀‖ < 1 := by rw [← dist_eq_norm]; exact hx
        linarith
      have hyR : ‖y‖ ≤ R := by
        have := norm_le_norm_add_norm_sub' y y₀
        have h2 : ‖y - y₀‖ < 1 := by rw [← dist_eq_norm]; exact hy
        linarith
      have hPx : ‖P x‖ ≤ ‖P‖ * R :=
        (P.le_opNorm x).trans (mul_le_mul_of_nonneg_left hxR (norm_nonneg _))
      have hNy : ‖N y‖ ≤ ‖N‖ * R :=
        (N.le_opNorm y).trans (mul_le_mul_of_nonneg_left hyR (norm_nonneg _))
      have hNd : ‖N x - N y‖ ≤ ‖N‖ * ‖x - y‖ := by
        rw [← map_sub]; exact N.le_opNorm _
      have hPd : |‖P x‖ - ‖P y‖| ≤ ‖P‖ * ‖x - y‖ := by
        refine (abs_norm_sub_norm_le _ _).trans ?_
        rw [← map_sub]; exact P.le_opNorm _
      have hJeq : ModelField.scaledNegativePart (D.chart p hp).hk x - ModelField.scaledNegativePart (D.chart p hp).hk y =
          ‖P x‖ • (N x - N y) + (‖P x‖ - ‖P y‖) • N y := by
        simp only [ModelField.scaledNegativePart, hP, hN, ModelField.posPartL_apply, ModelField.negPartL_apply,
          smul_sub, sub_smul]
        abel
      change dist _ _ ≤ (2 * ‖P‖ * ‖N‖ * R) * dist x y
      rw [dist_eq_norm, dist_eq_norm, hJeq]
      calc ‖‖P x‖ • (N x - N y) + (‖P x‖ - ‖P y‖) • N y‖
          ≤ ‖P x‖ * ‖N x - N y‖ + |‖P x‖ - ‖P y‖| * ‖N y‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm]
        _ ≤ (‖P‖ * R) * (‖N‖ * ‖x - y‖) + (‖P‖ * ‖x - y‖) * (‖N‖ * R) := by
            gcongr
        _ = 2 * ‖P‖ * ‖N‖ * R * ‖x - y‖ := by ring
    refine ⟨K' * K, t ∩ (fun w => (D.chart p hp).χ.symm (D.landing p hq ε c η w)) ⁻¹'
      Metric.ball y₀ 1, inter_mem ht
        (hg.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos)), ?_⟩
    exact hJ.comp (hL.mono inter_subset_left) (fun x hx => hx.2)
  calc dimH (D.sardMap p hq ε c η hp '' D.sardDom p hq ε c η hp)
      ≤ (((D.chart q hq).k - 1 : ℕ) : ENNReal) := key _ _ _ hU0 hray hloc
    _ < ((D.chart p hp).k : ENNReal) := by
        exact_mod_cast (by omega : (D.chart q hq).k - 1 < (D.chart p hp).k)

theorem exists_twist_stage_index (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {μ : ℕ} (hμ : 1 ≤ μ) {p : M} (hp : p ∈ crit)
    (hkp : (D.chart p hp).k = μ) (Q : Finset M) (hQ : ∀ q ∈ Q, q ∈ crit)
    (hkQ : ∀ q (hq : q ∈ crit), q ∈ Q → (D.chart q hq).k = μ) {ε c : ℝ} (hε : 0 < ε)
    (hεR : ∀ q hq, 2 * ε ≤ (D.chart q hq).R ^ 2) (hr₀p : 4 * (D.chart p hp).r₀ ^ 2 < 32 * ε)
    (hrmp : 65 * ε < D.rm p hp ^ 2) (hc : f p + 32 * ε < c) (hcb : c ≤ b)
    (hcQ : ∀ q ∈ Q, c ≤ f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + 32 * ε) c → ∀ p' hp', y ∉ D.smallBall p' hp') :
    ∃ D' : GradientLikeStrip I f a b crit,
      D'.chart = D.chart ∧
      D'.rm p hp ^ 2 = 32 * ε ∧ (∀ q hq, q ≠ p → D'.rm q hq = D.rm q hq) ∧
      (∀ x, f p + 32 * ε ≤ f x → D'.V x = D.V x) ∧
      (∀ x, x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' → D'.V x = D.V x) ∧
      ∀ q hq, q ∈ Q → Disjoint (D'.rightSphere p hp ε c) (D'.leftSphere q hq ε c) := by
  classical
  have hpa : a < f p := (D.f_mem_Ioo p hp).1
  have hrmp0 := D.rm_pos p hp
  have hrmpR : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 := pow_le_pow_left₀ hrmp0.le (D.hrm p hp).2 2
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 32 * ε := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ε := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hρ : 0 < ρ := by rw [hρdef]; exact hε
  have hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2 := by
    rw [hρdef, hηdef]
    have : 18 * ε ^ 2 / (32 * ε) = 9 * ε / 16 := by field_simp; ring
    rw [this]; linarith [hεR p hp]
  have hηrm : η ≤ D.rm p hp ^ 2 := by rw [hηdef]; linarith
  have hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η := by rw [hηdef]; exact hr₀p
  have hεη : ε ≤ η / 2 := by rw [hηdef]; linarith
  have hr₀ε : (D.chart p hp).r₀ ^ 2 ≤ 8 * ε := by linarith
  have hB : 2 * η + ρ ^ 2 / ε < D.rm p hp ^ 2 := by
    rw [hρdef, hηdef]
    have : ε ^ 2 / ε = ε := by field_simp
    rw [this]; linarith
  have hηc : f p + η < c := by rw [hηdef]; exact hc
  have hlevη : ∀ y, f y ∈ Icc (f p + η) c → ∀ p' hp', y ∉ D.smallBall p' hp' :=
    fun y hy => hlev y (by rw [hηdef] at hy; exact hy)
  set F : Set (EuclideanSpace ℝ (Fin (D.chart p hp).k)) := ⋃ q : {q // q ∈ Q},
    D.sardMap p (hQ q.1 q.2) ε c η hp '' D.sardDom p (hQ q.1 q.2) ε c η hp with hF
  have hkp1 : 1 ≤ (D.chart p hp).k := by rw [hkp]; exact hμ
  have hdimq : ∀ q : {q // q ∈ Q}, dimH (D.sardMap p (hQ q.1 q.2) ε c η hp ''
      D.sardDom p (hQ q.1 q.2) ε c η hp) < ((D.chart p hp).k : ENNReal) := fun q =>
    dimH_image_sardMap_lt hf D hp (hQ q.1 q.2) hε (hεR q.1 (hQ q.1 q.2))
      (by rw [hkQ q.1 (hQ q.1 q.2) q.2, hkp]) hkp1
  have hdimF : dimH F < ((D.chart p hp).k : ENNReal) := by
    rw [hF, dimH_iUnion]
    rcases isEmpty_or_nonempty {q // q ∈ Q} with hQe | hQne
    · rw [iSup_of_empty, bot_eq_zero]
      exact_mod_cast (show (0 : ℕ) < (D.chart p hp).k by omega)
    · exact Finite.ciSup_lt_iff.2 hdimq
  have hdimF' : dimH F < Module.finrank ℝ (EuclideanSpace ℝ (Fin (D.chart p hp).k)) := by
    rw [finrank_euclideanSpace_fin]; exact hdimF
  have hdense := dense_compl_of_dimH_lt_finrank hdimF'
  obtain ⟨z, hzF, hzρ⟩ := hdense.exists_mem_open Metric.isOpen_ball
    ⟨(0 : EuclideanSpace ℝ (Fin (D.chart p hp).k)), Metric.mem_ball_self hρ⟩
  have hz : ‖z‖ ≤ ρ := by
    have := Metric.mem_ball.1 hzρ
    rw [dist_zero_right] at this
    exact this.le
  have hzF' : ∀ q hq, q ∈ Q → z ∉ D.sardMap p hq ε c η hp '' D.sardDom p hq ε c η hp :=
    fun q hq hqQ h => hzF (mem_iUnion.2 ⟨⟨q, hqQ⟩, h⟩)
  refine ⟨twisted (z := z) hf hη hρ hsupp hηrm hr₀η, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [twisted_rm_self, Real.sq_sqrt hη.le, hηdef]
  · intro q hq h; exact twisted_rm_of_ne _ _ _ _ _ _ hq h
  · intro x hx
    rw [twisted_V]
    exact twistedV_eq_of_level_ge hη hρ hsupp (by rw [hηdef]; exact hx)
  · intro x hx
    rw [twisted_V]
    exact twistedV_of_notMem hx
  intro q hq hqQ
  have hεq : 2 * ε ≤ (D.chart q hq).R ^ 2 := hεR q hq
  have hcq : c ≤ f q - ε := hcQ q hqQ
  rw [leftSphere_twisted hf hη hρ hsupp hηrm hr₀η hq hεq hηc hcq]
  refine Set.disjoint_left.2 fun x hxR hxL => ?_
  have hxR' := rightSphere_twisted_subset hf hη hρ hsupp hηrm hr₀η hε hεη hr₀ε hz hB hηc hcb
    hlevη hxR
  obtain ⟨_, ⟨y₁, ⟨hy₁S, hy₁nf, hy₁J⟩, rfl⟩, rfl⟩ := hxR'
  obtain ⟨_, ⟨y₂, hy₂, rfl⟩, hx⟩ := hxL
  obtain ⟨hw0, hsp⟩ := (D.chart q hq).sphereParam_of_mem hε hy₂
  have hy₁R : morseNorm n y₁ < (D.chart p hp).R := by
    have := lt_of_pow_lt_pow_left₀ 2 (D.rm_pos p hp).le
      (lt_of_le_of_lt (show morseNorm n y₁ ^ 2 ≤ _ from hy₁S) hB)
    exact this.trans_le (D.hrm p hp).2
  have hland : D.landing p hq ε c η ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ)
      (negPart (D.chart q hq).hk y₂)) = (D.chart p hp).χ y₁ := by
    unfold landing
    rw [hsp, hx, flow_flow, show f p + η - c + (c - (f p + η)) = 0 by ring, flow_zero]
  apply hzF' q hq hqQ
  refine ⟨_, ⟨hw0, ?_⟩, ?_⟩
  · change D.landing p hq ε c η _ ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}
    rw [hland]
    exact ⟨y₁, hy₁R, rfl⟩
  · unfold sardMap
    rw [hland, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₁ hy₁R.le)]
    exact hy₁J

def portPrivate_3652466a_stageInvIdx (D₀ D : GradientLikeStrip I f a b crit) (S : Finset M) (ε : ℝ) : Prop :=
  (∀ q hq, (D.chart q hq).χ = (D₀.chart q hq).χ ∧ (D.chart q hq).k = (D₀.chart q hq).k ∧
    (D.chart q hq).R = (D₀.chart q hq).R ∧ (D.chart q hq).R' = (D₀.chart q hq).R') ∧
  (∀ q hq, (D.chart q hq).r₀ ≤ (D₀.chart q hq).r₀) ∧
  (∀ q hq, q ∈ S → D.rm q hq ^ 2 = 32 * ε) ∧
  (∀ q hq, q ∉ S → D.rm q hq = D₀.rm q hq) ∧
  (∀ q hq, q ∈ S → ∀ q' hq', morseIndex I f q' = morseIndex I f q → f q < f q' →
    Disjoint (D.rightSphere q hq ε (f q + 33 * ε)) (D.leftSphere q' hq' ε (f q + 33 * ε))) ∧
  (∀ q hq, q ∈ S → ∀ q' hq', morseIndex I f q' = morseIndex I f q → f q < f q' →
    ∀ x ∈ (D.chart q' hq').χ '' (D.chart q' hq').leftModelSphere ε, ∀ t, 0 ≤ t →
      D.flow t x ∉ D.smallBall q hq)

open Classical in
theorem portPrivate_3652466a_stageInvIdx.step (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {D₀ : GradientLikeStrip I f a b crit}
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ p ∈ crit, ∀ q ∈ crit, f p < f q → f p + 40 * ε < f q)
    (hab : ∀ p ∈ crit, a + 40 * ε < f p ∧ f p + 40 * ε < b)
    (hinj : ∀ p ∈ crit, ∀ q ∈ crit, f p = f q → p = q)
    (hmid : ∀ m ∈ crit, ∀ q ∈ crit, ∀ q' ∈ crit, f q < f m → f m < f q' →
      morseIndex I f q = morseIndex I f q' → morseIndex I f m = morseIndex I f q)
    (hR : ∀ q hq, 2 * ε ≤ (D₀.chart q hq).R ^ 2) (hr₀ : ∀ q hq, (D₀.chart q hq).r₀ ^ 2 < ε / 2)
    (hrm : ∀ q hq, 65 * ε < D₀.rm q hq ^ 2) {S' : Finset M}
    (hS' : ∀ q ∈ S', q ∈ crit ∧ 1 ≤ morseIndex I f q) {p : M} (hp : p ∈ crit)
    (hp1 : 1 ≤ morseIndex I f p) (hpS : p ∉ S') (hpmin : ∀ q ∈ S', f p < f q)
    (hup : ∀ q' ∈ crit, 1 ≤ morseIndex I f q' → f p < f q' → q' ∈ S')
    {D : GradientLikeStrip I f a b crit} (hD : portPrivate_3652466a_stageInvIdx D₀ D S' ε) :
    ∃ D' : GradientLikeStrip I f a b crit, portPrivate_3652466a_stageInvIdx D₀ D' (insert p S') ε := by
  classical
  obtain ⟨hD1, hD2, hD3, hD4, hD5, hD6⟩ := id hD
  have hr₀sq : ∀ q hq, (D.chart q hq).r₀ ^ 2 < ε / 2 := fun q hq =>
    lt_of_le_of_lt (pow_le_pow_left₀ (D.chart q hq).hr₀.le (hD2 q hq) 2) (hr₀ q hq)
  have hεR : ∀ q hq, 2 * ε ≤ (D.chart q hq).R ^ 2 := fun q hq => by
    rw [(hD1 q hq).2.2.1]; exact hR q hq
  have hsb : ∀ q hq x, x ∈ D.smallBall q hq → f x ∈ Icc (f q - ε / 4) (f q + ε / 4) := by
    intro q hq x hx
    have h := D.f_mem_Icc_of_mem_smallBall hx
    have h2 := hr₀sq q hq
    constructor <;> linarith [h.1, h.2]
  have hfarm : ∀ q' hq' x, x ∈ (D.chart q' hq').χ '' (D.chart q' hq').leftModelSphere ε →
      f x = f q' - ε := by
    intro q' hq' x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (D.chart q' hq').f_chart_of_mem_leftModelSphere (hεR q' hq') hy
  set μ : ℕ := morseIndex I f p with hμdef
  have hkp : (D.chart p hp).k = μ := (D.chart p hp).hkidx.symm
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = f p + 33 * ε := ⟨_, rfl⟩
  have hpab := hab p hp
  have hcb : c ≤ b := by linarith [hpab.2]
  have hcab : c ∈ Icc a b := ⟨by linarith [hpab.1], hcb⟩
  have hfar : ∀ q ∈ crit, q ≠ p → f q + 40 * ε < f p ∨ f p + 40 * ε < f q := by
    intro q hq hqp
    rcases lt_trichotomy (f q) (f p) with h | h | h
    · exact Or.inl (hgap q hq p hp h)
    · exact absurd (hinj q hq p hp h) hqp
    · exact Or.inr (hgap p hp q hq h)
  set Q : Finset M := S'.filter (fun q => morseIndex I f q = μ) with hQdef
  have hQS : ∀ q ∈ Q, q ∈ S' := fun q hq => (Finset.mem_filter.1 hq).1
  have hQ : ∀ q ∈ Q, q ∈ crit := fun q hq => (hS' q (hQS q hq)).1
  have hkQ : ∀ q (hq : q ∈ crit), q ∈ Q → (D.chart q hq).k = μ := fun q hq hqQ => by
    rw [← (D.chart q hq).hkidx]; exact (Finset.mem_filter.1 hqQ).2
  have hr₀p : 4 * (D.chart p hp).r₀ ^ 2 < 32 * ε := by linarith [hr₀sq p hp]
  have hrmp : 65 * ε < D.rm p hp ^ 2 := by rw [hD4 p hp hpS]; exact hrm p hp
  have hc : f p + 32 * ε < c := by rw [hcdef]; linarith
  have hcQ : ∀ q ∈ Q, c ≤ f q - ε := fun q hq => by
    have := hgap p hp q (hQ q hq) (hpmin q (hQS q hq)); rw [hcdef]; linarith
  have hlev : ∀ y, f y ∈ Icc (f p + 32 * ε) c → ∀ p' hp', y ∉ D.smallBall p' hp' := by
    intro y hy p' hp' hmem
    have h := hsb p' hp' y hmem
    by_cases hpp : p' = p
    · subst hpp; linarith [hy.1, h.2]
    · rcases hfar p' hp' hpp with h' | h' <;> linarith [hy.1, hy.2, h.1, h.2]
  obtain ⟨Dt, hDt_chart, hDt_rmp, hDt_rm, hDt_Vge, -, hDt_disj⟩ :=
    exists_twist_stage_index hf D hp1 hp hkp Q hQ hkQ hε hεR hr₀p hrmp hc hcb hcQ hlev
  have hmemQ : ∀ q' (hq' : q' ∈ crit), morseIndex I f q' = morseIndex I f p → f p < f q' →
      q' ∈ Q := by
    intro q' hq' hidx hlt
    refine Finset.mem_filter.2 ⟨hup q' hq' (by rw [hidx]; exact hp1) hlt, hidx⟩
  have htube : ∀ q hq, q ∈ Q → ∃ δ, 0 < δ ∧
      Disjoint (Dt.flow (f p + ε - c) '' ((Dt.chart p hp).χ '' Dt.rightTube p hp ε δ))
        (Dt.flow (f q - ε - c) '' ((Dt.chart q hq).χ '' Dt.leftTube q hq ε δ)) := by
    intro q hq hqQ
    exact exists_tube_disjoint Dt p hp q hq hε (by rw [hDt_chart]; exact hεR p hp)
      (by rw [hDt_chart]; exact hεR q hq) (hDt_disj q hq hqQ)
  obtain ⟨δ, hδ, hδdisj⟩ := exists_uniform_tube_disjoint Dt hp Q hQ htube
  have hr₀0 := (Dt.chart p hp).hr₀
  obtain ⟨r', hr'0, hr'A, -, hr'ε, hr'δ⟩ :=
    exists_small_radius hr₀0 hr₀0 hε (show 0 < 2 * ε * δ by positivity)
  have hr₀'pos : 0 < r' / 2 := by positivity
  have hle : r' / 2 ≤ (Dt.chart p hp).r₀ := by linarith
  obtain ⟨D', hD'def⟩ : ∃ D' : GradientLikeStrip I f a b crit,
    shrinkAt (D := Dt) hf hr₀'pos hle = D' := ⟨_, rfl⟩
  have hχt : ∀ q hq, (D'.chart q hq).χ = (Dt.chart q hq).χ := fun q hq => by
    rw [← hD'def]; rfl
  have hkt : ∀ q hq, (D'.chart q hq).k = (Dt.chart q hq).k := fun q hq => by
    rw [← hD'def]; rfl
  have hχ' : ∀ q hq, (D'.chart q hq).χ = (D.chart q hq).χ := fun q hq => by
    rw [hχt, hDt_chart]
  have hk' : ∀ q hq, (D'.chart q hq).k = (D.chart q hq).k := fun q hq => by
    rw [hkt, hDt_chart]
  have hR' : ∀ q hq, (D'.chart q hq).R = (D.chart q hq).R := fun q hq => by
    rw [← hD'def, shrinkAt_chart_R, hDt_chart]
  have hR'' : ∀ q hq, (D'.chart q hq).R' = (D.chart q hq).R' := fun q hq => by
    rw [← hD'def, shrinkAt_chart_R', hDt_chart]
  have hr₀'p : (D'.chart p hp).r₀ = r' / 2 := by
    rw [← hD'def]; exact shrinkAt_chart_r₀_self hf hr₀'pos hle
  have hr₀'ne : ∀ q hq, q ≠ p → (D'.chart q hq).r₀ = (D.chart q hq).r₀ := fun q hq h => by
    rw [← hD'def, shrinkAt_chart_r₀_of_ne hf hr₀'pos hle hq h, hDt_chart]
  have hrm' : ∀ q hq, D'.rm q hq = Dt.rm q hq := fun q hq => by rw [← hD'def]; rfl
  have hV't : ∀ x, f p + ε / 2 ≤ f x → D'.V x = Dt.V x := fun x hx => by
    rw [← hD'def, shrinkAt_V]
    exact shrunkV_eq_of_level hr₀'pos hle (ε₁ := ε / 2)
      (by rw [hDt_chart]; linarith [hr₀sq p hp]) (Or.inl hx)
  have hV' : ∀ x, f p + 32 * ε ≤ f x → D'.V x = D.V x := fun x hx => by
    rw [hV't x (by linarith), hDt_Vge x hx]
  have hle' : r' / 2 ≤ (D.chart p hp).r₀ := by rw [hDt_chart] at hle; exact hle
  have hsb' : ∀ q hq, D'.smallBall q hq ⊆ D.smallBall q hq := by
    intro q hq
    unfold smallBall
    rw [hχ' q hq]
    refine image_mono fun y (hy : morseNorm n y < _) => show morseNorm n y < _ from
      lt_of_lt_of_le hy ?_
    by_cases h : q = p
    · subst h; rw [hr₀'p]; exact hle'
    · rw [hr₀'ne q hq h]
  have hrm'p : D'.rm p hp ^ 2 = 32 * ε := by rw [hrm', hDt_rmp]
  have hrm'ne : ∀ q hq, q ≠ p → D'.rm q hq = D.rm q hq := fun q hq h => by
    rw [hrm', hDt_rm q hq h]
  have harm : ∀ q' hq', (D'.chart q' hq').χ '' (D'.chart q' hq').leftModelSphere ε =
      (D.chart q' hq').χ '' (D.chart q' hq').leftModelSphere ε := fun q' hq' => by
    rw [hχ' q' hq', leftModelSphere_eq (hk' q' hq')]
  have hsb'' : ∀ q hq x, x ∈ D'.smallBall q hq → f x ∈ Icc (f q - ε / 4) (f q + ε / 4) :=
    fun q hq x hx => hsb q hq x (hsb' q hq hx)
  refine ⟨D', fun q hq => ⟨?_, ?_, ?_, ?_⟩, fun q hq => ?_, fun q hq hqS => ?_,
    fun q hq hqS => ?_, fun q hq hqS q' hq' hidx hlt => ?_,
    fun q hq hqS q' hq' hidx hlt => ?_⟩
  · rw [hχ']; exact (hD1 q hq).1
  · rw [hk']; exact (hD1 q hq).2.1
  · rw [hR']; exact (hD1 q hq).2.2.1
  · rw [hR'']; exact (hD1 q hq).2.2.2
  · by_cases h : q = p
    · subst h; rw [hr₀'p]; exact hle'.trans (hD2 q hq)
    · rw [hr₀'ne q hq h]; exact hD2 q hq
  · rcases Finset.mem_insert.1 hqS with rfl | hqS
    · exact hrm'p
    · have h : q ≠ p := fun h => hpS (h ▸ hqS)
      rw [hrm'ne q hq h]; exact hD3 q hq hqS
  · have h : q ≠ p := fun h => hqS (h ▸ Finset.mem_insert_self p S')
    rw [hrm'ne q hq h]; exact hD4 q hq fun h' => hqS (Finset.mem_insert_of_mem h')
  · rcases Finset.mem_insert.1 hqS with rfl | hqS
    · have hq'Q : q' ∈ Q := hmemQ q' hq' hidx hlt
      have hcq' : c ≤ f q' - ε := hcQ q' hq'Q
      have hVt : ∀ x, f q + ε / 2 < f x → Dt.V x = D'.V x := fun x hx => (hV't x hx.le).symm
      have hRq : D'.rightSphere q hq ε (f q + 33 * ε) = Dt.rightSphere q hq ε c := by
        rw [← hcdef]
        refine rightSphere_eq_of_flow_eq (hχt q hq) (hkt q hq) fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := hx
        have hfx : f ((Dt.chart q hq).χ y) = f q + ε :=
          (Dt.chart q hq).f_chart_of_mem_rightModelSphere (by rw [hDt_chart]; exact hεR q hq) hy
        exact flow_eq_of_agree_above_neg hf hVt (x := (Dt.chart q hq).χ y) (by linarith)
          (T := 32 * ε) (by positivity) (f q + ε - c) ⟨by rw [hcdef]; linarith, by linarith⟩
      have hLq : D'.leftSphere q' hq' ε (f q + 33 * ε) = Dt.leftSphere q' hq' ε c := by
        rw [← hcdef]
        refine leftSphere_eq_of_flow_eq (hχt q' hq') (hkt q' hq') fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := hx
        have hfx : f ((Dt.chart q' hq').χ y) = f q' - ε :=
          (Dt.chart q' hq').f_chart_of_mem_leftModelSphere (by rw [hDt_chart]; exact hεR q' hq') hy
        exact flow_eq_of_agree_above_of_le hf hVt (T := f q' - ε - c) (by linarith) _
          (right_mem_Icc.2 (by linarith))
      rw [hRq, hLq]
      exact hDt_disj q' hq' hq'Q
    · have hfq : f p + 40 * ε < f q := hgap p hp q hq (hpmin q hqS)
      have hV : ∀ x, f p + 32 * ε < f x → D.V x = D'.V x := fun x hx => (hV' x hx.le).symm
      have hRq : D'.rightSphere q hq ε (f q + 33 * ε) = D.rightSphere q hq ε (f q + 33 * ε) := by
        refine rightSphere_eq_of_flow_eq (hχ' q hq) (hk' q hq) fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := hx
        have hfx : f ((D.chart q hq).χ y) = f q + ε :=
          (D.chart q hq).f_chart_of_mem_rightModelSphere (hεR q hq) hy
        exact flow_eq_of_agree_above_neg hf hV (x := (D.chart q hq).χ y) (by linarith)
          (T := 32 * ε) (by positivity) (f q + ε - (f q + 33 * ε)) ⟨by linarith, by linarith⟩
      have hLq : D'.leftSphere q' hq' ε (f q + 33 * ε) = D.leftSphere q' hq' ε (f q + 33 * ε) := by
        refine leftSphere_eq_of_flow_eq (hχ' q' hq') (hk' q' hq') fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := hx
        have hfx : f ((D.chart q' hq').χ y) = f q' - ε :=
          (D.chart q' hq').f_chart_of_mem_leftModelSphere (hεR q' hq') hy
        have hgap' := hgap q hq q' hq' hlt
        exact flow_eq_of_agree_above_of_le hf hV (T := f q' - ε - (f q + 33 * ε)) (by linarith) _
          (right_mem_Icc.2 (by linarith))
      rw [hRq, hLq]
      exact hD5 q hq hqS q' hq' hidx hlt
  · intro x hx t ht hmem
    have hxD : x ∈ (D.chart q' hq').χ '' (D.chart q' hq').leftModelSphere ε := by
      rw [← harm]; exact hx
    have hfx : f x = f q' - ε := hfarm q' hq' x hxD
    rcases Finset.mem_insert.1 hqS with rfl | hqS
    · have hq'Q : q' ∈ Q := hmemQ q' hq' hidx hlt
      have hV : ∀ x, f q + 32 * ε < f x → D'.V x = D.V x := fun x hx => hV' x hx.le
      have hflowD : ∀ s ∈ Icc 0 (f q' - ε - c), D.flow s x = D'.flow s x :=
        flow_eq_of_agree_above_of_le hf hV (T := f q' - ε - c)
          (by rw [hfx]; linarith [hcQ q' hq'Q])
      have hmem' : D'.flow t x ∈ (D'.chart q hq).χ '' {z | morseNorm n z < r' / 2} := by
        unfold smallBall at hmem; rw [hr₀'p] at hmem; exact hmem
      refine arm_avoids_of_tube hf hε hq hq' hlt hcdef hcab hr'0 hr'ε hr'δ hrm'p hχt hkt
        hV't hsb'' hfar (hab q' hq') (hab q hq) (hδdisj q' hq' hq'Q)
        (image_mono (leftModelSphere_subset_leftTube D' q' hq' hδ.le) hx) hfx ?_ ht hmem'
      intro p' hp' hfq hfq' s hs hmem'
      have hidx' : morseIndex I f p' = morseIndex I f q :=
        hmid p' hp' q hq q' hq' hfq hfq' hidx.symm
      have hp'S : p' ∈ S' := hup p' hp' (by rw [hidx']; exact hp1) hfq
      have := hD6 p' hp' hp'S q' hq' (hidx.trans hidx'.symm) hfq' x hxD s hs.1
      rw [hflowD s hs] at this
      exact this (hsb' p' hp' hmem')
    · have hfq : f p + 40 * ε < f q := hgap p hp q hq (hpmin q hqS)
      have hmemD : D'.flow t x ∈ D.smallBall q hq := hsb' q hq hmem
      have hlevm := hsb q hq _ hmemD
      have hV : ∀ x, f p + 32 * ε < f x → D'.V x = D.V x := fun x hx => hV' x hx.le
      have := flow_eq_of_agree_above hf hV (x := x) (t := t) (by linarith [hlevm.1]) t
        (right_mem_Icc.2 ht)
      rw [← this] at hmemD
      exact hD6 q hq hqS q' hq' hidx hlt x hxD t ht hmemD

open Classical in
theorem portPrivate_3652466a_exists_stageInvIdx_all (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D₀ : GradientLikeStrip I f a b crit)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ p ∈ crit, ∀ q ∈ crit, f p < f q → f p + 40 * ε < f q)
    (hab : ∀ p ∈ crit, a + 40 * ε < f p ∧ f p + 40 * ε < b)
    (hinj : ∀ p ∈ crit, ∀ q ∈ crit, f p = f q → p = q)
    (hmid : ∀ m ∈ crit, ∀ q ∈ crit, ∀ q' ∈ crit, f q < f m → f m < f q' →
      morseIndex I f q = morseIndex I f q' → morseIndex I f m = morseIndex I f q)
    (hR : ∀ q hq, 2 * ε ≤ (D₀.chart q hq).R ^ 2) (hr₀ : ∀ q hq, (D₀.chart q hq).r₀ ^ 2 < ε / 2)
    (hrm : ∀ q hq, 65 * ε < D₀.rm q hq ^ 2) :
    ∃ D : GradientLikeStrip I f a b crit,
      portPrivate_3652466a_stageInvIdx D₀ D (crit.filter fun q => 1 ≤ morseIndex I f q) ε := by
  classical
  set crit₁ : Finset M := crit.filter fun q => 1 ≤ morseIndex I f q with hcrit₁
  have hmem₁ : ∀ q, q ∈ crit₁ ↔ q ∈ crit ∧ 1 ≤ morseIndex I f q := fun q => by
    rw [hcrit₁, Finset.mem_filter]
  have key : ∀ N : ℕ, ∀ S : Finset M, S ⊆ crit₁ →
      (∀ q ∈ S, ∀ q' ∈ crit₁, f q < f q' → q' ∈ S) → S.card = N →
      ∃ D : GradientLikeStrip I f a b crit, portPrivate_3652466a_stageInvIdx D₀ D S ε := by
    intro N
    induction N with
    | zero =>
      intro S _ _ hcard
      rw [Finset.card_eq_zero] at hcard
      subst hcard
      refine ⟨D₀, fun q hq => ⟨rfl, rfl, rfl, rfl⟩, fun q hq => le_rfl, ?_, fun q hq _ => rfl,
        ?_, ?_⟩
      · intro q hq hqS; exact absurd hqS (Finset.notMem_empty q)
      · intro q hq hqS; exact absurd hqS (Finset.notMem_empty q)
      · intro q hq hqS; exact absurd hqS (Finset.notMem_empty q)
    | succ N ih =>
      intro S hSsub hup hcard
      have hne : S.Nonempty := by rw [← Finset.card_pos, hcard]; exact Nat.succ_pos N
      obtain ⟨p, hpS, hpmin⟩ := Finset.exists_min_image S f hne
      have hS'sub : S.erase p ⊆ crit₁ := (Finset.erase_subset p S).trans hSsub
      have hup' : ∀ q ∈ S.erase p, ∀ q' ∈ crit₁, f q < f q' → q' ∈ S.erase p := by
        intro q hq q' hq' hlt
        have hqS := (Finset.mem_erase.1 hq).2
        refine Finset.mem_erase.2 ⟨fun h => ?_, hup q hqS q' hq' hlt⟩
        subst h
        exact absurd (hpmin q hqS) (not_le.2 hlt)
      have hcard' : (S.erase p).card = N := by
        rw [Finset.card_erase_of_mem hpS, hcard]; rfl
      obtain ⟨D, hD⟩ := ih (S.erase p) hS'sub hup' hcard'
      have hp₁ : p ∈ crit₁ := hSsub hpS
      have hpS' : p ∉ S.erase p := fun h => (Finset.mem_erase.1 h).1 rfl
      have hpmin' : ∀ q ∈ S.erase p, f p < f q := by
        intro q hq
        obtain ⟨hqp, hqS⟩ := Finset.mem_erase.1 hq
        rcases (hpmin q hqS).lt_or_eq with h | h
        · exact h
        · exact absurd (hinj p ((hmem₁ p).1 hp₁).1 q ((hmem₁ q).1 (hSsub hqS)).1 h)
            (Ne.symm hqp)
      have hup'' : ∀ q' ∈ crit, 1 ≤ morseIndex I f q' → f p < f q' → q' ∈ S.erase p := by
        intro q' hq' hq'1 hlt
        refine Finset.mem_erase.2 ⟨fun h => ?_, hup p hpS q' ((hmem₁ q').2 ⟨hq', hq'1⟩) hlt⟩
        subst h; exact lt_irrefl _ hlt
      have hS'crit : ∀ q ∈ S.erase p, q ∈ crit ∧ 1 ≤ morseIndex I f q :=
        fun q hq => (hmem₁ q).1 (hS'sub hq)
      obtain ⟨D', hD'⟩ := portPrivate_3652466a_stageInvIdx.step hf hε hgap hab hinj hmid hR hr₀ hrm hS'crit
        ((hmem₁ p).1 hp₁).1 ((hmem₁ p).1 hp₁).2 hpS' hpmin' hup'' hD
      rw [Finset.insert_erase hpS] at hD'
      exact ⟨D', hD'⟩
  exact key crit₁.card crit₁ le_rfl (fun _ _ q' hq' _ => hq') rfl

theorem exists_stage_sameIndex (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D₀ : GradientLikeStrip I f a b crit)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ p ∈ crit, ∀ q ∈ crit, f p < f q → f p + 40 * ε < f q)
    (hab : ∀ p ∈ crit, a + 40 * ε < f p ∧ f p + 40 * ε < b)
    (hinj : ∀ p ∈ crit, ∀ q ∈ crit, f p = f q → p = q)
    (hmid : ∀ m ∈ crit, ∀ q ∈ crit, ∀ q' ∈ crit, f q < f m → f m < f q' →
      morseIndex I f q = morseIndex I f q' → morseIndex I f m = morseIndex I f q)
    (hR : ∀ q hq, 2 * ε ≤ (D₀.chart q hq).R ^ 2) (hr₀ : ∀ q hq, (D₀.chart q hq).r₀ ^ 2 < ε / 2)
    (hrm : ∀ q hq, 65 * ε < D₀.rm q hq ^ 2) :
    ∃ D : GradientLikeStrip I f a b crit,
      (∀ q hq, (D.chart q hq).χ = (D₀.chart q hq).χ ∧ (D.chart q hq).k = (D₀.chart q hq).k ∧
        (D.chart q hq).R = (D₀.chart q hq).R ∧ (D.chart q hq).R' = (D₀.chart q hq).R' ∧
        (D.chart q hq).r₀ ≤ (D₀.chart q hq).r₀) ∧
      (∀ q hq, D.rm q hq ^ 2 = 32 * ε ∨ D.rm q hq = D₀.rm q hq) ∧
      ∀ q hq q' hq', morseIndex I f q = morseIndex I f q' → 1 ≤ morseIndex I f q →
        f q < f q' →
        Disjoint (D.rightSphere q hq ε (f q + 33 * ε)) (D.leftSphere q' hq' ε (f q + 33 * ε)) ∧
        ∀ x ∈ (D.chart q' hq').χ '' (D.chart q' hq').leftModelSphere ε, ∀ t, 0 ≤ t →
          D.flow t x ∉ D.smallBall q hq := by
  classical
  obtain ⟨D, h1, h2, h3, h4, h5, h6⟩ :=
    portPrivate_3652466a_exists_stageInvIdx_all hf D₀ hε hgap hab hinj hmid hR hr₀ hrm
  refine ⟨D, fun q hq => ⟨(h1 q hq).1, (h1 q hq).2.1, (h1 q hq).2.2.1, (h1 q hq).2.2.2,
    h2 q hq⟩, fun q hq => ?_, fun q hq q' hq' hidx h1q hlt => ?_⟩
  · by_cases hS : q ∈ crit.filter fun q => 1 ≤ morseIndex I f q
    · exact Or.inl (h3 q hq hS)
    · exact Or.inr (h4 q hq hS)
  · have hS : q ∈ crit.filter fun q => 1 ≤ morseIndex I f q := Finset.mem_filter.2 ⟨hq, h1q⟩
    exact ⟨h5 q hq hS q' hq' hidx.symm hlt, h6 q hq hS q' hq' hidx.symm hlt⟩

end GradientLikeStrip

section BlockNormalForm

variable (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem exists_gradientLike_sameIndexPairs {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})
    (crit : Finset M) (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {R₀ : ℝ}
    (hR₀ : 0 < R₀) :
    ∃ D : GradientLikeStrip I f a b crit, ∃ ε, 0 < ε ∧ ∃ r', 0 < r' ∧ r' ^ 2 < ε ∧
      (∀ p hp, (D.chart p hp).R ≤ R₀ ∧ (D.chart p hp).r₀ ^ 2 < 2 * ε ∧
        24 * ε < D.rm p hp ^ 2 ∧ (D.chart p hp).r₀ < r') ∧
      ∀ p hp q hq, p ≠ q → morseIndex I f p = morseIndex I f q → D.noCommon p hp q hq r' r' := by
  classical
  obtain ⟨D, hR, hrm, -⟩ :=
    exists_gradientLikeStrip hf le_rfl hf.lt le_rfl hf.regular crit hcrit hR₀
  have hfs := hf.smooth
  obtain ⟨ρa, hρa, hρaT⟩ := exists_pos_le_forall_finset crit (fun p => min (f p - a) (b - f p))
    fun p hp => lt_min (sub_pos.2 ((hcrit p).1 hp).1.1) (sub_pos.2 ((hcrit p).1 hp).1.2)
  obtain ⟨ρg, hρg, hρgT⟩ := exists_pos_le_forall_finset
    ((crit ×ˢ crit).filter fun x => f x.1 < f x.2) (fun x => f x.2 - f x.1)
    fun x hx => sub_pos.2 (Finset.mem_filter.1 hx).2
  obtain ⟨ρR, hρR, hρRT⟩ := exists_pos_le_forall_finset crit.attach
    (fun p => (D.chart p.1 p.2).R ^ 2) fun p _ => pow_pos (D.chart p.1 p.2).R_pos 2
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (min ρa ρg) ρR / 80 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hεa : 80 * ε ≤ ρa := by
    rw [hεdef]; linarith [min_le_left (min ρa ρg) ρR, min_le_left ρa ρg]
  have hεg : 80 * ε ≤ ρg := by
    rw [hεdef]; linarith [min_le_left (min ρa ρg) ρR, min_le_right ρa ρg]
  have hεR : 80 * ε ≤ ρR := by rw [hεdef]; linarith [min_le_right (min ρa ρg) ρR]
  have hgap : ∀ p ∈ crit, ∀ q ∈ crit, f p < f q → f p + 40 * ε < f q := by
    intro p hp q hq hlt
    have := hρgT (p, q) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hp, hq⟩, hlt⟩)
    simp only at this
    linarith
  have hab : ∀ p ∈ crit, a + 40 * ε < f p ∧ f p + 40 * ε < b := by
    intro p hp
    have := hρaT p hp
    constructor <;> linarith [min_le_left (f p - a) (b - f p), min_le_right (f p - a) (b - f p)]
  have hRsq : ∀ p hp, 80 * ε ≤ (D.chart p hp).R ^ 2 := fun p hp =>
    hεR.trans (hρRT ⟨p, hp⟩ (Finset.mem_attach _ _))
  have hinj' : ∀ p ∈ crit, ∀ q ∈ crit, f p = f q → p = q :=
    fun p hp q hq h => hinj ((hcrit p).1 hp) ((hcrit q).1 hq) h
  have hmid : ∀ m ∈ crit, ∀ q ∈ crit, ∀ q' ∈ crit, f q < f m → f m < f q' →
      morseIndex I f q = morseIndex I f q' → morseIndex I f m = morseIndex I f q := by
    intro m hm q hq q' hq' h1 h2 hqq'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hsi m q ((hcrit m).1 hm).1 ((hcrit q).1 hq).1 ((hcrit m).1 hm).2
        ((hcrit q).1 hq).2 h
      linarith
    · have := hsi q' m ((hcrit q').1 hq').1 ((hcrit m).1 hm).1 ((hcrit q').1 hq').2
        ((hcrit m).1 hm).2 (by rw [← hqq']; exact h)
      linarith
  obtain ⟨ρ₀, hρ₀, hρ₀T⟩ := exists_pos_le_forall_finset crit.attach
    (fun p => (D.chart p.1 p.2).r₀) fun p _ => (D.chart p.1 p.2).hr₀
  obtain ⟨ρi, hρi, hρiA, -, hρiε, -⟩ := GradientLikeStrip.exists_small_radius hρ₀ hρ₀ hε one_pos
  obtain ⟨D₀, hD₀1, hD₀2, hD₀3, -⟩ := GradientLikeStrip.exists_shrinkAll hfs D hρi fun p hp =>
    hρiA.trans (hρ₀T ⟨p, hp⟩ (Finset.mem_attach _ _))
  have hD₀R : ∀ q hq, 80 * ε ≤ (D₀.chart q hq).R ^ 2 := fun q hq => by
    rw [(hD₀1 q hq).2.2.1]; exact hRsq q hq
  have hD₀r₀ : ∀ q hq, (D₀.chart q hq).r₀ ^ 2 < ε / 2 := fun q hq => by
    rw [hD₀2 q hq]
    have : (ρi / 2) ^ 2 = ρi ^ 2 / 4 := by ring
    rw [this]; linarith
  have hD₀rm : ∀ q hq, 80 * ε ≤ D₀.rm q hq ^ 2 := fun q hq => by
    rw [hD₀3 q hq, hrm q hq]; exact hRsq q hq
  obtain ⟨D₁, hD1, hD2, hD3, hD4, hD5, hD6⟩ := GradientLikeStrip.portPrivate_3652466a_exists_stageInvIdx_all hfs D₀ hε
    hgap hab hinj' hmid (fun q hq => by linarith [hD₀R q hq]) hD₀r₀
    (fun q hq => by linarith [hD₀rm q hq])
  have hS₁ : ∀ q (hq : q ∈ crit), 1 ≤ morseIndex I f q →
      q ∈ crit.filter fun q => 1 ≤ morseIndex I f q := fun q hq h => Finset.mem_filter.2 ⟨hq, h⟩
  have hD₁R : ∀ q hq, 80 * ε ≤ (D₁.chart q hq).R ^ 2 := fun q hq => by
    rw [(hD1 q hq).2.2.1]; exact hD₀R q hq
  have hD₁r₀ : ∀ q hq, (D₁.chart q hq).r₀ ^ 2 < ε / 2 := fun q hq =>
    lt_of_le_of_lt (pow_le_pow_left₀ (D₁.chart q hq).hr₀.le (hD2 q hq) 2) (hD₀r₀ q hq)
  have hhalf : ∀ m (hm : m ∈ crit) x,
      x ∈ (D₁.chart m hm).χ '' {z | morseNorm n z ≤ (D₁.chart m hm).r₀ / 2} →
      f x ∈ Icc (f m - ε / 16) (f m + ε / 16) := by
    intro m hm x hx
    have h := (D₁.chart m hm).f_mem_Icc_of_mem_image_le
      (by linarith [D₁.r₀_lt_R m hm, (D₁.chart m hm).hr₀]) hx
    have h1 := hD₁r₀ m hm
    have h2 : ((D₁.chart m hm).r₀ / 2) ^ 2 = (D₁.chart m hm).r₀ ^ 2 / 4 := by ring
    rw [h2] at h
    constructor <;> linarith [h.1, h.2]
  have hhalfsub : ∀ m (hm : m ∈ crit),
      (D₁.chart m hm).χ '' {z | morseNorm n z ≤ (D₁.chart m hm).r₀ / 2} ⊆ D₁.smallBall m hm :=
    fun m hm => image_mono fun z (hz : morseNorm n z ≤ _) => show morseNorm n z < _ by
      linarith [(D₁.chart m hm).hr₀]
  have hpairTube : ∀ q (hq : q ∈ crit) q' (hq' : q' ∈ crit), 1 ≤ morseIndex I f q →
      morseIndex I f q' = morseIndex I f q → f q < f q' →
      ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
        Disjoint
          (D₁.flow (f q + ε - (f q + 33 * ε)) '' ((D₁.chart q hq).χ '' D₁.rightTube q hq ε δ))
          (D₁.flow (f q' - ε - (f q + 33 * ε)) '' ((D₁.chart q' hq').χ '' D₁.leftTube q' hq' ε δ)) ∧
        ∀ y ∈ D₁.leftTube q' hq' ε δ, ∀ s ∈ Icc 0 (f q' - ε - (f q + 33 * ε)),
          D₁.flow s ((D₁.chart q' hq').χ y) ∉ D₁.halfBalls := by
    intro q hq q' hq' hq1 hqq' hlt
    have hgapq := hgap q hq q' hq' hlt
    obtain ⟨δ₁, hδ₁, hdisj₁⟩ := D₁.exists_tube_disjoint q hq q' hq' hε
      (by linarith [hD₁R q hq]) (by linarith [hD₁R q' hq']) (hD5 q hq (hS₁ q hq hq1) q' hq' hqq' hlt)
    set T := f q' - ε - (f q + 33 * ε) with hT
    set d := D₁.chart q' hq' with hd
    set W : Set (Fin n → ℝ) := {y | y ∈ Metric.ball (0 : Fin n → ℝ) d.R' ∧
      ∀ s ∈ Icc 0 T, D₁.flow s (d.χ y) ∉ D₁.halfBalls} with hW
    have hK := D₁.isClosed_halfBalls
    have hWo : IsOpen W := by
      rw [isOpen_iff_mem_nhds]
      rintro y₀ ⟨hy₀b, hy₀⟩
      have hχc : ContinuousAt d.χ y₀ :=
        d.χ.continuousOn.continuousAt (d.χ.open_source.mem_nhds (d.hball hy₀b))
      have hG : ∀ s, ContinuousAt (fun z : (Fin n → ℝ) × ℝ => D₁.flow z.2 (d.χ z.1)) (y₀, s) :=
        fun s => D₁.continuous_flow_joint.continuousAt.comp
          (continuousAt_snd.prodMk (hχc.comp continuousAt_fst))
      have hev : ∀ s ∈ Icc (0 : ℝ) T, ∀ᶠ z : (Fin n → ℝ) × ℝ in 𝓝 (y₀, s),
          D₁.flow z.2 (d.χ z.1) ∉ D₁.halfBalls := fun s hs =>
        (hG s).eventually_mem (hK.isOpen_compl.mem_nhds (hy₀ s hs))
      have h1 := isCompact_Icc.eventually_forall_of_forall_eventually
        (P := fun (y : Fin n → ℝ) (s : ℝ) => D₁.flow s (d.χ y) ∉ D₁.halfBalls) hev
      filter_upwards [h1, Metric.isOpen_ball.mem_nhds hy₀b] with y hy hyb
      exact ⟨hyb, hy⟩
    have hR2 : 2 * ε ≤ d.R ^ 2 := by linarith [hD₁R q' hq']
    have hSW : d.leftModelSphere ε ⊆ W := by
      intro y hy
      refine ⟨d.mem_ball_of_le (d.morseNorm_le_R_of_mem_leftModelSphere hR2 hy),
        fun s hs hmem => ?_⟩
      obtain ⟨m, hm, hmem⟩ := D₁.mem_halfBalls_iff.1 hmem
      have hfx : f (d.χ y) = f q' - ε := d.f_chart_of_mem_leftModelSphere hR2 hy
      have hlev := hhalf m hm _ hmem
      have hup : f (D₁.flow s (d.χ y)) ≤ f q' - ε :=
        hfx ▸ GradientLikeStrip.f_flow_le hfs _ hs.1
      have hlow : f q + 33 * ε ≤ f (D₁.flow s (d.χ y)) := by
        have := GradientLikeStrip.sub_le_f_flow (D := D₁) hfs (d.χ y) hs.1
        rw [hfx] at this; linarith [hs.2]
      rcases lt_or_ge (f m) (f q') with h | h
      · have hmidx : morseIndex I f m = morseIndex I f q' := by
          rcases lt_trichotomy (f m) (f q) with h' | h' | h'
          · exfalso; linarith [hlev.2]
          · rw [hinj' m hm q hq h', hqq']
          · rw [hmid m hm q hq q' hq' h' h hqq'.symm, hqq']
        exact hD6 m hm (hS₁ m hm (by rw [hmidx, hqq']; exact hq1)) q' hq' hmidx.symm h
          (d.χ y) ⟨y, hy, rfl⟩ s hs.1 (hhalfsub m hm hmem)
      · linarith [hlev.1]
    obtain ⟨δ₂, hδ₂, hδ₂W⟩ := D₁.exists_leftTube_subset_open q' hq' hε hWo hSW
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδle => ⟨?_, fun y hy s hs => ?_⟩⟩
    · exact hdisj₁.mono
        (image_mono (image_mono (GradientLikeStrip.rightTube_mono' _ _ _ _
          (hδle.trans (min_le_left _ _)))))
        (image_mono (image_mono (GradientLikeStrip.leftTube_mono' _ _ _ _
          (hδle.trans (min_le_left _ _)))))
    · exact (hδ₂W (GradientLikeStrip.leftTube_mono' _ _ _ _
        (hδle.trans (min_le_right _ _)) hy)).2 s hs
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := exists_pos_forall_small_finset (crit ×ˢ crit)
    (fun x δ => ∀ (hq : x.1 ∈ crit) (hq' : x.2 ∈ crit), 1 ≤ morseIndex I f x.1 →
      morseIndex I f x.2 = morseIndex I f x.1 → f x.1 < f x.2 →
      Disjoint
        (D₁.flow (f x.1 + ε - (f x.1 + 33 * ε)) '' ((D₁.chart x.1 hq).χ '' D₁.rightTube x.1 hq ε δ))
        (D₁.flow (f x.2 - ε - (f x.1 + 33 * ε)) ''
          ((D₁.chart x.2 hq').χ '' D₁.leftTube x.2 hq' ε δ)) ∧
      ∀ y ∈ D₁.leftTube x.2 hq' ε δ, ∀ s ∈ Icc 0 (f x.2 - ε - (f x.1 + 33 * ε)),
        D₁.flow s ((D₁.chart x.2 hq').χ y) ∉ D₁.halfBalls) (by
      rintro ⟨q, q'⟩ hx
      obtain ⟨hq, hq'⟩ := Finset.mem_product.1 hx
      by_cases hcond : 1 ≤ morseIndex I f q ∧ morseIndex I f q' = morseIndex I f q ∧ f q < f q'
      · obtain ⟨δ₀, hδ₀, h⟩ := hpairTube q hq q' hq' hcond.1 hcond.2.1 hcond.2.2
        exact ⟨δ₀, hδ₀, fun δ hδ hδle _ _ _ _ _ => h δ hδ hδle⟩
      · exact ⟨1, one_pos, fun _ _ _ _ _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcond⟩)
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℝ, δ₀ = min δ₁ ε := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; exact lt_min hδ₁ hε
  have hδ₀ε : δ₀ ≤ ε := by rw [hδ₀def]; exact min_le_right _ _
  have hδ₀₁ : δ₀ ≤ δ₁ := by rw [hδ₀def]; exact min_le_left _ _
  have hpair : ∀ q (hq : q ∈ crit) q' (hq' : q' ∈ crit), 1 ≤ morseIndex I f q →
      morseIndex I f q' = morseIndex I f q → f q < f q' →
      Disjoint
        (D₁.flow (f q + ε - (f q + 33 * ε)) '' ((D₁.chart q hq).χ '' D₁.rightTube q hq ε δ₀))
        (D₁.flow (f q' - ε - (f q + 33 * ε)) ''
          ((D₁.chart q' hq').χ '' D₁.leftTube q' hq' ε δ₀)) ∧
      ∀ y ∈ D₁.leftTube q' hq' ε δ₀, ∀ s ∈ Icc 0 (f q' - ε - (f q + 33 * ε)),
        D₁.flow s ((D₁.chart q' hq').χ y) ∉ D₁.halfBalls :=
    fun q hq q' hq' hq1 hqq' hlt =>
      hδ₁P (q, q') (Finset.mem_product.2 ⟨hq, hq'⟩) δ₀ hδ₀ hδ₀₁ hq hq' hq1 hqq' hlt
  obtain ⟨ρ₁, hρ₁, hρ₁le⟩ := exists_pos_le_forall_finset crit.attach
    (fun m => (D₁.chart m.1 m.2).r₀) fun m _ => (D₁.chart m.1 m.2).hr₀
  obtain ⟨ρ, hρ, hρA, -, hρε, hρδ⟩ := GradientLikeStrip.exists_small_radius hρ₁ hρ₁
    (show 0 < ε / 4 by positivity) (show 0 < 2 * ε * δ₀ / 16 by positivity)
  have hle : ∀ m hm, ρ ≤ (D₁.chart m hm).r₀ := fun m hm =>
    hρA.trans (hρ₁le ⟨m, hm⟩ (Finset.mem_attach _ _))
  obtain ⟨E, hE1, hE2, hE3, hE4⟩ := GradientLikeStrip.exists_shrinkAll hfs D₁ hρ hle
  have hρδ' : (2 * ρ) ^ 4 ≤ 2 * ε * δ₀ := by
    have : (2 * ρ) ^ 4 = 16 * ρ ^ 4 := by ring
    rw [this]; linarith
  have hV : ∀ x ∈ D₁.halfBallsᶜ, D₁.V x = E.V x := fun x hx =>
    (hE4 x fun m hm h => hx (D₁.mem_halfBalls_iff.2 ⟨m, hm, h⟩)).symm
  have hKo : IsOpen D₁.halfBallsᶜ := D₁.isClosed_halfBalls.isOpen_compl
  have hfar : ∀ q ∈ crit, ∀ m ∈ crit, m ≠ q → f m + 40 * ε < f q ∨ f q + 40 * ε < f m := by
    intro q hq m hm hmq
    rcases lt_trichotomy (f m) (f q) with h | h | h
    · exact Or.inl (hgap m hm q hq h)
    · exact absurd (hinj' m hm q hq h) hmq
    · exact Or.inr (hgap q hq m hm h)
  have hER : ∀ q hq, 80 * ε ≤ (E.chart q hq).R ^ 2 := fun q hq => by
    rw [(hE1 q hq).2.2.1]; exact hD₁R q hq
  have hErm32 : ∀ q hq, 1 ≤ morseIndex I f q → E.rm q hq ^ 2 = 32 * ε := fun q hq h => by
    rw [hE3 q hq]; exact hD3 q hq (hS₁ q hq h)
  have htube : ∀ q (hq : q ∈ crit) q' (hq' : q' ∈ crit), 1 ≤ morseIndex I f q →
      morseIndex I f q' = morseIndex I f q → f q < f q' →
      Disjoint
        (E.flow (f q + ε - (f q + 33 * ε)) '' ((E.chart q hq).χ '' E.rightTube q hq ε δ₀))
        (E.flow (f q' - ε - (f q + 33 * ε)) ''
          ((E.chart q' hq').χ '' E.leftTube q' hq' ε δ₀)) := by
    intro q hq q' hq' hq1 hqq' hlt
    obtain ⟨hdisj, havoid⟩ := hpair q hq q' hq' hq1 hqq' hlt
    have hgapq := hgap q hq q' hq' hlt
    have hRT : E.flow (f q + ε - (f q + 33 * ε)) '' ((E.chart q hq).χ '' E.rightTube q hq ε δ₀) =
        D₁.flow (f q + ε - (f q + 33 * ε)) '' ((D₁.chart q hq).χ '' D₁.rightTube q hq ε δ₀) := by
      rw [(hE1 q hq).1, GradientLikeStrip.rightTube_eq (D := D₁) hq (hE1 q hq).2.1]
      refine image_congr fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨-, hfy⟩ := D₁.f_mem_of_mem_rightTube hδ₀ε (by linarith [hD₁R q hq]) hy
      refine GradientLikeStrip.flow_eq_of_agree_neg (D₁ := D₁) (D₂ := E) hKo hV (T := 32 * ε)
        (by positivity) (fun s hs hmem => ?_) _ ⟨by linarith, by linarith⟩
      obtain ⟨m, hm, hmem⟩ := D₁.mem_halfBalls_iff.1 hmem
      have hlev := hhalf m hm _ hmem
      have h1 := GradientLikeStrip.le_f_flow_of_nonpos (D := D₁) hfs ((D₁.chart q hq).χ y) hs.2.le
      have h2 := GradientLikeStrip.f_flow_le_sub_of_nonpos (D := D₁) hfs ((D₁.chart q hq).χ y)
        hs.2.le
      rw [hfy] at h1 h2
      by_cases hmq : m = q
      · subst hmq; linarith [hlev.2]
      · rcases hfar q hq m hm hmq with h | h <;> linarith [hlev.1, hlev.2, hs.1]
    have hLT : E.flow (f q' - ε - (f q + 33 * ε)) ''
          ((E.chart q' hq').χ '' E.leftTube q' hq' ε δ₀) =
        D₁.flow (f q' - ε - (f q + 33 * ε)) ''
          ((D₁.chart q' hq').χ '' D₁.leftTube q' hq' ε δ₀) := by
      rw [(hE1 q' hq').1, GradientLikeStrip.leftTube_eq (D := D₁) hq' (hE1 q' hq').2.1]
      refine image_congr fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      exact GradientLikeStrip.flow_eq_of_agree (D₁ := D₁) (D₂ := E) hKo hV
        (fun s hs => havoid y hy s (Ico_subset_Icc_self hs)) _ (right_mem_Icc.2 (by linarith))
    rw [hRT, hLT]
    exact hdisj
  have hER4 : ∀ m hm, 4 * ε ≤ (E.chart m hm).R ^ 2 := fun m hm => by linarith [hER m hm]
  have hsbE : ∀ m hm x, x ∈ E.smallBall m hm → f x ∈ Icc (f m - ε / 4) (f m + ε / 4) := by
    intro m hm x hx
    have h := E.f_mem_Icc_of_mem_smallBall hx
    rw [hE2 m hm] at h
    have : (ρ / 2) ^ 2 = ρ ^ 2 / 4 := by ring
    rw [this] at h
    constructor <;> linarith [h.1, h.2]
  have hnoball : ∀ q' (hq' : q' ∈ crit), 1 ≤ morseIndex I f q' →
      ∀ e, e ∈ (E.chart q' hq').χ '' E.leftTube q' hq' ε δ₀ →
      ∀ q (hq : q ∈ crit), morseIndex I f q = morseIndex I f q' → f q < f q' → ∀ t, 0 ≤ t →
        E.flow t e ∉ (E.chart q hq).χ '' {z | morseNorm n z < ρ} := by
    intro q' hq' hq'1 e he q hq hqi hlt t ht hmem
    have hfe : f e = f q' - ε := by
      obtain ⟨y, hy, rfl⟩ := he
      exact (E.f_mem_of_mem_leftTube hδ₀ε (hER4 q' hq') hy).2
    set A : Finset M := crit.filter fun m => morseIndex I f m = morseIndex I f q' ∧
      f q ≤ f m ∧ f m < f q' ∧
      ∃ t, 0 ≤ t ∧ ∃ hm : m ∈ crit, E.flow t e ∈ (E.chart m hm).χ '' {z | morseNorm n z < ρ}
      with hA
    have hqA : q ∈ A := Finset.mem_filter.2 ⟨hq, hqi, le_rfl, hlt, t, ht, hq, hmem⟩
    obtain ⟨m₀, hm₀A, hm₀max⟩ := Finset.exists_max_image A f ⟨q, hqA⟩
    obtain ⟨hm₀, hm₀i, -, hm₀lt, t₀, ht₀, hm₀', hmem₀⟩ := Finset.mem_filter.1 hm₀A
    have hm₀ab := hab m₀ hm₀
    have hm₀1 : 1 ≤ morseIndex I f m₀ := by rw [hm₀i]; exact hq'1
    refine GradientLikeStrip.arm_avoids_of_tube (D' := E) (Dt := E) hfs hε hm₀ hq' hm₀lt
      (c := f m₀ + 33 * ε) rfl ⟨by linarith [hm₀ab.1], by linarith [hm₀ab.2]⟩ (r' := 2 * ρ)
      (by positivity) (by nlinarith) hρδ' (hErm32 m₀ hm₀ hm₀1) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) hsbE (hfar m₀ hm₀) (hab q' hq') hm₀ab
      (htube m₀ hm₀ q' hq' hm₀1 hm₀i.symm hm₀lt) he hfe ?_ ht₀ ?_
    · intro p' hp' hfm hfq' s hs hmem'
      have hp'i : morseIndex I f p' = morseIndex I f q' := by
        rw [hmid p' hp' m₀ hm₀ q' hq' hfm hfq' hm₀i, hm₀i]
      have hp'A : p' ∈ A := Finset.mem_filter.2 ⟨hp', hp'i, by linarith [hm₀max q hqA], hfq', s,
        hs.1, hp', image_mono (fun z (hz : morseNorm n z < _) => show morseNorm n z < ρ by
          rw [hE2 p' hp'] at hz; linarith) hmem'⟩
      exact absurd (hm₀max p' hp'A) (not_le.2 hfm)
    · have : 2 * ρ / 2 = ρ := by ring
      rw [this]; exact hmem₀
  have hball : ∀ p (hp : p ∈ crit) q (hq : q ∈ crit), 1 ≤ morseIndex I f p →
      morseIndex I f q = morseIndex I f p → f p < f q →
      ∀ x ∈ (E.chart p hp).χ '' {y | morseNorm n y < ρ}, ∀ t,
        E.flow t x ∉ (E.chart q hq).χ '' {y | morseNorm n y < ρ} := by
    intro p hp q hq hp1 hqp hlt x hx t hmem
    have hq1 : 1 ≤ morseIndex I f q := by rw [hqp]; exact hp1
    have hgapq := hgap p hp q hq hlt
    have hρR : ρ ≤ (E.chart q hq).R := by
      have h := hER4 q hq
      nlinarith [(E.chart q hq).R_pos]
    have hρR' : ρ ≤ (E.chart p hp).R := by
      have h := hER4 p hp
      nlinarith [(E.chart p hp).R_pos]
    obtain ⟨x', hx'⟩ : ∃ x' : M, E.flow t x = x' := ⟨_, rfl⟩
    have hxx' : E.flow (-t) x' = x := by rw [← hx', GradientLikeStrip.flow_neg_flow]
    rw [hx'] at hmem
    rw [← hxx'] at hx
    clear hx' hxx'
    have hfx := (E.chart q hq).f_mem_Icc_of_mem_image_lt hρR hmem
    have hft := (E.chart p hp).f_mem_Icc_of_mem_image_lt hρR' hx
    have ht : 0 ≤ -t := by
      by_contra hneg
      have := GradientLikeStrip.le_f_flow_of_nonpos (D := E) hfs x' (not_le.1 hneg).le
      linarith [hfx.1, hft.2]
    obtain ⟨y, hy, rfl⟩ := hmem
    have hy : morseNorm n y < ρ := hy
    have hysq : morseNorm n y ^ 2 < ρ ^ 2 :=
      pow_lt_pow_left₀ hy (ModelField.morseNorm_nonneg y) two_ne_zero
    have hsq :=
      DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
        (E.chart q hq).hk y
    have hu0 := sq_nonneg ‖negPart (E.chart q hq).hk y‖
    have hv0 := sq_nonneg ‖posPart (E.chart q hq).hk y‖
    have hrmq := hErm32 q hq hq1
    have hrmq0 := E.rm_pos q hq
    have hyrm : morseNorm n y < E.rm q hq := by
      apply lt_of_pow_lt_pow_left₀ 2 hrmq0.le; rw [hrmq]; linarith
    have hyR : morseNorm n y ≤ (E.chart q hq).R := hyrm.le.trans (E.hrm q hq).2
    have hnfy : morseNormalForm (E.chart q hq).hk (f q) y = f ((E.chart q hq).χ y) :=
      ((E.chart q hq).hnorm y hyR).symm
    have hpq : p ≠ q := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    have hu : negPart (E.chart q hq).hk y ≠ 0 := by
      intro hu0'
      have h1 := GradientLikeStrip.flow_mem_of_negPart_eq_zero (D := E) hq hyrm hu0' ht
      have h2 : E.flow (-t) ((E.chart q hq).χ y) ∈
          (E.chart q hq).χ '' Metric.ball 0 (E.chart q hq).R' :=
        image_mono (fun z hz => (E.chart q hq).mem_ball_of_le (hz.1.trans hyR)) h1
      have h3 : E.flow (-t) ((E.chart q hq).χ y) ∈
          (E.chart p hp).χ '' Metric.ball 0 (E.chart p hp).R' :=
        image_mono (fun z (hz : morseNorm n z < ρ) =>
          (E.chart p hp).mem_ball_of_le (hz.le.trans hρR')) hx
      exact Set.disjoint_left.1 (E.disjoint q hq p hp (Ne.symm hpq)) h2 h3
    obtain ⟨t₁, ht₁, hft₁, hstay, hprod⟩ :=
      GradientLikeStrip.exists_exit_desc (D := E) hfs hq hε (y := y)
        (by rw [hrmq]; linarith) hu (by rw [hnfy]; linarith [hfx.1])
    obtain ⟨y₁, hy₁, hy₁e⟩ := hstay t₁ (right_mem_Icc.2 ht₁)
    have hy₁sq : morseNorm n y₁ ^ 2 ≤ 2 * ε + 2 * ‖posPart (E.chart q hq).hk y‖ ^ 2 := hy₁
    have hy₁R : morseNorm n y₁ ≤ (E.chart q hq).R := by
      have h2 : E.rm q hq ^ 2 ≤ (E.chart q hq).R ^ 2 :=
        pow_le_pow_left₀ hrmq0.le (E.hrm q hq).2 2
      refine MorseNormalChart.morseNorm_le_of_sq_le (E.chart q hq).R_pos.le ?_
      rw [hrmq] at h2; linarith
    have hsymm : (E.chart q hq).χ.symm (E.flow t₁ ((E.chart q hq).χ y)) = y₁ := by
      rw [← hy₁e, (E.chart q hq).χ.left_inv ((E.chart q hq).hsrc y₁ hy₁R)]
    rw [hsymm] at hprod
    have he : E.flow t₁ ((E.chart q hq).χ y) ∈ (E.chart q hq).χ '' E.leftTube q hq ε δ₀ := by
      refine ⟨y₁, ⟨?_, ?_⟩, hy₁e⟩
      · rw [← (E.chart q hq).hnorm y₁ hy₁R, hy₁e]; exact hft₁
      · have hprod' : ‖negPart (E.chart q hq).hk y‖ ^ 2 * ‖posPart (E.chart q hq).hk y‖ ^ 2 ≤
            (2 * ρ) ^ 4 / 16 := by
          have h1 : ‖negPart (E.chart q hq).hk y‖ ^ 2 ≤ ρ ^ 2 := by linarith
          have h2 : ‖posPart (E.chart q hq).hk y‖ ^ 2 ≤ ρ ^ 2 := by linarith
          calc _ ≤ ρ ^ 2 * ρ ^ 2 := mul_le_mul h1 h2 hv0 (by positivity)
            _ = (2 * ρ) ^ 4 / 16 := by ring
        have h3 : (2 * ρ) ^ 4 / 16 ≤ 2 * ε * δ₀ :=
          (div_le_self (by positivity) (by norm_num)).trans hρδ'
        exact le_of_mul_le_mul_left (hprod.trans (hprod'.trans h3)) (by positivity)
    have htt₁ : t₁ ≤ -t := by
      by_contra hneg
      have := GradientLikeStrip.f_flow_antitone (D := E) hfs ((E.chart q hq).χ y)
        (not_le.1 hneg).le
      simp only at this
      rw [hft₁] at this
      linarith [hft.2]
    have := hnoball q hq hq1 _ he p hp hqp.symm hlt (-t - t₁) (by linarith)
    rw [GradientLikeStrip.flow_flow, add_sub_cancel] at this
    exact this hx
  have hρ2 : ρ ^ 2 < ε / 4 := hρε
  have hErm : ∀ m hm, 24 * ε < E.rm m hm ^ 2 := fun m hm => by
    by_cases hm1 : 1 ≤ morseIndex I f m
    · rw [hErm32 m hm hm1]; linarith
    · rw [hE3 m hm, hD4 m hm fun h => hm1 (Finset.mem_filter.1 h).2]; linarith [hD₀rm m hm]
  have hρrm : ∀ m hm, ρ < E.rm m hm := fun m hm => by
    apply lt_of_pow_lt_pow_left₀ 2 (E.rm_pos m hm).le; linarith [hErm m hm]
  have hsubrm : ∀ m (hm : m ∈ crit), (E.chart m hm).χ '' {w | morseNorm n w < ρ} ⊆
      (E.chart m hm).χ '' {w | morseNorm n w < E.rm m hm} := fun m hm =>
    image_mono fun w (hw : morseNorm n w < ρ) =>
      show morseNorm n w < E.rm m hm from hw.trans (hρrm m hm)
  have hsubR' : ∀ m (hm : m ∈ crit), (E.chart m hm).χ '' {w | morseNorm n w < E.rm m hm} ⊆
      (E.chart m hm).χ '' Metric.ball 0 (E.chart m hm).R' := fun m hm =>
    image_mono fun w (hw : morseNorm n w < E.rm m hm) =>
      (E.chart m hm).mem_ball_of_le (hw.le.trans (E.hrm m hm).2)
  have hzero : ∀ p (hp : p ∈ crit) q (hq : q ∈ crit), p ≠ q → (E.chart p hp).k = 0 →
      (E.chart q hq).k = 0 → E.noCommon p hp q hq ρ ρ := by
    intro p hp q hq hpq hkp hkq z hz s hs
    rcases le_or_gt 0 s with h | h
    · have h1 := GradientLikeStrip.flow_mem_modelBall_of_index_zero (D := E) hkp
        (hsubrm p hp hz) h
      exact Set.disjoint_left.1 (E.disjoint p hp q hq hpq) (hsubR' p hp h1)
        (hsubR' q hq (hsubrm q hq hs))
    · have h1 := GradientLikeStrip.flow_mem_modelBall_of_index_zero (D := E) hkq
        (hsubrm q hq hs) (t := -s) (by linarith)
      rw [GradientLikeStrip.flow_neg_flow] at h1
      exact Set.disjoint_left.1 (E.disjoint p hp q hq hpq) (hsubR' p hp (hsubrm p hp hz))
        (hsubR' q hq h1)
  refine ⟨E, ε, hε, ρ, hρ, by linarith, fun p hp => ⟨?_, ?_, hErm p hp, ?_⟩,
    fun p hp q hq hpq hidx => ?_⟩
  · rw [(hE1 p hp).2.2.1, (hD1 p hp).2.2.1, (hD₀1 p hp).2.2.1]; exact hR p hp
  · rw [hE2 p hp]
    have : (ρ / 2) ^ 2 = ρ ^ 2 / 4 := by ring
    rw [this]; linarith
  · rw [hE2 p hp]; linarith
  · by_cases h0 : morseIndex I f p = 0
    · refine hzero p hp q hq hpq ?_ ?_
      · rw [← (E.chart p hp).hkidx]; exact h0
      · rw [← (E.chart q hq).hkidx, ← hidx]; exact h0
    · have h1 : 1 ≤ morseIndex I f p := Nat.one_le_iff_ne_zero.2 h0
      rcases lt_trichotomy (f p) (f q) with hlt | heq | hgt
      · exact hball p hp q hq h1 hidx.symm hlt
      · exact absurd (hinj' p hp q hq heq) hpq
      · intro z hz s hs
        have := hball q hq p hp (hidx ▸ h1) hidx hgt (E.flow s z) hs (-s)
        rw [GradientLikeStrip.flow_neg_flow] at this
        exact this hz

theorem exists_merge_lowest {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) {crit : Finset M}
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {ε r' : ℝ} (hε : 0 < ε) (hr' : 0 < r')
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {ℓ : ℕ}
    (hmin : ∀ x ∈ crit, ℓ ≤ morseIndex I f x)
    (hnoc : ∀ p hp q hq, p ≠ q → morseIndex I f p = morseIndex I f q →
      morseIndex I f p ≤ ℓ + 1 → D.noCommon p hp q hq r' r') :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ sameCritIn I f g a b ∧
      ∃ α β : ℝ, a < α ∧ α < β ∧ β < b ∧
        (∀ x ∈ crit, morseIndex I f x = ℓ → g x = α) ∧
        (∀ x ∈ crit, morseIndex I f x = ℓ + 1 → g x = β) ∧
        (∀ x ∈ crit, ℓ + 1 < morseIndex I f x → β < g x) ∧
        ∃ D' : GradientLikeStrip I g a b crit, ∃ ε' : ℝ, 0 < ε' ∧
          ∀ x hx, (D'.chart x hx).r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < D'.rm x hx ^ 2 := by
  classical
  have gap : ∀ (h : M → ℝ) (lo hi : ℝ) (A B : Finset M), lo < hi → (∀ x ∈ A, h x < hi) →
      (∀ y ∈ B, lo < h y) → (∀ x ∈ A, ∀ y ∈ B, h x < h y) →
      ∃ t, lo < t ∧ t < hi ∧ (∀ x ∈ A, h x < t) ∧ ∀ y ∈ B, t < h y := by
    intro h lo hi A B hlh hA hB hAB
    set m := (insert lo (A.image h)).max' (Finset.insert_nonempty _ _) with hm
    set m' := (insert hi (B.image h)).min' (Finset.insert_nonempty _ _) with hm'
    have hmm' : m < m' := by
      refine (Finset.max'_lt_iff _ _).2 (fun y hy => (Finset.lt_min'_iff _ _).2 (fun z hz => ?_))
      rcases Finset.mem_insert.1 hy with rfl | hy
      · rcases Finset.mem_insert.1 hz with rfl | hz
        · exact hlh
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
          exact hB w hw
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact hA v hv
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
          exact hAB v hv w hw
    have hlo : lo ≤ m := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
    have hhi : m' ≤ hi := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    refine ⟨(m + m') / 2, by linarith, by linarith, fun x hx => ?_, fun y hy => ?_⟩
    · have : h x ≤ m := Finset.le_max' _ _
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem h hx))
      linarith
    · have : m' ≤ h y := Finset.min'_le _ _
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem h hy))
      linarith
  have hcritg : ∀ g : M → ℝ, ModifiedWithin f a b g → sameCritIn I f g a b →
      ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
    intro g hmod hsc x
    have hx : g x ∈ Ioo a b ↔ f x ∈ Ioo a b := Set.ext_iff.1 hmod.preimage_Ioo x
    rw [hcrit x]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hx.2 h1, (hsc.1 x h1).2 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hx.1 h1, (hsc.1 x (hx.1 h1)).1 h2⟩
  have phase : ∀ (k : ℕ), k ≤ ℓ + 1 → ∀ (t : ℝ), a < t → t < b → ∀ (N : ℕ) (g : M → ℝ)
      (D : GradientLikeStrip I g a b crit) (ε : ℝ),
      ModifiedWithin f a b g → MorseStrip I g a b → sameCritIn I f g a b → 0 < ε →
      (∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) →
      (∀ p hp q hq, p ≠ q → morseIndex I f p = morseIndex I f q →
        morseIndex I f p ≤ ℓ + 1 → D.noCommon p hp q hq r' r') →
      (∀ x ∈ crit, ∀ y ∈ crit, morseIndex I f x < morseIndex I f y → g x < g y) →
      (∀ x ∈ crit, morseIndex I f x = k → g x ≤ t) →
      (∀ x ∈ crit, morseIndex I f x < k → g x < t) →
      (∀ x ∈ crit, k < morseIndex I f x → t < g x) →
      (crit.filter (fun x => morseIndex I f x = k ∧ g x ≠ t)).card ≤ N →
      ∃ g' : M → ℝ, ∃ D' : GradientLikeStrip I g' a b crit, ∃ ε' : ℝ,
        ModifiedWithin f a b g' ∧ MorseStrip I g' a b ∧ sameCritIn I f g' a b ∧ 0 < ε' ∧
        (∀ x hx, (D'.chart x hx).r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < D'.rm x hx ^ 2) ∧
        (∀ p hp q hq, p ≠ q → morseIndex I f p = morseIndex I f q →
          morseIndex I f p ≤ ℓ + 1 → D'.noCommon p hp q hq r' r') ∧
        (∀ x ∈ crit, ∀ y ∈ crit, morseIndex I f x < morseIndex I f y → g' x < g' y) ∧
        (∀ x ∈ crit, morseIndex I f x = k → g' x = t) ∧
        (∀ x ∈ crit, morseIndex I f x ≠ k → g' x = g x) := by
    intro k hk t hat htb N
    induction N with
    | zero =>
      intro g D ε hmod hms hsc hε0 hεr0 hnoc0 hsi0 hle hlo hhi hcard
      refine ⟨g, D, ε, hmod, hms, hsc, hε0, hεr0, hnoc0, hsi0, fun x hx hxk => ?_,
        fun x _ _ => rfl⟩
      by_contra hne
      have hmem : x ∈ crit.filter (fun x => morseIndex I f x = k ∧ g x ≠ t) :=
        Finset.mem_filter.2 ⟨hx, hxk, hne⟩
      have := Finset.card_pos.2 ⟨x, hmem⟩
      omega
    | succ N ih =>
      intro g D ε hmod hms hsc hε0 hεr0 hnoc0 hsi0 hle hlo hhi hcard
      set T := crit.filter (fun x => morseIndex I f x = k ∧ g x ≠ t) with hT
      by_cases hTe : T.Nonempty
      swap
      · refine ⟨g, D, ε, hmod, hms, hsc, hε0, hεr0, hnoc0, hsi0, fun x hx hxk => ?_,
          fun x _ _ => rfl⟩
        by_contra hne
        exact hTe ⟨x, Finset.mem_filter.2 ⟨hx, hxk, hne⟩⟩
      have hcg := hcritg g hmod hsc
      obtain ⟨z₀, hz₀T, hmax⟩ := T.exists_max_image g hTe
      obtain ⟨hz₀, hz₀k, hz₀t⟩ := Finset.mem_filter.1 hz₀T
      have hs₀t : g z₀ < t := lt_of_le_of_ne (hle z₀ hz₀ hz₀k) hz₀t
      have hz₀ab := ((hcg z₀).1 hz₀).1
      obtain ⟨u, hau, hus₀, hu, -⟩ := gap g a (g z₀) (crit.filter (fun x => g x < g z₀)) ∅
        hz₀ab.1 (fun x hx => (Finset.mem_filter.1 hx).2) (fun y hy => by simp at hy)
        (fun x _ y hy => by simp at hy)
      obtain ⟨v, htv, hvb, -, hv⟩ := gap g t b ∅ (crit.filter (fun x => t < g x))
        htb (fun x hx => by simp at hx) (fun y hy => (Finset.mem_filter.1 hy).2)
        (fun x hx _ _ => by simp at hx)
      set S := crit.filter (fun x => morseIndex I f x = k ∧ g x = g z₀) with hS
      have hSc : ∀ x ∈ S, x ∈ crit := fun x hx => (Finset.mem_filter.1 hx).1
      have hSlev : ∀ x ∈ S, g x = g z₀ := fun x hx => (Finset.mem_filter.1 hx).2.2
      have hSk : ∀ x ∈ S, morseIndex I f x = k := fun x hx => (Finset.mem_filter.1 hx).2.1
      have hwin : ∀ x ∈ crit, g x ∈ Icc u v → g x = g z₀ ∨ g x = t := by
        intro x hx hxuv
        have h1 : g z₀ ≤ g x := by
          by_contra h
          push Not at h
          have := hu x (Finset.mem_filter.2 ⟨hx, h⟩)
          linarith [hxuv.1]
        have h2 : g x ≤ t := by
          by_contra h
          push Not at h
          have := hv x (Finset.mem_filter.2 ⟨hx, h⟩)
          linarith [hxuv.2]
        by_contra hne
        push Not at hne
        have h1' : g z₀ < g x := lt_of_le_of_ne h1 (Ne.symm hne.1)
        have h2' : g x < t := lt_of_le_of_ne h2 hne.2
        rcases lt_trichotomy (morseIndex I f x) k with hxk | hxk | hxk
        · have := hsi0 x hx z₀ hz₀ (hz₀k ▸ hxk)
          linarith
        · have := hmax x (Finset.mem_filter.2 ⟨hx, hxk, ne_of_lt h2'⟩)
          linarith
        · have := hhi x hx hxk
          linarith
      have hidx_t : ∀ y ∈ crit, g y = t → morseIndex I f y = k := by
        intro y hy hyt
        rcases lt_trichotomy (morseIndex I f y) k with hyk | hyk | hyk
        · have := hlo y hy hyk
          linarith
        · exact hyk
        · have := hhi y hy hyk
          linarith
      obtain ⟨g₁, hmod₁, hms₁, hsc₁, hS₁, hnS₁, D₁, hresc, hχ, ε₁, hε₁, -, hεr₁, -⟩ :=
        exists_vertical_move I hms hcg D hε0 hεr0 S hSc hSlev hau hvb
          ⟨lt_of_lt_of_le hus₀ le_rfl, by linarith⟩ ⟨by linarith, htv⟩ hwin
          (fun _ _ => r') (fun _ _ => hr')
          (fun x hx y hy hxS hyS hyt => by
            have hxk := hSk x hxS
            have hyk := hidx_t y hy hyt
            have hxy : x ≠ y := fun h => hyS (h ▸ hxS)
            exact hnoc0 x hx y hy hxy (hxk.trans hyk.symm) (hxk ▸ hk))
      have hmodf₁ : ModifiedWithin f a b g₁ := hmod.trans (hmod₁.mono hau.le hvb.le)
      have hscf₁ : sameCritIn I f g₁ a b := hsc.trans hmod hsc₁
      have hne₁ : ∀ x ∈ crit, morseIndex I f x ≠ k → g₁ x = g x := fun x hx hxk =>
        hnS₁ x hx (fun hxS => hxk (hSk x hxS))
      have hnoc₁ : ∀ p hp q hq, p ≠ q → morseIndex I f p = morseIndex I f q →
          morseIndex I f p ≤ ℓ + 1 → D₁.noCommon p hp q hq r' r' :=
        fun p hp q hq hpq hidx hl =>
          GradientLikeStrip.noCommon.of_rescale hresc (fun x hx => (hχ x hx).1)
            (hnoc0 p hp q hq hpq hidx hl)
      have hsi₁ : ∀ x ∈ crit, ∀ y ∈ crit, morseIndex I f x < morseIndex I f y →
          g₁ x < g₁ y := by
        intro x hx y hy hxy
        by_cases hxS : x ∈ S
        · have hy' : y ∉ S := fun hyS => by
            rw [hSk x hxS, hSk y hyS] at hxy
            exact lt_irrefl _ hxy
          rw [hS₁ x hxS, hnS₁ y hy hy']
          exact hhi y hy (hSk x hxS ▸ hxy)
        · by_cases hyS : y ∈ S
          · rw [hS₁ y hyS, hnS₁ x hx hxS]
            exact hlo x hx (hSk y hyS ▸ hxy)
          · rw [hnS₁ x hx hxS, hnS₁ y hy hyS]
            exact hsi0 x hx y hy hxy
      have hle₁ : ∀ x ∈ crit, morseIndex I f x = k → g₁ x ≤ t := by
        intro x hx hxk
        by_cases hxS : x ∈ S
        · rw [hS₁ x hxS]
        · rw [hnS₁ x hx hxS]
          exact hle x hx hxk
      have hlo₁ : ∀ x ∈ crit, morseIndex I f x < k → g₁ x < t := fun x hx hxk => by
        rw [hne₁ x hx (ne_of_lt hxk)]
        exact hlo x hx hxk
      have hhi₁ : ∀ x ∈ crit, k < morseIndex I f x → t < g₁ x := fun x hx hxk => by
        rw [hne₁ x hx (ne_of_gt hxk)]
        exact hhi x hx hxk
      have hsub : crit.filter (fun x => morseIndex I f x = k ∧ g₁ x ≠ t) ⊂ T := by
        have hss : crit.filter (fun x => morseIndex I f x = k ∧ g₁ x ≠ t) ⊆ T := by
          intro x hx
          obtain ⟨hxc, hxk, hxt⟩ := Finset.mem_filter.1 hx
          have hxS : x ∉ S := fun hxS => hxt (hS₁ x hxS)
          rw [hnS₁ x hxc hxS] at hxt
          exact Finset.mem_filter.2 ⟨hxc, hxk, hxt⟩
        refine (Finset.ssubset_iff_of_subset hss).2 ⟨z₀, hz₀T, fun h => ?_⟩
        have hz₀S : z₀ ∈ S := Finset.mem_filter.2 ⟨hz₀, hz₀k, rfl⟩
        exact (Finset.mem_filter.1 h).2.2 (hS₁ z₀ hz₀S)
      have hcard₁ := Finset.card_lt_card hsub
      obtain ⟨g₂, D₂, ε₂, hmod₂, hms₂, hsc₂, hε₂, hεr₂, hnoc₂, hsi₂, hk₂, hne₂⟩ :=
        ih g₁ D₁ ε₁ hmodf₁ hms₁ hscf₁ hε₁ hεr₁ hnoc₁ hsi₁ hle₁ hlo₁ hhi₁ (by omega)
      exact ⟨g₂, D₂, ε₂, hmod₂, hms₂, hsc₂, hε₂, hεr₂, hnoc₂, hsi₂, hk₂,
        fun x hx hxk => (hne₂ x hx hxk).trans (hne₁ x hx hxk)⟩
  have hsi0 : ∀ x ∈ crit, ∀ y ∈ crit, morseIndex I f x < morseIndex I f y → f x < f y :=
    fun x hx y hy hxy => hsi x y ((hcrit x).1 hx).1 ((hcrit y).1 hy).1 ((hcrit x).1 hx).2
      ((hcrit y).1 hy).2 hxy
  obtain ⟨α, haα, hαb, hαP, hαH⟩ := gap f a b (crit.filter (fun x => morseIndex I f x = ℓ))
    (crit.filter (fun x => ℓ < morseIndex I f x)) hf.lt
    (fun x hx => ((hcrit x).1 (Finset.mem_filter.1 hx).1).1.2)
    (fun y hy => ((hcrit y).1 (Finset.mem_filter.1 hy).1).1.1)
    (fun x hx y hy => hsi0 x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1
      ((Finset.mem_filter.1 hx).2 ▸ (Finset.mem_filter.1 hy).2))
  obtain ⟨g₁, D₁, ε₁, hmod₁, hms₁, hsc₁, hε₁, hεr₁, hnoc₁, hsi₁, hP₁, hne₁⟩ :=
    phase ℓ (Nat.le_succ ℓ) α haα hαb _ f D ε (ModifiedWithin.refl f a b) hf
      (sameCritIn.refl I f a b) hε hεr hnoc hsi0
      (fun x hx hxk => (hαP x (Finset.mem_filter.2 ⟨hx, hxk⟩)).le)
      (fun x hx hxk => absurd (hmin x hx) (not_le.2 hxk))
      (fun x hx hxk => hαH x (Finset.mem_filter.2 ⟨hx, hxk⟩)) le_rfl
  have hcg₁ := hcritg g₁ hmod₁ hsc₁
  obtain ⟨β, hαβ, hβb, hβQ, hβH⟩ := gap g₁ α b
    (crit.filter (fun x => morseIndex I f x = ℓ + 1))
    (crit.filter (fun x => ℓ + 1 < morseIndex I f x)) hαb
    (fun x hx => ((hcg₁ x).1 (Finset.mem_filter.1 hx).1).1.2)
    (fun y hy => by
      obtain ⟨hy, hyk⟩ := Finset.mem_filter.1 hy
      rw [hne₁ y hy (by omega)]
      exact hαH y (Finset.mem_filter.2 ⟨hy, by omega⟩))
    (fun x hx y hy => hsi₁ x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1
      ((Finset.mem_filter.1 hx).2 ▸ (Finset.mem_filter.1 hy).2))
  obtain ⟨g₂, D₂, ε₂, hmod₂, hms₂, hsc₂, hε₂, hεr₂, -, -, hQ₂, hne₂⟩ :=
    phase (ℓ + 1) le_rfl β (haα.trans hαβ) hβb _ g₁ D₁ ε₁ hmod₁ hms₁ hsc₁ hε₁ hεr₁ hnoc₁ hsi₁
      (fun x hx hxk => (hβQ x (Finset.mem_filter.2 ⟨hx, hxk⟩)).le)
      (fun x hx hxk => by
        have hxℓ : morseIndex I f x = ℓ := by have := hmin x hx; omega
        rw [hP₁ x hx hxℓ]
        exact hαβ)
      (fun x hx hxk => hβH x (Finset.mem_filter.2 ⟨hx, hxk⟩)) le_rfl
  refine ⟨g₂, hmod₂, hms₂, hsc₂, α, β, haα, hαβ, hβb, fun x hx hxk => ?_, hQ₂,
    fun x hx hxk => ?_, D₂, ε₂, hε₂, hεr₂⟩
  · rw [hne₂ x hx (by omega)]
    exact hP₁ x hx hxk
  · rw [hne₂ x hx (by omega)]
    exact hβH x (Finset.mem_filter.2 ⟨hx, hxk⟩)

omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem exists_blockConfig_of_levels {g : M → ℝ} {a b : ℝ} (hg : MorseStrip I g a b)
    {crit : Finset M} (hcrit : ∀ x, x ∈ crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x)
    (D : GradientLikeStrip I g a b crit) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2) {ℓ : ℕ}
    (hmin : ∀ x ∈ crit, ℓ ≤ morseIndex I g x) {α β c : ℝ} (haα : a < α) (hαc : α < c)
    (hcβ : c < β) (hβb : β < b) (hP : ∀ x ∈ crit, morseIndex I g x = ℓ → g x = α)
    (hQ : ∀ x ∈ crit, morseIndex I g x = ℓ + 1 → g x = β)
    (hhigh : ∀ x ∈ crit, ℓ + 1 < morseIndex I g x → β < g x) :
    ∃ B : BlockConfig I g a b ℓ, B.crit = crit ∧ B.α = α ∧ B.β = β ∧ B.c = c ∧ B.ε ≤ ε ∧
      (∀ x (hx : x ∈ crit) (hx' : x ∈ B.crit), (B.D.chart x hx').χ = (D.chart x hx).χ ∧
        (B.D.chart x hx').k = (D.chart x hx).k) ∧
      ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ z, B.D.V z = φ z • D.V z := by
  set ε₁ : ℝ := min ε (min ((c - α) / 2) ((β - c) / 2)) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε (lt_min (by linarith) (by linarith))
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  have hε₁α : ε₁ ≤ (c - α) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₁β : ε₁ ≤ (β - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρ0 : (0 : ℝ) < 8 * ε₁ + 1 := by linarith
  have hρ : 8 * ε₁ < (8 * ε₁ + 1) ^ 2 := by nlinarith
  have hrm : ∀ x hx, 8 * ε₁ < D.rm x hx ^ 2 := fun x hx => by
    have := (hεr x hx).2
    linarith
  obtain ⟨D', hresc, hchart, hsmall, -⟩ :=
    GradientLikeStrip.exists_shrink_field hg.smooth D hε₁ hρ0 hρ hrm
  have hr₀' : ∀ x hx, (D'.chart x hx).r₀ ^ 2 < 2 * ε := fun x hx => by
    have := (hsmall x hx).1
    linarith
  have hrm' : ∀ x hx, 8 * ε₁ < D'.rm x hx ^ 2 := fun x hx => by
    rw [(hsmall x hx).2]
    rcases min_choice (8 * ε₁ + 1) (D.rm x hx) with h | h
    · rw [h]; exact hρ
    · rw [h]; exact hrm x hx
  have hlev : ∀ y, g y ∈ Icc (α + ε₁) (β - ε₁) → ∀ x hx, y ∉ D'.smallBall x hx := by
    intro y hy x hx hmem
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hmem
    have h2 := (hsmall x hx).1
    rw [abs_lt] at h1
    have hxm := hmin x hx
    rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I g x) with h | h
    · have := hhigh x hx h
      linarith [hy.2]
    · rcases Nat.lt_or_ge (morseIndex I g x) (ℓ + 1) with h' | h'
      · have hx' : morseIndex I g x = ℓ := by omega
        have := hP x hx hx'
        linarith [hy.1]
      · have hx' : morseIndex I g x = ℓ + 1 := by omega
        have := hQ x hx hx'
        linarith [hy.2]
  let B : BlockConfig I g a b ℓ :=
    { crit := crit
      hcrit := hcrit
      D := D'
      α := α
      β := β
      ε := ε₁
      c := c
      hε := hε₁
      hr₀ := fun x hx => (hsmall x hx).1
      hrm := hrm'
      haα := haα
      hαc := by linarith
      hcβ := by linarith
      hβb := hβb
      hmin := hmin
      hP := hP
      hQ := hQ
      hhigh := hhigh
      hlev := hlev }
  obtain ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hφV⟩ := hresc
  have hφpos : ∀ x, 0 < φ x := fun x => hm.trans_le (hφb x).1
  have hM₀ : 0 < max M₀ m := lt_max_of_lt_right hm
  refine ⟨B, rfl, rfl, rfl, rfl, hε₁ε, fun x hx _ => ⟨(hchart x hx).1, (hchart x hx).2.1⟩,
    fun x => (φ x)⁻¹, hφc.inv₀ fun x => (hφpos x).ne', ⟨(max M₀ m)⁻¹, m⁻¹, inv_pos.2 hM₀, fun x =>
      ⟨inv_anti₀ (hφpos x) ((hφb x).2.trans (le_max_left _ _)), inv_anti₀ hm (hφb x).1⟩⟩, fun z => ?_⟩
  change D'.V z = (φ z)⁻¹ • D.V z
  rw [hφV z, smul_smul, inv_mul_cancel₀ (hφpos z).ne', one_smul]

theorem exists_blockConfig {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b) {ℓ : ℕ}
    (hmin : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → ℓ ≤ morseIndex I f x) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ sameCritIn I f g a b ∧
      Nonempty (BlockConfig I g a b ℓ) := by
  classical
  have bubble : ∀ N : ℕ, ∀ f₀ : M → ℝ, MorseStrip I f₀ a b →
      InjOn f₀ {x | f₀ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₀ x} →
      (Swap.invSet I f₀ a b).ncard = N →
      ∃ g : M → ℝ, ModifiedWithin f₀ a b g ∧ MorseStrip I g a b ∧ isSelfIndexing I g a b ∧
        (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₀ x) ∧
        (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₀ x → morseIndex I g x = morseIndex I f₀ x) ∧
        InjOn g {x | g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x} := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro f₀ hf₀ hinj hN
      by_cases h0 : Swap.invSet I f₀ a b = ∅
      · exact ⟨f₀, ModifiedWithin.refl f₀ a b, hf₀,
          Swap.isSelfIndexing_of_invSet_eq_empty hinj h0, fun _ => Iff.rfl, fun _ _ => rfl, hinj⟩
      · have hne : (Swap.invSet I f₀ a b).Nonempty := nonempty_iff_ne_empty.2 h0
        obtain ⟨p, q, hp, hq, hcp, hcq, hlt, hidx, hadj⟩ := Swap.exists_adjacent_inversion hf₀ hne
        obtain ⟨g, hmod, hg, hcritIff, hidxEq, hgp, hgq, -, hother, hsep, hinjg⟩ :=
          Swap.exists_swap hf₀ hinj hp hq hcp hcq hlt hadj hidx
        have hss := Swap.invSet_ssubset_of_swap hinj hp hq hcp hcq hlt hadj hidx hmod hcritIff
          hidxEq hgp hgq hother hsep
        have hlt' : (Swap.invSet I g a b).ncard < N := by
          rw [← hN]
          exact Set.ncard_lt_ncard hss (Swap.invSet_finite hf₀)
        obtain ⟨g', hmod', hg', hself, hcritIff', hidxEq', hinj'⟩ := ih _ hlt' g hg hinjg rfl
        refine ⟨g', hmod.trans hmod', hg', hself, fun x => (hcritIff' x).trans (hcritIff x),
          fun x hx => ?_, hinj'⟩
        rw [hidxEq' x ((hcritIff x).2 hx), hidxEq x hx]
  obtain ⟨g₁, hmod₁, hg₁, hcrit₁, hidx₁, hinj₁'⟩ := exists_distinct_critical_values I hf
  have hsc₁ : sameCritIn I f g₁ a b := ⟨hcrit₁, hidx₁⟩
  have hpre₁ : ∀ x, g₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₁.preimage_Ioo x
  have hinj₁ : InjOn g₁ {x | g₁ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₁ x} := by
    refine hinj₁'.mono fun x hx => ?_
    have hfx : f x ∈ Ioo a b := (hpre₁ x).1 hx.1
    exact ⟨hfx, (hcrit₁ x hfx).1 hx.2⟩
  obtain ⟨g₂, hmod₂, hg₂, hsi₂, hcrit₂, hidx₂, hinj₂⟩ := bubble _ g₁ hg₁ hinj₁ rfl
  have hsc₂ : sameCritIn I g₁ g₂ a b := ⟨fun x _ => hcrit₂ x, fun x _ hc => hidx₂ x hc⟩
  have hsc₁₂ : sameCritIn I f g₂ a b := hsc₁.trans hmod₁ hsc₂
  have hmod₁₂ : ModifiedWithin f a b g₂ := hmod₁.trans hmod₂
  have hfin : {x | g₂ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x}.Finite :=
    hg₂.finite_critical.subset fun x hx => ⟨Ioo_subset_Icc_self hx.1, hx.2⟩
  set crit : Finset M := hfin.toFinset with hcritdef
  have hcrit : ∀ x, x ∈ crit ↔ g₂ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₂ x := fun x => by
    rw [hcritdef, Set.Finite.mem_toFinset]; rfl
  obtain ⟨D, ε, hε, r', hr', -, hbounds, hnoc⟩ :=
    exists_gradientLike_sameIndexPairs I hg₂ hsi₂ hinj₂ crit hcrit (R₀ := 1) one_pos
  have hεr : ∀ x hx, (D.chart x hx).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm x hx ^ 2 := fun x hx =>
    ⟨(hbounds x hx).2.1, by linarith [(hbounds x hx).2.2.1]⟩
  have hmin₂ : ∀ x ∈ crit, ℓ ≤ morseIndex I g₂ x := by
    intro x hx
    obtain ⟨h1, h2⟩ := (hcrit x).1 hx
    obtain ⟨hf1, hf2, hf3⟩ := hsc₁₂.crit_of hmod₁₂ h1 h2
    rw [hf3]
    exact hmin x hf1 hf2
  obtain ⟨g₃, hmod₃, hg₃, hsc₃, α, β, haα, hαβ, hβb, hP, hQ, hhigh, D', ε', hε', hεr'⟩ :=
    exists_merge_lowest I hg₂ hsi₂ hcrit D hε hr' hεr hmin₂
      (fun p hp q hq hpq hidx _ => hnoc p hp q hq hpq hidx)
  have hpre₃ : ∀ x, g₃ x ∈ Ioo a b ↔ g₂ x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₃.preimage_Ioo x
  have hcrit₃ : ∀ x, x ∈ crit ↔ g₃ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₃ x := by
    intro x
    rw [hcrit x, hpre₃ x]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hsc₃.1 x h1).2 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hsc₃.1 x h1).1 h2⟩
  have hidx₃ : ∀ x ∈ crit, morseIndex I g₃ x = morseIndex I g₂ x := by
    intro x hx
    obtain ⟨h1, h2⟩ := (hcrit x).1 hx
    exact hsc₃.2 x h1 h2
  obtain ⟨B, -⟩ := exists_blockConfig_of_levels I hg₃ hcrit₃ D' hε' hεr' (ℓ := ℓ)
    (fun x hx => (hidx₃ x hx).symm ▸ hmin₂ x hx) (c := (α + β) / 2) haα
    (by linarith) (by linarith) hβb
    (fun x hx h => hP x hx ((hidx₃ x hx).symm.trans h))
    (fun x hx h => hQ x hx ((hidx₃ x hx).symm.trans h))
    (fun x hx h => hhigh x hx (h.trans_eq (hidx₃ x hx)))
  exact ⟨g₃, hmod₁₂.trans hmod₃, hg₃, hsc₁₂.trans hmod₁₂ hsc₃, ⟨B⟩⟩

end BlockNormalForm

theorem SardData.exists_small_regular_value {k l : ℕ} (hkl : k = l + 1) {ι : Type*}
    (s : Finset ι) (S : ι → (Fin k → ℝ) → EuclideanSpace ℝ (Fin l)) (U : ι → Set (Fin k → ℝ))
    (hU : ∀ i ∈ s, IsOpen (U i)) (hray : ∀ i ∈ s, SardData.rayInvariant (S i) (U i))
    (hdiff : ∀ i ∈ s, DifferentiableOn ℝ (S i) (U i)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z : EuclideanSpace ℝ (Fin l), ‖z‖ < ρ ∧
      ∀ i ∈ s, ∀ w ∈ U i, S i w = z → Function.Surjective (fderiv ℝ (S i) w) := by
  subst hkl
  classical
  let ψ : EuclideanSpace ℝ (Fin l) ≃L[ℝ] (Fin l → ℝ) := EuclideanSpace.equiv (Fin l) ℝ
  let φ : Fin (l + 1) → Bool → EuclideanSpace ℝ (Fin l) → (Fin (l + 1) → ℝ) :=
    fun j b x => Fin.insertNth j (if b then (1 : ℝ) else -1) (ψ x)
  let C : ι → Fin (l + 1) → Bool → Set (EuclideanSpace ℝ (Fin l)) :=
    fun i j b => {x | φ j b x ∈ U i ∧ ¬ Function.Surjective (fderiv ℝ (S i) (φ j b x))}
  let B : Set (EuclideanSpace ℝ (Fin l)) :=
    ⋃ i ∈ (s : Set ι), ⋃ j, ⋃ b, (S i ∘ φ j b) '' C i j b
  have hφd : ∀ j b x, DifferentiableAt ℝ (φ j b) x := by
    intro j b x
    rw [differentiableAt_pi]
    intro m
    induction m using Fin.succAboveCases j with
    | x => simp only [φ, Fin.insertNth_apply_same]; exact differentiableAt_const _
    | p m =>
      simp only [φ, Fin.insertNth_apply_succAbove]
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin l => ℝ) m).comp
        ψ.toContinuousLinearMap).differentiableAt
  have hnull : MeasureTheory.volume B = 0 := by
    refine (MeasureTheory.measure_biUnion_null_iff s.countable_toSet).2 fun i hi => ?_
    refine MeasureTheory.measure_iUnion_null fun j => MeasureTheory.measure_iUnion_null fun b => ?_
    have hSd : ∀ x ∈ C i j b, DifferentiableAt ℝ (S i) (φ j b x) := fun x hx =>
      (hdiff i hi).differentiableAt ((hU i hi).mem_nhds hx.1)
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (f' := fun x => fderiv ℝ (S i ∘ φ j b) x) _ (fun x hx => ?_) (fun x hx => ?_)
    · exact ((hSd x hx).comp x (hφd j b x)).hasFDerivAt.hasFDerivWithinAt
    · by_contra hdet
      apply hx.2
      have hunit : IsUnit ((fderiv ℝ (S i ∘ φ j b) x :
          EuclideanSpace ℝ (Fin l) →ₗ[ℝ] EuclideanSpace ℝ (Fin l)) : Module.End ℝ _) :=
        (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
      have hsurj := ((Module.End.isUnit_iff _).1 hunit).2
      intro y
      obtain ⟨v, hv⟩ := hsurj y
      refine ⟨fderiv ℝ (φ j b) x v, ?_⟩
      have := fderiv_comp x (hSd x hx) (hφd j b x)
      simp only [ContinuousLinearMap.coe_coe, this] at hv
      exact hv
  have hpos : 0 < MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin l)) ρ) :=
    Metric.measure_ball_pos _ _ hρ
  obtain ⟨z, hzball, hzB⟩ : ∃ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin l)) ρ, z ∉ B := by
    by_contra h
    push Not at h
    exact hpos.ne' (MeasureTheory.measure_mono_null h hnull)
  refine ⟨z, by simpa using hzball, fun i hi w hw hSw => ?_⟩
  by_contra hns
  apply hzB
  obtain ⟨hne0, hinv⟩ := hray i hi
  have hw0 : w ≠ 0 := hne0 w hw
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  have ht : 0 < |w j|⁻¹ := inv_pos.2 (abs_pos.2 hj)
  obtain ⟨htw, hStw⟩ := hinv w hw _ ht
  have hSd' : DifferentiableAt ℝ (S i) (|w j|⁻¹ • w) :=
    (hdiff i hi).differentiableAt ((hU i hi).mem_nhds htw)
  have heq : (S i ∘ fun v => |w j|⁻¹ • v) =ᶠ[𝓝 w] S i := by
    filter_upwards [(hU i hi).mem_nhds hw] with v hv
    exact (hinv v hv _ ht).2
  have hsm : HasFDerivAt (fun v : Fin (l + 1) → ℝ => |w j|⁻¹ • v)
      (|w j|⁻¹ • ContinuousLinearMap.id ℝ (Fin (l + 1) → ℝ)) w := by
    have h := (|w j|⁻¹ • ContinuousLinearMap.id ℝ (Fin (l + 1) → ℝ)).hasFDerivAt (x := w)
    have hfun : (⇑(|w j|⁻¹ • ContinuousLinearMap.id ℝ (Fin (l + 1) → ℝ))) =
        fun v => |w j|⁻¹ • v := by
      funext v
      simp
    rwa [hfun] at h
  have hfd : fderiv ℝ (S i) w =
      (fderiv ℝ (S i) (|w j|⁻¹ • w)).comp (|w j|⁻¹ • ContinuousLinearMap.id ℝ _) := by
    rw [← heq.fderiv_eq, fderiv_comp w hSd' hsm.differentiableAt, hsm.fderiv]
  have hns' : ¬ Function.Surjective (fderiv ℝ (S i) (|w j|⁻¹ • w)) := by
    intro hs
    apply hns
    intro y
    obtain ⟨v, hv⟩ := hs y
    refine ⟨|w j| • v, ?_⟩
    rw [hfd]
    simpa [smul_smul, mul_inv_cancel₀ (abs_pos.2 hj).ne'] using hv
  let b : Bool := decide (0 < w j)
  have hwj : (|w j|⁻¹ • w) j = if b then (1 : ℝ) else -1 := by
    simp only [Pi.smul_apply, smul_eq_mul, b]
    split_ifs with h
    · rw [abs_of_pos (by simpa using h), inv_mul_cancel₀ hj]
    · have : w j < 0 := lt_of_le_of_ne (not_lt.1 (by simpa using h)) hj
      rw [abs_of_neg this, inv_neg, neg_mul, inv_mul_cancel₀ hj]
  let x : EuclideanSpace ℝ (Fin l) := ψ.symm (Fin.removeNth j (|w j|⁻¹ • w))
  have hφx : φ j b x = |w j|⁻¹ • w := by
    simp only [φ, x, ContinuousLinearEquiv.apply_symm_apply]
    rw [← hwj, Fin.insertNth_self_removeNth]
  simp only [B, Set.mem_iUnion, Set.mem_image]
  refine ⟨i, hi, j, b, x, ⟨?_, ?_⟩, ?_⟩
  · rw [hφx]; exact htw
  · rw [hφx]; exact hns'
  · simp only [Function.comp_apply, hφx, hStw, hSw]

namespace GradientLikeStrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem sardMap_twisted_of_small (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {p : M} (hp : p ∈ crit) {η ρ : ℝ}
    {z : EuclideanSpace ℝ (Fin (D.chart p hp).k)} (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (hηrm : η ≤ D.rm p hp ^ 2)
    (hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η) {q : M} (hq : q ∈ crit) {ε c : ℝ} (hε : 0 < ε)
    (hεη : 8 * ε < η) (hz : ‖z‖ ≤ ρ) (hB : 2 * η + 4 * ρ ^ 2 / ε < D.rm p hp ^ 2)
    (hr₀q : (D.chart q hq).r₀ ^ 2 < 2 * ε) (hηq : 2 * η < D.rm q hq ^ 2)
    (hεq : 2 * ε ≤ (D.chart q hq).R ^ 2) (hc : f p + η < c) (hcq : c < f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp')
    {w : Fin (D.chart q hq).k → ℝ} (hw : w ∈ D.sardDom p hq η c η hp)
    (hsmall : ‖D.sardMap p hq η c η hp w‖ < ρ) :
    w ∈ (twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η).sardDom p hq ε c ε hp ∧
      (twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η).sardMap p hq ε c ε hp w =
        D.sardMap p hq η c η hp w - z := by
  obtain ⟨hw0, hwL⟩ := hw
  have hw0' : w ≠ 0 := hw0
  have hpa : a < f p := (D.f_mem_Ioo p hp).1
  have hqb : f q < b := (D.f_mem_Ioo q hq).2
  have hqside : D.flow (η - ε) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) =
      (D.chart q hq).χ ((D.chart q hq).sphereParam η w) := by
    have hymem := (D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw0'
    have hyv : posPart (D.chart q hq).hk ((D.chart q hq).sphereParam ε w) = 0 := hymem.1
    have hyu : ‖negPart (D.chart q hq).hk ((D.chart q hq).sphereParam ε w)‖ ^ 2 = 2 * ε :=
      hymem.2
    have hu0 : negPart (D.chart q hq).hk ((D.chart q hq).sphereParam ε w) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hyu
      linarith
    have hrm0 := D.rm_pos q hq
    have hball : 2 * η + 2 * ‖posPart (D.chart q hq).hk ((D.chart q hq).sphereParam ε w)‖ ^ 2 <
        D.rm q hq ^ 2 := by
      rw [hyv, norm_zero]; linarith
    have hlevel : f q - η ≤
        morseNormalForm (D.chart q hq).hk (f q) ((D.chart q hq).sphereParam ε w) := by
      rw [(D.chart q hq).nf_of_mem_leftModelSphere hymem]; linarith
    obtain ⟨t, ht0, hft, hstay, -⟩ := exists_exit_desc hf hq hη hball hu0 hlevel
    rw [hyv, norm_zero] at hstay
    have hSsub : {z : Fin n → ℝ | morseNorm n z ^ 2 ≤ 2 * η + 2 * 0 ^ 2} ⊆
        {z | morseNorm n z < D.rm q hq} := fun z hz => by
      have hz' : morseNorm n z ^ 2 ≤ 2 * η + 2 * 0 ^ 2 := hz
      exact lt_of_pow_lt_pow_left₀ 2 hrm0.le (by linarith)
    have hODE : ∀ s ∈ Icc 0 t, D.flow s ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) ∈
        (D.chart q hq).χ '' {z | morseNorm n z < D.rm q hq} :=
      fun s hs => image_mono hSsub (hstay s hs)
    have hγ := hasDerivAt_symm_flow_Icc hq hODE
    have hyrm : morseNorm n ((D.chart q hq).sphereParam ε w) < D.rm q hq := by
      apply lt_of_pow_lt_pow_left₀ 2 hrm0.le
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart (D.chart q hq).hk, hyu, hyv, norm_zero]
      linarith
    have hyR : morseNorm n ((D.chart q hq).sphereParam ε w) ≤ (D.chart q hq).R :=
      hyrm.le.trans (D.hrm q hq).2
    have hγ0 : (D.chart q hq).χ.symm
        (D.flow 0 ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) =
        (D.chart q hq).sphereParam ε w := by
      rw [flow_zero, (D.chart q hq).χ.left_inv ((D.chart q hq).hsrc _ hyR)]
    have hmono := ModelField.normSq_negPart_monotoneOn (D.chart q hq).hk (D.chart q hq).hr₀ hγ
    have hunit : ∀ s ∈ Icc 0 t, (D.chart q hq).r₀ / 2 ≤ morseNorm n ((D.chart q hq).χ.symm
        (D.flow s ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)))) := by
      intro s hs
      have h1 := hmono (left_mem_Icc.2 ht0) hs hs.1
      simp only at h1
      rw [hγ0, hyu] at h1
      have h2 := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart (D.chart q hq).hk ((D.chart q hq).χ.symm
        (D.flow s ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))))
      have h3 := sq_nonneg ‖posPart (D.chart q hq).hk ((D.chart q hq).χ.symm
        (D.flow s ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))))‖
      have h4 : ((D.chart q hq).r₀ / 2) ^ 2 ≤ morseNorm n ((D.chart q hq).χ.symm
          (D.flow s ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)))) ^ 2 := by
        have h5 : ((D.chart q hq).r₀ / 2) ^ 2 ≤ (D.chart q hq).r₀ ^ 2 := by
          have := (D.chart q hq).hr₀
          nlinarith only [this]
        linarith only [h1, h2, h3, h5, hr₀q]
      exact (pow_le_pow_iff_left₀ (by linarith [(D.chart q hq).hr₀])
        (ModelField.morseNorm_nonneg _) two_ne_zero).1 h4
    have hnf := ModelField.nf_curve_eq_sub (D.chart q hq).hk (f q) (D.chart q hq).hr₀ hγ hunit t
      (right_mem_Icc.2 ht0)
    have htO := hODE t (right_mem_Icc.2 ht0)
    have hfe : f (D.flow t ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) =
        morseNormalForm (D.chart q hq).hk (f q) ((D.chart q hq).χ.symm
          (D.flow t ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)))) :=
      (D.chart q hq).f_eq_nf_symm (D.modelBall_subset_image_le q hq htO)
    rw [hγ0, (D.chart q hq).nf_of_mem_leftModelSphere hymem, ← hfe, hft] at hnf
    have ht : t = η - ε := by linarith
    obtain ⟨l, hl0, -, -, hl⟩ := CrossField.model_flow_scaling D hq hyrm (t := t)
      (fun s hs => hODE s (by rwa [uIcc_of_le ht0] at hs))
    rw [hyv, smul_zero, (D.chart q hq).negPart_sphereParam] at hl
    have hfe' := hfe
    rw [hft, hl, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, ModelField.negPart_recombine,
      ModelField.posPart_recombine, norm_zero, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hl0] at hfe'
    have hE : ‖(D.chart q hq).toE w‖ ≠ 0 := norm_ne_zero_iff.2 ((D.chart q hq).toE_ne_zero hw0')
    have hE' : 0 < ‖(D.chart q hq).toE w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE)
    have hs2ε : 0 ≤ Real.sqrt (2 * ε) := Real.sqrt_nonneg _
    rw [abs_of_nonneg (div_nonneg hs2ε hE'.le), div_mul_cancel₀ _ hE] at hfe'
    have hl2 : (l * Real.sqrt (2 * ε)) ^ 2 = 2 * η := by linarith only [hfe']
    have hl3 : l * Real.sqrt (2 * ε) = Real.sqrt (2 * η) := by
      rw [← hl2, Real.sqrt_sq (by positivity)]
    have hpt : (D.chart q hq).χ.symm
        (D.flow t ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) =
        (D.chart q hq).sphereParam η w := by
      rw [hl, MorseNormalChart.sphereParam, smul_smul, ← hl3, mul_div_assoc]
    rw [← ht, ← hpt, (D.chart q hq).symm_image_eq (D.modelBall_subset_image_ball q hq htO)]
  have hLeq : D.landing p hq η c η w = D.landing p hq ε c η w := by
    change D.flow (c - (f p + η)) (D.flow (f q - η - c)
        ((D.chart q hq).χ ((D.chart q hq).sphereParam η w))) =
      D.flow (c - (f p + η)) (D.flow (f q - ε - c)
        ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)))
    rw [← hqside, flow_flow (D := D) _ (η - ε) (f q - η - c),
      show η - ε + (f q - η - c) = f q - ε - c by ring]
  have hwL' : D.landing p hq η c η w ∈
      (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R} := hwL
  rw [hLeq] at hwL'
  have hsmall' : ‖ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm
      (D.landing p hq ε c η w))‖ < ρ := by
    have h := hsmall
    unfold sardMap at h
    rwa [hLeq] at h
  have hSeq : D.sardMap p hq η c η hp w = ModelField.scaledNegativePart (D.chart p hp).hk
      ((D.chart p hp).χ.symm (D.landing p hq ε c η w)) := by
    unfold sardMap
    rw [hLeq]
  obtain ⟨yL, hyLR, hyLL⟩ := hwL'
  have hyLR' : morseNorm n yL < (D.chart p hp).R := hyLR
  have hfL : f (D.landing p hq ε c η w) = f p + η :=
    f_landing hp hf hε hη hεq hc.le hcq.le
      (fun y hy => hlev y ⟨by linarith [hy.1], hy.2⟩) hw0'
  have hLsymm : (D.chart p hp).χ.symm (D.landing p hq ε c η w) = yL := by
    rw [← hyLL, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc yL hyLR'.le)]
  have hnfL : morseNormalForm (D.chart p hp).hk (f p) yL = f p + η := by
    rw [← (D.chart p hp).hnorm yL hyLR'.le, hyLL, hfL]
  rw [hLsymm] at hsmall' hSeq
  set Dt := twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η with hDt
  set L := D.landing p hq ε c η w with hL
  have hfxε : f ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) = f q - ε :=
    (D.chart q hq).f_chart_of_mem_leftModelSphere hεq
      ((D.chart q hq).sphereParam_mem_leftModelSphere hε.le hw0')
  have hTL : Dt.landing p hq ε c ε w = Dt.flow (η - ε) L := by
    have h1 : Dt.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) =
        D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) := by
      refine flow_eq_of_agree (D₁ := D) (D₂ := Dt) (isOpen_above hf.continuous (f p + η))
        (fun x hx => (twistedV_eq_of_level_ge hη hρ hsupp (le_of_lt hx)).symm) (fun s hs => ?_) _
        (right_mem_Icc.2 (by linarith))
      change f p + η < f (D.flow s _)
      have := sub_le_f_flow (D := D) hf ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w)) hs.1
      rw [hfxε] at this
      linarith [hs.2]
    have hfxc : c ≤ f (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) := by
      have := sub_le_f_flow (D := D) hf ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))
        (show 0 ≤ f q - ε - c by linarith)
      rw [hfxε] at this
      linarith
    have h2 : Dt.flow (c - (f p + η))
        (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) =
        D.flow (c - (f p + η))
          (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) := by
      refine flow_eq_of_agree (D₁ := D) (D₂ := Dt) (isOpen_above hf.continuous (f p + η))
        (fun x hx => (twistedV_eq_of_level_ge hη hρ hsupp (le_of_lt hx)).symm) (fun s hs => ?_) _
        (right_mem_Icc.2 (by linarith))
      change f p + η < f (D.flow s _)
      have := sub_le_f_flow (D := D) hf
        (D.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) hs.1
      linarith [hs.2]
    change Dt.flow (c - (f p + ε))
      (Dt.flow (f q - ε - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam ε w))) = _
    rw [h1, show c - (f p + ε) = (c - (f p + η)) + (η - ε) by ring, ← flow_flow, h2]
    rfl
  have hrm0 := D.rm_pos p hp
  set B₀ := 2 * η + 4 * ρ ^ 2 / ε with hB₀
  set S : Set (Fin n → ℝ) := {y | morseNorm n y ^ 2 ≤ B₀} with hS
  set O := (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} with hO
  have hOopen : IsOpen O := D.isOpen_modelBall p hp
  have hSsub : S ⊆ {y | morseNorm n y < D.rm p hp} := fun y hy =>
    lt_of_pow_lt_pow_left₀ 2 hrm0.le (lt_of_le_of_lt hy hB)
  have hSsub' : S ⊆ {y | morseNorm n y ≤ Real.sqrt B₀} := fun y hy =>
    MorseNormalChart.morseNorm_le_sqrt_of_sq_le hy
  have hSclosed : IsClosed S := isClosed_le (continuous_morseNorm.pow 2) continuous_const
  have hSK : IsCompact ((D.chart p hp).χ '' S) :=
    (D.chart p hp).isCompact_image_of_subset
      ((isCompact_morseNorm_le _).of_isClosed_subset hSclosed hSsub')
      (((Real.sqrt_lt' hrm0).2 hB).trans (D.rm_lt_R' p hp)) hSsub'
  have hKO : (D.chart p hp).χ '' S ⊆ O := image_mono hSsub
  have hOball := D.modelBall_subset_image_ball p hp
  have hbound : ∀ y : Fin n → ℝ,
      morseNormalForm (D.chart p hp).hk (f p) y ∈ Icc (f p + ε) (f p + η) →
      ‖ModelField.scaledNegativePart (D.chart p hp).hk y‖ ≤ 2 * ρ → y ∈ S := by
    intro y hy hJ
    change morseNorm n y ^ 2 ≤ B₀
    have := ModelField.morseNorm_sq_le_of_scaledNegativePart_le (D.chart p hp).hk hε (η := η)
      (by rw [ModelField.nf_sub_eq (D.chart p hp).hk (f p)]; linarith [hy.1])
      (by rw [ModelField.nf_sub_eq (D.chart p hp).hk (f p)]; linarith [hy.2]) hJ
    rw [hB₀]
    convert this using 2
    ring
  have hfDt : ∀ s ∈ Icc 0 (η - ε), f (Dt.flow s L) = f p + η - s := by
    intro s hs
    have := f_flow_eq_sub_of_levels hf (D := Dt) (x := L) (T := η - ε)
      (by rw [hfL]; exact ⟨by linarith, by linarith⟩)
      (by rw [hfL]; exact ⟨by linarith, by linarith⟩)
      (by
        intro y hy p' hp'
        rw [hfL, uIcc_of_ge (by linarith)] at hy
        exact hlev y ⟨by linarith [hy.1], by linarith [hy.2]⟩ p' hp')
      s (by rw [uIcc_of_le (by linarith)]; exact hs)
    rw [this, hfL]
  have hchart : ∀ s ∈ Icc 0 (η - ε), Dt.flow s L ∈ O →
      morseNormalForm (D.chart p hp).hk (f p) ((D.chart p hp).χ.symm (Dt.flow s L)) =
        f p + η - s ∧
      (D.chart p hp).r₀ / 2 ≤ morseNorm n ((D.chart p hp).χ.symm (Dt.flow s L)) ∧
      posPart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L)) ≠ 0 := by
    intro s hs hsO
    have h2 : morseNormalForm (D.chart p hp).hk (f p) ((D.chart p hp).χ.symm (Dt.flow s L)) =
        f p + η - s := by
      rw [← (D.chart p hp).f_eq_nf_symm (D.modelBall_subset_image_le p hp hsO), hfDt s hs]
    refine ⟨h2, ?_, ModelField.posPart_ne_zero_of_lt_nf (D.chart p hp).hk
      (by rw [h2]; linarith [hs.2])⟩
    by_contra hlt'
    have hlt := not_le.1 hlt'
    have hmem : Dt.flow s L ∈ D.smallBall p hp :=
      ⟨_, show morseNorm n ((D.chart p hp).χ.symm (Dt.flow s L)) < (D.chart p hp).r₀ by
        linarith [(D.chart p hp).hr₀], (D.chart p hp).symm_image_eq (hOball hsO)⟩
    exact hlev _ (by rw [hfDt s hs]; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩) p hp hmem
  have key : ∀ s', s' ≤ η - ε → 0 ≤ s' → (∀ u ∈ Icc 0 s', Dt.flow u L ∈ O) →
      ∀ s ∈ Icc 0 s',
        ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L)) -
          ModelField.levelCutoff (f p) η (morseNormalForm (D.chart p hp).hk (f p)
            ((D.chart p hp).χ.symm (Dt.flow s L))) • z =
          ModelField.scaledNegativePart (D.chart p hp).hk yL - z ∧
        ‖ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L))‖ < 2 * ρ := by
    intro s' hs'T hs'0 hODE
    have hI : ∀ t ∈ Icc 0 s', t ∈ Icc 0 (η - ε) := fun t ht => ⟨ht.1, ht.2.trans hs'T⟩
    have hγ : ∀ t ∈ Icc 0 s', HasDerivAt (fun s => (D.chart p hp).χ.symm (Dt.flow s L))
        (ModelField.modelField (D.chart p hp).k (D.chart p hp).r₀
            ((D.chart p hp).χ.symm (Dt.flow t L)) +
          ModelField.twist (D.chart p hp).hk (f p) η ρ z
            ((D.chart p hp).χ.symm (Dt.flow t L))) t :=
      fun t ht => hasDerivAt_symm_flow_twisted hf hη hρ hsupp hηrm hr₀η (hODE t ht)
    set g : ℝ → EuclideanSpace ℝ (Fin (D.chart p hp).k) := fun s =>
      ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L)) -
        ModelField.levelCutoff (f p) η (morseNormalForm (D.chart p hp).hk (f p)
          ((D.chart p hp).χ.symm (Dt.flow s L))) • z -
        (ModelField.scaledNegativePart (D.chart p hp).hk yL - z) with hg
    have hγc : ContinuousOn (fun s => (D.chart p hp).χ.symm (Dt.flow s L)) (Icc 0 s') :=
      HasDerivAt.continuousOn hγ
    have hJcont : ContinuousOn
        (fun s => ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L)))
        (Icc 0 s') :=
      (ModelField.continuous_scaledNegativePart _).comp_continuousOn hγc
    have hBcont : ContinuousOn (fun s => ModelField.levelCutoff (f p) η (morseNormalForm (D.chart p hp).hk
        (f p) ((D.chart p hp).χ.symm (Dt.flow s L)))) (Icc 0 s') :=
      ((ModelField.contDiff_levelCutoff (f p) η).continuous.comp
        (ModelField.contDiff_nf (D.chart p hp).hk (f p)).continuous).comp_continuousOn hγc
    have hgcont : ContinuousOn g (Icc 0 s') := fun x hx =>
      ((hJcont x hx).sub ((hBcont x hx).smul continuousWithinAt_const)).sub
        continuousWithinAt_const
    have hGclosed : IsClosed ({s | g s = 0} ∩ Icc 0 s') := by
      rw [inter_comm]
      exact hgcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hnormJ : ∀ s, g s = 0 →
        ‖ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L))‖ < 2 * ρ := by
      intro s hs
      have h0 := sub_eq_zero.1 hs
      set Bs := ModelField.levelCutoff (f p) η (morseNormalForm (D.chart p hp).hk (f p)
          ((D.chart p hp).χ.symm (Dt.flow s L))) with hBs
      have hJs : ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L)) =
          ModelField.scaledNegativePart (D.chart p hp).hk yL - (1 - Bs) • z := by
        calc ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L))
            = (ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L)) - Bs • z) +
                Bs • z := (sub_add_cancel _ _).symm
          _ = (ModelField.scaledNegativePart (D.chart p hp).hk yL - z) + Bs • z := by rw [h0]
          _ = ModelField.scaledNegativePart (D.chart p hp).hk yL - (1 - Bs) • z := by
            rw [sub_smul, one_smul, sub_sub_eq_add_sub, sub_add_eq_add_sub]
      have hB0 : 0 ≤ Bs := ModelField.levelCutoff_nonneg _ _ _
      have hB1 : Bs ≤ 1 := ModelField.levelCutoff_le_one _ _ _
      rw [hJs]
      calc ‖ModelField.scaledNegativePart (D.chart p hp).hk yL - (1 - Bs) • z‖
          ≤ ‖ModelField.scaledNegativePart (D.chart p hp).hk yL‖ + ‖(1 - Bs) • z‖ := norm_sub_le _ _
        _ = ‖ModelField.scaledNegativePart (D.chart p hp).hk yL‖ + (1 - Bs) * ‖z‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hB1])]
        _ < 2 * ρ := by
          have := mul_le_of_le_one_left (norm_nonneg z) (show 1 - Bs ≤ 1 by linarith only [hB0])
          linarith only [this, hsmall', hz]
    have hsubset : Icc 0 s' ⊆ {s | g s = 0} := by
      refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin hGclosed ?_ ?_
      · change g 0 = 0
        simp only [hg, flow_zero, hLsymm, hnfL, ModelField.levelCutoff_eq_one hη le_rfl, one_smul, sub_self]
      · rintro x ⟨hx, hxI⟩
        have hx0 : g x = 0 := hx
        have hxIcc : x ∈ Icc 0 s' := ⟨hxI.1, hxI.2.le⟩
        have hxlt := hnormJ x hx0
        have hIcc : Icc 0 s' ∈ 𝓝[>] x :=
          Filter.mem_of_superset (Icc_mem_nhdsGT hxI.2) (Icc_subset_Icc hxI.1 le_rfl)
        have hev1 : ∀ᶠ s in 𝓝[>] x,
            ‖ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow s L))‖ < 2 * ρ := by
          have h := ((hJcont.continuousWithinAt hxIcc).norm.tendsto).eventually
            (eventually_lt_nhds hxlt)
          exact h.filter_mono (nhdsWithin_le_of_mem hIcc)
        have hev2 : ∀ᶠ s in 𝓝[>] x, s ∈ Icc 0 s' := hIcc
        obtain ⟨u, hu, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hev1.and hev2)
        refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨u, hu, fun s hs => ?_⟩
        have hs' := hIoo hs
        change g s = 0
        have hxs : x ≤ s := hs.1.le
        have hd : ∀ r ∈ Ico x s, HasDerivWithinAt g 0 (Ici r) r := by
          intro r hr
          have hrI : r ∈ Icc 0 s' := ⟨hxI.1.trans hr.1, hr.2.le.trans hs'.2.2⟩
          have hαr : ‖ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.flow r L))‖ ≤
              2 * ρ := by
            rcases hr.1.lt_or_eq with h | h
            · exact (hIoo ⟨h, hr.2.trans hs.2⟩).1.le
            · rw [← h]; exact hxlt.le
          obtain ⟨-, hun, hpos⟩ := hchart r (hI r hrI) (hODE r hrI)
          have := ModelField.hasDerivAt_invariant (D.chart p hp).hk (c := f p) (ε := η) (ρ := ρ)
            (r₀ := (D.chart p hp).r₀) (z := z)
            (γ := fun s => (D.chart p hp).χ.symm (Dt.flow s L)) (D.chart p hp).hr₀ hη hρ
            (σ := 1) (t := r) ((hγ r hrI).congr_deriv (one_smul ℝ _).symm) hun hpos hαr
          exact (this.sub_const (ModelField.scaledNegativePart (D.chart p hp).hk yL - z)).hasDerivWithinAt
        have := constant_of_has_deriv_right_zero
          (hgcont.mono (Icc_subset_Icc hxIcc.1 hs'.2.2)) hd s (right_mem_Icc.2 hxs)
        rw [this, hx0]
    intro s hs
    exact ⟨sub_eq_zero.1 (hsubset hs), hnormJ s (hsubset hs)⟩
  have hJL2 : ‖ModelField.scaledNegativePart (D.chart p hp).hk yL‖ ≤ 2 * ρ := by linarith only [hsmall', hρ]
  have hyLS : yL ∈ S := hbound yL (by rw [hnfL]; exact ⟨by linarith only [hεη, hε], le_rfl⟩) hJL2
  have hQc : IsClosed {s : ℝ | Dt.flow s L ∈ (D.chart p hp).χ '' S} :=
    hSK.isClosed.preimage (Dt.continuous_flow_curve L)
  have hmain : Icc 0 (η - ε) ⊆ {s | Dt.flow s L ∈ (D.chart p hp).χ '' S} := by
    refine Icc_subset_of_isClosed_of_step hQc ?_ ?_
    · change Dt.flow 0 L ∈ (D.chart p hp).χ '' S
      rw [flow_zero, ← hyLL]
      exact ⟨yL, hyLS, rfl⟩
    · intro t ht hIcc
      have htO : Dt.flow t L ∈ O := hKO (hIcc (right_mem_Icc.2 ht.1))
      obtain ⟨δ, hδ, hδO⟩ := Dt.exists_Icc_flow_mem_open hOopen htO
      refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (t + δ) (η - ε), ?_, fun s hs => ?_⟩
      · change t < min (t + δ) (η - ε)
        exact lt_min (by linarith only [hδ]) ht.2
      change Dt.flow s L ∈ (D.chart p hp).χ '' S
      have hs0 : 0 ≤ s := ht.1.trans hs.1.le
      have hsT : s ≤ η - ε := hs.2.trans (min_le_right _ _)
      have hODE : ∀ u ∈ Icc 0 s, Dt.flow u L ∈ O := fun u hu => by
        rcases le_or_gt u t with h | h
        · exact hKO (hIcc ⟨hu.1, h⟩)
        · exact hδO u ⟨by linarith only [h, hδ], hu.2.trans (hs.2.trans (min_le_left _ _))⟩
      have hsI : s ∈ Icc 0 (η - ε) := ⟨hs0, hsT⟩
      have hsO := hODE s (right_mem_Icc.2 hs0)
      obtain ⟨-, h3⟩ := key s hsT hs0 hODE s (right_mem_Icc.2 hs0)
      obtain ⟨h2, -, -⟩ := hchart s hsI hsO
      exact (D.chart p hp).mem_image_of_symm_mem (hOball hsO)
        (hbound _ (by rw [h2]; exact ⟨by linarith only [hsT], by linarith only [hs0]⟩) h3.le)
  have hODEall : ∀ u ∈ Icc 0 (η - ε), Dt.flow u L ∈ O := fun u hu => hKO (hmain hu)
  have hTI : η - ε ∈ Icc 0 (η - ε) := right_mem_Icc.2 (by linarith only [hεη, hε])
  obtain ⟨h1, -⟩ := key (η - ε) le_rfl (by linarith only [hεη, hε]) hODEall (η - ε) hTI
  obtain ⟨h2, -, -⟩ := hchart (η - ε) hTI (hODEall _ hTI)
  rw [h2, ModelField.levelCutoff_eq_zero hη (by linarith only [hεη, hε]), zero_smul, sub_zero] at h1
  obtain ⟨yE, hyES, hyE⟩ := hmain hTI
  have hyE' : morseNorm n yE ^ 2 ≤ B₀ := hyES
  have hyER : morseNorm n yE < (D.chart p hp).R :=
    (lt_of_pow_lt_pow_left₀ 2 hrm0.le (lt_of_le_of_lt hyE' hB)).trans_le (D.hrm p hp).2
  refine ⟨⟨hw0, ?_⟩, ?_⟩
  · change Dt.landing p hq ε c ε w ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}
    rw [hTL, ← hyE]
    exact ⟨yE, hyER, rfl⟩
  · change ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (Dt.landing p hq ε c ε w)) = _
    rw [hTL, h1, hSeq]

theorem sardMap_twisted_zero (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {p : M} (hp : p ∈ crit) {η ρ : ℝ}
    {z : EuclideanSpace ℝ (Fin (D.chart p hp).k)} (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (hηrm : η ≤ D.rm p hp ^ 2)
    (hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η) {q : M} (hq : q ∈ crit) {ε c : ℝ} (hε : 0 < ε)
    (hεη : 8 * ε < η) (hr₀ε : (D.chart p hp).r₀ ^ 2 ≤ 8 * ε) (hz : ‖z‖ ≤ ρ)
    (hB : 2 * η + 4 * ρ ^ 2 / ε < D.rm p hp ^ 2) (hεq : 2 * ε ≤ (D.chart q hq).R ^ 2)
    (hr₀q : (D.chart q hq).r₀ ^ 2 < 2 * ε) (hηq : 2 * η < D.rm q hq ^ 2)
    (hc : f p + η < c) (hcq : c < f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp')
    {w : Fin (D.chart q hq).k → ℝ}
    (hw : w ∈ (twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η).sardDom p hq ε c ε hp)
    (hw0 : (twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η).sardMap p hq ε c ε hp w = 0) :
    w ∈ D.sardDom p hq η c η hp ∧ D.sardMap p hq η c η hp w = z := by
  have _ := hr₀q
  set Dt := twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η with hDt
  have hpa : a < f p := (D.f_mem_Ioo p hp).1
  have hqb : f q < b := (D.f_mem_Ioo q hq).2
  have hfpq : f p + ε < f q - η := by linarith
  obtain ⟨hw0', hwland⟩ := hw
  have hwne : w ≠ 0 := hw0'
  set y := (D.chart q hq).sphereParam ε w with hy
  set x := (D.chart q hq).χ y with hx
  have hyS : y ∈ (D.chart q hq).leftModelSphere ε := (D.chart q hq).sphereParam_mem_leftModelSphere hε.le hwne
  have hfx : f x = f q - ε := (D.chart q hq).f_chart_of_mem_leftModelSphere hεq hyS
  have hrmq := D.rm_pos q hq
  have hyv : posPart (D.chart q hq).hk y = 0 := hyS.1
  have hyu : ‖negPart (D.chart q hq).hk y‖ ^ 2 = 2 * ε := hyS.2
  have hu0 : negPart (D.chart q hq).hk y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hyu
    linarith
  obtain ⟨t', ht'0, hft', hstay, -⟩ := exists_exit_desc (D := D) hf hq hη (y := y)
    (by rw [hyv, norm_zero]; linarith) hu0
    (by rw [(D.chart q hq).nf_of_mem_leftModelSphere hyS]; linarith)
  have ht'ge : η - ε ≤ t' := by
    have := sub_le_f_flow (D := D) hf x ht'0
    rw [hfx, hft'] at this
    linarith
  have hball : ∀ s ∈ uIcc 0 (η - ε),
      D.flow s ((D.chart q hq).χ y) ∈ (D.chart q hq).χ '' {z | morseNorm n z < D.rm q hq} := by
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    refine image_mono (fun z hz => ?_) (hstay s ⟨hs.1, hs.2.trans ht'ge⟩)
    have hz' : morseNorm n z ^ 2 ≤ 2 * η + 2 * ‖posPart (D.chart q hq).hk y‖ ^ 2 := hz
    rw [hyv, norm_zero] at hz'
    exact lt_of_pow_lt_pow_left₀ 2 hrmq.le (by linarith)
  have hyrm : morseNorm n y < D.rm q hq := by
    apply lt_of_pow_lt_pow_left₀ 2 hrmq.le
    rw [(D.chart q hq).morseNorm_sq_of_mem_leftModelSphere hyS]
    linarith
  obtain ⟨l, hl0, -, -, hscale⟩ := CrossField.model_flow_scaling D hq hyrm hball
  have hlevq : f (D.flow (η - ε) x) = f q - η := by
    have := f_flow_eq_sub_of_levels hf (D := D) (x := x) (T := η - ε)
      (by rw [hfx]; exact ⟨by linarith, by linarith⟩)
      (by rw [hfx]; exact ⟨by linarith, by linarith⟩) (by
        intro y' hy'
        rw [hfx, uIcc_of_ge (by linarith)] at hy'
        exact hlev y' ⟨by linarith [hy'.1], by linarith [hy'.2]⟩) (η - ε) right_mem_uIcc
    rw [this, hfx]
    ring
  have hxO : D.flow (η - ε) x ∈ (D.chart q hq).χ '' {z | morseNorm n z < D.rm q hq} :=
    hball _ right_mem_uIcc
  have hxle : D.flow (η - ε) x ∈ (D.chart q hq).χ '' {z | morseNorm n z ≤ (D.chart q hq).R} :=
    image_mono (fun z (hz : morseNorm n z < D.rm q hq) => hz.le.trans (D.hrm q hq).2) hxO
  have hnf : morseNormalForm (D.chart q hq).hk (f q)
      (recombine (D.chart q hq).hk (l • negPart (D.chart q hq).hk y) (l⁻¹ • posPart (D.chart q hq).hk y)) = f q - η := by
    rw [← hscale, ← (D.chart q hq).f_eq_nf_symm hxle, hlevq]
  rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, ModelField.negPart_recombine, ModelField.posPart_recombine, hyv,
    smul_zero, norm_zero, norm_smul, mul_pow, hyu, Real.norm_eq_abs, sq_abs] at hnf
  have hl2 : (l * Real.sqrt (2 * ε)) ^ 2 = 2 * η := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    linarith
  have hlsq : l * Real.sqrt (2 * ε) = Real.sqrt (2 * η) := by
    rw [← hl2, Real.sqrt_sq (mul_nonneg hl0.le (Real.sqrt_nonneg _))]
  have hxη : D.flow (η - ε) x = (D.chart q hq).χ ((D.chart q hq).sphereParam η w) := by
    have hχ : (D.chart q hq).χ ((D.chart q hq).χ.symm (D.flow (η - ε) x)) = D.flow (η - ε) x :=
      (D.chart q hq).symm_image_eq (D.modelBall_subset_image_ball q hq hxO)
    rw [← hχ, hscale]
    congr 1
    have hyneg : negPart (D.chart q hq).hk y = (Real.sqrt (2 * ε) / ‖(D.chart q hq).toE w‖) • (D.chart q hq).toE w :=
      (D.chart q hq).negPart_sphereParam ε w
    rw [hyv, smul_zero, hyneg, smul_smul, MorseNormalChart.sphereParam, ← hlsq, mul_div_assoc]
  set yc := D.flow (f q - ε - c) x with hyc
  have hfyc : c ≤ f yc := by
    have := sub_le_f_flow (D := D) hf x (t := f q - ε - c) (by linarith)
    rw [hfx] at this
    linarith
  have hland_eq : D.landing p hq η c η w = D.flow (c - (f p + η)) yc := by
    change D.flow (c - (f p + η)) (D.flow (f q - η - c) ((D.chart q hq).χ ((D.chart q hq).sphereParam η w))) = _
    rw [← hxη, flow_flow (D := D) x (η - ε) (f q - η - c),
      show η - ε + (f q - η - c) = f q - ε - c by ring]
  have hagree1 : Dt.flow (f q - ε - c) x = yc := by
    refine flow_eq_of_agree (D₁ := D) (isOpen_above hf.continuous (f p + η))
      (fun x hx => (twistedV_eq_of_level_ge hη hρ hsupp (le_of_lt hx)).symm) (fun s hs => ?_) _
      (right_mem_Icc.2 (by linarith))
    change f p + η < f (D.flow s x)
    have := sub_le_f_flow (D := D) hf x hs.1
    rw [hfx] at this
    linarith [hs.2]
  set xη := D.flow (c - (f p + η)) yc with hxηdef
  have hagree2 : Dt.flow (c - (f p + η)) yc = xη := by
    refine flow_eq_of_agree (D₁ := D) (isOpen_above hf.continuous (f p + η))
      (fun x hx => (twistedV_eq_of_level_ge hη hρ hsupp (le_of_lt hx)).symm) (fun s hs => ?_) _
      (right_mem_Icc.2 (by linarith))
    change f p + η < f (D.flow s yc)
    have := sub_le_f_flow (D := D) hf yc hs.1
    linarith [hs.2]
  have hDtland : Dt.landing p hq ε c ε w = Dt.flow (η - ε) xη := by
    change Dt.flow (c - (f p + ε)) (Dt.flow (f q - ε - c) x) = _
    rw [hagree1, ← hagree2, flow_flow]
    congr 1
    ring
  obtain ⟨y₀, hy₀R, hy₀eq⟩ := hwland
  have hy₀R' : morseNorm n y₀ < (D.chart p hp).R := hy₀R
  have hsymm₀ : (D.chart p hp).χ.symm (Dt.landing p hq ε c ε w) = y₀ := by
    rw [← hy₀eq]
    exact (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₀ hy₀R'.le)
  have hJ0 : ModelField.scaledNegativePart (D.chart p hp).hk y₀ = 0 := by
    rw [← hsymm₀]
    exact hw0
  have hfland : f (Dt.landing p hq ε c ε w) = f p + ε :=
    f_landing (D := Dt) hp hf hε hε hεq (by linarith) hcq.le hlev hwne
  have hnf0 : morseNormalForm (D.chart p hp).hk (f p) y₀ = f p + ε := by
    rw [← (D.chart p hp).hnorm y₀ hy₀R'.le]
    rw [← hfland, ← hy₀eq]
    rfl
  have hB' : 2 * η + ρ ^ 2 / ε < D.rm p hp ^ 2 := by
    have : ρ ^ 2 / ε ≤ 4 * ρ ^ 2 / ε := by
      apply div_le_div_of_nonneg_right _ hε.le
      nlinarith [sq_nonneg ρ]
    linarith
  obtain ⟨h1, -, h3⟩ := twisted_ascent_end hf hη hρ hsupp hηrm hr₀η hε (by linarith) hr₀ε hz hB'
    hJ0 hnf0
  have hback : Dt.flow (-(η - ε)) ((D.chart p hp).χ y₀) = xη := by
    have : (D.chart p hp).χ y₀ = Dt.landing p hq ε c ε w := hy₀eq
    rw [this, hDtland, flow_neg_flow]
  rw [hback] at h1 h3
  obtain ⟨y₁, hy₁, hy₁eq⟩ := h1
  have hy₁R : morseNorm n y₁ < (D.chart p hp).R := by
    have := lt_of_pow_lt_pow_left₀ 2 (D.rm_pos p hp).le
      (lt_of_le_of_lt (show morseNorm n y₁ ^ 2 ≤ _ from hy₁) hB')
    exact this.trans_le (D.hrm p hp).2
  refine ⟨⟨hwne, ?_⟩, ?_⟩
  · change D.landing p hq η c η w ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}
    rw [hland_eq]
    exact ⟨y₁, hy₁R, hy₁eq⟩
  · change ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.landing p hq η c η w)) = z
    rw [hland_eq]
    exact h3

theorem sardAgree_twisted_of_ne (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {p : M} (hp : p ∈ crit) {η ρ : ℝ}
    {z : EuclideanSpace ℝ (Fin (D.chart p hp).k)} (hη : 0 < η) (hρ : 0 < ρ)
    (hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2) (hηrm : η ≤ D.rm p hp ^ 2)
    (hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η) {p' q : M} (hp' : p' ∈ crit) (hq : q ∈ crit)
    (hp'p : p' ≠ p) (hlevel : f p' = f p) {ε : ℝ} (hε : 0 < ε) (hεη : 8 * ε < η)
    (hz : ‖z‖ ≤ ρ) (hB : 2 * η + 9 * ρ ^ 2 / ε < D.rm p hp ^ 2)
    (hv : D.sardValid ε p' hq hp') (c c' : ℝ) :
    D.sardAgree (twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η) ε ε c c' p' hq hp' := by
  have _ := hz
  obtain ⟨-, -, -, -, hrmq, hlev', hfree⟩ := hv
  have hpa : a < f p' := (D.f_mem_Ioo p' hp').1
  have hqb : f q < b := (D.f_mem_Ioo q hq).2
  have hrmq0 := D.rm_pos q hq
  have hrmqR := (D.hrm q hq).2
  have hεR : 2 * ε ≤ (D.chart q hq).R ^ 2 := by nlinarith
  have hDtV : (twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η).V =
      twistedV (D := D) p hp η ρ z := rfl
  have hDtchart : ∀ x hx, (twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η).chart x hx =
      D.chart x hx := fun _ _ => rfl
  have hDtsmall : ∀ x hx, (twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η).smallBall x hx =
      D.smallBall x hx := fun _ _ => rfl
  generalize twisted (D := D) (z := z) hf hη hρ hsupp hηrm hr₀η = Dt at hDtV hDtchart hDtsmall ⊢
  set Kmod : Set (Fin n → ℝ) := {y | morseNorm n y ≤ twistR η ρ} ∩
    ModelField.twistSupp (D.chart p hp).hk (f p) η ρ with hKmod
  have hYK : ∀ y ∉ Kmod, twistY (D := D) p hp η ρ z y = 0 := by
    intro y hy
    by_cases h1 : morseNorm n y ≤ twistR η ρ
    · have h2 : y ∉ ModelField.twistSupp (D.chart p hp).hk (f p) η ρ := fun h => hy ⟨h1, h⟩
      by_contra h3
      exact h2 (ModelField.support_twist_subset (D.chart p hp).hk hη hρ z
        (Function.mem_support.2 h3))
    · exact twistY_eq_zero_of_notMem hη hρ h1
  have htwR : twistR η ρ < (D.chart p hp).R' := (twistR_lt_R hsupp).trans (D.chart p hp).hRR'
  have hKmodc : IsCompact Kmod :=
    (isCompact_morseNorm_le _).of_isClosed_subset
      ((isClosed_le continuous_morseNorm continuous_const).inter
        (ModelField.isClosed_twistSupp _ _ _ _)) inter_subset_left
  have hKc : IsCompact ((D.chart p hp).χ '' Kmod) :=
    (D.chart p hp).isCompact_image_of_subset hKmodc htwR inter_subset_left
  have hUo : IsOpen ((D.chart p hp).χ '' Kmod)ᶜ := hKc.isClosed.isOpen_compl
  have hVU : ∀ x ∈ ((D.chart p hp).χ '' Kmod)ᶜ, D.V x = Dt.V x := by
    intro x hx
    rw [hDtV]
    exact (addPush_of_notMem_image p hp _ hYK hx).symm
  set B₀ : ℝ := 2 * η + 9 * ρ ^ 2 / ε with hB₀
  set S : Set (Fin n → ℝ) := {y | morseNorm n y ^ 2 ≤ B₀} with hS
  set O := (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} with hO
  have hOopen : IsOpen O := D.isOpen_modelBall p hp
  have hrm := D.rm_pos p hp
  have hrmR' := D.rm_lt_R' p hp
  have hSsub : S ⊆ {y | morseNorm n y < D.rm p hp} := fun y hy =>
    lt_of_pow_lt_pow_left₀ 2 hrm.le (lt_of_le_of_lt hy hB)
  have hSsub' : S ⊆ {y | morseNorm n y ≤ Real.sqrt B₀} := fun y hy =>
    MorseNormalChart.morseNorm_le_sqrt_of_sq_le hy
  have hSclosed : IsClosed S := isClosed_le (continuous_morseNorm.pow 2) continuous_const
  have hSK : IsCompact ((D.chart p hp).χ '' S) :=
    (D.chart p hp).isCompact_image_of_subset
      ((isCompact_morseNorm_le _).of_isClosed_subset hSclosed hSsub')
      (((Real.sqrt_lt' hrm).2 hB).trans hrmR') hSsub'
  have hKO : (D.chart p hp).χ '' S ⊆ O := image_mono hSsub
  have hOball := D.modelBall_subset_image_ball p hp
  have hOle := D.modelBall_subset_image_le p hp
  have hbound : ∀ y : Fin n → ℝ, f p + ε ≤ morseNormalForm (D.chart p hp).hk (f p) y →
      morseNormalForm (D.chart p hp).hk (f p) y ≤ f p + η →
      ‖ModelField.scaledNegativePart (D.chart p hp).hk y‖ ≤ 3 * ρ → y ∈ S := by
    intro y h1 h2 h3
    change morseNorm n y ^ 2 ≤ B₀
    have := ModelField.morseNorm_sq_le_of_scaledNegativePart_le (D.chart p hp).hk (η := η) hε
      (by rw [ModelField.nf_sub_eq (D.chart p hp).hk (f p)]; linarith)
      (by rw [ModelField.nf_sub_eq (D.chart p hp).hk (f p)]; linarith) h3
    have e : (3 * ρ) ^ 2 / ε = 9 * ρ ^ 2 / ε := by ring
    rw [hB₀]; linarith
  have starD : ∀ y₁ ∈ Kmod, ∀ τ : ℝ, 0 ≤ τ →
      morseNormalForm (D.chart p hp).hk (f p) y₁ - τ = f p + ε →
      (∀ s ∈ Icc 0 τ, f (D.flow s ((D.chart p hp).χ y₁)) = f ((D.chart p hp).χ y₁) - s) →
      D.flow τ ((D.chart p hp).χ y₁) ∈ (D.chart p hp).χ '' S := by
    intro y₁ hy₁ τ hτ hnfτ hunit
    obtain ⟨hy₁R, hy₁a, hy₁b, hy₁J⟩ := hy₁
    have hy₁R' : morseNorm n y₁ ≤ (D.chart p hp).R := hy₁R.trans (twistR_lt_R hsupp).le
    have hfx₀ : f ((D.chart p hp).χ y₁) = morseNormalForm (D.chart p hp).hk (f p) y₁ :=
      (D.chart p hp).hnorm y₁ hy₁R'
    have hy₁S : y₁ ∈ S := hbound y₁ (by linarith) hy₁b hy₁J
    have hγ0 : (D.chart p hp).χ.symm (D.flow 0 ((D.chart p hp).χ y₁)) = y₁ := by
      rw [flow_zero, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₁ hy₁R')]
    have hQc : IsClosed {s : ℝ | D.flow s ((D.chart p hp).χ y₁) ∈ (D.chart p hp).χ '' S} :=
      hSK.isClosed.preimage (D.continuous_flow_curve _)
    have hmain : Icc 0 τ ⊆ {s : ℝ | D.flow s ((D.chart p hp).χ y₁) ∈ (D.chart p hp).χ '' S} := by
      refine Icc_subset_of_isClosed_of_step hQc ?_ ?_
      · change D.flow 0 ((D.chart p hp).χ y₁) ∈ (D.chart p hp).χ '' S
        rw [flow_zero]; exact ⟨y₁, hy₁S, rfl⟩
      · intro t ht hIcc
        have htO : D.flow t ((D.chart p hp).χ y₁) ∈ O := hKO (hIcc (right_mem_Icc.2 ht.1))
        obtain ⟨δ, hδ, hδO⟩ := D.exists_Icc_flow_mem_open hOopen htO
        refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (t + δ) τ, ?_, fun s hs => ?_⟩
        · change t < min (t + δ) τ
          exact lt_min (by linarith) ht.2
        change D.flow s ((D.chart p hp).χ y₁) ∈ (D.chart p hp).χ '' S
        have hs0 : 0 ≤ s := ht.1.trans hs.1.le
        have hsτ : s ≤ τ := hs.2.trans (min_le_right _ _)
        have hODE : ∀ u ∈ Icc 0 s, D.flow u ((D.chart p hp).χ y₁) ∈ O := fun u hu => by
          rcases le_or_gt u t with h | h
          · exact hKO (hIcc ⟨hu.1, h⟩)
          · exact hδO u ⟨by linarith, hu.2.trans (hs.2.trans (min_le_left _ _))⟩
        have hγ := hasDerivAt_symm_flow_Icc hp hODE
        have hprod := ModelField.normSq_negPart_mul_posPart_const (D.chart p hp).hk hγ s
          (right_mem_Icc.2 hs0)
        rw [hγ0] at hprod
        have hsO := hODE s (right_mem_Icc.2 hs0)
        have hnf : f (D.flow s ((D.chart p hp).χ y₁)) = morseNormalForm (D.chart p hp).hk (f p)
            ((D.chart p hp).χ.symm (D.flow s ((D.chart p hp).χ y₁))) :=
          (D.chart p hp).f_eq_nf_symm (hOle hsO)
        rw [hunit s ⟨hs0, hsτ⟩, hfx₀] at hnf
        refine (D.chart p hp).mem_image_of_symm_mem (hOball hsO)
          (hbound _ (by linarith) (by linarith) ?_)
        rw [ModelField.norm_scaledNegativePart]
        rw [ModelField.norm_scaledNegativePart] at hy₁J
        have h3 := pow_le_pow_left₀ (by positivity) hy₁J 2
        have hP2 : (‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm
              (D.flow s ((D.chart p hp).χ y₁)))‖ *
            ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm
              (D.flow s ((D.chart p hp).χ y₁)))‖) ^ 2 ≤ (3 * ρ) ^ 2 := by
          have e1 : (‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm
                (D.flow s ((D.chart p hp).χ y₁)))‖ *
              ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm
                (D.flow s ((D.chart p hp).χ y₁)))‖) ^ 2 =
              ‖negPart (D.chart p hp).hk ((D.chart p hp).χ.symm
                (D.flow s ((D.chart p hp).χ y₁)))‖ ^ 2 *
              ‖posPart (D.chart p hp).hk ((D.chart p hp).χ.symm
                (D.flow s ((D.chart p hp).χ y₁)))‖ ^ 2 := by ring
          have e0 : (‖posPart (D.chart p hp).hk y₁‖ * ‖negPart (D.chart p hp).hk y₁‖) ^ 2 =
              ‖negPart (D.chart p hp).hk y₁‖ ^ 2 * ‖posPart (D.chart p hp).hk y₁‖ ^ 2 := by ring
          rw [e1, hprod, ← e0]
          exact h3
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hP2
    exact hmain ⟨hτ, le_rfl⟩
  set T : ℝ := f q - f p' - 2 * ε with hT
  have hTnn : 0 ≤ T := by linarith
  have hunitAll : ∀ E : GradientLikeStrip I f a b crit,
      (∀ w hw, E.smallBall w hw = D.smallBall w hw) → ∀ x : M, f x = f q - ε →
      ∀ s ∈ Icc 0 T, f (E.flow s x) = f x - s := by
    intro E hEs x hfx s hs
    refine f_flow_eq_sub_of_levels hf (D := E) (x := x) (T := T) ?_ ?_ ?_ s
      (by rw [uIcc_of_le hTnn]; exact hs)
    · rw [hfx]; constructor <;> linarith
    · rw [hfx]; constructor <;> linarith
    · intro w hw r hr
      rw [hEs]
      rw [hfx, uIcc_of_ge (by linarith)] at hw
      exact hfree w ⟨by linarith [hw.1], hw.2⟩ r hr
  have star : ∀ E : GradientLikeStrip I f a b crit,
      (∀ x ∈ ((D.chart p hp).χ '' Kmod)ᶜ, E.V x = D.V x) →
      ∀ x : M, f x = f q - ε → (∀ s ∈ Icc 0 T, f (E.flow s x) = f x - s) →
      E.flow T x ∈ (D.chart p' hp').χ '' {w | morseNorm n w < (D.chart p' hp').R} →
      ∀ s ∈ Ico 0 T, E.flow s x ∈ ((D.chart p hp).χ '' Kmod)ᶜ := by
    intro E hEV x hfx hunitE hend s₀ hs₀
    by_contra hK
    rw [mem_compl_iff, not_not] at hK
    set A : Set ℝ := Icc 0 T ∩ {s | E.flow s x ∈ (D.chart p hp).χ '' Kmod} with hA
    have hAc : IsClosed A :=
      isClosed_Icc.inter (hKc.isClosed.preimage (E.continuous_flow_curve x))
    have hAne : A.Nonempty := ⟨s₀, ⟨hs₀.1, hs₀.2.le⟩, hK⟩
    have hAbdd : BddAbove A := ⟨T, fun s hs => hs.1.2⟩
    have hs₁A : sSup A ∈ A := hAc.csSup_mem hAne hAbdd
    have hs₁le : ∀ s ∈ A, s ≤ sSup A := fun s hs => le_csSup hAbdd hs
    set s₁ := sSup A with hs₁
    obtain ⟨⟨hs₁0, hs₁T⟩, y₁, hy₁, hy₁x⟩ := hs₁A
    have hy₁R' : morseNorm n y₁ ≤ (D.chart p hp).R := hy₁.1.trans (twistR_lt_R hsupp).le
    have hf₁ : f ((D.chart p hp).χ y₁) = morseNormalForm (D.chart p hp).hk (f p) y₁ :=
      (D.chart p hp).hnorm y₁ hy₁R'
    have hf₁' : f (E.flow s₁ x) = f x - s₁ := hunitE s₁ ⟨hs₁0, hs₁T⟩
    rw [← hy₁x, hf₁] at hf₁'
    have hnf₁ : f p + η / 2 ≤ morseNormalForm (D.chart p hp).hk (f p) y₁ := hy₁.2.1
    have hs₁T' : s₁ < T := by linarith
    have hC : IsClosed {s : ℝ | D.flow (T - s) (E.flow s x) = E.flow T x} := by
      refine isClosed_eq ?_ continuous_const
      exact D.continuous_flow_joint.comp
        ((continuous_const.sub continuous_id).prodMk (E.continuous_flow_curve x))
    have hIoc : Ioc s₁ T ⊆ {s : ℝ | D.flow (T - s) (E.flow s x) = E.flow T x} := by
      intro s hs
      change D.flow (T - s) (E.flow s x) = E.flow T x
      have hmem : ∀ u ∈ Ico 0 (T - s), E.flow u (E.flow s x) ∈ ((D.chart p hp).χ '' Kmod)ᶜ := by
        intro u hu
        rw [flow_flow]
        intro hmemK
        have := hs₁le (s + u) ⟨⟨by linarith [hs.1, hu.1], by linarith [hu.2]⟩, hmemK⟩
        linarith [hs.1, hu.1]
      have := flow_eq_of_agree (D₁ := E) (D₂ := D) hUo hEV hmem (T - s)
        ⟨by linarith [hs.2], le_rfl⟩
      rw [this, flow_flow]
      congr 1
      ring
    have hs₁C : s₁ ∈ {s : ℝ | D.flow (T - s) (E.flow s x) = E.flow T x} := by
      have h := closure_mono hIoc (show s₁ ∈ closure (Ioc s₁ T) by
        rw [closure_Ioc hs₁T'.ne]; exact ⟨le_rfl, hs₁T'.le⟩)
      rwa [hC.closure_eq] at h
    have hs₁C' : D.flow (T - s₁) ((D.chart p hp).χ y₁) = E.flow T x := by
      rw [hy₁x]; exact hs₁C
    have hunitD : ∀ s ∈ Icc 0 (T - s₁),
        f (D.flow s ((D.chart p hp).χ y₁)) = f ((D.chart p hp).χ y₁) - s := by
      have h := f_flow_eq_sub_of_levels hf (D := D) (x := (D.chart p hp).χ y₁) (T := T - s₁)
        ?_ ?_ ?_
      · intro s hs
        exact h s (by rw [uIcc_of_le (by linarith)]; exact hs)
      · rw [hf₁]; constructor <;> linarith
      · rw [hf₁]; constructor <;> linarith
      · intro w hw
        rw [hf₁, uIcc_of_ge (by linarith)] at hw
        exact hfree w ⟨by linarith [hw.1], by linarith [hw.2]⟩
    have hland := starD y₁ hy₁ (T - s₁) (by linarith) (by linarith) hunitD
    rw [hs₁C'] at hland
    have h1 : E.flow T x ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' :=
      hOball (hKO hland)
    have h2 : E.flow T x ∈ (D.chart p' hp').χ '' Metric.ball 0 (D.chart p' hp').R' :=
      image_mono ((D.chart p' hp').lt_subset_ball (D.chart p' hp').hRR'.le) hend
    exact (D.disjoint p' hp' p hp hp'p).notMem_of_mem_left h2 h1
  refine sardAgree_of_flow_agree D Dt hDtchart hp' hq hε hεR ?_ c c'
  intro y hy hor
  have hfx : f ((D.chart q hq).χ y) = f q - ε :=
    (D.chart q hq).f_chart_of_mem_leftModelSphere hεR hy
  have hDtU : ∀ x ∈ ((D.chart p hp).χ '' Kmod)ᶜ, Dt.V x = D.V x := fun x hx => (hVU x hx).symm
  rcases hor with h | h
  · have hmem := star D (fun _ _ => rfl) _ hfx (hunitAll D (fun _ _ => rfl) _ hfx) h
    exact flow_eq_of_agree (D₁ := D) (D₂ := Dt) hUo hVU hmem T ⟨hTnn, le_rfl⟩
  · have hmem := star Dt hDtU _ hfx (hunitAll Dt hDtsmall _ hfx) h
    exact (flow_eq_of_agree (D₁ := Dt) (D₂ := D) hUo hDtU hmem T ⟨hTnn, le_rfl⟩).symm

end GradientLikeStrip

namespace BlockConfig

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {ℓ : ℕ}

theorem exists_twist_row (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ) {p : M}
    (hp : p ∈ B.lowerIndexCriticalPoints) :
    ∃ B' : BlockConfig I f a b ℓ, B'.crit = B.crit ∧ (∀ q ∈ B.upperIndexCriticalPoints, B'.pairTransverse p q) ∧
      (∀ p' ∈ B.lowerIndexCriticalPoints, p' ≠ p → ∀ q ∈ B.upperIndexCriticalPoints, (B'.pairTransverse p' q ↔ B.pairTransverse p' q) ∧
        B'.count p' q = B.count p' q ∧ B'.zerosCard p' q = B.zerosCard p' q) ∧
      B'.c = B.c ∧ B'.α = B.α ∧ B'.β = B.β ∧ B'.ε ≤ B.ε ∧
      (∀ x (hx : x ∈ B.crit) (hx' : x ∈ B'.crit), (B'.D.chart x hx').χ = (B.D.chart x hx).χ ∧
        (B'.D.chart x hx').k = (B.D.chart x hx).k) ∧
      (∀ q ∈ B.upperIndexCriticalPoints, ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
        B'.D.leftSphereMap q (ℓ + 1) B'.ε B.c y = B.D.leftSphereMap q (ℓ + 1) B.ε B.c y) ∧
      ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ z, f z ≤ B.α → B'.D.V z = φ z • B.D.V z := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hpidx : morseIndex I f p = ℓ := (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hfp : f p = B.α := B.hP p hpc hpidx
  have hη : 0 < B.ε := B.hε
  obtain ⟨B₁, hcrit, hα₁, hβ₁, hc₁, hε₁eq, hch, ⟨φ, hφc, hφb, hφV⟩, -, -, -, hsph, hpair⟩ :=
    exists_shrink hf B (ε₁ := B.ε / 16) (ρ := B.D.rm p hpc) (by positivity) (by linarith)
      (B.D.rm_pos p hpc) (by have := B.hrm p hpc; linarith)
  have hp₁ : p ∈ B₁.crit := hcrit ▸ hpc
  have hε₁ : 0 < B₁.ε := B₁.hε
  have hrm₁ : ∀ x (hx₁ : x ∈ B₁.crit), 8 * B.ε < B₁.D.rm x hx₁ ^ 2 := by
    intro x hx₁
    have hx : x ∈ B.crit := hcrit ▸ hx₁
    have h := (hch x hx).2.2.2.2
    rw [show B₁.D.rm x hx₁ = B₁.D.rm x (hcrit ▸ hx) from rfl, h]
    rcases min_cases (B.D.rm p hpc) (B.D.rm x hx) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact B.hrm p hpc
    · rw [h1]; exact B.hrm x hx
  have hR₁ : ∀ x (hx₁ : x ∈ B₁.crit), 8 * B.ε < (B₁.D.chart x hx₁).R ^ 2 := by
    intro x hx₁
    have h1 := hrm₁ x hx₁
    have h2 := (B₁.D.hrm x hx₁).2
    have h3 := B₁.D.rm_pos x hx₁
    nlinarith
  have hρ : 0 < B.ε / 32 := by positivity
  have hsupp : 2 * B.ε + 18 * (B.ε / 32) ^ 2 / B.ε < (B₁.D.chart p hp₁).R ^ 2 := by
    have h1 : 18 * (B.ε / 32) ^ 2 / B.ε = 18 * B.ε / 1024 := by field_simp; ring
    rw [h1]; linarith [hR₁ p hp₁]
  have hηrm : B.ε ≤ B₁.D.rm p hp₁ ^ 2 := by linarith [hrm₁ p hp₁]
  have hr₀η : 4 * (B₁.D.chart p hp₁).r₀ ^ 2 < B.ε := by
    have := B₁.hr₀ p hp₁; rw [hε₁eq] at this; linarith
  have hB9 : 2 * B.ε + 9 * (B.ε / 32) ^ 2 / B₁.ε < B₁.D.rm p hp₁ ^ 2 := by
    have h1 : 9 * (B.ε / 32) ^ 2 / B₁.ε = 9 * B.ε / 64 := by rw [hε₁eq]; field_simp; ring
    rw [h1]; linarith [hrm₁ p hp₁]
  have hB4 : 2 * B.ε + 4 * (B.ε / 32) ^ 2 / B₁.ε < B₁.D.rm p hp₁ ^ 2 := by
    have h1 : 4 * (B.ε / 32) ^ 2 / B₁.ε = B.ε / 16 := by rw [hε₁eq]; field_simp; ring
    rw [h1]; linarith [hrm₁ p hp₁]
  have hεη : 8 * B₁.ε < B.ε := by rw [hε₁eq]; linarith
  have hr₀ε : (B₁.D.chart p hp₁).r₀ ^ 2 ≤ 8 * B₁.ε := by have := B₁.hr₀ p hp₁; linarith
  have hfp₁ : f p = B₁.α := by rw [hα₁]; exact hfp
  have hQc : ∀ q ∈ B.upperIndexCriticalPoints, q ∈ B₁.crit := fun q hq => hcrit ▸ (B.mem_upperIndexCriticalPoints.1 hq).1
  have hfq : ∀ q ∈ B.upperIndexCriticalPoints, f q = B₁.β := fun q hq => by
    rw [hβ₁]; exact B.hQ q (B.mem_upperIndexCriticalPoints.1 hq).1 (B.mem_upperIndexCriticalPoints.1 hq).2
  have hlev₁ : ∀ q ∈ B.upperIndexCriticalPoints, ∀ y, f y ∈ Icc (f p + B₁.ε) (f q - B₁.ε) →
      ∀ p' hp', y ∉ B₁.D.smallBall p' hp' := by
    intro q hq y hy
    rw [hfp₁, hfq q hq] at hy
    exact B₁.hlev y hy
  have hlevη : ∀ q ∈ B.upperIndexCriticalPoints, ∀ y, f y ∈ Icc (f p + B.ε) (f q - B.ε) →
      ∀ p' hp', y ∉ B₁.D.smallBall p' hp' := by
    intro q hq y hy
    exact hlev₁ q hq y ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hηc : f p + B.ε < B₁.c := by rw [hfp, hc₁]; exact B.hαc
  have hcqη : ∀ q ∈ B.upperIndexCriticalPoints, B₁.c < f q - B.ε := fun q hq => by
    rw [hc₁, B.hQ q (B.mem_upperIndexCriticalPoints.1 hq).1 (B.mem_upperIndexCriticalPoints.1 hq).2]; exact B.hcβ
  have hcq₁ : ∀ q ∈ B.upperIndexCriticalPoints, B₁.c < f q - B₁.ε := fun q hq => by
    rw [hfq q hq]; exact B₁.hcβ
  have hkq : ∀ q (hq : q ∈ B.upperIndexCriticalPoints),
      (B₁.D.chart p hp₁).k + 1 = (B₁.D.chart q (hQc q hq)).k := by
    intro q hq
    rw [← (B₁.D.chart p hp₁).hkidx, ← (B₁.D.chart q (hQc q hq)).hkidx, hpidx,
      (B.mem_upperIndexCriticalPoints.1 hq).2]
  let e : ∀ i : {q // q ∈ B.upperIndexCriticalPoints}, (Fin ((B₁.D.chart p hp₁).k + 1) → ℝ) ≃L[ℝ]
      (Fin (B₁.D.chart i.1 (hQc i.1 i.2)).k → ℝ) := fun i =>
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ) (finCongr (hkq i.1 i.2))
  let S : {q // q ∈ B.upperIndexCriticalPoints} → (Fin ((B₁.D.chart p hp₁).k + 1) → ℝ) →
      EuclideanSpace ℝ (Fin (B₁.D.chart p hp₁).k) := fun i w =>
    B₁.D.sardMap p (hQc i.1 i.2) B.ε B₁.c B.ε hp₁ (e i w)
  let U : {q // q ∈ B.upperIndexCriticalPoints} → Set (Fin ((B₁.D.chart p hp₁).k + 1) → ℝ) := fun i =>
    (e i) ⁻¹' B₁.D.sardDom p (hQc i.1 i.2) B.ε B₁.c B.ε hp₁
  have hRq : ∀ q (hq : q ∈ B.upperIndexCriticalPoints), 2 * B.ε ≤ (B₁.D.chart q (hQc q hq)).R ^ 2 := fun q hq => by
    linarith [hR₁ q (hQc q hq)]
  have hopen : ∀ q (hq : q ∈ B.upperIndexCriticalPoints), IsOpen (B₁.D.sardDom p (hQc q hq) B.ε B₁.c B.ε hp₁) :=
    fun q hq => GradientLikeStrip.isOpen_sardDom hη.le (hRq q hq)
  have hdiff : ∀ q (hq : q ∈ B.upperIndexCriticalPoints), DifferentiableOn ℝ
      (B₁.D.sardMap p (hQc q hq) B.ε B₁.c B.ε hp₁) (B₁.D.sardDom p (hQc q hq) B.ε B₁.c B.ε hp₁) :=
    fun q hq => GradientLikeStrip.differentiableOn_sardMap hfs hη hη (hRq q hq) hηc.le
      (hcqη q hq).le (hlevη q hq)
  obtain ⟨z, hzρ, hreg⟩ := SardData.exists_small_regular_value (k := (B₁.D.chart p hp₁).k + 1)
    (l := (B₁.D.chart p hp₁).k) rfl (Finset.univ : Finset {q // q ∈ B.upperIndexCriticalPoints}) S U
    (fun i _ => (hopen i.1 i.2).preimage (e i).continuous)
    (fun i _ => by
      refine ⟨fun w hw h0 => hw.1 (by rw [h0, map_zero]), fun w hw t ht => ?_⟩
      have hw0 : e i w ≠ 0 := hw.1
      have hland := B₁.D.landing_smul p (hQc i.1 i.2) B.ε B₁.c B.ε ht hw0
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change e i (t • w) ≠ 0
        rw [map_smul]; exact smul_ne_zero ht.ne' hw0
      · change B₁.D.landing p (hQc i.1 i.2) B.ε B₁.c B.ε (e i (t • w)) ∈
          (B₁.D.chart p hp₁).χ '' {y | morseNorm n y < (B₁.D.chart p hp₁).R}
        rw [map_smul, hland]; exact hw.2
      · change ModelField.scaledNegativePart _ ((B₁.D.chart p hp₁).χ.symm
            (B₁.D.landing p (hQc i.1 i.2) B.ε B₁.c B.ε (e i (t • w)))) =
          ModelField.scaledNegativePart _ ((B₁.D.chart p hp₁).χ.symm
            (B₁.D.landing p (hQc i.1 i.2) B.ε B₁.c B.ε (e i w)))
        rw [map_smul, hland])
    (fun i _ => (hdiff i.1 i.2).comp (e i).differentiable.differentiableOn (fun w hw => hw)) hρ
  let Dt := GradientLikeStrip.twisted (D := B₁.D) (p := p) (hp := hp₁) (z := z) hfs hη hρ hsupp
    hηrm hr₀η
  have hrmDt : ∀ x hx, 8 * B₁.ε < Dt.rm x hx ^ 2 := by
    intro x hx
    rcases eq_or_ne x p with rfl | hxp
    · have h := GradientLikeStrip.twisted_rm_self (D := B₁.D) (z := z) hfs hη hρ hsupp hηrm hr₀η
      rw [show Dt.rm x hx = Dt.rm x hp₁ from rfl, h, Real.sq_sqrt hη.le]
      exact hεη
    · rw [GradientLikeStrip.twisted_rm_of_ne (D := B₁.D) (z := z) hfs hη hρ hsupp hηrm hr₀η hx hxp]
      exact B₁.hrm x hx
  have hVlev : ∀ x, (f x ≤ f p + B.ε / 2 ∨ f p + B.ε ≤ f x) → Dt.V x = B₁.D.V x := by
    intro x hx
    refine GradientLikeStrip.addPush_of_notMem_image (D := B₁.D) p hp₁ _
      (K := {y | morseNorm n y < (B₁.D.chart p hp₁).R ∧
        f p + B.ε / 2 < morseNormalForm (B₁.D.chart p hp₁).hk (f p) y ∧
        morseNormalForm (B₁.D.chart p hp₁).hk (f p) y < f p + B.ε}) ?_ ?_
    · intro y hy
      simp only [mem_ofPred_eq, not_and_or, not_lt] at hy
      rcases hy with h | h | h
      · exact GradientLikeStrip.twistY_eq_zero_of_R_le (D := B₁.D) (p := p) (hp := hp₁) (z := z)
          hη hρ hsupp h
      · exact ModelField.twist_eq_zero_of_nf_le _ hη z h
      · exact ModelField.twist_eq_zero_of_nf_ge _ hη z h
    · rintro ⟨y, ⟨hyR, h1, h2⟩, rfl⟩
      have := (B₁.D.chart p hp₁).hnorm y hyR.le
      rcases hx with hx | hx <;> linarith
  have hrq : ∀ q (hq : q ∈ B.upperIndexCriticalPoints), (B₁.D.chart q (hQc q hq)).r₀ ^ 2 < 2 * B₁.ε :=
    fun q hq => B₁.hr₀ q (hQc q hq)
  have hηq : ∀ q (hq : q ∈ B.upperIndexCriticalPoints), 2 * B.ε < B₁.D.rm q (hQc q hq) ^ 2 :=
    fun q hq => by linarith [hrm₁ q (hQc q hq)]
  have hεq : ∀ q (hq : q ∈ B.upperIndexCriticalPoints), 2 * B₁.ε ≤ (B₁.D.chart q (hQc q hq)).R ^ 2 :=
    fun q hq => by linarith [hR₁ q (hQc q hq)]
  refine ⟨⟨B₁.crit, B₁.hcrit, Dt, B₁.α, B₁.β, B₁.ε, B₁.c, B₁.hε, B₁.hr₀, hrmDt, B₁.haα,
      B₁.hαc, B₁.hcβ, B₁.hβb, B₁.hmin, B₁.hP, B₁.hQ, B₁.hhigh, B₁.hlev⟩, hcrit, ?_, ?_, hc₁,
      hα₁, hβ₁, ?_, ?_, ?_, ?_⟩
  · intro q hq
    refine ⟨hp₁, hQc q hq, ?_⟩
    intro w hw hw0
    obtain ⟨hwη, hSz⟩ := GradientLikeStrip.sardMap_twisted_zero hfs B₁.D hp₁ (z := z) hη hρ
      hsupp hηrm hr₀η (hQc q hq) hε₁ hεη hr₀ε hzρ.le hB4 (hεq q hq) (hrq q hq) (hηq q hq) hηc
      (hcq₁ q hq) (hlev₁ q hq) hw hw0
    have hsurj : Function.Surjective
        (fderiv ℝ (B₁.D.sardMap p (hQc q hq) B.ε B₁.c B.ε hp₁) w) := by
      have h := hreg ⟨q, hq⟩ (Finset.mem_univ _) ((e ⟨q, hq⟩).symm w)
        (show e ⟨q, hq⟩ ((e ⟨q, hq⟩).symm w) ∈ B₁.D.sardDom p (hQc q hq) B.ε B₁.c B.ε hp₁ by
          rw [(e ⟨q, hq⟩).apply_symm_apply w]; exact hwη)
        (show B₁.D.sardMap p (hQc q hq) B.ε B₁.c B.ε hp₁ (e ⟨q, hq⟩ ((e ⟨q, hq⟩).symm w)) = z by
          rw [(e ⟨q, hq⟩).apply_symm_apply w]; exact hSz)
      have h2 : fderiv ℝ (S ⟨q, hq⟩) ((e ⟨q, hq⟩).symm w) =
          (fderiv ℝ (B₁.D.sardMap p (hQc q hq) B.ε B₁.c B.ε hp₁) w).comp
            (e ⟨q, hq⟩ : (Fin ((B₁.D.chart p hp₁).k + 1) → ℝ) →L[ℝ]
              (Fin (B₁.D.chart q (hQc q hq)).k → ℝ)) := by
        have := (e ⟨q, hq⟩).comp_right_fderiv
          (f := B₁.D.sardMap p (hQc q hq) B.ε B₁.c B.ε hp₁) (x := (e ⟨q, hq⟩).symm w)
        rw [(e ⟨q, hq⟩).apply_symm_apply w] at this
        exact this
      rw [h2] at h
      intro y
      obtain ⟨x, hx⟩ := h y
      exact ⟨_, hx⟩
    have hdiffAt := (hdiff q hq).differentiableAt ((hopen q hq).mem_nhds hwη)
    have hlt : ‖B₁.D.sardMap p (hQc q hq) B.ε B₁.c B.ε hp₁ w‖ < B.ε / 32 := by
      rw [hSz]; exact hzρ
    have hev : Dt.sardMap p (hQc q hq) B₁.ε B₁.c B₁.ε hp₁ =ᶠ[𝓝 w]
        fun v => B₁.D.sardMap p (hQc q hq) B.ε B₁.c B.ε hp₁ v - z := by
      filter_upwards [(hopen q hq).mem_nhds hwη,
        hdiffAt.continuousAt.norm (Iio_mem_nhds hlt)] with v hv1 hv2
      exact (GradientLikeStrip.sardMap_twisted_of_small hfs B₁.D hp₁ (z := z) hη hρ hsupp hηrm
        hr₀η (hQc q hq) hε₁ hεη hzρ.le hB4 (hrq q hq) (hηq q hq) (hεq q hq) hηc (hcq₁ q hq)
        (hlev₁ q hq) hv1 hv2).2
    change Function.Surjective (fderiv ℝ (Dt.sardMap p (hQc q hq) B₁.ε B₁.c B₁.ε hp₁) w)
    rw [hev.fderiv_eq]
    have hsc := fderiv_sub_const (𝕜 := ℝ) (f := B₁.D.sardMap p (hQc q hq) B.ε B₁.c B.ε hp₁)
      (x := w) z
    erw [hsc]
    exact hsurj
  · intro p' hp' hp'p q hq
    have hp'₁ : p' ∈ B₁.crit := hcrit ▸ (B.mem_lowerIndexCriticalPoints.1 hp').1
    have hP₁ : p' ∈ B₁.lowerIndexCriticalPoints := by rw [B.lowerIndexCriticalPoints_eq_of_crit_eq hcrit]; exact hp'
    have hQ₁ : q ∈ B₁.upperIndexCriticalPoints := by rw [B.upperIndexCriticalPoints_eq_of_crit_eq hcrit]; exact hq
    have hag := GradientLikeStrip.sardAgree_twisted_of_ne hfs B₁.D hp₁ (z := z) hη hρ hsupp hηrm
      hr₀η hp'₁ (hQc q hq) hp'p (by rw [B.hP p' (B.mem_lowerIndexCriticalPoints.1 hp').1 (B.mem_lowerIndexCriticalPoints.1 hp').2, hfp]) hε₁
      hεη hzρ.le hB9 (B₁.sardValid hP₁ hQ₁) B₁.c B₁.c
    obtain ⟨h1, h2, h3⟩ := hpair p' hp' q hq
    refine ⟨Iff.trans ?_ h1, Eq.trans ?_ h2, Eq.trans ?_ h3⟩
    · constructor
      · rintro ⟨ha, hb, hc⟩; exact ⟨ha, hb, hag.1.1 hc⟩
      · rintro ⟨ha, hb, hc⟩; exact ⟨ha, hb, hag.1.2 hc⟩
    · have hq₁ : q ∈ B₁.crit := hQc q hq
      simp only [BlockConfig.count, hp'₁, hq₁, ↓reduceDIte]
      exact hag.2.1
    · have hq₁ : q ∈ B₁.crit := hQc q hq
      simp only [BlockConfig.zerosCard, hp'₁, hq₁, ↓reduceDIte]
      exact hag.2.2
  · change B₁.ε ≤ B.ε
    rw [hε₁eq]; linarith
  · intro x hx hx'
    exact ⟨(hch x hx).1, (hch x hx).2.1⟩
  · intro q hq y hy
    rw [← hsph q hq y hy]
    have hq₁ : q ∈ B₁.crit := hQc q hq
    have hk : (B₁.D.chart q hq₁).k = ℓ + 1 := by
      rw [← (B₁.D.chart q hq₁).hkidx]; exact (B.mem_upperIndexCriticalPoints.1 hq).2
    have hw : Handle.reidx (k := (B₁.D.chart q hq₁).k) y ≠ 0 := by
      intro h0
      apply hy
      ext j
      have hj : (j : ℕ) < (B₁.D.chart q hq₁).k := by rw [hk]; exact j.2
      have := congr_fun h0 ⟨j, hj⟩
      simpa [Handle.reidx, j.2] using this
    have hfx₀ : f ((B₁.D.chart q hq₁).χ ((B₁.D.chart q hq₁).sphereParam B₁.ε
        (Handle.reidx y))) = f q - B₁.ε :=
      (B₁.D.chart q hq₁).f_chart_of_mem_leftModelSphere (hεq q hq)
        ((B₁.D.chart q hq₁).sphereParam_mem_leftModelSphere hε₁.le hw)
    have hcc : B.c = B₁.c := hc₁.symm
    have hαε := B₁.hαc
    have haα := B₁.haα
    have hβb := B₁.hβb
    have hfqβ := hfq q hq
    have hcβ₁ := hcq₁ q hq
    have hflow := GradientLikeStrip.f_flow_eq_sub_of_levels hfs (D := B₁.D)
      (x := (B₁.D.chart q hq₁).χ ((B₁.D.chart q hq₁).sphereParam B₁.ε (Handle.reidx y)))
      (T := f q - B₁.ε - B.c) (by rw [hfx₀]; constructor <;> linarith)
      (by rw [hfx₀]; constructor <;> linarith) (by
        intro y' hy'
        rw [hfx₀, uIcc_of_ge (by linarith)] at hy'
        exact B₁.hlev y' ⟨by linarith [hy'.1], by linarith [hy'.2]⟩)
    have heq := GradientLikeStrip.flow_eq_of_agree (D₁ := B₁.D) (D₂ := Dt)
      (U := {x | f p + B.ε < f x}) (isOpen_lt continuous_const hfs.continuous)
      (fun x hx => (hVlev x (Or.inr (le_of_lt hx))).symm)
      (x := (B₁.D.chart q hq₁).χ ((B₁.D.chart q hq₁).sphereParam B₁.ε (Handle.reidx y)))
      (T := f q - B₁.ε - B.c) (by
        intro s hs
        change f p + B.ε < f _
        rw [hflow s (Icc_subset_uIcc ⟨hs.1, hs.2.le⟩), hfx₀]
        linarith [hs.2])
      (f q - B₁.ε - B.c) ⟨by linarith, le_rfl⟩
    simp only [GradientLikeStrip.leftSphereMap, hq₁, ↓reduceDIte]
    exact heq
  · refine ⟨φ, hφc, hφb, fun x hx => ?_⟩
    rw [← hφV x]
    exact hVlev x (Or.inl (by rw [hfp]; linarith))

end BlockConfig

section Isolation

variable (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem isCancellingPair_of_isolated [DecidableEq M] {f : M → ℝ} {a b : ℝ}
    (hf : MorseStrip I f a b) {crit : Finset M}
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (D : GradientLikeStrip I f a b crit) {ε c : ℝ} {p q : M} (hp : p ∈ crit) (hq : q ∈ crit)
    (hv : D.sardValid ε p hq hp) (hc₁ : f p + ε < c) (hc₂ : c < f q - ε)
    (htr : D.isSardTransverse p hq ε c hp) (hone : (D.sardZeros p hq ε c hp).ncard = 1)
    (hidx : morseIndex I f q = morseIndex I f p + 1) {a' b' : ℝ} (ha' : a < a') (hb' : b' < b)
    (ha'p : a' < f p) (hqb' : f q < b')
    (honly : ∀ x ∈ crit, f x ∈ Icc a' b' → x = p ∨ x = q)
    (hother : ∀ x (hx : x ∈ crit), x ≠ p → x ≠ q → ∀ y ∈ D.smallBall x hx, f y ∉ Icc a' b') :
    isCancellingPair I f a' b' p q := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hfc : Continuous f := hfs.continuous
  have hv₀ := hv
  obtain ⟨hε, hr₀p, hr₀q, hrmp, hrmq, hpq, hlevD⟩ := hv₀
  have hfpq : f p < f q := by linarith
  have hnb : ∀ x (hx : x ∈ crit), f x ∈ Ioo a' b' →
      ∃ σ > 0, (D.chart x hx).χ '' Metric.ball 0 σ ⊆ f ⁻¹' Ioo a' b' := by
    intro x hx hfx
    have h0 : (0 : Fin n → ℝ) ∈ (D.chart x hx).χ.source :=
      (D.chart x hx).hball (D.chart x hx).zero_mem_ball
    have hca : ContinuousAt (f ∘ (D.chart x hx).χ) 0 :=
      hfc.continuousAt.comp ((D.chart x hx).χ.continuousAt h0)
    have hmem : (f ∘ (D.chart x hx).χ) ⁻¹' Ioo a' b' ∈ 𝓝 (0 : Fin n → ℝ) := by
      apply hca.preimage_mem_nhds
      have : (f ∘ (D.chart x hx).χ) 0 = f x := by
        simp only [Function.comp_apply, (D.chart x hx).hχ0]
      rw [this]
      exact isOpen_Ioo.mem_nhds hfx
    obtain ⟨σ, hσ, hsub⟩ := Metric.mem_nhds_iff.1 hmem
    exact ⟨σ, hσ, by rintro _ ⟨y, hy, rfl⟩; exact hsub hy⟩
  obtain ⟨σp, hσp, hσpsub⟩ := hnb p hp ⟨ha'p, by linarith⟩
  obtain ⟨σq, hσq, hσqsub⟩ := hnb q hq ⟨by linarith, hqb'⟩
  set σ : ℝ := min σp σq with hσdef
  have hσ : 0 < σ := lt_min hσp hσq
  set ρ : ℝ := σ / 3 with hρdef
  have hρ : 0 < ρ := by positivity
  obtain ⟨m, hm, hmle⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x (hx : x ∈ crit), m ≤ D.rm x hx ^ 2 := by
    obtain ⟨x₀, -, hx₀⟩ := crit.attach.exists_min_image (fun x => D.rm x.1 x.2 ^ 2)
      ⟨⟨p, hp⟩, Finset.mem_attach _ _⟩
    refine ⟨D.rm x₀.1 x₀.2 ^ 2, by have := D.rm_pos x₀.1 x₀.2; positivity, fun x hx => ?_⟩
    exact hx₀ ⟨x, hx⟩ (Finset.mem_attach _ _)
  set ε' : ℝ := min ε (min (ρ ^ 2) m) / 16 with hε'def
  have hε' : 0 < ε' := by
    have : 0 < min ε (min (ρ ^ 2) m) := lt_min hε (lt_min (by positivity) hm)
    positivity
  have hε'ε : ε' ≤ ε := by
    have := min_le_left ε (min (ρ ^ 2) m); rw [hε'def]; linarith
  have hε'ρ : 16 * ε' ≤ ρ ^ 2 := by
    have := (min_le_right ε (min (ρ ^ 2) m)).trans (min_le_left (ρ ^ 2) m)
    rw [hε'def]; linarith
  have hε'm : 16 * ε' ≤ m := by
    have := (min_le_right ε (min (ρ ^ 2) m)).trans (min_le_right (ρ ^ 2) m)
    rw [hε'def]; linarith
  obtain ⟨D₁, hresc₁, hch₁, hr₁, -⟩ := GradientLikeStrip.exists_shrink_field hfs D
    (ε₁ := ε' / 2) (ρ := ρ) (by positivity) hρ (by linarith)
    (fun x hx => by linarith [hmle x hx])
  have hr₀₁ : ∀ x (hx : x ∈ crit), 4 * (D₁.chart x hx).r₀ < ρ := by
    intro x hx
    have h1 := (hr₁ x hx).1
    have h0 := (D₁.chart x hx).hr₀
    have h2 : (4 * (D₁.chart x hx).r₀) ^ 2 < ρ ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hρ.le h2
  have hrm₁ρ : ∀ x (hx : x ∈ crit), D₁.rm x hx ≤ ρ := fun x hx => by
    rw [(hr₁ x hx).2]; exact min_le_left _ _
  obtain ⟨D₂, hch₂, hrm₂, hV₂⟩ := GradientLikeStrip.exists_restrict D₁ (a' := a) (b' := b) le_rfl
    le_rfl crit (fun r hr => hr) (fun r hr hr' => absurd hr hr')
    (fun r hr => min (D₁.chart r hr).R (2 * ρ)) (fun r hr => min (D₁.chart r hr).R' (3 * ρ))
    (fun r hr => D₁.rm r hr)
    (fun r hr => ⟨lt_min (D₁.chart r hr).hr₀R (by linarith [hr₀₁ r hr]), min_le_left _ _⟩)
    (fun r hr => ⟨lt_min ((min_le_left _ _).trans_lt (D₁.chart r hr).hRR')
      ((min_le_right _ _).trans_lt (by linarith)), min_le_left _ _⟩)
    (fun r hr => ⟨(D₁.hrm r hr).1, le_rfl, le_min (D₁.hrm r hr).2 (by linarith [hrm₁ρ r hr])⟩)
    (fun r hr => (image_mono (Metric.ball_subset_ball (min_le_left _ _))).trans (D₁.inStrip r hr))
    (fun x _ h => h)
  have hχ₂ : ∀ x (hx : x ∈ crit), (D₂.chart x hx).χ = (D.chart x hx).χ ∧
      (D₂.chart x hx).k = (D.chart x hx).k := fun x hx =>
    ⟨(hch₂ x hx).1.trans (hch₁ x hx).1, (hch₂ x hx).2.1.trans (hch₁ x hx).2.1⟩
  have hr₀₂ : ∀ x (hx : x ∈ crit), (D₂.chart x hx).r₀ ^ 2 < ε' := fun x hx => by
    rw [(hch₂ x hx).2.2.1]; linarith [(hr₁ x hx).1]
  have hrm₂' : ∀ x (hx : x ∈ crit), 8 * ε' < D₂.rm x hx ^ 2 := fun x hx => by
    rw [hrm₂ x hx, (hr₁ x hx).2]
    rcases min_choice ρ (D.rm x hx) with h | h <;> rw [h]
    · linarith
    · linarith [hmle x hx]
  have hsb : ∀ x (hx : x ∈ crit), D₂.smallBall x hx ⊆ D.smallBall x hx := by
    intro x hx
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_, ?_⟩
    · have hy' : morseNorm n y < (D₂.chart x hx).r₀ := hy
      change morseNorm n y < (D.chart x hx).r₀
      rw [(hch₂ x hx).2.2.1] at hy'
      exact hy'.trans_le (hch₁ x hx).2.2.2.2
    · rw [(hχ₂ x hx).1]
  have hlev₂ : ∀ y, f y ∈ Icc (f p + ε') (f q - ε') → ∀ x (hx : x ∈ crit),
      y ∉ D₂.smallBall x hx := by
    intro y hy x hx hyx
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hyx
    have h2 := hr₀₂ x hx
    rw [abs_lt] at h1
    by_cases hxp : x = p
    · subst hxp; linarith [hy.1]
    by_cases hxq : x = q
    · subst hxq; linarith [hy.2]
    exact hother x hx hxp hxq y (hsb x hx hyx) ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hv₂ : D₂.sardValid ε' p hq hp :=
    ⟨hε', by linarith [hr₀₂ p hp], by linarith [hr₀₂ q hq], hrm₂' p hp, hrm₂' q hq,
      by linarith, hlev₂⟩
  have hresc₂ : D₂.isRescaleOf D := by
    obtain ⟨φ, hφc, hφb, hφ⟩ := hresc₁
    exact ⟨φ, hφc, hφb, fun x => by rw [hφ x, hV₂ x]⟩
  have hagree := GradientLikeStrip.sardAgree_of_rescale hfs hfs D D₂ hresc₂ hχ₂ hε'ε hp hq hv hv₂
    c c
  have htr₂ : D₂.isSardTransverse p hq ε' c hp := hagree.1.2 htr
  have hone₂ : (D₂.sardZeros p hq ε' c hp).ncard = 1 := hagree.2.2.trans hone
  have htail₂ : ∃ w₀ ∈ D₂.sardDom p hq ε' c ε' hp, D₂.sardMap p hq ε' c ε' hp w₀ = 0 ∧
      (∀ w ∈ D₂.sardDom p hq ε' c ε' hp, D₂.sardMap p hq ε' c ε' hp w = 0 →
        ∃ t : ℝ, 0 < t ∧ w = t • w₀) ∧
      Function.Surjective (fderiv ℝ (D₂.sardMap p hq ε' c ε' hp) w₀) := by
    obtain ⟨w₀, hw₀⟩ := Set.ncard_eq_one.1 hone₂
    have hw₀mem : w₀ ∈ D₂.sardZeros p hq ε' c hp := by rw [hw₀]; rfl
    obtain ⟨hw₀U, -, hw₀S⟩ := hw₀mem
    refine ⟨w₀, hw₀U, hw₀S, fun w hwU hwS => ?_, htr₂ w₀ hw₀U hw₀S⟩
    have hw0 : w ≠ 0 := hwU.1
    have ht : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hland : D₂.landing p hq ε' c ε' (‖w‖⁻¹ • w) = D₂.landing p hq ε' c ε' w :=
      D₂.landing_smul p hq ε' c ε' (inv_pos.2 ht) hw0
    have hw'mem : ‖w‖⁻¹ • w ∈ D₂.sardZeros p hq ε' c hp := by
      refine ⟨⟨smul_ne_zero (inv_ne_zero ht.ne') hw0, ?_⟩, ?_, ?_⟩
      · have h2 := hwU.2
        simp only [Set.mem_preimage] at h2 ⊢
        rw [hland]; exact h2
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']
      · show GradientLikeStrip.sardMap D₂ p hq ε' c ε' hp (‖w‖⁻¹ • w) = 0
        unfold GradientLikeStrip.sardMap
        rw [hland]; exact hwS
    rw [hw₀] at hw'mem
    have heq : ‖w‖⁻¹ • w = w₀ := hw'mem
    refine ⟨‖w‖, ht, ?_⟩
    rw [← heq, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hsub : ∀ r ∈ ({p, q} : Finset M), r ∈ crit := by
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact hp
    · rw [Finset.mem_singleton.1 hr]; exact hq
  have hother₂ : ∀ r (hr : r ∈ crit), r ∉ ({p, q} : Finset M) → ∀ y ∈ D₂.smallBall r hr,
      f y ∉ Icc a' b' := by
    intro r hr hrpq y hy
    have hrp : r ≠ p := fun h => hrpq (h ▸ mem_pair_left p q)
    have hrq : r ≠ q := fun h => hrpq (h ▸ mem_pair_right p q)
    exact hother r hr hrp hrq y (hsb r hr hy)
  obtain ⟨D'', hch'', hrm'', hV''⟩ := GradientLikeStrip.exists_restrict D₂ (a' := a') (b' := b')
    ha'.le hb'.le {p, q} hsub hother₂
    (fun r hr => (D₂.chart r (hsub r hr)).R) (fun r hr => (D₂.chart r (hsub r hr)).R')
    (fun r hr => D₂.rm r (hsub r hr))
    (fun r hr => ⟨(D₂.chart r (hsub r hr)).hr₀R, le_rfl⟩)
    (fun r hr => ⟨(D₂.chart r (hsub r hr)).hRR', le_rfl⟩)
    (fun r hr => ⟨(D₂.hrm r (hsub r hr)).1, le_rfl, (D₂.hrm r (hsub r hr)).2⟩)
    (fun r hr => by
      have hR' : (D₂.chart r (hsub r hr)).R' ≤ σ := by
        rw [(hch₂ r (hsub r hr)).2.2.2.2]
        exact (min_le_right _ _).trans (by rw [hρdef]; linarith)
      have hball := image_mono (f := (D₂.chart r (hsub r hr)).χ) (Metric.ball_subset_ball hR'
        (x := (0 : Fin n → ℝ)))
      refine hball.trans ?_
      rw [(hχ₂ r (hsub r hr)).1]
      rcases Finset.mem_insert.1 hr with rfl | hr'
      · exact (image_mono (Metric.ball_subset_ball (min_le_left _ _))).trans hσpsub
      · obtain rfl := Finset.mem_singleton.1 hr'
        exact (image_mono (Metric.ball_subset_ball (min_le_right _ _))).trans hσqsub)
    (fun x hx hxpq hxc => by
      rcases honly x hxc hx with rfl | rfl
      · exact hxpq (mem_pair_left _ _)
      · exact hxpq (mem_pair_right _ _))
  have hcheq : ∀ r (hr : r ∈ ({p, q} : Finset M)), D''.chart r hr = D₂.chart r (hsub r hr) := by
    intro r hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hch'' r hr
    revert h1 h2 h3 h4 h5
    generalize D''.chart r hr = c₁
    generalize D₂.chart r (hsub r hr) = c₂
    intro h1 h2 h3 h4 h5
    cases c₁; cases c₂
    simp only at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5
    rfl
  have hflow : D''.flow = D₂.flow :=
    funext fun t => funext fun x => GradientLikeStrip.flow_eq_of_V_eq D₂ D'' hV'' t x
  have hsb'' : ∀ r (hr : r ∈ ({p, q} : Finset M)), D''.smallBall r hr = D₂.smallBall r (hsub r hr) :=
    fun r hr => by unfold GradientLikeStrip.smallBall; rw [hcheq r hr]
  have hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x hx hxc
    have hxI : f x ∈ Ioo a b := by
      rcases hx with h | h <;> rw [h] <;> exact ⟨by linarith, by linarith⟩
    rcases honly x ((hcrit x).2 ⟨hxI, hxc⟩) (by rcases hx with h | h <;> rw [h] <;>
      exact ⟨by linarith, by linarith⟩) with rfl | rfl
    · rcases hx with h | h <;> linarith
    · rcases hx with h | h <;> linarith
  refine ⟨hf.substrip ha'.le (by linarith) hb'.le hreg, fun x => ?_, hfpq, hidx, D'', ε', c,
    hε', ?_, ?_, ?_, ?_, by linarith, by linarith, ?_, ?_⟩
  · constructor
    · intro hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact ⟨⟨ha'p, by linarith⟩, ((hcrit x).1 hp).2⟩
      · obtain rfl := Finset.mem_singleton.1 hx'
        exact ⟨⟨by linarith, hqb'⟩, ((hcrit x).1 hq).2⟩
    · rintro ⟨h1, h2⟩
      have hx : x ∈ crit := (hcrit x).2 ⟨⟨ha'.trans h1.1, h1.2.trans hb'⟩, h2⟩
      rcases honly x hx (Ioo_subset_Icc_self h1) with rfl | rfl
      · exact mem_pair_left _ _
      · exact mem_pair_right _ _
  · rw [hcheq]; linarith [hr₀₂ p hp]
  · rw [hcheq]; linarith [hr₀₂ q hq]
  · rw [hrm'']; exact hrm₂' p hp
  · rw [hrm'']; exact hrm₂' q hq
  · intro y hy r hr
    rw [hsb'' r hr]
    exact hlev₂ y hy r (hsub r hr)
  · have key : ∀ (cp : MorseNormalChart I f p) (cq : MorseNormalChart I f q),
        cp = D₂.chart p hp → cq = D₂.chart q hq →
        ∃ w₀ ∈ {w : Fin cq.k → ℝ | w ≠ 0} ∩ (fun w => D''.flow (c - (f p + ε'))
            (D''.flow (f q - ε' - c) (cq.χ (cq.sphereParam ε' w)))) ⁻¹'
            (cp.χ '' {y | morseNorm n y < cp.R}),
          ModelField.scaledNegativePart cp.hk (cp.χ.symm (D''.flow (c - (f p + ε'))
            (D''.flow (f q - ε' - c) (cq.χ (cq.sphereParam ε' w₀))))) = 0 ∧
          (∀ w ∈ {w : Fin cq.k → ℝ | w ≠ 0} ∩ (fun w => D''.flow (c - (f p + ε'))
              (D''.flow (f q - ε' - c) (cq.χ (cq.sphereParam ε' w)))) ⁻¹'
              (cp.χ '' {y | morseNorm n y < cp.R}),
            ModelField.scaledNegativePart cp.hk (cp.χ.symm (D''.flow (c - (f p + ε'))
              (D''.flow (f q - ε' - c) (cq.χ (cq.sphereParam ε' w))))) = 0 →
            ∃ t : ℝ, 0 < t ∧ w = t • w₀) ∧
          Function.Surjective (fderiv ℝ (fun w => ModelField.scaledNegativePart cp.hk (cp.χ.symm
            (D''.flow (c - (f p + ε')) (D''.flow (f q - ε' - c) (cq.χ (cq.sphereParam ε' w))))))
            w₀) := by
      rintro _ _ rfl rfl
      rw [hflow]
      exact htail₂
    exact key _ _ (hcheq p (mem_pair_left p q)) (hcheq q (mem_pair_right p q))

end Isolation

end

end DifferentialGeometry.Topology
