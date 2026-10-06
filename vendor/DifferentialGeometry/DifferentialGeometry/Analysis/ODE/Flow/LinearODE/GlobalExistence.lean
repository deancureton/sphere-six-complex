module

public import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Solution

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

section GlobalExistence

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem exists_linearODE_solution_of_short_at
    {A : ℝ → (G →L[ℝ] G)} {c T M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (c - T) (c + T)))
    (hA_bd : ∀ t ∈ Icc (c - T) (c + T), ‖A t‖ ≤ M)
    (Y_c : G) :
    ∃ Z : ℝ → G, Z c = Y_c ∧
      ∀ t ∈ Icc (c - T) (c + T), HasDerivWithinAt Z (A t (Z t))
        (Icc (c - T) (c + T)) t :=
  exists_linearODE_solution_of_short (A := A) (h₀ := c) (T := T) (M := M)
    hT hM hMT hA_cont hA_bd Y_c

omit [CompleteSpace G] in
theorem portPrivate_c647eb87_hasDerivWithinAt_glue_Icc_at_pt
    {f g : ℝ → G} {A : ℝ → (G →L[ℝ] G)} {α t₁ β : ℝ}
    (hα_le : α ≤ t₁) (hβ_ge : t₁ ≤ β)
    (hf : ∀ t ∈ Icc α t₁, HasDerivWithinAt f (A t (f t)) (Icc α t₁) t)
    (hg : ∀ t ∈ Icc t₁ β, HasDerivWithinAt g (A t (g t)) (Icc t₁ β) t)
    (h_match : f t₁ = g t₁) :
    let Z : ℝ → G := fun t => if t ≤ t₁ then f t else g t
    Z t₁ = f t₁ ∧
      ∀ t ∈ Icc α β, HasDerivWithinAt Z (A t (Z t)) (Icc α β) t := by
  intro Z
  have hZ_t1 : Z t₁ = f t₁ := by simp [Z]
  refine ⟨hZ_t1, ?_⟩
  have hZ_eq_f : ∀ t, t ≤ t₁ → Z t = f t := by
    intro t ht; simp [Z, ht]
  have hZ_eq_g : ∀ t, t₁ ≤ t → Z t = g t := by
    intro t ht
    by_cases htle : t ≤ t₁
    · have : t = t₁ := le_antisymm htle ht
      simp [Z, this, h_match]
    · simp [Z, htle]
  intro t ht
  have hunion : Icc α t₁ ∪ Icc t₁ β = Icc α β :=
    Set.Icc_union_Icc_eq_Icc hα_le hβ_ge
  rcases le_total t t₁ with htle | htge
  · have ht_left : t ∈ Icc α t₁ := ⟨ht.1, htle⟩
    have hf_deriv : HasDerivWithinAt f (A t (f t)) (Icc α t₁) t := hf t ht_left
    have hZ_eq_set : EqOn Z f (Icc α t₁) := fun s hs => hZ_eq_f s hs.2
    have hZf_deriv : HasDerivWithinAt Z (A t (f t)) (Icc α t₁) t :=
      hf_deriv.congr (fun s hs => hZ_eq_set hs) (hZ_eq_f t htle)
    by_cases hteq : t = t₁
    · subst hteq
      have ht_right : t ∈ Icc t β := ⟨le_rfl, hβ_ge⟩
      have hg_deriv : HasDerivWithinAt g (A t (g t)) (Icc t β) t := hg t ht_right
      have hZ_eq_set_r : EqOn Z g (Icc t β) := fun s hs => hZ_eq_g s hs.1
      have hZg_deriv : HasDerivWithinAt Z (A t (g t)) (Icc t β) t :=
        hg_deriv.congr (fun s hs => hZ_eq_set_r hs) (hZ_eq_g t le_rfl)
      have h_ZAt_val : Z t = f t := hZ_t1
      have h_AZ_eq_Af : A t (Z t) = A t (f t) := by rw [h_ZAt_val]
      have h_AZ_eq_Ag : A t (Z t) = A t (g t) := by rw [h_ZAt_val, h_match]
      have hZf_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc α t) t := by
        rw [h_AZ_eq_Af]; exact hZf_deriv
      have hZg_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc t β) t := by
        rw [h_AZ_eq_Ag]; exact hZg_deriv
      have := (hZf_at_t1).union hZg_at_t1
      rwa [hunion] at this
    · have htlt : t < t₁ := lt_of_le_of_ne htle hteq
      have h_AZ_eq : A t (Z t) = A t (f t) := by rw [hZ_eq_f t htle]
      have hZf_at_t : HasDerivWithinAt Z (A t (Z t)) (Icc α t₁) t := by
        rw [h_AZ_eq]; exact hZf_deriv
      have h_nhds_eq : 𝓝[Icc α β] t = 𝓝[Icc α t₁] t := by
        apply le_antisymm
        · rw [nhdsWithin_le_iff]
          have h_Iic_nhd : Iic t₁ ∈ 𝓝 t := Iic_mem_nhds htlt
          have : Iic t₁ ∈ 𝓝[Icc α β] t := mem_nhdsWithin_of_mem_nhds h_Iic_nhd
          have h_inter : Icc α β ∩ Iic t₁ = Icc α t₁ := by
            ext s; constructor
            · intro ⟨h1, h2⟩; exact ⟨h1.1, h2⟩
            · intro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hβ_ge⟩, h2⟩
          have := inter_mem_nhdsWithin (Icc α β) h_Iic_nhd
          rw [h_inter] at this; exact this
        · exact nhdsWithin_mono _ (Icc_subset_Icc_right hβ_ge)
      rw [HasDerivWithinAt, h_nhds_eq.symm] at hZf_at_t
      exact hZf_at_t
  · have ht_right : t ∈ Icc t₁ β := ⟨htge, ht.2⟩
    have hg_deriv : HasDerivWithinAt g (A t (g t)) (Icc t₁ β) t := hg t ht_right
    have hZ_eq_set_r : EqOn Z g (Icc t₁ β) := fun s hs => hZ_eq_g s hs.1
    have hZg_deriv : HasDerivWithinAt Z (A t (g t)) (Icc t₁ β) t :=
      hg_deriv.congr (fun s hs => hZ_eq_set_r hs) (hZ_eq_g t htge)
    by_cases hteq : t = t₁
    · subst hteq
      have ht_left : t ∈ Icc α t := ⟨hα_le, le_rfl⟩
      have hf_deriv : HasDerivWithinAt f (A t (f t)) (Icc α t) t := hf t ht_left
      have hZ_eq_set : EqOn Z f (Icc α t) := fun s hs => hZ_eq_f s hs.2
      have hZf_deriv : HasDerivWithinAt Z (A t (f t)) (Icc α t) t :=
        hf_deriv.congr (fun s hs => hZ_eq_set hs) (hZ_eq_f t le_rfl)
      have h_ZAt_val : Z t = f t := hZ_t1
      have h_AZ_eq_Af : A t (Z t) = A t (f t) := by rw [h_ZAt_val]
      have h_AZ_eq_Ag : A t (Z t) = A t (g t) := by rw [h_ZAt_val, h_match]
      have hZf_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc α t) t := by
        rw [h_AZ_eq_Af]; exact hZf_deriv
      have hZg_at_t1 : HasDerivWithinAt Z (A t (Z t)) (Icc t β) t := by
        rw [h_AZ_eq_Ag]; exact hZg_deriv
      have := (hZf_at_t1).union hZg_at_t1
      rwa [hunion] at this
    · have htgt : t₁ < t := lt_of_le_of_ne htge (Ne.symm hteq)
      have h_AZ_eq : A t (Z t) = A t (g t) := by rw [hZ_eq_g t htge]
      have hZg_at_t : HasDerivWithinAt Z (A t (Z t)) (Icc t₁ β) t := by
        rw [h_AZ_eq]; exact hZg_deriv
      have h_nhds_eq : 𝓝[Icc α β] t = 𝓝[Icc t₁ β] t := by
        apply le_antisymm
        · rw [nhdsWithin_le_iff]
          have h_Ici_nhd : Ici t₁ ∈ 𝓝 t := Ici_mem_nhds htgt
          have h_inter : Icc α β ∩ Ici t₁ = Icc t₁ β := by
            ext s; constructor
            · intro ⟨h1, h2⟩; exact ⟨h2, h1.2⟩
            · intro ⟨h1, h2⟩; exact ⟨⟨le_trans hα_le h1, h2⟩, h1⟩
          have := inter_mem_nhdsWithin (Icc α β) h_Ici_nhd
          rw [h_inter] at this; exact this
        · exact nhdsWithin_mono _ (Icc_subset_Icc_left hα_le)
      rw [HasDerivWithinAt, h_nhds_eq.symm] at hZg_at_t
      exact hZg_at_t

theorem portPrivate_c647eb87_exists_linearODE_solution_right_iterated
    {A : ℝ → (G →L[ℝ] G)} {h₀ M T B : ℝ}
    (hT_pos : 0 < T) (hM_nn : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - T) (h₀ + B + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - T) (h₀ + B + T), ‖A t‖ ≤ M)
    (Y₀ : G) :
    ∀ n : ℕ, (n : ℝ) * T ≤ B →
      ∃ Z : ℝ → G, Z h₀ = Y₀ ∧
        ∀ t ∈ Icc h₀ (h₀ + (n : ℝ) * T),
          HasDerivWithinAt Z (A t (Z t)) (Icc h₀ (h₀ + (n : ℝ) * T)) t := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => Y₀, rfl, fun t ht => ?_⟩
    simp only [Nat.cast_zero, zero_mul, add_zero] at ht ⊢
    have hsub : (Icc h₀ h₀).Subsingleton := by
      intro x hx y hy
      have hx_eq : x = h₀ := le_antisymm hx.2 hx.1
      have hy_eq : y = h₀ := le_antisymm hy.2 hy.1
      rw [hx_eq, hy_eq]
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact HasFDerivWithinAt.of_finite hsub.finite
  | succ k ih =>
    intro hkT
    have hkT_prev : (k : ℝ) * T ≤ B := by
      have : ((k : ℝ) + 1) * T = (k : ℝ) * T + T := by ring
      push_cast at hkT
      linarith [hT_pos]
    obtain ⟨Z_k, hZ_k_initial, hZ_k_deriv⟩ := ih hkT_prev
    set c : ℝ := h₀ + (k : ℝ) * T + T with hc_def
    have hsub_picard : Icc (c - T) (c + T) ⊆ Icc (h₀ - T) (h₀ + B + T) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : h₀ - T ≤ c - T := by
          rw [hc_def]; have hkT_nn : (0 : ℝ) ≤ k * T := by positivity
          linarith
        linarith [hs.1]
      · have : c + T ≤ h₀ + B + T := by
          rw [hc_def]; have h_step : (↑k + 1) * T ≤ B := by push_cast at hkT; exact hkT
          have : (k : ℝ) * T + T + T = ((k : ℝ) + 1) * T + T := by ring
          linarith
        linarith [hs.2]
    have hA_cont_picard : ContinuousOn A (Icc (c - T) (c + T)) := hA_cont.mono hsub_picard
    have hA_bd_picard : ∀ t ∈ Icc (c - T) (c + T), ‖A t‖ ≤ M :=
      fun t ht => hA_bd t (hsub_picard ht)
    set Y_c : G := Z_k (h₀ + (k : ℝ) * T) with hY_c_def
    have h_t1_mem : h₀ + (k : ℝ) * T ∈ Icc (c - T) (c + T) := by
      rw [hc_def]; refine ⟨by linarith, by linarith [hT_pos]⟩
    set t₁ : ℝ := h₀ + (k : ℝ) * T with ht₁_def
    have h_picard_sub : Icc (t₁ - T) (t₁ + T) ⊆ Icc (h₀ - T) (h₀ + B + T) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : h₀ - T ≤ t₁ - T := by
          rw [ht₁_def]; have hkT_nn : (0 : ℝ) ≤ k * T := by positivity
          linarith
        linarith [hs.1]
      · have : t₁ + T ≤ h₀ + B + T := by
          rw [ht₁_def]; have h_step : (↑k + 1) * T ≤ B := by push_cast at hkT; exact hkT
          have : (k : ℝ) * T + T = ((k : ℝ) + 1) * T := by ring
          linarith
        linarith [hs.2]
    have hA_cont_picard' : ContinuousOn A (Icc (t₁ - T) (t₁ + T)) := hA_cont.mono h_picard_sub
    have hA_bd_picard' : ∀ t ∈ Icc (t₁ - T) (t₁ + T), ‖A t‖ ≤ M :=
      fun t ht => hA_bd t (h_picard_sub ht)
    obtain ⟨Z_pic, hZ_pic_initial, hZ_pic_deriv⟩ :=
      exists_linearODE_solution_of_short_at hT_pos hM_nn hMT hA_cont_picard' hA_bd_picard' Y_c
    have h_pic_right : ∀ t ∈ Icc t₁ (t₁ + T),
        HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc t₁ (t₁ + T)) t := by
      intro t ht
      have ht_in_picard : t ∈ Icc (t₁ - T) (t₁ + T) :=
        ⟨by linarith [ht.1, hT_pos], ht.2⟩
      have hd : HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc (t₁ - T) (t₁ + T)) t :=
        hZ_pic_deriv t ht_in_picard
      exact hd.mono (Icc_subset_Icc_left (by linarith [hT_pos]))
    have h_match : Z_k t₁ = Z_pic t₁ := by
      rw [hZ_pic_initial]
    have h_prev_deriv : ∀ t ∈ Icc h₀ t₁,
        HasDerivWithinAt Z_k (A t (Z_k t)) (Icc h₀ t₁) t := by
      intro t ht
      exact hZ_k_deriv t ht
    have h_ht1_le_top : t₁ ≤ t₁ + T := by linarith [hT_pos]
    have h_h0_le_t1 : h₀ ≤ t₁ := by
      change h₀ ≤ h₀ + (k : ℝ) * T
      have hkT_nn : (0 : ℝ) ≤ k * T := mul_nonneg (Nat.cast_nonneg _) hT_pos.le
      linarith
    have h_glued :=
      portPrivate_c647eb87_hasDerivWithinAt_glue_Icc_at_pt (f := Z_k) (g := Z_pic) (A := A)
        (α := h₀) (t₁ := t₁) (β := t₁ + T) h_h0_le_t1 h_ht1_le_top
        h_prev_deriv h_pic_right h_match
    set Z : ℝ → G := fun t => if t ≤ t₁ then Z_k t else Z_pic t with hZ_def
    obtain ⟨hZ_t1, hZ_deriv⟩ := h_glued
    have hZ_initial : Z h₀ = Y₀ := by
      simp [Z, h_h0_le_t1, hZ_k_initial]
    have h_dom_eq : h₀ + ((k : ℝ) + 1) * T = t₁ + T := by
      rw [ht₁_def]; ring
    refine ⟨Z, hZ_initial, fun t ht => ?_⟩
    have h_dom_eq' : h₀ + ((k : ℕ) + 1 : ℝ) * T = t₁ + T := by
      change h₀ + ((k : ℝ) + 1) * T = (h₀ + (k : ℝ) * T) + T; ring
    have h_dom_cast : h₀ + (↑(k + 1) : ℝ) * T = t₁ + T := by
      have : (↑(k + 1) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
      rw [this]; exact h_dom_eq'
    have ht_cast : t ∈ Icc h₀ (t₁ + T) := by
      rcases ht with ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h_dom_cast] at h2; exact h2
    have hd := hZ_deriv t ht_cast
    have hset_eq : Icc h₀ (t₁ + T) = Icc h₀ (h₀ + (↑(k + 1) : ℝ) * T) := by
      rw [h_dom_cast]
    rw [hset_eq] at hd
    exact hd

theorem portPrivate_c647eb87_exists_linearODE_solution_left_iterated
    {A : ℝ → (G →L[ℝ] G)} {h₀ M T B : ℝ}
    (hT_pos : 0 < T) (hM_nn : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - B - T) (h₀ + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - B - T) (h₀ + T), ‖A t‖ ≤ M)
    (Y₀ : G) :
    ∀ n : ℕ, (n : ℝ) * T ≤ B →
      ∃ Z : ℝ → G, Z h₀ = Y₀ ∧
        ∀ t ∈ Icc (h₀ - (n : ℝ) * T) h₀,
          HasDerivWithinAt Z (A t (Z t)) (Icc (h₀ - (n : ℝ) * T) h₀) t := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => Y₀, rfl, fun t ht => ?_⟩
    simp only [Nat.cast_zero, zero_mul, sub_zero] at ht ⊢
    have hsub : (Icc h₀ h₀).Subsingleton := by
      intro x hx y hy
      have hx_eq : x = h₀ := le_antisymm hx.2 hx.1
      have hy_eq : y = h₀ := le_antisymm hy.2 hy.1
      rw [hx_eq, hy_eq]
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact HasFDerivWithinAt.of_finite hsub.finite
  | succ k ih =>
    intro hkT
    have hkT_prev : (k : ℝ) * T ≤ B := by
      have : ((k : ℝ) + 1) * T = (k : ℝ) * T + T := by ring
      push_cast at hkT
      linarith [hT_pos]
    obtain ⟨Z_k, hZ_k_initial, hZ_k_deriv⟩ := ih hkT_prev
    set t₁ : ℝ := h₀ - (k : ℝ) * T with ht₁_def
    have h_picard_sub : Icc (t₁ - T) (t₁ + T) ⊆ Icc (h₀ - B - T) (h₀ + T) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : h₀ - B - T ≤ t₁ - T := by
          rw [ht₁_def]; have h_step : (↑k + 1) * T ≤ B := by push_cast at hkT; exact hkT
          have : (k : ℝ) * T + T = ((k : ℝ) + 1) * T := by ring
          linarith
        linarith [hs.1]
      · have : t₁ + T ≤ h₀ + T := by
          rw [ht₁_def]; have hkT_nn : (0 : ℝ) ≤ k * T := mul_nonneg (Nat.cast_nonneg _) hT_pos.le
          linarith
        linarith [hs.2]
    have hA_cont_picard' : ContinuousOn A (Icc (t₁ - T) (t₁ + T)) := hA_cont.mono h_picard_sub
    have hA_bd_picard' : ∀ t ∈ Icc (t₁ - T) (t₁ + T), ‖A t‖ ≤ M :=
      fun t ht => hA_bd t (h_picard_sub ht)
    set Y_c : G := Z_k t₁ with hY_c_def
    obtain ⟨Z_pic, hZ_pic_initial, hZ_pic_deriv⟩ :=
      exists_linearODE_solution_of_short_at hT_pos hM_nn hMT hA_cont_picard' hA_bd_picard' Y_c
    have h_pic_left : ∀ t ∈ Icc (t₁ - T) t₁,
        HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc (t₁ - T) t₁) t := by
      intro t ht
      have ht_in_picard : t ∈ Icc (t₁ - T) (t₁ + T) :=
        ⟨ht.1, by linarith [ht.2, hT_pos]⟩
      have hd : HasDerivWithinAt Z_pic (A t (Z_pic t)) (Icc (t₁ - T) (t₁ + T)) t :=
        hZ_pic_deriv t ht_in_picard
      exact hd.mono (Icc_subset_Icc_right (by linarith [hT_pos]))
    have h_match : Z_pic t₁ = Z_k t₁ := hZ_pic_initial
    have h_next_deriv : ∀ t ∈ Icc t₁ h₀,
        HasDerivWithinAt Z_k (A t (Z_k t)) (Icc t₁ h₀) t := by
      intro t ht
      exact hZ_k_deriv t ht
    have h_t1_le_h0 : t₁ ≤ h₀ := by
      change h₀ - (k : ℝ) * T ≤ h₀
      have hkT_nn : (0 : ℝ) ≤ k * T := mul_nonneg (Nat.cast_nonneg _) hT_pos.le
      linarith
    have h_ht1m_le_t1 : t₁ - T ≤ t₁ := by linarith [hT_pos]
    have h_glued :=
      portPrivate_c647eb87_hasDerivWithinAt_glue_Icc_at_pt (f := Z_pic) (g := Z_k) (A := A)
        (α := t₁ - T) (t₁ := t₁) (β := h₀) h_ht1m_le_t1 h_t1_le_h0
        h_pic_left h_next_deriv h_match
    set Z : ℝ → G := fun t => if t ≤ t₁ then Z_pic t else Z_k t with hZ_def
    obtain ⟨hZ_t1, hZ_deriv⟩ := h_glued
    have hZ_initial : Z h₀ = Y₀ := by
      by_cases h : h₀ ≤ t₁
      · have h_eq : h₀ = t₁ := le_antisymm h h_t1_le_h0
        have h_match' : Z_pic t₁ = Y₀ := by rw [hY_c_def] at hZ_pic_initial
                                            rw [hZ_pic_initial, ← h_eq, hZ_k_initial]
        simp only [Z, h, ↓reduceIte]
        rw [h_eq]; exact h_match'
      · rw [not_le] at h
        simp only [Z, not_le.mpr h, ↓reduceIte, hZ_k_initial]
    have h_dom_cast : h₀ - (↑(k + 1) : ℝ) * T = t₁ - T := by
      rw [ht₁_def]; push_cast; ring
    refine ⟨Z, hZ_initial, fun t ht => ?_⟩
    have ht_cast : t ∈ Icc (t₁ - T) h₀ := by
      rcases ht with ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [h_dom_cast] at h1; exact h1
    have hd := hZ_deriv t ht_cast
    have hset_eq : Icc (t₁ - T) h₀ = Icc (h₀ - (↑(k + 1) : ℝ) * T) h₀ := by
      rw [h_dom_cast]
    rw [hset_eq] at hd
    exact hd

theorem portPrivate_c647eb87_exists_linearODE_solution_on_Icc_subset
    {A : ℝ → (G →L[ℝ] G)} {a b α β h₀ : ℝ}
    (hα_lt : a < α) (hβ_lt : β < b)
    (hα_le : α ≤ h₀) (hβ_ge : h₀ ≤ β)
    (hA_cont : ContinuousOn A (Ioo a b))
    (Y₀ : G) :
    ∃ Z : ℝ → G, Z h₀ = Y₀ ∧
      ∀ t ∈ Icc α β, HasDerivWithinAt Z (A t (Z t)) (Icc α β) t := by
  set α'' : ℝ := (a + α) / 2 with hα''_def
  set β'' : ℝ := (β + b) / 2 with hβ''_def
  have hα''_lt : a < α'' := by rw [hα''_def]; linarith
  have hα''_le_α : α'' < α := by rw [hα''_def]; linarith
  have hβ''_lt : β'' < b := by rw [hβ''_def]; linarith
  have hβ''_ge_β : β < β'' := by rw [hβ''_def]; linarith
  have h_subset : Icc α'' β'' ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le hα''_lt hs.1, lt_of_le_of_lt hs.2 hβ''_lt⟩
  have hα''_le : α'' ≤ β'' := by linarith [hα_le.trans hβ_ge]
  have hα''_lt_β'' : α'' < β'' := by linarith [hα_le.trans hβ_ge]
  have hcont' : ContinuousOn A (Icc α'' β'') := hA_cont.mono h_subset
  have hcont_norm : ContinuousOn (fun t => ‖A t‖) (Icc α'' β'') :=
    continuous_norm.comp_continuousOn hcont'
  have hcpt : IsCompact (Icc α'' β'') := isCompact_Icc
  have hne : (Icc α'' β'').Nonempty := ⟨α'', left_mem_Icc.mpr hα''_le⟩
  rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨τ_max, _, hτ_max⟩
  set M : ℝ := ‖A τ_max‖ with hM_def
  have hM_nn : 0 ≤ M := norm_nonneg _
  have hM_bd : ∀ t ∈ Icc α'' β'', ‖A t‖ ≤ M := fun t ht => hτ_max ht
  set T : ℝ := 1 / (2 * (M + 1)) with hT_def
  have hT_pos : 0 < T := by
    rw [hT_def]; positivity
  have hMT : M * T < 1 := by
    have h_denom_pos : 0 < 2 * (M + 1) := by positivity
    have hT_eq : T = 1 / (2 * (M + 1)) := hT_def
    rw [hT_eq]
    have : M * (1 / (2 * (M + 1))) = M / (2 * (M + 1)) := by ring
    rw [this, div_lt_one h_denom_pos]
    have h_M_le_M1 : M ≤ M + 1 := by linarith
    calc M = M * 1 := (mul_one _).symm
      _ ≤ (M + 1) * 1 := mul_le_mul_of_nonneg_right h_M_le_M1 zero_le_one
      _ < 2 * (M + 1) := by linarith
  set δ_R : ℝ := (β'' - β) / 2 with hδ_R_def
  set δ_L : ℝ := (α - α'') / 2 with hδ_L_def
  have hδ_R_pos : 0 < δ_R := by rw [hδ_R_def]; linarith
  have hδ_L_pos : 0 < δ_L := by rw [hδ_L_def]; linarith
  set T' : ℝ := min T (min δ_R δ_L) with hT'_def
  have hT'_pos : 0 < T' := by
    rw [hT'_def]; exact lt_min hT_pos (lt_min hδ_R_pos hδ_L_pos)
  have hT'_le_T : T' ≤ T := by rw [hT'_def]; exact min_le_left _ _
  have hT'_le_δ_R : T' ≤ δ_R := by
    rw [hT'_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hT'_le_δ_L : T' ≤ δ_L := by
    rw [hT'_def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hMT' : M * T' < 1 := by
    have : M * T' ≤ M * T := mul_le_mul_of_nonneg_left hT'_le_T hM_nn
    linarith
  set B_R : ℝ := β - h₀ with hB_R_def
  set B_L : ℝ := h₀ - α with hB_L_def
  have hB_R_nn : 0 ≤ B_R := by rw [hB_R_def]; linarith
  have hB_L_nn : 0 ≤ B_L := by rw [hB_L_def]; linarith
  set n_R : ℕ := ⌈B_R / T'⌉₊ with hn_R_def
  have hn_R_bound : B_R ≤ (n_R : ℝ) * T' := by
    rw [hn_R_def]
    have := Nat.le_ceil (B_R / T')
    have h_div : B_R / T' * T' = B_R := by
      field_simp
    calc B_R = B_R / T' * T' := h_div.symm
      _ ≤ (⌈B_R / T'⌉₊ : ℝ) * T' := mul_le_mul_of_nonneg_right this hT'_pos.le
  have hn_R_step_bound : (n_R : ℝ) * T' ≤ B_R + T' := by
    rw [hn_R_def]
    have hceil := Nat.ceil_lt_add_one (a := B_R / T') (div_nonneg hB_R_nn hT'_pos.le)
    have : (⌈B_R / T'⌉₊ : ℝ) ≤ B_R / T' + 1 := le_of_lt hceil
    calc (⌈B_R / T'⌉₊ : ℝ) * T' ≤ (B_R / T' + 1) * T' :=
          mul_le_mul_of_nonneg_right this hT'_pos.le
      _ = B_R / T' * T' + T' := by ring
      _ = B_R + T' := by field_simp
  set n_L : ℕ := ⌈B_L / T'⌉₊ with hn_L_def
  have hn_L_bound : B_L ≤ (n_L : ℝ) * T' := by
    rw [hn_L_def]
    have := Nat.le_ceil (B_L / T')
    have h_div : B_L / T' * T' = B_L := by field_simp
    calc B_L = B_L / T' * T' := h_div.symm
      _ ≤ (⌈B_L / T'⌉₊ : ℝ) * T' := mul_le_mul_of_nonneg_right this hT'_pos.le
  have hn_L_step_bound : (n_L : ℝ) * T' ≤ B_L + T' := by
    rw [hn_L_def]
    have hceil := Nat.ceil_lt_add_one (a := B_L / T') (div_nonneg hB_L_nn hT'_pos.le)
    have : (⌈B_L / T'⌉₊ : ℝ) ≤ B_L / T' + 1 := le_of_lt hceil
    calc (⌈B_L / T'⌉₊ : ℝ) * T' ≤ (B_L / T' + 1) * T' :=
          mul_le_mul_of_nonneg_right this hT'_pos.le
      _ = B_L / T' * T' + T' := by ring
      _ = B_L + T' := by field_simp
  have h_right_end : h₀ + (n_R : ℝ) * T' + T' ≤ β'' := by
    have : (n_R : ℝ) * T' + T' ≤ B_R + 2 * T' := by linarith
    have h1 : h₀ + (B_R + 2 * T') = β + 2 * T' := by rw [hB_R_def]; ring
    have h2 : β + 2 * T' ≤ β + 2 * δ_R := by linarith
    have h3 : β + 2 * δ_R = β'' := by rw [hδ_R_def]; ring
    linarith
  have h_left_end : α'' ≤ h₀ - (n_L : ℝ) * T' - T' := by
    have h1 : (n_L : ℝ) * T' + T' ≤ B_L + 2 * T' := by linarith
    have h2 : h₀ - (B_L + 2 * T') = α - 2 * T' := by rw [hB_L_def]; ring
    have h3 : α - 2 * T' ≥ α - 2 * δ_L := by linarith
    have h4 : α - 2 * δ_L = α'' := by rw [hδ_L_def]; ring
    linarith
  have h_R_sub_α'β'' : Icc (h₀ - T') (h₀ + (n_R : ℝ) * T' + T') ⊆ Icc α'' β'' := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have : α'' ≤ h₀ - T' := by
        have hL_step : h₀ - (n_L : ℝ) * T' - T' ≤ h₀ - T' := by
          have : (0 : ℝ) ≤ (n_L : ℝ) * T' := by positivity
          linarith
        linarith
      linarith [hs.1]
    · linarith [hs.2, h_right_end]
  have hA_cont_R : ContinuousOn A (Icc (h₀ - T') (h₀ + (n_R : ℝ) * T' + T')) :=
    hcont'.mono h_R_sub_α'β''
  have hA_bd_R : ∀ t ∈ Icc (h₀ - T') (h₀ + (n_R : ℝ) * T' + T'), ‖A t‖ ≤ M :=
    fun t ht => hM_bd t (h_R_sub_α'β'' ht)
  obtain ⟨Z_R, hZ_R_initial, hZ_R_deriv⟩ :=
    portPrivate_c647eb87_exists_linearODE_solution_right_iterated (A := A) (h₀ := h₀) (M := M) (T := T')
      (B := (n_R : ℝ) * T') hT'_pos hM_nn hMT' hA_cont_R hA_bd_R Y₀ n_R le_rfl
  have h_L_sub_α'β'' : Icc (h₀ - (n_L : ℝ) * T' - T') (h₀ + T') ⊆ Icc α'' β'' := by
    intro s hs
    refine ⟨?_, ?_⟩
    · linarith [hs.1, h_left_end]
    · have : h₀ + T' ≤ β'' := by
        have hR_step : h₀ + T' ≤ h₀ + (n_R : ℝ) * T' + T' := by
          have : (0 : ℝ) ≤ (n_R : ℝ) * T' := by positivity
          linarith
        linarith
      linarith [hs.2]
  have hA_cont_L : ContinuousOn A (Icc (h₀ - (n_L : ℝ) * T' - T') (h₀ + T')) :=
    hcont'.mono h_L_sub_α'β''
  have hA_bd_L : ∀ t ∈ Icc (h₀ - (n_L : ℝ) * T' - T') (h₀ + T'), ‖A t‖ ≤ M :=
    fun t ht => hM_bd t (h_L_sub_α'β'' ht)
  obtain ⟨Z_L, hZ_L_initial, hZ_L_deriv⟩ :=
    portPrivate_c647eb87_exists_linearODE_solution_left_iterated (A := A) (h₀ := h₀) (M := M) (T := T')
      (B := (n_L : ℝ) * T') hT'_pos hM_nn hMT' hA_cont_L hA_bd_L Y₀ n_L le_rfl
  have h_match : Z_L h₀ = Z_R h₀ := by rw [hZ_L_initial, hZ_R_initial]
  have h_α_ge_L : h₀ - (n_L : ℝ) * T' ≤ h₀ := by
    have h : (0 : ℝ) ≤ (n_L : ℝ) * T' := by positivity
    linarith
  have h_R_ge_β : h₀ ≤ h₀ + (n_R : ℝ) * T' := by
    have h : (0 : ℝ) ≤ (n_R : ℝ) * T' := by positivity
    linarith
  have h_glued := portPrivate_c647eb87_hasDerivWithinAt_glue_Icc_at_pt
    (f := Z_L) (g := Z_R) (A := A)
    (α := h₀ - (n_L : ℝ) * T') (t₁ := h₀) (β := h₀ + (n_R : ℝ) * T')
    h_α_ge_L h_R_ge_β hZ_L_deriv hZ_R_deriv h_match
  set Z : ℝ → G := fun t => if t ≤ h₀ then Z_L t else Z_R t with hZ_def
  obtain ⟨hZ_h0, hZ_LR_deriv⟩ := h_glued
  have hZ_initial : Z h₀ = Y₀ := by
    simp only [Z, le_refl, ↓reduceIte, hZ_L_initial]
  refine ⟨Z, hZ_initial, ?_⟩
  have h_α_lb : h₀ - (n_L : ℝ) * T' ≤ α := by
    have : (n_L : ℝ) * T' ≥ B_L := hn_L_bound
    have hα_eq : h₀ - B_L = α := by rw [hB_L_def]; ring
    linarith
  have h_β_ub : β ≤ h₀ + (n_R : ℝ) * T' := by
    have : (n_R : ℝ) * T' ≥ B_R := hn_R_bound
    have hβ_eq : h₀ + B_R = β := by rw [hB_R_def]; ring
    linarith
  have h_Icc_sub : Icc α β ⊆ Icc (h₀ - (n_L : ℝ) * T') (h₀ + (n_R : ℝ) * T') := fun s hs =>
    ⟨le_trans h_α_lb hs.1, le_trans hs.2 h_β_ub⟩
  intro t ht
  have ht' : t ∈ Icc (h₀ - (n_L : ℝ) * T') (h₀ + (n_R : ℝ) * T') := h_Icc_sub ht
  have hd := hZ_LR_deriv t ht'
  exact hd.mono h_Icc_sub

def portPrivate_c647eb87_subIntervalSeq (a h₀ b : ℝ) (n : ℕ) : ℝ × ℝ :=
  (a + (h₀ - a) / ((n : ℝ) + 2), b - (b - h₀) / ((n : ℝ) + 2))

theorem hasLinearODESolution_of_continuousOn
    {F G : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : F → ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {Z₀ : F → G}
    {a b : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b)
    {U : Set F}
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b))
    {x : F} (hx : x ∈ U) :
    HasLinearODESolution A a b h₀ Z₀ x := by
  classical
  have hA_x_cont : ContinuousOn (A x) (Ioo a b) :=
    ContinuousOn.uncurry_left (a := x) (sα := U) (sβ := Ioo a b) hx hA_cont
  have hh0a : a < h₀ := h₀_mem.1
  have hh0b : h₀ < b := h₀_mem.2
  let α : ℕ → ℝ := fun n => a + (h₀ - a) / ((n : ℝ) + 2)
  let β : ℕ → ℝ := fun n => b - (b - h₀) / ((n : ℝ) + 2)
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hden_ge1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 2 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith
  have hα_lt_a : ∀ n, a < α n := fun n => by
    change a < a + (h₀ - a) / ((n : ℝ) + 2)
    have h : 0 < (h₀ - a) / ((n : ℝ) + 2) := div_pos (by linarith) (hden n)
    linarith
  have hβ_lt_b : ∀ n, β n < b := fun n => by
    change b - (b - h₀) / ((n : ℝ) + 2) < b
    have h : 0 < (b - h₀) / ((n : ℝ) + 2) := div_pos (by linarith) (hden n)
    linarith
  have hα_le_h0 : ∀ n, α n ≤ h₀ := fun n => by
    change a + (h₀ - a) / ((n : ℝ) + 2) ≤ h₀
    have h : (h₀ - a) / ((n : ℝ) + 2) ≤ h₀ - a := by
      rw [div_le_iff₀ (hden n)]
      calc h₀ - a = (h₀ - a) * 1 := (mul_one _).symm
        _ ≤ (h₀ - a) * ((n : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left (hden_ge1 n) (by linarith)
    linarith
  have hh0_le_β : ∀ n, h₀ ≤ β n := fun n => by
    change h₀ ≤ b - (b - h₀) / ((n : ℝ) + 2)
    have h : (b - h₀) / ((n : ℝ) + 2) ≤ b - h₀ := by
      rw [div_le_iff₀ (hden n)]
      calc b - h₀ = (b - h₀) * 1 := (mul_one _).symm
        _ ≤ (b - h₀) * ((n : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left (hden_ge1 n) (by linarith)
    linarith
  have h_exists : ∀ n : ℕ, ∃ Z : ℝ → G, Z h₀ = Z₀ x ∧
      ∀ t ∈ Icc (α n) (β n), HasDerivWithinAt Z (A x t (Z t)) (Icc (α n) (β n)) t :=
    fun n => portPrivate_c647eb87_exists_linearODE_solution_on_Icc_subset
      (hα_lt_a n) (hβ_lt_b n) (hα_le_h0 n) (hh0_le_β n) hA_x_cont (Z₀ x)
  choose Zn hZn_initial hZn_deriv using h_exists
  have hα_mono : ∀ k₁ k₂, k₁ ≤ k₂ → α k₂ ≤ α k₁ := by
    intro k₁ k₂ hk
    change a + (h₀ - a) / ((k₂ : ℝ) + 2) ≤ a + (h₀ - a) / ((k₁ : ℝ) + 2)
    have h_le : (k₁ : ℝ) + 2 ≤ (k₂ : ℝ) + 2 := by exact_mod_cast by linarith
    have hd2 : (h₀ - a) / ((k₂ : ℝ) + 2) ≤ (h₀ - a) / ((k₁ : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (hden k₁) h_le
    linarith
  have hβ_mono : ∀ k₁ k₂, k₁ ≤ k₂ → β k₁ ≤ β k₂ := by
    intro k₁ k₂ hk
    change b - (b - h₀) / ((k₁ : ℝ) + 2) ≤ b - (b - h₀) / ((k₂ : ℝ) + 2)
    have h_le : (k₁ : ℝ) + 2 ≤ (k₂ : ℝ) + 2 := by exact_mod_cast by linarith
    have hd2 : (b - h₀) / ((k₂ : ℝ) + 2) ≤ (b - h₀) / ((k₁ : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (hden k₁) h_le
    linarith
  have h_unique : ∀ n m : ℕ, ∀ s ∈ Ioo (α (min n m)) (β (min n m)),
      Zn n s = Zn m s := by
    intro n m s hs_min
    set N := min n m
    have hαn_le : α n ≤ α N := hα_mono N n (min_le_left _ _)
    have hαm_le : α m ≤ α N := hα_mono N m (min_le_right _ _)
    have hβn_ge : β N ≤ β n := hβ_mono N n (min_le_left _ _)
    have hβm_ge : β N ≤ β m := hβ_mono N m (min_le_right _ _)
    have h_subset_n : Ioo (α N) (β N) ⊆ Icc (α n) (β n) := fun u hu =>
      ⟨le_of_lt (lt_of_le_of_lt hαn_le hu.1), le_of_lt (lt_of_lt_of_le hu.2 hβn_ge)⟩
    have h_subset_m : Ioo (α N) (β N) ⊆ Icc (α m) (β m) := fun u hu =>
      ⟨le_of_lt (lt_of_le_of_lt hαm_le hu.1), le_of_lt (lt_of_lt_of_le hu.2 hβm_ge)⟩
    have h_h0_in_N : h₀ ∈ Ioo (α N) (β N) := by
      refine ⟨?_, ?_⟩
      · change a + (h₀ - a) / ((N : ℝ) + 2) < h₀
        have h_pos : 0 < (h₀ - a) / ((N : ℝ) + 2) :=
          div_pos (by linarith) (hden N)
        have h_lt : (h₀ - a) / ((N : ℝ) + 2) < h₀ - a := by
          have h_den_gt1 : (1 : ℝ) < (N : ℝ) + 2 := by
            have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
          have h_h0a_pos : 0 < h₀ - a := by linarith
          calc (h₀ - a) / ((N : ℝ) + 2)
              < (h₀ - a) / 1 := by
                apply div_lt_div_of_pos_left h_h0a_pos (by norm_num) h_den_gt1
            _ = h₀ - a := by norm_num
        linarith
      · change h₀ < b - (b - h₀) / ((N : ℝ) + 2)
        have h_pos : 0 < (b - h₀) / ((N : ℝ) + 2) :=
          div_pos (by linarith) (hden N)
        have h_lt : (b - h₀) / ((N : ℝ) + 2) < b - h₀ := by
          have h_den_gt1 : (1 : ℝ) < (N : ℝ) + 2 := by
            have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
          have h_bh0_pos : 0 < b - h₀ := by linarith
          calc (b - h₀) / ((N : ℝ) + 2)
              < (b - h₀) / 1 := by
                apply div_lt_div_of_pos_left h_bh0_pos (by norm_num) h_den_gt1
            _ = b - h₀ := by norm_num
        linarith
    have h_subN_to_Ioo : Ioo (α N) (β N) ⊆ Ioo a b := fun u hu =>
      ⟨lt_of_lt_of_le (hα_lt_a N) hu.1.le, lt_of_le_of_lt hu.2.le (hβ_lt_b N)⟩
    have hA_cont_N : ContinuousOn (A x) (Ioo (α N) (β N)) :=
      hA_x_cont.mono h_subN_to_Ioo
    have h_Zn_deriv_open : ∀ u ∈ Ioo (α N) (β N), HasDerivAt (Zn n) (A x u (Zn n u)) u := by
      intro u hu
      have hd := hZn_deriv n u (h_subset_n hu)
      exact hd.hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hαn_le hu.1) (lt_of_lt_of_le hu.2 hβn_ge))
    have h_Zm_deriv_open : ∀ u ∈ Ioo (α N) (β N), HasDerivAt (Zn m) (A x u (Zn m u)) u := by
      intro u hu
      have hd := hZn_deriv m u (h_subset_m hu)
      exact hd.hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hαm_le hu.1) (lt_of_lt_of_le hu.2 hβm_ge))
    have h_match : Zn n h₀ = Zn m h₀ := by rw [hZn_initial, hZn_initial]
    exact linearODE_unique_on_Ioo (A := A x) h_h0_in_N hA_cont_N
      h_Zn_deriv_open h_Zm_deriv_open h_match hs_min
  have h_exhaust : ∀ t ∈ Ioo a b, ∃ n : ℕ, t ∈ Ioo (α n) (β n) := by
    intro t ht
    have hta : 0 < t - a := by linarith [ht.1]
    have htb : 0 < b - t := by linarith [ht.2]
    obtain ⟨N, hN⟩ :=
      exists_nat_gt (max ((h₀ - a) / (t - a)) ((b - h₀) / (b - t)))
    have hN1 : (h₀ - a) / (t - a) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
    have hN2 : (b - h₀) / (b - t) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    refine ⟨N, ?_, ?_⟩
    · change a + (h₀ - a) / ((N : ℝ) + 2) < t
      have h_den : (0 : ℝ) < (N : ℝ) + 2 := by positivity
      have h_key : (h₀ - a) / ((N : ℝ) + 2) < t - a := by
        rw [div_lt_iff₀ h_den]
        have h_eq : (h₀ - a) = (h₀ - a) / (t - a) * (t - a) := by field_simp
        rw [h_eq]
        rw [mul_comm (t - a) ((N : ℝ) + 2)]
        calc (h₀ - a) / (t - a) * (t - a)
            < (N : ℝ) * (t - a) := mul_lt_mul_of_pos_right hN1 hta
          _ ≤ ((N : ℝ) + 2) * (t - a) :=
              mul_le_mul_of_nonneg_right (by linarith) hta.le
      linarith
    · change t < b - (b - h₀) / ((N : ℝ) + 2)
      have h_den : (0 : ℝ) < (N : ℝ) + 2 := by positivity
      have h_key : (b - h₀) / ((N : ℝ) + 2) < b - t := by
        rw [div_lt_iff₀ h_den]
        have h_eq : (b - h₀) = (b - h₀) / (b - t) * (b - t) := by field_simp
        rw [h_eq]
        rw [mul_comm (b - t) ((N : ℝ) + 2)]
        calc (b - h₀) / (b - t) * (b - t)
            < (N : ℝ) * (b - t) := mul_lt_mul_of_pos_right hN2 htb
          _ ≤ ((N : ℝ) + 2) * (b - t) :=
              mul_le_mul_of_nonneg_right (by linarith) htb.le
      linarith
  let Z : ℝ → G := fun t =>
    if h : ∃ n, t ∈ Ioo (α n) (β n) then Zn (Nat.find h) t else Z₀ x
  refine ⟨Z, ?_, ?_⟩
  · have h_h0_mem : ∃ n, h₀ ∈ Ioo (α n) (β n) := by
      refine ⟨0, ?_, ?_⟩
      · change a + (h₀ - a) / ((0 : ℕ) + 2 : ℝ) < h₀
        have : 0 < (h₀ - a) / ((0 : ℕ) + 2 : ℝ) :=
          div_pos (by linarith) (by norm_num)
        linarith
      · change h₀ < b - (b - h₀) / ((0 : ℕ) + 2 : ℝ)
        have : 0 < (b - h₀) / ((0 : ℕ) + 2 : ℝ) :=
          div_pos (by linarith) (by norm_num)
        linarith
    change (if h : ∃ n, h₀ ∈ Ioo (α n) (β n) then Zn (Nat.find h) h₀ else Z₀ x) = Z₀ x
    rw [dite_eq_left h_h0_mem]
    exact hZn_initial _
  · intro t ht
    obtain ⟨N, hN⟩ := h_exhaust t ht
    have h_ex_t : ∃ n, t ∈ Ioo (α n) (β n) := ⟨N, hN⟩
    let N₀ := Nat.find h_ex_t
    have hN0_spec : t ∈ Ioo (α N₀) (β N₀) := Nat.find_spec h_ex_t
    have h_in_Icc : t ∈ Icc (α N₀) (β N₀) := ⟨hN0_spec.1.le, hN0_spec.2.le⟩
    have h_nhd : Icc (α N₀) (β N₀) ∈ 𝓝 t := Icc_mem_nhds hN0_spec.1 hN0_spec.2
    have hd_within := hZn_deriv N₀ t h_in_Icc
    have hd : HasDerivAt (Zn N₀) (A x t (Zn N₀ t)) t := hd_within.hasDerivAt h_nhd
    have h_Z_eq_eventually : Z =ᶠ[𝓝 t] Zn N₀ := by
      have h_nhd_open : Ioo (α N₀) (β N₀) ∈ 𝓝 t := Ioo_mem_nhds hN0_spec.1 hN0_spec.2
      filter_upwards [h_nhd_open] with s hs
      have h_ex_s : ∃ n, s ∈ Ioo (α n) (β n) := ⟨N₀, hs⟩
      change (if h : ∃ n, s ∈ Ioo (α n) (β n) then Zn (Nat.find h) s else Z₀ x) = Zn N₀ s
      rw [dite_eq_left h_ex_s]
      let M_s := Nat.find h_ex_s
      have hMs_spec : s ∈ Ioo (α M_s) (β M_s) := Nat.find_spec h_ex_s
      apply h_unique M_s N₀ s
      refine ⟨?_, ?_⟩
      · rcases le_total M_s N₀ with h | h
        · rw [min_eq_left h]; exact hMs_spec.1
        · rw [min_eq_right h]; exact hs.1
      · rcases le_total M_s N₀ with h | h
        · rw [min_eq_left h]; exact hMs_spec.2
        · rw [min_eq_right h]; exact hs.2
    have h_Z_t_eq : Z t = Zn N₀ t := h_Z_eq_eventually.eq_of_nhds
    rw [h_Z_t_eq]
    exact hd.congr_of_eventuallyEq h_Z_eq_eventually

theorem linearODESolution_hasDerivAt
    {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : F → ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {Z₀ : F → G}
    {a b : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b)
    {U : Set F}
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b))
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (linearODESolution A a b h₀ Z₀ x ·)
      (A x t (linearODESolution A a b h₀ Z₀ x t)) t :=
  linearODESolution_hasDerivAt_of_hasSolution A a b h₀ Z₀
    (hasLinearODESolution_of_continuousOn h₀_mem hA_cont hx) ht

end GlobalExistence

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
