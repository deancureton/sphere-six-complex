module

public import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.Variational.FiniteOrder
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable local instance variationalAugmentedEndNormedAddCommGroup :
    NormedAddCommGroup
      ((E × (E →L[ℝ] E)) →L[ℝ] (E × (E →L[ℝ] E))) :=
  ContinuousLinearMap.toNormedAddCommGroup

section OrbitEquality

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}

omit [CompleteSpace E] in
theorem orbit_eq_of_augmentedFlow_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)))
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    {x : E} (hx_Φ : x ∈ closedBall x₀ (r : ℝ))
    (hx_a : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall
      ((x₀, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) (R_aug : ℝ))
    (ht₀_Φ : t₀ ∈ Ioo tmin tmax) (ht₀_a : t₀ ∈ Ioo tmin_a tmax_a) :
    (fun s => Φ ⟨x, s⟩) =ᶠ[𝓝 t₀]
      (fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) := by
  have hcd_at : ContDiffAt ℝ 1 (uncurry f) (t₀, x) :=
    hf_C1.contDiffAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))
  obtain ⟨K, sNhd, hsNhd, hl⟩ := hcd_at.exists_lipschitzOnWith
  obtain ⟨ρ_Lip, hρ_Lip_pos, hρ_Lip_sub⟩ := Metric.mem_nhds_iff.mp hsNhd
  set α_Φ : ℝ → E := fun s => Φ ⟨x, s⟩ with hα_Φ_def
  set α_a : ℝ → E := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1
    with hα_a_def
  have hα_Φ_initial : α_Φ t₀ = x := hΦ.apply_initial x hx_Φ
  have hα_a_initial : α_a t₀ = x := by
    change (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t₀⟩).1 = x
    rw [haΦ.apply_initial _ hx_a]
  have hIcc_nhds_Φ : Icc tmin tmax ∈ 𝓝 t₀ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht₀_Φ) Ioo_subset_Icc_self
  have hIcc_nhds_a : Icc tmin_a tmax_a ∈ 𝓝 t₀ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht₀_a) Ioo_subset_Icc_self
  have hα_Φ_cont_on : ContinuousOn α_Φ (Icc tmin tmax) := hΦ.orbit_continuousOn x hx_Φ
  have hα_Φ_cont : ContinuousAt α_Φ t₀ :=
    hα_Φ_cont_on.continuousAt hIcc_nhds_Φ
  have h_orbit_cont_on : ContinuousOn
      (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
      (Icc tmin_a tmax_a) :=
    haΦ.orbit_continuousOn (x, ContinuousLinearMap.id ℝ E) hx_a
  have hα_a_cont : ContinuousAt α_a t₀ := by
    have h_pair_cont_at : ContinuousAt
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩) t₀ :=
      h_orbit_cont_on.continuousAt hIcc_nhds_a
    exact continuous_fst.continuousAt.comp h_pair_cont_at
  set ρ' : ℝ := ρ_Lip / 2 with hρ'_def
  have hρ'_pos : 0 < ρ' := by positivity
  have hρ'_lt_Lip : ρ' < ρ_Lip := by rw [hρ'_def]; linarith
  set S : Set E := ball x ρ' with hS_def
  have hS_nhds_x : S ∈ 𝓝 x := ball_mem_nhds x hρ'_pos
  have hα_Φ_eventually : ∀ᶠ t in 𝓝 t₀, α_Φ t ∈ S := by
    have h := hα_Φ_cont (show S ∈ 𝓝 (α_Φ t₀) by rw [hα_Φ_initial]; exact hS_nhds_x)
    exact h
  have hα_a_eventually : ∀ᶠ t in 𝓝 t₀, α_a t ∈ S := by
    have h := hα_a_cont (show S ∈ 𝓝 (α_a t₀) by rw [hα_a_initial]; exact hS_nhds_x)
    exact h
  have h_v_lip_event : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K (f t) S := by
    rw [eventually_iff_exists_mem]
    refine ⟨ball t₀ ρ', ball_mem_nhds t₀ hρ'_pos, ?_⟩
    intro t ht
    rw [mem_ball] at ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro y₁ hy₁ y₂ hy₂
    have h_pair₁ : ((t, y₁) : ℝ × E) ∈ ball (t₀, x) ρ_Lip := by
      rw [mem_ball, Prod.dist_eq]
      rw [mem_ball] at hy₁
      have hmax_le_ρ' : max (dist t t₀) (dist y₁ x) ≤ ρ' :=
        max_le (le_of_lt ht) (le_of_lt hy₁)
      exact lt_of_le_of_lt hmax_le_ρ' hρ'_lt_Lip
    have h_pair₂ : ((t, y₂) : ℝ × E) ∈ ball (t₀, x) ρ_Lip := by
      rw [mem_ball, Prod.dist_eq]
      rw [mem_ball] at hy₂
      have hmax_le_ρ' : max (dist t t₀) (dist y₂ x) ≤ ρ' :=
        max_le (le_of_lt ht) (le_of_lt hy₂)
      exact lt_of_le_of_lt hmax_le_ρ' hρ'_lt_Lip
    have h_in_S₁ : ((t, y₁) : ℝ × E) ∈ sNhd := hρ_Lip_sub h_pair₁
    have h_in_S₂ : ((t, y₂) : ℝ × E) ∈ sNhd := hρ_Lip_sub h_pair₂
    have hd : dist (uncurry f (t, y₁)) (uncurry f (t, y₂))
        ≤ K * dist ((t, y₁) : ℝ × E) (t, y₂) :=
      hl.dist_le_mul _ h_in_S₁ _ h_in_S₂
    have hdist_eq : dist ((t, y₁) : ℝ × E) (t, y₂) = dist y₁ y₂ := by
      rw [Prod.dist_eq]; simp [dist_self]
    rw [hdist_eq] at hd
    change dist (uncurry f (t, y₁)) (uncurry f (t, y₂)) ≤ K * dist y₁ y₂
    exact hd
  have hα_Φ_deriv_event : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt α_Φ (f t (α_Φ t)) t ∧ α_Φ t ∈ S := by
    have h_int : Ioo tmin tmax ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀_Φ
    refine Filter.eventually_of_mem (Filter.inter_mem h_int hα_Φ_eventually) ?_
    intro t ht
    rcases ht with ⟨ht_int, ht_S⟩
    refine ⟨?_, ht_S⟩
    have h_dw : HasDerivWithinAt (fun s => Φ ⟨x, s⟩) (f t (Φ ⟨x, t⟩))
        (Icc tmin tmax) t :=
      hΦ.hasDerivWithinAt x hx_Φ t (Ioo_subset_Icc_self ht_int)
    have hIcc_nhds_t : Icc tmin tmax ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht_int) Ioo_subset_Icc_self
    exact h_dw.hasDerivAt hIcc_nhds_t
  have hα_a_deriv_event : ∀ᶠ t in 𝓝 t₀,
      HasDerivAt α_a (f t (α_a t)) t ∧ α_a t ∈ S := by
    have h_int : Ioo tmin_a tmax_a ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀_a
    refine Filter.eventually_of_mem (Filter.inter_mem h_int hα_a_eventually) ?_
    intro t ht
    rcases ht with ⟨ht_int, ht_S⟩
    refine ⟨?_, ht_S⟩
    have h_orbit_dw : HasDerivWithinAt
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
        (augmentedVectorField f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩))
        (Icc tmin_a tmax_a) t :=
      haΦ.hasDerivWithinAt _ hx_a t (Ioo_subset_Icc_self ht_int)
    have hIcc_a_nhds_t : Icc tmin_a tmax_a ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht_int) Ioo_subset_Icc_self
    have h_orbit_at : HasDerivAt
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
        (augmentedVectorField f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩)) t :=
      h_orbit_dw.hasDerivAt hIcc_a_nhds_t
    have h_fst_fd : HasFDerivAt
        (fun p : E × (E →L[ℝ] E) => p.1)
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
        (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩) :=
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt
    have h_comp : HasDerivAt α_a
        ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augmentedVectorField f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩))) t :=
      h_fst_fd.comp_hasDerivAt t h_orbit_at
    have h_first_eq :
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augmentedVectorField f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩))
        = f t (α_a t) := by
      change (augmentedVectorField f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩)).1
        = f t (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1
      rfl
    rw [h_first_eq] at h_comp
    exact h_comp
  have h_initial_eq : α_Φ t₀ = α_a t₀ := by rw [hα_Φ_initial, hα_a_initial]
  exact ODE_solution_unique_of_eventually
    (K := K) (v := fun t y => f t y) (s := fun _ => S)
    h_v_lip_event hα_Φ_deriv_event hα_a_deriv_event h_initial_eq

end OrbitEquality

section SmoothnessInheritance

variable {f : ℝ → E → E} {x₀ : E} {t₀ : ℝ}

omit [CompleteSpace E] in
theorem contDiffOn_fromAugmentedFlow_inherits
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {ρ_a ρ : ℝ≥0} {T_a T : ℝ}
    (hρ_le : (ρ : ℝ) ≤ (ρ_a : ℝ)) (hT_le : T ≤ T_a)
    (haΦ_C1 : ContDiffOn ℝ 1 aΦ
      ((ball ((x₀, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E))
          (ρ_a : ℝ)) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a))) :
    ContDiffOn ℝ 1 (fromAugmentedFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀_def
  set U : Set (E × ℝ) := ball x₀ (ρ : ℝ) ×ˢ Ioo (t₀ - T) (t₀ + T) with hU_def
  set U_a : Set ((E × (E →L[ℝ] E)) × ℝ) :=
    ball p₀ (ρ_a : ℝ) ×ˢ Ioo (t₀ - T_a) (t₀ + T_a) with hU_a_def
  have hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2)) U U_a := by
    intro q hq
    rcases hq with ⟨hq_x, hq_t⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball] at hq_x ⊢
      have hd : dist ((q.1, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) p₀
          = dist q.1 x₀ := by
        change max (dist q.1 x₀) (dist (ContinuousLinearMap.id ℝ E)
          (ContinuousLinearMap.id ℝ E)) = dist q.1 x₀
        rw [dist_self, max_eq_left dist_nonneg]
      rw [hd]
      exact lt_of_lt_of_le hq_x hρ_le
    · rcases hq_t with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  exact contDiffOn_fromAugmentedFlow (k := (1 : ℕ∞)) (Ω := U_a) (U := U) haΦ_C1 hmap

end SmoothnessInheritance

section OrbitEqualityIcc

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ}
  {Φ : E × ℝ → E}

omit [CompleteSpace E] in
theorem orbit_eq_Icc_of_augmentedFlow_isLocalFlow
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {R_aug : ℝ≥0} {tmin_a tmax_a : ℝ}
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augmentedVectorField f) t₀ (x₀, ContinuousLinearMap.id ℝ E) R_aug
      tmin_a tmax_a aΦ)
    {x : E} (hx_Φ : x ∈ closedBall x₀ (r : ℝ))
    (hx_a : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall
      ((x₀, ContinuousLinearMap.id ℝ E) : E × (E →L[ℝ] E)) (R_aug : ℝ))
    {T : ℝ} (hT_sub_Φ : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin tmax)
    (hT_sub_a : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin_a tmax_a)
    (ht₀_Ioo : t₀ ∈ Ioo (t₀ - T) (t₀ + T))
    {r₀ : ℝ} {K : ℝ≥0}
    (h_Φ_in : ∀ t ∈ Ioo (t₀ - T) (t₀ + T), Φ ⟨x, t⟩ ∈ closedBall x₀ r₀)
    (h_a_in : ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
      (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1 ∈ closedBall x₀ r₀)
    (h_lip : ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
      LipschitzOnWith K (f t) (closedBall x₀ r₀)) :
    EqOn (fun s => Φ ⟨x, s⟩)
      (fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1)
      (Icc (t₀ - T) (t₀ + T)) := by
  set α_Φ : ℝ → E := fun s => Φ ⟨x, s⟩ with hα_Φ_def
  set α_a : ℝ → E := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1
    with hα_a_def
  have hα_Φ_initial : α_Φ t₀ = x := hΦ.apply_initial x hx_Φ
  have hα_a_initial : α_a t₀ = x := by
    change (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t₀⟩).1 = x
    rw [haΦ.apply_initial _ hx_a]
  have hα_Φ_cont : ContinuousOn α_Φ (Icc (t₀ - T) (t₀ + T)) :=
    (hΦ.orbit_continuousOn x hx_Φ).mono hT_sub_Φ
  have hα_a_cont : ContinuousOn α_a (Icc (t₀ - T) (t₀ + T)) := by
    have h_pair_cont : ContinuousOn
        (fun s => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)
        (Icc tmin_a tmax_a) :=
      haΦ.orbit_continuousOn (x, ContinuousLinearMap.id ℝ E) hx_a
    have h_fst_cont : ContinuousOn α_a (Icc tmin_a tmax_a) :=
      continuous_fst.continuousOn.comp h_pair_cont (fun _ _ => mem_univ _)
    exact h_fst_cont.mono hT_sub_a
  have hα_Φ_deriv : ∀ s ∈ Ioo (t₀ - T) (t₀ + T),
      HasDerivAt α_Φ (f s (α_Φ s)) s := by
    intro s hs
    have h_in_Icc_Φ : s ∈ Icc tmin tmax := hT_sub_Φ (Ioo_subset_Icc_self hs)
    have h_dw : HasDerivWithinAt (fun u => Φ ⟨x, u⟩) (f s (Φ ⟨x, s⟩))
        (Icc tmin tmax) s := hΦ.hasDerivWithinAt x hx_Φ s h_in_Icc_Φ
    have h_nhds : Icc tmin tmax ∈ 𝓝 s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs)
        (fun u hu => hT_sub_Φ (Ioo_subset_Icc_self hu))
    exact h_dw.hasDerivAt h_nhds
  have hα_a_deriv : ∀ s ∈ Ioo (t₀ - T) (t₀ + T),
      HasDerivAt α_a (f s (α_a s)) s := by
    intro s hs
    have h_in_Icc_a : s ∈ Icc tmin_a tmax_a := hT_sub_a (Ioo_subset_Icc_self hs)
    have h_orbit_dw : HasDerivWithinAt
        (fun u => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), u⟩)
        (augmentedVectorField f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩))
        (Icc tmin_a tmax_a) s :=
      haΦ.hasDerivWithinAt _ hx_a s h_in_Icc_a
    have h_nhds : Icc tmin_a tmax_a ∈ 𝓝 s :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs)
        (fun u hu => hT_sub_a (Ioo_subset_Icc_self hu))
    have h_orbit_at : HasDerivAt
        (fun u => aΦ ⟨(x, ContinuousLinearMap.id ℝ E), u⟩)
        (augmentedVectorField f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩)) s :=
      h_orbit_dw.hasDerivAt h_nhds
    have h_fst_fd : HasFDerivAt
        (fun p : E × (E →L[ℝ] E) => p.1)
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
        (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩) :=
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt
    have h_comp : HasDerivAt α_a
        ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augmentedVectorField f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩))) s :=
      h_fst_fd.comp_hasDerivAt s h_orbit_at
    have h_first_eq :
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (augmentedVectorField f s (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩))
        = f s (α_a s) := rfl
    rw [h_first_eq] at h_comp
    exact h_comp
  have h_initial_eq : α_Φ t₀ = α_a t₀ := by rw [hα_Φ_initial, hα_a_initial]
  exact ODE_solution_unique_of_mem_Icc
    (v := fun t y => f t y)
    (s := fun _ => closedBall x₀ r₀)
    (K := K)
    (fun t ht => h_lip t ht)
    ht₀_Ioo hα_Φ_cont
    (fun t ht => hα_Φ_deriv t ht)
    (fun t ht => h_Φ_in t ht)
    hα_a_cont
    (fun t ht => hα_a_deriv t ht)
    (fun t ht => h_a_in t ht)
    h_initial_eq

end OrbitEqualityIcc

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
