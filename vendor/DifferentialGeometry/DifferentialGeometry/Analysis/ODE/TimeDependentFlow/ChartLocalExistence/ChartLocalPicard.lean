module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

@[expose] public section


namespace DifferentialGeometry.Analysis.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem time_dependent_vf_chart_local_picard_with_lipschitz
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hCont :
      ContinuousOn (Function.uncurry (fun t x => X t x)) (Set.univ : Set (ℝ × M)))
    (hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ r' : ℝ, 0 < r' ∧
      ∃ flow : E → ℝ → E,
        (∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r',
          flow y 0 = y ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            HasDerivWithinAt (flow y)
              ((X t ((chartAt H α).symm (I.symm (flow y t)))) : E)
              (Set.Icc (0 : ℝ) T) t) := by
  obtain ⟨L, K, r, hL, hr, hK, hLipt⟩ := hLip
  set f : ℝ → E → E :=
    fun t y => (X t ((chartAt H α).symm (I.symm y)) : E) with hf_def
  set x₀ : E := I ((chartAt H α) α) with hx₀_def
  have hCont_at_centre : ContinuousOn (fun t : ℝ => f t x₀) (Set.Icc 0 L) := by
    have hsymm₁ : I.symm x₀ = (chartAt H α) α := by
      simp [hx₀_def]
    have hsymm₂ : (chartAt H α).symm (I.symm x₀) = α := by
      rw [hsymm₁]
      exact (chartAt H α).left_inv (mem_chart_source H α)
    have hrw : (fun t : ℝ => f t x₀) = fun t : ℝ => (X t α : E) := by
      funext t
      change X t ((chartAt H α).symm (I.symm x₀)) = X t α
      rw [hsymm₂]
    rw [hrw]
    have hCont' : Continuous (fun t : ℝ => X t α) := by
      have hpair : Continuous (fun t : ℝ => ((t, α) : ℝ × M)) := by fun_prop
      have hCont'' : Continuous (Function.uncurry fun t x => X t x) :=
        continuousOn_univ.mp hCont
      exact hCont''.comp hpair
    exact hCont'.continuousOn.mono (Set.subset_univ _)
  have hcompactL : IsCompact (Set.Icc (0 : ℝ) L) := isCompact_Icc
  have hnonemptyL : (Set.Icc (0 : ℝ) L).Nonempty := ⟨0, by simp [hL.le]⟩
  obtain ⟨Mctr, hMctr⟩ :
      ∃ Mctr : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) L, ‖f t x₀‖ ≤ Mctr := by
    have hbdd : Bornology.IsBounded ((fun t : ℝ => ‖f t x₀‖) '' Set.Icc 0 L) :=
      (hcompactL.image_of_continuousOn (hCont_at_centre.norm)).isBounded
    obtain ⟨C, hC⟩ := hbdd.subset_closedBall 0
    refine ⟨C, fun t ht => ?_⟩
    have := hC (Set.mem_image_of_mem _ ht)
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using this
  set a : ℝ := r / 2 with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; linarith
  set r' : ℝ := r / 4 with hr'_def
  have hr'_pos : 0 < r' := by rw [hr'_def]; linarith
  have hr'_lt_a : r' < a := by rw [hr'_def, ha_def]; linarith
  set Lbound : ℝ := max Mctr 0 + K * a + 1 with hLbound_def
  have hLbound_pos : 0 < Lbound := by
    have hKa : 0 ≤ K * a := mul_nonneg hK ha_pos.le
    have hM0 : 0 ≤ max Mctr 0 := le_max_right _ _
    rw [hLbound_def]; linarith
  set T : ℝ := min L ((a - r') / (Lbound + 1)) with hT_def
  have hT_pos : 0 < T := by
    have hLb1 : 0 < Lbound + 1 := by linarith
    have hdiff : 0 < a - r' := by linarith
    have hdiv : 0 < (a - r') / (Lbound + 1) := by positivity
    rw [hT_def]
    exact lt_min hL hdiv
  have hT_le_L : T ≤ L := min_le_left _ _
  set aN : NNReal := Real.toNNReal a
  set rN : NNReal := Real.toNNReal r'
  set LboundN : NNReal := Real.toNNReal Lbound
  set Kn : NNReal := Real.toNNReal K
  have haN : (aN : ℝ) = a := Real.coe_toNNReal _ ha_pos.le
  have hrN : (rN : ℝ) = r' := Real.coe_toNNReal _ hr'_pos.le
  have hLboundN : (LboundN : ℝ) = Lbound := Real.coe_toNNReal _ hLbound_pos.le
  have hLipt_closed :
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        LipschitzOnWith Kn (f t) (Metric.closedBall x₀ aN) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) L := ⟨ht.1, ht.2.trans hT_le_L⟩
    have hLip_open : LipschitzOnWith Kn (f t) (Metric.ball x₀ r) :=
      hLipt t ht'
    refine hLip_open.mono (fun y hy => ?_)
    have hy_le : dist y x₀ ≤ a := by
      rw [Metric.mem_closedBall, haN] at hy
      exact hy
    have ha_lt_r : a < r := by rw [ha_def]; linarith
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hy_le ha_lt_r)
  have hnorm_le :
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Metric.closedBall x₀ aN,
        ‖f t y‖ ≤ Lbound := by
    intro t ht y hy
    have ht' : t ∈ Set.Icc (0 : ℝ) L := ⟨ht.1, ht.2.trans hT_le_L⟩
    have hy_open : y ∈ Metric.ball x₀ r := by
      have hy_le : dist y x₀ ≤ a := by
        rw [Metric.mem_closedBall, haN] at hy
        exact hy
      have ha_lt_r : a < r := by rw [ha_def]; linarith
      exact Metric.mem_ball.mpr (lt_of_le_of_lt hy_le ha_lt_r)
    have h_x₀_open : x₀ ∈ Metric.ball x₀ r := Metric.mem_ball_self hr
    have hLip := (hLipt t ht').dist_le_mul y hy_open x₀ h_x₀_open
    have hdist : dist y x₀ ≤ a := by
      rw [Metric.mem_closedBall, haN] at hy
      exact hy
    have hMctr_t : ‖f t x₀‖ ≤ max Mctr 0 :=
      le_trans (hMctr t ht') (le_max_left _ _)
    have hKKn_eq : (Kn : ℝ) = K := Real.coe_toNNReal _ hK
    calc ‖f t y‖
        ≤ ‖f t y - f t x₀‖ + ‖f t x₀‖ := norm_le_norm_sub_add _ _
      _ = dist (f t y) (f t x₀) + ‖f t x₀‖ := by rw [dist_eq_norm]
      _ ≤ (Kn : ℝ) * dist y x₀ + ‖f t x₀‖ := by
          gcongr
      _ ≤ K * a + max Mctr 0 := by
          rw [hKKn_eq]; gcongr
      _ ≤ Lbound := by rw [hLbound_def]; linarith
  have hcont_closed :
      ∀ y ∈ Metric.closedBall x₀ aN,
        ContinuousOn (fun t : ℝ => f t y) (Set.Icc 0 T) := by
    intro y _
    set z : M := (chartAt H α).symm (I.symm y) with hz_def
    have hrw : (fun t : ℝ => f t y) = fun t : ℝ => (X t z : E) := by
      funext t; rfl
    rw [hrw]
    have hCont' : Continuous (fun t : ℝ => X t z) := by
      have hpair : Continuous (fun t : ℝ => ((t, z) : ℝ × M)) := by fun_prop
      have hCont'' : Continuous (Function.uncurry fun t x => X t x) :=
        continuousOn_univ.mp hCont
      exact hCont''.comp hpair
    exact hCont'.continuousOn.mono (Set.subset_univ _)
  have hT0 : (0 : ℝ) ≤ T := hT_pos.le
  set t₀_set : Set.Icc (0 : ℝ) T := ⟨0, by simp [hT0]⟩
  have hmul_max :
      (LboundN : ℝ) * max (T - (t₀_set : ℝ)) ((t₀_set : ℝ) - 0) ≤ aN - rN := by
    have hLb1 : (0 : ℝ) < Lbound + 1 := by linarith
    have hT_le : T ≤ (a - r') / (Lbound + 1) := min_le_right _ _
    have hdiff : 0 ≤ a - r' := by linarith
    have hcore : Lbound * T ≤ a - r' := by
      calc Lbound * T
          ≤ Lbound * ((a - r') / (Lbound + 1)) := by
              have hLb_nn : 0 ≤ Lbound := hLbound_pos.le
              exact mul_le_mul_of_nonneg_left hT_le hLb_nn
        _ = (Lbound / (Lbound + 1)) * (a - r') := by ring
        _ ≤ 1 * (a - r') := by
              apply mul_le_mul_of_nonneg_right _ hdiff
              rw [div_le_one hLb1]; linarith
        _ = a - r' := one_mul _
    have ht₀_val : (t₀_set : ℝ) = 0 := rfl
    have hmax_eq : max (T - (t₀_set : ℝ)) ((t₀_set : ℝ) - 0) = T := by
      rw [ht₀_val]; simp [hT0]
    rw [hmax_eq]
    have : (aN - rN : ℝ) = a - r' := by
      push_cast [haN, hrN]; ring
    calc (LboundN : ℝ) * T = Lbound * T := by rw [hLboundN]
      _ ≤ a - r' := hcore
      _ = ((aN : ℝ) - (rN : ℝ)) := by rw [this]
  have hPL :
      IsPicardLindelof f (tmin := 0) (tmax := T) t₀_set x₀ aN rN LboundN Kn := by
    refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · intro t ht; exact hLipt_closed t ht
    · intro y hy; exact hcont_closed y hy
    · intro t ht y hy
      have hLb := hnorm_le t ht y hy
      have : (LboundN : ℝ) = Lbound := hLboundN
      rw [this]; exact hLb
    · exact hmul_max
  obtain ⟨flow, hflow⟩ :=
    hPL.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  refine ⟨T, hT_pos, r', hr'_pos, flow, ?_⟩
  intro y hy
  have hy' : y ∈ Metric.closedBall x₀ rN := by
    rw [Metric.mem_closedBall] at hy ⊢
    rw [hrN]; exact hy
  obtain ⟨h_initial, h_flow⟩ := hflow y hy'
  refine ⟨?_, ?_⟩
  · have : flow y (t₀_set : ℝ) = y := h_initial
    simpa [t₀_set] using this
  · intro t ht
    have hd := h_flow t ht
    exact hd
end DifferentialGeometry.Analysis.ODE
