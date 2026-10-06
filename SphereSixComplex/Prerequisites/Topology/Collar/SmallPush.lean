module

public import SphereSixComplex.Prerequisites.Topology.Collar.OpenPush

/-! # Small positive collar pushes -/

@[expose] public section

open Set Topology

namespace SphereSixComplex.OpenTopologicalCollar

variable {X : Type*} [TopologicalSpace X] {B : Set X}

theorem push_pos_notMem_boundary (c : OpenTopologicalCollar X B)
    (w : c.PushWeight) (s : unitInterval) (hs : 0 < s) (x : X) :
    c.push w.weight s x ∉ B := by
  by_cases hx : x ∈ B
  · let p := c.chart.symm ⟨x, c.boundary_subset hx⟩
    have hp : (c.chart p).1 = x := congrArg Subtype.val (c.chart.apply_symm_apply _)
    rw [← hp, push_chart, c.chart_mem_boundary]
    intro h
    have hw : w.weight (c.chart p).1 = 1 := hp ▸ w.one_boundary x hx
    have hv := congrArg (fun t : TopologicalCollarParameter ↦ (t : ℝ)) h
    change max (p.2 : ℝ) ((s : ℝ) * (w.weight (c.chart p).1 : ℝ) / 2) = 0 at hv
    rw [hw, Set.Icc.coe_one, mul_one] at hv
    have hpos : 0 < (s : ℝ) := hs
    have := le_max_right (p.2 : ℝ) ((s : ℝ) / 2)
    linarith
  · exact c.push_notMem_boundary w.weight s hx

/-- A compact boundary remains in any prescribed neighborhood during a sufficiently short
positive collar push. -/
theorem exists_pos_forall_push_mem (c : OpenTopologicalCollar X B)
    (w : c.PushWeight) (hBc : IsCompact B) {V : Set X}
    (hV : IsOpen V) (hBV : B ⊆ V) :
    ∃ τ : unitInterval, 0 < τ ∧
      ∀ (s : unitInterval), s ≤ τ → ∀ b ∈ B, c.push w.weight s b ∈ V := by
  have hcont := c.continuous_push w.weight w.inner w.closure_subset w.zero_outside
  obtain ⟨U, W, hU, _, hzero, hBW, hUW⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : unitInterval))) hBc
      (hV.preimage hcont) (by
        rintro ⟨s, b⟩ ⟨hs, hb⟩
        have hs0 : s = 0 := hs
        subst s
        change c.push w.weight 0 b ∈ V
        simpa only [push_zero] using hBV hb)
  obtain ⟨t, ht, htU⟩ := exists_Ico_subset_of_mem_nhds
    (hU.mem_nhds (hzero (mem_singleton 0))) ⟨(1 : unitInterval), zero_lt_one⟩
  obtain ⟨τ, hτ, hτt⟩ := exists_between ht
  refine ⟨τ, hτ, ?_⟩
  intro s hs b hb
  exact hUW (show (s, b) ∈ U ×ˢ W from ⟨htU ⟨bot_le, hs.trans_lt hτt⟩, hBW hb⟩)

end SphereSixComplex.OpenTopologicalCollar
