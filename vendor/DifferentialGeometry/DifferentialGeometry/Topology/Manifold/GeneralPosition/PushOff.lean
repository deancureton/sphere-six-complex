module

public import DifferentialGeometry.Topology.Manifold.GeneralPosition.GeneralPosition

@[expose] public section

namespace DifferentialGeometry.Topology

open Metric Set unitInterval _root_.Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

theorem exists_push_off_center [T2Space M] (hn : 3 ≤ n)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {c : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ φ.target) {F : I × I → M}
    (hF : Continuous F) :
    ∃ F' : I × I → M, Continuous F' ∧ (∀ z, F' z ≠ φ.symm c) ∧
      (∀ z, ¬ (F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R) → F' z = F z) ∧
      (∀ z, F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R → F' z ∈ φ.source ∧ ‖φ (F' z) - c‖ < R) := by
  classical
  have h14 : R / 4 < R / 2 := by linarith
  have h24 : R / 2 < 3 * R / 4 := by linarith
  have hsub2 : closedBall c (R / 2) ⊆ φ.target :=
    (closedBall_subset_closedBall (by linarith)).trans hsub
  have hsub3 : closedBall c (3 * R / 4) ⊆ φ.target :=
    (closedBall_subset_closedBall (by linarith)).trans hsub
  have hball : ball c R ⊆ φ.target := ball_subset_closedBall.trans hsub
  have hc : c ∈ φ.target := hsub (mem_closedBall_self hR.le)
  set κ : M → ℝ := chartCutoff φ c (R / 4) (R / 2) with hκ
  set μ : M → ℝ := chartCutoff φ c (R / 2) (3 * R / 4) with hμ
  have hf : Continuous fun z : I × I => μ (F z) • (φ (F z) - c) :=
    (continuous_chartCutoff_smul h24 hsub3).comp hF
  obtain ⟨g, d, hg, hd, hgf, hgd⟩ :=
    exists_continuous_near_avoiding hn hf (ε := R / 8) (by linarith)
  set f : I × I → EuclideanSpace ℝ (Fin n) := fun z => μ (F z) • (φ (F z) - c) with hf_def
  set lam : I × I → ℝ := fun z => κ (F z) with hlam
  have hlamc : Continuous lam := (chartCutoff_continuous h14 hsub2).comp hF
  set H : I × I → EuclideanSpace ℝ (Fin n) :=
    fun z => (1 - lam z) • φ (F z) + lam z • (c + g z - d) with hH
  have hHz : ∀ z, H z = (1 - lam z) • φ (F z) + lam z • (c + g z - d) := fun z => rfl
  have hlam01 : ∀ z, lam z ∈ Icc (0 : ℝ) 1 := fun z => chartCutoff_mem_Icc (F z)
  have hlam_pos : ∀ z, 0 < lam z → F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R / 2 :=
    fun z h => lt_of_chartCutoff_pos h14 h
  have hf_eq : ∀ z, 0 < lam z → f z = φ (F z) - c := by
    intro z h
    have hμ1 : μ (F z) = 1 := chartCutoff_eq_one h24 (hlam_pos z h).1 (hlam_pos z h).2.le
    change μ (F z) • (φ (F z) - c) = φ (F z) - c
    rw [hμ1, one_smul]
  have hH_zero : ∀ z, lam z = 0 → H z = φ (F z) := by
    intro z h
    rw [hHz, h]; simp
  have hH_one : ∀ z, lam z = 1 → H z - c = g z - d := by
    intro z h
    rw [hHz, h]
    simp only [sub_self, zero_smul, one_smul, zero_add]
    abel
  have hH_sub : ∀ z, 0 < lam z → H z - φ (F z) = lam z • (g z - f z - d) := by
    intro z h
    rw [hHz, hf_eq z h]
    module
  have hHnorm : ∀ z, 0 < lam z → ‖H z - φ (F z)‖ < R / 4 := by
    intro z h
    rw [hH_sub z h, norm_smul, Real.norm_of_nonneg (hlam01 z).1]
    have h1 : ‖g z - f z - d‖ < R / 4 :=
      (norm_sub_le _ _).trans_lt (by linarith [hgf z, hd])
    calc lam z * ‖g z - f z - d‖ ≤ ‖g z - f z - d‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (hlam01 z).2
      _ < R / 4 := h1
  have hHball : ∀ z, F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R → ‖H z - c‖ < R ∧ H z ≠ c := by
    intro z hz
    rcases (hlam01 z).1.lt_or_eq with hpos | hzero
    · have hsub' := hHnorm z hpos
      have hFz := hlam_pos z hpos
      refine ⟨?_, ?_⟩
      · calc ‖H z - c‖ = ‖(H z - φ (F z)) + (φ (F z) - c)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖H z - φ (F z)‖ + ‖φ (F z) - c‖ := norm_add_le _ _
          _ < R := by linarith
      · rcases (hlam01 z).2.lt_or_eq with hlt | heq
        · have h14' : R / 4 < ‖φ (F z) - c‖ := lt_of_chartCutoff_lt_one h14 hFz.1 hlt
          intro hHc
          rw [hHc, norm_sub_rev] at hsub'
          linarith
        · have h1 := hH_one z heq
          intro hHc
          rw [hHc, sub_self] at h1
          exact hgd z (sub_eq_zero.1 h1.symm)
    · have hHz' := hH_zero z hzero.symm
      refine ⟨by rw [hHz']; exact hz.2, ?_⟩
      rw [hHz']
      intro hφc
      have hκ1 : κ (F z) = 1 :=
        chartCutoff_eq_one h14 hz.1 (by rw [hφc, sub_self, norm_zero]; linarith)
      have : lam z = κ (F z) := rfl
      rw [this, hκ1] at hzero
      exact zero_ne_one hzero
  have hHtarget : ∀ z, F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R → H z ∈ φ.target := fun z hz =>
    hball (mem_ball_iff_norm.2 (hHball z hz).1)
  set S : Set (I × I) := {z | F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R} with hS
  have hSopen : IsOpen S := by
    have : S = F ⁻¹' (φ.symm '' ball c R) := by
      ext z
      simp only [hS, mem_ofPred_eq, mem_preimage, φ.symm_image_eq_source_inter_preimage hball,
        mem_inter_iff, mem_ball_iff_norm]
    rw [this]
    exact (φ.isOpen_image_symm_of_subset_target isOpen_ball hball).preimage hF
  have hcl : closure S ⊆ F ⁻¹' (φ.symm '' closedBall c R) := by
    refine closure_minimal (fun z hz => ⟨φ (F z), ?_, φ.left_inv hz.1⟩)
      ((isClosed_symm_image_closedBall hsub).preimage hF)
    rw [mem_closedBall_iff_norm]; exact hz.2.le
  have hcl' : ∀ z ∈ closure S, F z ∈ φ.source ∧ ‖φ (F z) - c‖ ≤ R := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hcl hz
    have hyt : y ∈ φ.target := hsub hy
    refine ⟨hyz ▸ φ.map_target hyt, ?_⟩
    rw [← hyz, φ.right_inv hyt, ← mem_closedBall_iff_norm]; exact hy
  have hfront : ∀ z ∈ frontier S, φ.symm (H z) = F z := by
    intro z hz
    rw [hSopen.frontier_eq] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨hzs, hzR⟩ := hcl' z hz1
    have hR' : ‖φ (F z) - c‖ = R := le_antisymm hzR (not_lt.1 fun h => hz2 ⟨hzs, h⟩)
    have hlam0 : lam z = 0 := chartCutoff_eq_zero h14 (Or.inr (by rw [hR']; linarith))
    rw [hH_zero z hlam0, φ.left_inv hzs]
  have hHcont : ContinuousOn H (closure S) := by
    have hFc : ContinuousOn (fun z => φ (F z)) (closure S) :=
      φ.continuousOn.comp hF.continuousOn fun z hz => (hcl' z hz).1
    exact ((continuousOn_const.sub hlamc.continuousOn).smul hFc).add
      (hlamc.continuousOn.smul ((continuousOn_const.add hg.continuousOn).sub continuousOn_const))
  have hHmaps : MapsTo H (closure S) φ.target := by
    intro z hz
    by_cases hzS : z ∈ S
    · exact hHtarget z hzS
    · obtain ⟨hzs, hzR⟩ := hcl' z hz
      have hR' : ‖φ (F z) - c‖ = R := le_antisymm hzR (not_lt.1 fun h => hzS ⟨hzs, h⟩)
      have hlam0 : lam z = 0 := chartCutoff_eq_zero h14 (Or.inr (by rw [hR']; linarith))
      rw [hH_zero z hlam0]
      exact φ.map_source hzs
  have hsymmH : ContinuousOn (fun z => φ.symm (H z)) (closure S) :=
    φ.continuousOn_symm.comp hHcont hHmaps
  refine ⟨fun z => if F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R then φ.symm (H z) else F z,
    ?_, ?_, ?_, ?_⟩
  · exact continuous_if hfront hsymmH hF.continuousOn
  · intro z hz
    by_cases hzS : F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R
    · dsimp only at hz
      rw [ite_eq_left hzS] at hz
      have h1 := congrArg φ hz
      rw [φ.right_inv (hHtarget z hzS), φ.right_inv hc] at h1
      exact (hHball z hzS).2 h1
    · dsimp only at hz
      rw [ite_eq_right hzS] at hz
      refine hzS ⟨hz ▸ φ.map_target hc, ?_⟩
      rw [hz, φ.right_inv hc, sub_self, norm_zero]; exact hR
  · intro z hz
    exact ite_eq_right hz
  · intro z hz
    dsimp only
    rw [ite_eq_left hz]
    refine ⟨φ.map_target (hHtarget z hz), ?_⟩
    rw [φ.right_inv (hHtarget z hz)]
    exact (hHball z hz).1

theorem exists_chartBall_retraction [T2Space M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {c : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ φ.target) :
    ∃ r : M → M, ContinuousOn r {φ.symm c}ᶜ ∧
      (∀ x, ¬ (x ∈ φ.source ∧ ‖φ x - c‖ < R) → r x = x) ∧
      (∀ x, x ≠ φ.symm c → x ∈ φ.source ∧ ‖φ x - c‖ < R →
        r x ∈ φ.source ∧ ‖φ (r x) - c‖ = R) := by
  classical
  have hball : ball c R ⊆ φ.target := ball_subset_closedBall.trans hsub
  have hc : c ∈ φ.target := hsub (mem_closedBall_self hR.le)
  set ρ : M → EuclideanSpace ℝ (Fin n) := fun x => c + R • radialProj (φ x - c) with hρ
  have hρnorm : ∀ x, φ x - c ≠ 0 → ‖ρ x - c‖ = R := by
    intro x hx
    change ‖c + R • radialProj (φ x - c) - c‖ = R
    rw [add_sub_cancel_left, norm_smul, norm_radialProj hx, Real.norm_of_nonneg hR.le, mul_one]
  have hρtarget : ∀ x, φ x - c ≠ 0 → ρ x ∈ φ.target := fun x hx =>
    hsub (mem_closedBall_iff_norm.2 (hρnorm x hx).le)
  have hne : ∀ x, x ≠ φ.symm c → x ∈ φ.source → φ x - c ≠ 0 := by
    intro x hx hxs h
    apply hx
    rw [← φ.left_inv hxs, sub_eq_zero.1 h]
  set S : Set M := {x | x ∈ φ.source ∧ ‖φ x - c‖ < R} with hS
  have hSopen : IsOpen S := by
    have : S = φ.symm '' ball c R := by
      ext x
      simp only [hS, mem_ofPred_eq, φ.symm_image_eq_source_inter_preimage hball, mem_inter_iff,
        mem_preimage, mem_ball_iff_norm]
    rw [this]
    exact φ.isOpen_image_symm_of_subset_target isOpen_ball hball
  have hcl : closure S ⊆ φ.symm '' closedBall c R := by
    refine closure_minimal (fun x hx => ⟨φ x, ?_, φ.left_inv hx.1⟩)
      (isClosed_symm_image_closedBall hsub)
    rw [mem_closedBall_iff_norm]; exact hx.2.le
  have hcl' : ∀ x ∈ closure S, x ∈ φ.source ∧ ‖φ x - c‖ ≤ R := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcl hx
    have hyt : y ∈ φ.target := hsub hy
    refine ⟨hyx ▸ φ.map_target hyt, ?_⟩
    rw [← hyx, φ.right_inv hyt, ← mem_closedBall_iff_norm]; exact hy
  refine ⟨fun x => if x ∈ φ.source ∧ ‖φ x - c‖ < R then φ.symm (ρ x) else x, ?_, ?_, ?_⟩
  · refine ContinuousOn.if ?_ ?_ continuousOn_id
    · rintro x ⟨hxc, hxf⟩
      rw [hSopen.frontier_eq] at hxf
      obtain ⟨hx1, hx2⟩ := hxf
      obtain ⟨hxs, hxR⟩ := hcl' x hx1
      have hR' : ‖φ x - c‖ = R := le_antisymm hxR (not_lt.1 fun h => hx2 ⟨hxs, h⟩)
      have hρx : ρ x = φ x := by
        change c + R • radialProj (φ x - c) = φ x
        rw [radialProj, hR', smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
      rw [hρx, φ.left_inv hxs]
    · have hne' : ∀ x ∈ {φ.symm c}ᶜ ∩ closure S, φ x - c ≠ 0 := fun x hx =>
        hne x hx.1 (hcl' x hx.2).1
      have hρc : ContinuousOn ρ ({φ.symm c}ᶜ ∩ closure S) := by
        have hφc : ContinuousOn (fun x => φ x - c) ({φ.symm c}ᶜ ∩ closure S) :=
          (φ.continuousOn.mono fun x hx => (hcl' x hx.2).1).sub continuousOn_const
        have : ContinuousOn (fun x => radialProj (φ x - c)) ({φ.symm c}ᶜ ∩ closure S) := by
          simp only [radialProj]
          exact (hφc.norm.inv₀ fun x hx => norm_ne_zero_iff.2 (hne' x hx)).smul hφc
        exact continuousOn_const.add (this.const_smul R)
      exact φ.continuousOn_symm.comp hρc fun x hx => hρtarget x (hne' x hx)
  · intro x hx
    exact ite_eq_right hx
  · intro x hx hxS
    dsimp only
    rw [ite_eq_left hxS]
    have hx0 := hne x hx hxS.1
    refine ⟨φ.map_target (hρtarget x hx0), ?_⟩
    rw [φ.right_inv (hρtarget x hx0)]
    exact hρnorm x hx0

section ChartDisk

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem isChartDisk.exists_push_off [T2Space M] (hn : 3 ≤ n) {e : Disk n → M}
    (he : isChartDisk e) {F : I × I → M} (hF : Continuous F) :
    ∃ F' : I × I → M, Continuous F' ∧ (∀ z, F' z ∉ e '' diskInterior n) ∧
      (∀ z, F z ∉ e '' diskInterior n → F' z = F z) ∧
      (∀ z, F z ∈ e '' diskInterior n → F' z ∈ range e) := by
  obtain ⟨φ, c, r, -, hr, hsub, he⟩ := he
  simp only [mem_image_diskInterior_iff hr hsub he, mem_range_chartDisk_iff hr hsub he]
  obtain ⟨F₁, hF₁, hne, hfix, hin⟩ := exists_push_off_center hn φ hr hsub hF
  obtain ⟨ret, hret, hretfix, hretin⟩ := exists_chartBall_retraction φ hr hsub
  refine ⟨fun z => ret (F₁ z), hret.comp_continuous hF₁ fun z => hne z, ?_, ?_, ?_⟩
  · intro z hz
    dsimp only at hz
    by_cases h₁ : F₁ z ∈ φ.source ∧ ‖φ (F₁ z) - c‖ < r
    · have := (hretin (F₁ z) (hne z) h₁).2
      rw [this] at hz
      exact lt_irrefl _ hz.2
    · rw [hretfix _ h₁] at hz
      exact h₁ hz
  · intro z hz
    dsimp only
    rw [hfix z hz, hretfix _ hz]
  · intro z hz
    dsimp only
    by_cases h₁ : F₁ z ∈ φ.source ∧ ‖φ (F₁ z) - c‖ < r
    · obtain ⟨h1, h2⟩ := hretin (F₁ z) (hne z) h₁
      exact ⟨h1, h2.le⟩
    · rw [hretfix _ h₁]
      exact ⟨(hin z hz).1, (hin z hz).2.le⟩

theorem exists_push_off_two [T2Space M] (hn : 3 ≤ n) {e₀ e₁ : Disk n → M}
    (h₀ : isChartDisk e₀) (h₁ : isChartDisk e₁) (hdisj : Disjoint (range e₀) (range e₁))
    {F : I × I → M} (hF : Continuous F) :
    ∃ F' : I × I → M, Continuous F' ∧
      (∀ z, F' z ∈ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ) ∧
      (∀ z, F z ∈ (e₀ '' diskInterior n ∪ e₁ '' diskInterior n)ᶜ → F' z = F z) := by
  obtain ⟨F₁, hF₁, hne₁, hfix₁, -⟩ := h₀.exists_push_off hn hF
  obtain ⟨F₂, hF₂, hne₂, hfix₂, hin₂⟩ := h₁.exists_push_off hn hF₁
  refine ⟨F₂, hF₂, fun z => ?_, fun z hz => ?_⟩
  · simp only [mem_compl_iff, mem_union, not_or]
    refine ⟨fun hz => ?_, hne₂ z⟩
    by_cases h : F₁ z ∈ e₁ '' diskInterior n
    · exact Set.disjoint_left.1 hdisj (image_subset_range _ _ hz) (hin₂ z h)
    · rw [hfix₂ z h] at hz
      exact hne₁ z hz
  · simp only [mem_compl_iff, mem_union, not_or] at hz
    rw [hfix₂ z (by rw [hfix₁ z hz.1]; exact hz.2), hfix₁ z hz.1]

end ChartDisk

end DifferentialGeometry.Topology
