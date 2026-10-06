module

public import DifferentialGeometry.Topology.Morse.Cancellation.Flow.CancelFlowQ2

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split recombine_decompose)
open CancelModel

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

variable {f : M → ℝ}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} (c : IndexZeroCancellingPair I f a' b' p q)

def pClosedAnnulus : Set M := c.e.χ '' {y | c.ρs ≤ morseNorm n y ∧ morseNorm n y ≤ c.ρB}

theorem isCompact_pClosedAnnulus : IsCompact c.pClosedAnnulus :=
  (c.e.isCompact_image_le c.ρB_lt_R').of_isClosed_subset
    (c.e.isCompact_image_of_subset
      ((isCompact_morseNorm_le c.ρB).of_isClosed_subset
        ((isClosed_le continuous_const continuous_morseNorm).inter
          (isClosed_le continuous_morseNorm continuous_const)) fun _ hy => hy.2)
      c.ρB_lt_R' fun _ hy => hy.2).isClosed (image_mono fun _ hy => hy.2)

theorem pClosedAnnulus_subset_pClosedBall : c.pClosedAnnulus ⊆ c.pClosedBall := image_mono fun _ hy => hy.2

theorem pClosedAnnulus_subset_pBall' : c.pClosedAnnulus ⊆ c.pBall' := c.pClosedAnnulus_subset_pClosedBall.trans c.pClosedBall_subset_pBall'

theorem symm_mem_of_mem_pClosedAnnulus {x : M} (hx : x ∈ c.pClosedAnnulus) :
    c.ρs ≤ morseNorm n (c.e.χ.symm x) ∧ morseNorm n (c.e.χ.symm x) ≤ c.ρB := by
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [c.chart_p_symm_eq' (c.sq_lt_three_ε_of_le_ρB hy.2)]

theorem mem_pClosedAnnulus_of_symm {x : M} (hx : x ∈ c.pBall')
    (h : c.ρs ≤ morseNorm n (c.e.χ.symm x) ∧ morseNorm n (c.e.χ.symm x) ≤ c.ρB) : x ∈ c.pClosedAnnulus :=
  c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball hx) h

theorem symm_sq_lt_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') :
    morseNorm n (c.e.χ.symm x) ^ 2 < 3 * c.ε := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' hy]; exact hy

theorem symm_ne_zero_of_mem_pClosedAnnulus {x : M} (hx : x ∈ c.pClosedAnnulus) : c.e.χ.symm x ≠ 0 := by
  intro h
  have := (c.symm_mem_of_mem_pClosedAnnulus hx).1
  rw [h, morseNorm_zero] at this
  linarith [c.ρs_pos]

theorem f_eq_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') :
    f x = f p + morseNorm n (c.e.χ.symm x) ^ 2 / 2 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [c.chart_p_symm_eq' hy]
  exact c.f_chart_p ((c.morseNorm_lt_rmp_of_sq_lt hy).le.trans (c.D.hrm p c.hp).2)

theorem f_le_lo₂_of_mem_pClosedAnnulus {x : M} (hx : x ∈ c.pClosedAnnulus) : f x ≤ c.lo₂ := by
  rw [c.f_eq_of_mem_pBall' (c.pClosedAnnulus_subset_pBall' hx)]
  have h := (c.symm_mem_of_mem_pClosedAnnulus hx).2
  have h2 := c.ρB_sq_eq
  have := pow_le_pow_left₀ (ModelField.morseNorm_nonneg _) h 2
  linarith

theorem a'_lt_f_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') : a' < f x := by
  rw [c.f_eq_of_mem_pBall' hx]
  have := c.f_p_mem.1
  nlinarith [sq_nonneg (morseNorm n (c.e.χ.symm x))]

theorem a'_lt_lo₂ : a' < c.lo₂ := by
  have := c.a'_lt_c₁_sub_η; have := c.η_pos; unfold lo₂; linarith

theorem mem_pClosedAnnulus_of_mem_middleTube_lo₂ (k : c.CancelConsts) (hk : k.Good) {x : M} (hx : x ∈ k.middleTube)
    (hf : f x = c.lo₂) : x ∈ c.pClosedAnnulus := by
  obtain ⟨hp, hρ⟩ := hk.closedFlowTube_lo₂_radius hx.1 hf
  exact c.mem_pClosedAnnulus_of_symm hp ⟨by rw [hρ]; exact c.ρs_lt_ρB.le, hρ.le⟩

theorem mem_qPositiveRegion_of_mem_middleTube_hi₁ (k : c.CancelConsts) (hk : k.Good) {x : M} (hx : x ∈ k.middleTube)
    (hf : f x = c.hi₁) : x ∈ k.qPositiveRegion :=
  k.closedFlowTube_high_subset_qPositiveRegion hk ⟨hx.1, hf.ge⟩

theorem notMem_pBall'_of_mem_qBall' {x : M} (hx : x ∈ c.qBall') : x ∉ c.pBall' :=
  fun h => c.disjoint_pBall'_qBall'.notMem_of_mem_left h hx

theorem notMem_qBall'_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') : x ∉ c.qBall' :=
  fun h => c.disjoint_pBall'_qBall'.notMem_of_mem_left hx h

open scoped Classical in
def lyapunovFunction (x : M) : ℝ :=
  if x ∈ c.pBall' then axialDefect c.e₁ (c.e.χ.symm x)
  else if x ∈ c.qBall' then c.qAxialDefect (c.d.χ.symm x)
  else if x ∈ c.orientedChartTube then c.sheetAxialDefect (c.ζ x) else 0

theorem lyapunovFunction_of_mem_pBall' {x : M} (hx : x ∈ c.pBall') : c.lyapunovFunction x = axialDefect c.e₁ (c.e.χ.symm x) := by
  classical simp [lyapunovFunction, hx]

theorem lyapunovFunction_of_mem_qBall' {x : M} (hx : x ∈ c.qBall') : c.lyapunovFunction x = c.qAxialDefect (c.d.χ.symm x) := by
  classical simp [lyapunovFunction, hx, c.notMem_pBall'_of_mem_qBall' hx]

theorem lyapunovFunction_of_mem_tube {x : M} (hp : x ∉ c.pBall') (hq : x ∉ c.qBall') (hT : x ∈ c.orientedChartTube) :
    c.lyapunovFunction x = c.sheetAxialDefect (c.ζ x) := by
  classical simp [lyapunovFunction, hp, hq, hT]

theorem lyapunovFunction_nonneg (x : M) : 0 ≤ c.lyapunovFunction x := by
  classical
  unfold lyapunovFunction
  split_ifs
  · exact axialDefect_nonneg c.morseNorm_e₁ _
  · exact c.qAxialDefect_nonneg _
  · exact c.sheetAxialDefect_nonneg _
  · exact le_rfl

theorem continuousAt_axialDefect_symm {x : M} (hx : x ∈ c.pBall') (h0 : c.e.χ.symm x ≠ 0) :
    ContinuousAt (fun w => axialDefect c.e₁ (c.e.χ.symm w)) x :=
  (contDiffAt_axialDefect c.e₁ h0).continuousAt.comp
    (c.e.contMDiffAt_symm (c.pBall'_subset_image_ball hx)).continuousAt

namespace CancelConsts

variable {c} (k : c.CancelConsts)

def crossingRegion : Set M := c.pClosedAnnulus ∪ k.middleTube ∪ k.qPositiveRegion

theorem isCompact_crossingRegion (hk : k.Good) : IsCompact k.crossingRegion :=
  (c.isCompact_pClosedAnnulus.union k.isCompact_middleTube).union (k.isCompact_qPositiveRegion hk)

theorem pClosedAnnulus_subset_crossingRegion : c.pClosedAnnulus ⊆ k.crossingRegion := fun _ hx => Or.inl (Or.inl hx)

theorem middleTube_subset_crossingRegion : k.middleTube ⊆ k.crossingRegion := fun _ hx => Or.inl (Or.inr hx)

theorem qPositiveRegion_subset_crossingRegion : k.qPositiveRegion ⊆ k.crossingRegion := fun _ hx => Or.inr hx

theorem a'_lt_f_of_mem_crossingRegion (hk : k.Good) {x : M} (hx : x ∈ k.crossingRegion) : a' < f x := by
  rcases hx with (h | h) | h
  · exact c.a'_lt_f_of_mem_pBall' (c.pClosedAnnulus_subset_pBall' h)
  · exact c.a'_lt_lo₂.trans_le h.2.1
  · exact c.a'_lt_lo₂.trans (c.lo₂_lt_hi₁.trans_le (k.hi₁_le_f_of_mem_qRegion hk (k.qPositiveRegion_subset_qRegion h)))

theorem notMem_crossingRegion_of_f_le (hk : k.Good) {x : M} (hx : f x ≤ a') : x ∉ k.crossingRegion :=
  fun h => absurd (k.a'_lt_f_of_mem_crossingRegion hk h) (not_lt.2 hx)

theorem mem_middleTube_of_mem_crossingRegion (hk : k.Good) {x : M} (hx : x ∈ k.crossingRegion) (h1 : c.lo₂ < f x)
    (h2 : f x < c.hi₁) : x ∈ k.middleTube := by
  rcases hx with (h | h) | h
  · exact absurd (c.f_le_lo₂_of_mem_pClosedAnnulus h) (not_le.2 h1)
  · exact h
  · exact absurd (k.hi₁_le_f_of_mem_qRegion hk (k.qPositiveRegion_subset_qRegion h)) (not_le.2 h2)

theorem f_ge_lo₂_of_mem_qPositiveRegion (hk : k.Good) {x : M} (hx : x ∈ k.qPositiveRegion) : c.lo₂ ≤ f x :=
  c.lo₂_lt_hi₁.le.trans (k.hi₁_le_f_of_mem_qRegion hk (k.qPositiveRegion_subset_qRegion hx))

theorem qPositiveRegion_subset_qBall' (hk : k.Good) : k.qPositiveRegion ⊆ c.qBall' :=
  k.qPositiveRegion_subset_qRegion.trans (k.qRegion_subset_qBall' hk)

theorem lyapunovFunction_eq_sheetAxialDefect_ζ_of_mem_middleTube (hk : k.Good) {x : M} (hx : x ∈ k.middleTube) :
    c.lyapunovFunction x = c.sheetAxialDefect (c.ζ x) := by
  have hT := k.middleTube_subset_orientedChartTube hx
  have hζ : ‖c.ζ x‖ < hk.δ'' := (k.norm_ζ_le_of_mem_closedFlowTube hx.1).trans_lt hk.hδ'δ''
  by_cases hp : x ∈ c.pBall'
  · rw [c.lyapunovFunction_of_mem_pBall' hp, hk.sheetAxialDefect_eq_axialDefect hp hT hζ]
  by_cases hq : x ∈ c.qBall'
  · rw [c.lyapunovFunction_of_mem_qBall' hq]
    have hχ : c.d.χ (c.d.χ.symm x) = x := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
    have := qAxialDefect_eq_sheetAxialDefect_ζ (c := c) (c.symm_sq_lt_of_mem_qBall' hq) (by rw [hχ]; exact hT.1)
    rwa [hχ] at this
  · exact c.lyapunovFunction_of_mem_tube hp hq hT

theorem symm_ne_zero_of_mem_crossingRegion (hk : k.Good) {x : M} (hx : x ∈ k.crossingRegion) (hp : x ∈ c.pBall') :
    c.e.χ.symm x ≠ 0 := by
  rcases hx with (h | h) | h
  · exact c.symm_ne_zero_of_mem_pClosedAnnulus h
  · have hT := k.middleTube_subset_orientedChartTube h
    have hχ : c.e.χ (c.e.χ.symm x) = x := c.e.symm_image_eq (c.pBall'_subset_image_ball hp)
    exact c.ne_zero_of_mem_openChartTube (c.symm_sq_lt_of_mem_pBall' hp) (by rw [hχ]; exact hT.1)
  · exact absurd hp (c.notMem_pBall'_of_mem_qBall' (k.qPositiveRegion_subset_qBall' hk h))

theorem qNormProductSq_le_of_mem_crossingRegion (hk : k.Good) {x : M} (hx : x ∈ k.crossingRegion) (hq : x ∈ c.qBall') :
    c.qNormProductSq (c.d.χ.symm x) ≤ k.qNormProductBound := by
  rcases hx with (h | h) | h
  · exact absurd hq (c.notMem_qBall'_of_mem_pBall' (c.pClosedAnnulus_subset_pBall' h))
  · have hT := k.middleTube_subset_orientedChartTube h
    have hχ : c.d.χ (c.d.χ.symm x) = x := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
    have := (c.norm_ζ_le_iff_qNormProductSq_le k (c.symm_sq_lt_of_mem_qBall' hq) (by rw [hχ]; exact hT.1)).1
      (by rw [hχ]; exact k.norm_ζ_le_of_mem_closedFlowTube h.1)
    exact this
  · exact (k.symm_mem_qPositiveCoordinateRegion_of_mem_qPositiveRegion hk h).2.2.2

theorem σ_uq_nonneg_of_mem_crossingRegion (hk : k.Good) {x : M} (hx : x ∈ k.crossingRegion) (hq : x ∈ c.qBall') :
    0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) := by
  rcases hx with (h | h) | h
  · exact absurd hq (c.notMem_qBall'_of_mem_pBall' (c.pClosedAnnulus_subset_pBall' h))
  · have hT := k.middleTube_subset_orientedChartTube h
    have hχ : c.d.χ (c.d.χ.symm x) = x := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
    exact (c.σ_uq_pos_of_mem_orientedChartTube (c.symm_sq_lt_of_mem_qBall' hq) (by rw [hχ]; exact hT)).le
  · exact (k.symm_mem_qPositiveCoordinateRegion_of_mem_qPositiveRegion hk h).1

theorem σ_uq_pos_of_mem_middleTube {x : M} (hx : x ∈ k.middleTube) (hq : x ∈ c.qBall') :
    0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) := by
  have hT := k.middleTube_subset_orientedChartTube hx
  have hχ : c.d.χ (c.d.χ.symm x) = x := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
  exact c.σ_uq_pos_of_mem_orientedChartTube (c.symm_sq_lt_of_mem_qBall' hq) (by rw [hχ]; exact hT)

theorem continuousAt_qAxialDefect_symm (hk : k.Good) {x : M} (hx : x ∈ c.qBall')
    (hQ : c.qNormProductSq (c.d.χ.symm x) ≤ k.qNormProductBound) : ContinuousAt (fun w => c.qAxialDefect (c.d.χ.symm w)) x := by
  have h1 : ContinuousAt c.qAxialDefect (c.d.χ.symm x) :=
    (hk.continuousAt_sheetAxialDefect (k.norm_ζhat_lt_δ''_of_qNormProductSq_le hk hQ)).comp (c.continuousAt_ζhat _)
  exact h1.comp (c.d.contMDiffAt_symm (c.qBall'_subset_image_ball hx)).continuousAt

theorem continuousOn_lyapunovFunction_crossingRegion (hk : k.Good) : ContinuousOn c.lyapunovFunction k.crossingRegion := by
  intro z hz
  by_cases hp : z ∈ c.pBall'
  · have hev : (fun w => axialDefect c.e₁ (c.e.χ.symm w)) =ᶠ[𝓝 z] c.lyapunovFunction := by
      filter_upwards [c.isOpen_pBall'.mem_nhds hp] with w hw
      exact (c.lyapunovFunction_of_mem_pBall' hw).symm
    exact ((c.continuousAt_axialDefect_symm hp (k.symm_ne_zero_of_mem_crossingRegion hk hz hp)).congr
      hev).continuousWithinAt
  by_cases hq : z ∈ c.qBall'
  · have hev : (fun w => c.qAxialDefect (c.d.χ.symm w)) =ᶠ[𝓝 z] c.lyapunovFunction := by
      filter_upwards [c.isOpen_qBall'.mem_nhds hq] with w hw
      exact (c.lyapunovFunction_of_mem_qBall' hw).symm
    exact ((k.continuousAt_qAxialDefect_symm hk hq (k.qNormProductSq_le_of_mem_crossingRegion hk hz hq)).congr
      hev).continuousWithinAt
  have hzT : z ∈ k.middleTube := by
    rcases hz with (h | h) | h
    · exact absurd (c.pClosedAnnulus_subset_pBall' h) hp
    · exact h
    · exact absurd (k.qPositiveRegion_subset_qBall' hk h) hq
  have hlo : c.lo₂ < f z := by
    rcases hzT.2.1.eq_or_lt with h | h
    · exact absurd (c.pClosedAnnulus_subset_pBall' (c.mem_pClosedAnnulus_of_mem_middleTube_lo₂ k hk hzT h.symm)) hp
    · exact h
  have hhi : f z < c.hi₁ := by
    rcases hzT.2.2.eq_or_lt with h | h
    · exact absurd (k.qPositiveRegion_subset_qBall' hk (c.mem_qPositiveRegion_of_mem_middleTube_hi₁ k hk hzT h)) hq
    · exact h
  have hT := k.middleTube_subset_orientedChartTube hzT
  have hcont : ContinuousAt (fun w => c.sheetAxialDefect (c.ζ w)) z :=
    (hk.continuousAt_sheetAxialDefect ((k.norm_ζ_le_of_mem_closedFlowTube hzT.1).trans_lt hk.hδ'δ'')).comp
      (c.continuousOn_ζ.continuousAt (c.isOpen_openChartTube.mem_nhds hT.1))
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (k.lyapunovFunction_eq_sheetAxialDefect_ζ_of_mem_middleTube hk hzT)
  have hO : {w | c.lo₂ < f w ∧ f w < c.hi₁} ∈ 𝓝 z :=
    ((isOpen_lt continuous_const c.hfs.continuous).inter
      (isOpen_lt c.hfs.continuous continuous_const)).mem_nhds ⟨hlo, hhi⟩
  filter_upwards [nhdsWithin_le_nhds hO, self_mem_nhdsWithin] with w hw hwC
  exact k.lyapunovFunction_eq_sheetAxialDefect_ζ_of_mem_middleTube hk (k.mem_middleTube_of_mem_crossingRegion hk hwC hw.1 hw.2)

theorem isOpen_pBall'_sdiff : IsOpen (c.pBall' \ {p}) :=
  c.isOpen_pBall'.sdiff isClosed_singleton

theorem symm_p_eq_zero : c.e.χ.symm p = 0 := by
  have h := congrArg c.e.χ.symm c.e.hχ0
  rw [c.chart_p_symm_eq' (by rw [morseNorm_zero]; nlinarith [c.hε])] at h
  exact h.symm

theorem symm_ne_zero_iff {x : M} (hx : x ∈ c.pBall') : c.e.χ.symm x ≠ 0 ↔ x ≠ p := by
  have hχ : c.e.χ (c.e.χ.symm x) = x := c.e.symm_image_eq (c.pBall'_subset_image_ball hx)
  constructor
  · intro h hxp
    subst hxp
    exact h (symm_p_eq_zero (c := c))
  · intro h h0
    apply h
    rw [← hχ, h0, c.e.hχ0]

theorem exists_right_le_lyapunovFunction_of_mem_pBall' (hk : k.Good) {x : M} {t : ℝ} (hz : k.cancellationFlow t x ∈ k.crossingRegion)
    (hp : k.cancellationFlow t x ∈ c.pBall') :
    ∃ ε > 0, ∀ s ∈ Icc t (t + ε), c.lyapunovFunction (k.cancellationFlow s x) ≤ c.lyapunovFunction (k.cancellationFlow t x) := by
  have h0 := k.symm_ne_zero_of_mem_crossingRegion hk hz hp
  have hO : k.cancellationFlow t x ∈ c.pBall' \ {p} := ⟨hp, (symm_ne_zero_iff hp).1 h0⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open (isOpen_pBall'_sdiff (c := c)) hO
  refine ⟨ε, hε, fun s hs => ?_⟩
  have hall : ∀ u ∈ Icc t s, k.cancellationFlow u x ∈ c.pBall' \ {p} := fun u hu =>
    hεO u ⟨by linarith [hu.1], hu.2.trans hs.2⟩
  have hanti : AntitoneOn (fun u => axialDefect c.e₁ (c.e.χ.symm (k.cancellationFlow u x))) (Icc t s) := by
    refine antitoneOn_Icc_of_hasDerivAt_nonpos
      (g' := fun u => axialDefectDeriv c.e₁ (c.e.χ.symm (k.cancellationFlow u x)) (k.pCancellationField (c.e.χ.symm (k.cancellationFlow u x))))
      (fun u hu => k.hasDerivAt_axialDefect_cancellationFlow_p (hall u hu).1
        ((symm_ne_zero_iff (hall u hu).1).2 (hall u hu).2))
      (fun u hu => k.axialDefectDeriv_pCancellationField_nonpos (c.symm_sq_lt_of_mem_pBall' (hall u hu).1)
        ((symm_ne_zero_iff (hall u hu).1).2 (hall u hu).2))
  have h1 : axialDefect c.e₁ (c.e.χ.symm (k.cancellationFlow s x)) ≤ axialDefect c.e₁ (c.e.χ.symm (k.cancellationFlow t x)) :=
    hanti (left_mem_Icc.2 hs.1) (right_mem_Icc.2 hs.1) hs.1
  rw [c.lyapunovFunction_of_mem_pBall' (hall s (right_mem_Icc.2 hs.1)).1, c.lyapunovFunction_of_mem_pBall' hp]
  exact h1

theorem exists_right_le_lyapunovFunction_of_mem_qBall' (hk : k.Good) {x : M} {T t : ℝ}
    (hT : ∀ s ∈ Icc 0 T, k.cancellationFlow s x ∈ k.crossingRegion) (ht : t ∈ Ico 0 T) (hq : k.cancellationFlow t x ∈ c.qBall') :
    ∃ ε > 0, ∀ s ∈ Icc t (t + ε), s ≤ T → c.lyapunovFunction (k.cancellationFlow s x) ≤ c.lyapunovFunction (k.cancellationFlow t x) := by
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_qBall' hq
  refine ⟨ε, hε, fun s hs hsT => ?_⟩
  have hall : ∀ u ∈ Icc t s, k.cancellationFlow u x ∈ c.qBall' := fun u hu =>
    hεO u ⟨by linarith [hu.1], hu.2.trans hs.2⟩
  have hσ : ∀ u ∈ Icc t s, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow u x)) := fun u hu =>
    k.σ_uq_nonneg_of_mem_crossingRegion hk (hT u ⟨ht.1.trans hu.1, hu.2.trans hsT⟩) (hall u hu)
  have hQ := k.qNormProductSq_le_of_mem_crossingRegion hk (hT t ⟨ht.1, ht.2.le⟩) hq
  have := k.qAxialDefect_le_cancellationFlow hall hk hσ hQ s (right_mem_Icc.2 hs.1)
  rw [c.lyapunovFunction_of_mem_qBall' (hall s (right_mem_Icc.2 hs.1)), c.lyapunovFunction_of_mem_qBall' hq]
  exact this

theorem hasDerivAt_sheetAxialDefect_ζ_cancellationFlow (hk : k.Good) {x : M} {u : ℝ} (hu : k.cancellationFlow u x ∈ c.orientedChartTube)
    (h1 : c.lo₂ ≤ f (k.cancellationFlow u x)) (h2 : f (k.cancellationFlow u x) ≤ c.hi₁) (hζ : ‖c.ζ (k.cancellationFlow u x)‖ < hk.δ'') :
    HasDerivAt (fun s => c.sheetAxialDefect (c.ζ (k.cancellationFlow s x)))
      (-(2 * (c.lam * k.βm' (k.cancellationFlow u x))) * fderiv ℝ c.sheetAxialDefect (c.ζ (k.cancellationFlow u x)) (c.ζ (k.cancellationFlow u x))) u := by
  have h := (hk.hasFDerivAt_sheetAxialDefect hζ).comp_hasDerivAt u (k.hasDerivAt_ζ_cancellationFlow hu.1)
  rw [k.dζ_cancellationField_mid hu h1 h2] at h
  rw [← (hk.hasFDerivAt_sheetAxialDefect hζ).fderiv, map_smul, smul_eq_mul] at h
  exact h

theorem deriv_sheetAxialDefect_ζ_nonpos (hk : k.Good) {x : M} {u : ℝ} (hu : k.cancellationFlow u x ∈ c.orientedChartTube)
    (hζ : ‖c.ζ (k.cancellationFlow u x)‖ < hk.δ'') :
    -(2 * (c.lam * k.βm' (k.cancellationFlow u x))) * fderiv ℝ c.sheetAxialDefect (c.ζ (k.cancellationFlow u x)) (c.ζ (k.cancellationFlow u x)) ≤ 0 := by
  have _ := hu
  have h1 := hk.fderiv_sheetAxialDefect_self_nonneg hζ
  have h2 := k.βm'_nonneg (k.cancellationFlow u x)
  have h3 := c.lam_pos
  have : 0 ≤ 2 * (c.lam * k.βm' (k.cancellationFlow u x)) * fderiv ℝ c.sheetAxialDefect (c.ζ (k.cancellationFlow u x)) (c.ζ (k.cancellationFlow u x)) := by
    positivity
  linarith

theorem exists_right_le_lyapunovFunction_of_mem_middleTube (hk : k.Good) {x : M} {T t : ℝ}
    (hT : ∀ s ∈ Icc 0 T, k.cancellationFlow s x ∈ k.crossingRegion) (ht : t ∈ Ico 0 T) (hz : k.cancellationFlow t x ∈ k.middleTube)
    (hlo : c.lo₂ < f (k.cancellationFlow t x)) (hhi : f (k.cancellationFlow t x) < c.hi₁) :
    ∃ ε > 0, ∀ s ∈ Icc t (t + ε), s ≤ T → c.lyapunovFunction (k.cancellationFlow s x) ≤ c.lyapunovFunction (k.cancellationFlow t x) := by
  have hO : k.cancellationFlow t x ∈ c.orientedChartTube ∩ {w | c.lo₂ < f w ∧ f w < c.hi₁} :=
    ⟨k.middleTube_subset_orientedChartTube hz, hlo, hhi⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open (c.isOpen_orientedChartTube.inter
    ((isOpen_lt continuous_const c.hfs.continuous).inter
      (isOpen_lt c.hfs.continuous continuous_const))) hO
  refine ⟨ε, hε, fun s hs hsT => ?_⟩
  have hall : ∀ u ∈ Icc t s, k.cancellationFlow u x ∈ k.middleTube := fun u hu => by
    have hO' := hεO u ⟨by linarith [hu.1], hu.2.trans hs.2⟩
    exact k.mem_middleTube_of_mem_crossingRegion hk (hT u ⟨ht.1.trans hu.1, hu.2.trans hsT⟩) hO'.2.1 hO'.2.2
  have hζ : ∀ u ∈ Icc t s, ‖c.ζ (k.cancellationFlow u x)‖ < hk.δ'' := fun u hu =>
    (k.norm_ζ_le_of_mem_closedFlowTube (hall u hu).1).trans_lt hk.hδ'δ''
  have hanti : AntitoneOn (fun u => c.sheetAxialDefect (c.ζ (k.cancellationFlow u x))) (Icc t s) :=
    antitoneOn_Icc_of_hasDerivAt_nonpos
      (fun u hu => k.hasDerivAt_sheetAxialDefect_ζ_cancellationFlow hk (k.middleTube_subset_orientedChartTube (hall u hu))
        (hall u hu).2.1 (hall u hu).2.2 (hζ u hu))
      (fun u hu => k.deriv_sheetAxialDefect_ζ_nonpos hk (k.middleTube_subset_orientedChartTube (hall u hu)) (hζ u hu))
  have h1 : c.sheetAxialDefect (c.ζ (k.cancellationFlow s x)) ≤ c.sheetAxialDefect (c.ζ (k.cancellationFlow t x)) :=
    hanti (left_mem_Icc.2 hs.1) (right_mem_Icc.2 hs.1) hs.1
  rw [k.lyapunovFunction_eq_sheetAxialDefect_ζ_of_mem_middleTube hk (hall s (right_mem_Icc.2 hs.1)),
    k.lyapunovFunction_eq_sheetAxialDefect_ζ_of_mem_middleTube hk hz]
  exact h1

theorem antitoneOn_lyapunovFunction_cancellationFlow (hk : k.Good) {x : M} {T : ℝ} (hT : ∀ s ∈ Icc 0 T, k.cancellationFlow s x ∈ k.crossingRegion) :
    AntitoneOn (fun s => c.lyapunovFunction (k.cancellationFlow s x)) (Icc 0 T) := by
  refine antitoneOn_Icc_of_right_local
    ((k.continuousOn_lyapunovFunction_crossingRegion hk).comp (k.continuous_cancellationFlow_curve x).continuousOn fun s hs => hT s hs)
    fun t ht => ?_
  have hz := hT t (Ico_subset_Icc_self ht)
  by_cases hp : k.cancellationFlow t x ∈ c.pBall'
  · obtain ⟨ε, hε, h⟩ := k.exists_right_le_lyapunovFunction_of_mem_pBall' hk hz hp
    exact ⟨ε, hε, fun s hs _ => h s ⟨hs.1.le, hs.2⟩⟩
  by_cases hq : k.cancellationFlow t x ∈ c.qBall'
  · obtain ⟨ε, hε, h⟩ := k.exists_right_le_lyapunovFunction_of_mem_qBall' hk hT ht hq
    exact ⟨ε, hε, fun s hs hsT => h s ⟨hs.1.le, hs.2⟩ hsT⟩
  have hzT : k.cancellationFlow t x ∈ k.middleTube := by
    rcases hz with (h | h) | h
    · exact absurd (c.pClosedAnnulus_subset_pBall' h) hp
    · exact h
    · exact absurd (k.qPositiveRegion_subset_qBall' hk h) hq
  have hlo : c.lo₂ < f (k.cancellationFlow t x) := by
    rcases hzT.2.1.eq_or_lt with h | h
    · exact absurd (c.pClosedAnnulus_subset_pBall' (c.mem_pClosedAnnulus_of_mem_middleTube_lo₂ k hk hzT h.symm)) hp
    · exact h
  have hhi : f (k.cancellationFlow t x) < c.hi₁ := by
    rcases hzT.2.2.eq_or_lt with h | h
    · exact absurd (k.qPositiveRegion_subset_qBall' hk (c.mem_qPositiveRegion_of_mem_middleTube_hi₁ k hk hzT h)) hq
    · exact h
  obtain ⟨ε, hε, h⟩ := k.exists_right_le_lyapunovFunction_of_mem_middleTube hk hT ht hzT hlo hhi
  exact ⟨ε, hε, fun s hs hsT => h s ⟨hs.1.le, hs.2⟩ hsT⟩

theorem exists_lyapunovFunction_lt_of_mem_pClosedAnnulus {x : M} (hx : x ∈ c.pClosedAnnulus) (hT : x ∈ c.orientedChartTube)
    (hζ0 : c.ζ x ≠ 0) (hζ : ‖c.ζ x‖ < k.δ') : ∃ t, 0 < t ∧ c.lyapunovFunction (k.cancellationFlow t x) < c.lyapunovFunction x := by
  have hp := c.pClosedAnnulus_subset_pBall' hx
  have hy0 := c.symm_ne_zero_of_mem_pClosedAnnulus hx
  have hsq := c.symm_sq_lt_of_mem_pBall' hp
  set y := c.e.χ.symm x with hydef
  have hχ : c.e.χ y = x := c.e.symm_image_eq (c.pBall'_subset_image_ball hp)
  have hd := k.hasDerivAt_axialDefect_cancellationFlow_p (x := x) (s := 0) (by rw [k.cancellationFlow_zero]; exact hp)
    (by rw [k.cancellationFlow_zero]; exact hy0)
  rw [k.cancellationFlow_zero] at hd
  have hneg : axialDefectDeriv c.e₁ y (k.pCancellationField y) < 0 := by
    rw [k.axialDefectDeriv_pCancellationField hy0]
    have h1 : c.m' * (βp k.δ k.τ c.e₁ y * ψp c.ρA c.ρB y) * axialDefectDeriv c.e₁ y c.e₁ ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos
      · exact mul_nonneg c.m'_pos.le (mul_nonneg (βp_nonneg _) (ψp_nonneg _))
      · rw [axialDefectDeriv_e₁ c.morseNorm_e₁ hy0]
        have := perpSq_nonneg c.morseNorm_e₁ y
        have := morseNorm_pos hy0
        have : 0 ≤ perpSq c.e₁ y / morseNorm n y ^ 3 := by positivity
        linarith
    have hBp : 0 < k.pTransverseWeight y := by
      rw [k.pTransverseWeight_of_mem (by rw [hχ]; exact hT), hχ]
      have hψ : c.ψm' x = 1 := by
        apply c.ψm'_eq_one
        · rw [c.f_eq_of_mem_pBall' hp]
          have h := (c.symm_mem_of_mem_pClosedAnnulus hx).1
          have h2 := c.ρA_sq_eq
          have h3 := c.ρA_le_ρs
          have := pow_le_pow_left₀ c.ρA_pos.le (h3.trans h) 2
          linarith
        · exact (c.f_le_lo₂_of_mem_pClosedAnnulus hx).trans (by unfold lo₂ hi₂; linarith [c.c₁_lt_c₂])
      rw [hψ, mul_one]
      exact cut_pos_of_lt k.two_δ_sq_lt_δ'_sq (pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero)
    have h2 : axialDefectDeriv c.e₁ y (c.pRestrictedTransverseField y) < 0 := by
      rw [c.pRestrictedTransverseField_of_mem (by rw [hχ]; exact hT)]
      refine k.hdB y hsq (by rw [hχ]; exact hT) ?_ ?_
      · rw [hχ]; exact norm_pos_iff.2 hζ0
      · rw [hχ]; exact hζ
    have h3 : 2 * (c.lam * k.pTransverseWeight y) * axialDefectDeriv c.e₁ y (c.pRestrictedTransverseField y) < 0 :=
      mul_neg_of_pos_of_neg (by have := c.lam_pos; positivity) h2
    linarith
  have hev := eventually_lt_of_hasDerivAt_neg hneg hd
  have hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), k.cancellationFlow s x ∈ c.pBall' := by
    refine nhdsWithin_le_nhds ?_
    exact (k.continuous_cancellationFlow_curve x).continuousAt.preimage_mem_nhds
      (c.isOpen_pBall'.mem_nhds (by rw [k.cancellationFlow_zero]; exact hp))
  obtain ⟨t, ⟨hlt, hmem'⟩, ht⟩ := ((hev.and hmem).and self_mem_nhdsWithin).exists
  rw [k.cancellationFlow_zero] at hlt
  refine ⟨t, ht, ?_⟩
  rw [c.lyapunovFunction_of_mem_pBall' hmem', c.lyapunovFunction_of_mem_pBall' hp]
  exact hlt

theorem exists_lyapunovFunction_lt_of_mem_qPositiveRegion (hk : k.Good) {x : M} (hx : x ∈ k.qPositiveRegion)
    (hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm x)) (hQ0 : 0 < c.qNormProductSq (c.d.χ.symm x))
    (hβ : βq c.d.hk c.hkq k.δ k.τ c.σ (c.d.χ.symm x) *
      ψq c.d.hk c.hkq c.uA c.uB (c.d.χ.symm x) ≠ 0 ∨ k.qTransverseWeight (c.d.χ.symm x) ≠ 0) :
    ∃ t, 0 < t ∧ c.lyapunovFunction (k.cancellationFlow t x) < c.lyapunovFunction x := by
  have hq := k.qPositiveRegion_subset_qBall' hk hx
  have hy := k.symm_mem_qPositiveCoordinateRegion_of_mem_qPositiveRegion hk hx
  set y := c.d.χ.symm x with hydef
  have hrate : k.qNormProductRate y < 0 := by
    unfold qNormProductRate
    have hv : 0 < ‖posPart c.d.hk y‖ ^ 2 := by
      by_contra h
      push Not at h
      have : ‖posPart c.d.hk y‖ ^ 2 = 0 := le_antisymm h (by positivity)
      have hQ := c.qNormProductSq_eq_uq y
      rw [this, mul_zero] at hQ
      linarith
    have hu0 : 0 < uq c.d.hk c.hkq y ^ 2 := by
      have : uq c.d.hk c.hkq y ≠ 0 := fun h => by rw [h, mul_zero] at hu; exact lt_irrefl _ hu
      positivity
    have h1 : 0 ≤ c.σ * uq c.d.hk c.hkq y *
        (c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y)) :=
      mul_nonneg hu.le (mul_nonneg c.m'_pos.le (mul_nonneg (βq_nonneg _ _ _) (ψq_nonneg _ _ _)))
    have h2 : 0 ≤ 2 * (c.lam * k.qTransverseWeight y) * (c.κ (c.d.χ y) * uq c.d.hk c.hkq y ^ 2) :=
      mul_nonneg (by have := c.lam_pos; have := k.qTransverseWeight_nonneg y; positivity)
        (mul_nonneg (c.κ_pos _).le (sq_nonneg _))
    have hsum : 0 < c.σ * uq c.d.hk c.hkq y *
        (c.m' * (βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y)) +
        2 * (c.lam * k.qTransverseWeight y) * (c.κ (c.d.χ y) * uq c.d.hk c.hkq y ^ 2) := by
      rcases hβ with hβ | hβ
      · have : 0 < βq c.d.hk c.hkq k.δ k.τ c.σ y * ψq c.d.hk c.hkq c.uA c.uB y :=
          lt_of_le_of_ne (mul_nonneg (βq_nonneg _ _ _) (ψq_nonneg _ _ _)) (Ne.symm hβ)
        have := mul_pos hu (mul_pos c.m'_pos this)
        linarith
      · have hB : 0 < k.qTransverseWeight y := lt_of_le_of_ne (k.qTransverseWeight_nonneg y) (Ne.symm hβ)
        have := mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) (mul_pos c.lam_pos hB))
          (mul_pos (c.κ_pos (c.d.χ y)) hu0)
        linarith
    nlinarith
  have hd := k.hasDerivAt_qNormProductSq_cancellationFlow (x := x) (s := 0) (by rw [k.cancellationFlow_zero]; exact hq)
  rw [k.cancellationFlow_zero] at hd
  have hev := eventually_lt_of_hasDerivAt_neg hrate hd
  have hO : k.cancellationFlow 0 x ∈ c.qBall' ∩ {w | 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm w)} := by
    rw [k.cancellationFlow_zero]; exact ⟨hq, hu⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open
    (c.isOpen_qBall'_inter (P := fun r => 0 < r) (isOpen_lt continuous_const continuous_id)) hO
  obtain ⟨t, hlt, ht⟩ := (hev.and (Ioc_mem_nhdsGT (show (0:ℝ) < ε from hε))).exists
  have hall : ∀ u ∈ Icc 0 t, k.cancellationFlow u x ∈ c.qBall' := fun u hu =>
    (hεO u ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩).1
  have hσ : ∀ u ∈ Icc 0 t, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow u x)) := fun u hu =>
    (hεO u ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩).2.le
  have hQ' : c.qNormProductSq (c.d.χ.symm (k.cancellationFlow 0 x)) ≤ k.qNormProductBound := by rw [k.cancellationFlow_zero]; exact hy.2.2.2
  have hQ0' : 0 < c.qNormProductSq (c.d.χ.symm (k.cancellationFlow 0 x)) := by rw [k.cancellationFlow_zero]; exact hQ0
  have hlt' : c.qNormProductSq (c.d.χ.symm (k.cancellationFlow t x)) < c.qNormProductSq (c.d.χ.symm (k.cancellationFlow 0 x)) := hlt
  have := k.qAxialDefect_lt_cancellationFlow hall hk hσ hQ' hQ0' (right_mem_Icc.2 ht.1.le) hlt'
  rw [k.cancellationFlow_zero] at this
  refine ⟨t, ht.1, ?_⟩
  rw [c.lyapunovFunction_of_mem_qBall' (hall t (right_mem_Icc.2 ht.1.le)), c.lyapunovFunction_of_mem_qBall' hq]
  exact this

theorem exists_lyapunovFunction_lt_of_mem_middleTube (hk : k.Good) {x : M} (hcon : ∀ t, 0 ≤ t → k.cancellationFlow t x ∈ k.crossingRegion)
    (hx : x ∈ k.middleTube) (hlo : c.lo₂ < f x) (hhi : f x < c.hi₁) (hζ0 : c.ζ x ≠ 0)
    (hζ : ‖c.ζ x‖ < k.δ') : ∃ t, 0 < t ∧ c.lyapunovFunction (k.cancellationFlow t x) < c.lyapunovFunction x := by
  have hT := k.middleTube_subset_orientedChartTube hx
  have hζ'' : ‖c.ζ x‖ < hk.δ'' := hζ.trans hk.hδ'δ''
  have hd := k.hasDerivAt_sheetAxialDefect_ζ_cancellationFlow hk (x := x) (u := 0) (by rw [k.cancellationFlow_zero]; exact hT)
    (by rw [k.cancellationFlow_zero]; exact hlo.le) (by rw [k.cancellationFlow_zero]; exact hhi.le) (by rw [k.cancellationFlow_zero]; exact hζ'')
  rw [k.cancellationFlow_zero] at hd
  have hneg : -(2 * (c.lam * k.βm' x)) * fderiv ℝ c.sheetAxialDefect (c.ζ x) (c.ζ x) < 0 := by
    have h1 := hk.fderiv_sheetAxialDefect_self_pos hζ0 hζ''
    have h2 : 0 < k.βm' x :=
      cut_pos_of_lt k.two_δ_sq_lt_δ'_sq (pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero)
    have h3 := c.lam_pos
    have : 0 < 2 * (c.lam * k.βm' x) * fderiv ℝ c.sheetAxialDefect (c.ζ x) (c.ζ x) := by positivity
    linarith
  have hev := eventually_lt_of_hasDerivAt_neg hneg hd
  have hO : k.cancellationFlow 0 x ∈ c.orientedChartTube ∩ {w | c.lo₂ < f w ∧ f w < c.hi₁} := by
    rw [k.cancellationFlow_zero]; exact ⟨hT, hlo, hhi⟩
  have hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), k.cancellationFlow s x ∈ c.orientedChartTube ∩ {w | c.lo₂ < f w ∧ f w < c.hi₁} := by
    refine nhdsWithin_le_nhds ?_
    exact (k.continuous_cancellationFlow_curve x).continuousAt.preimage_mem_nhds
      ((c.isOpen_orientedChartTube.inter ((isOpen_lt continuous_const c.hfs.continuous).inter
        (isOpen_lt c.hfs.continuous continuous_const))).mem_nhds hO)
  obtain ⟨t, ⟨hlt, hmem'⟩, ht⟩ := ((hev.and hmem).and self_mem_nhdsWithin).exists
  rw [k.cancellationFlow_zero] at hlt
  have htT : k.cancellationFlow t x ∈ k.middleTube := k.mem_middleTube_of_mem_crossingRegion hk (hcon t ht.le) hmem'.2.1 hmem'.2.2
  refine ⟨t, ht, ?_⟩
  rw [k.lyapunovFunction_eq_sheetAxialDefect_ζ_of_mem_middleTube hk htT, k.lyapunovFunction_eq_sheetAxialDefect_ζ_of_mem_middleTube hk hx]
  exact hlt

def lyapunovExceptionalSet : Set M :=
  {x | x ∈ c.pClosedAnnulus ∧ (x ∉ c.orientedChartTube ∨ c.ζ x = 0 ∨ k.δ' ≤ ‖c.ζ x‖)} ∪
  {x | x ∈ k.middleTube ∧ (c.ζ x = 0 ∨ k.δ' ≤ ‖c.ζ x‖)} ∪
  {x | x ∈ k.qPositiveRegion ∧ (c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) = 0 ∨ c.qNormProductSq (c.d.χ.symm x) = 0 ∨
    (βq c.d.hk c.hkq k.δ k.τ c.σ (c.d.χ.symm x) * ψq c.d.hk c.hkq c.uA c.uB (c.d.χ.symm x) = 0 ∧
      k.qTransverseWeight (c.d.χ.symm x) = 0))}

theorem exists_lyapunovFunction_lt_of_notMem_lyapunovExceptionalSet (hk : k.Good) {x : M} (hx : x ∈ k.crossingRegion) (hZ : x ∉ k.lyapunovExceptionalSet)
    (hcon : ∀ t, 0 ≤ t → k.cancellationFlow t x ∈ k.crossingRegion) : ∃ t, 0 < t ∧ c.lyapunovFunction (k.cancellationFlow t x) < c.lyapunovFunction x := by
  by_cases hA : x ∈ c.pClosedAnnulus
  · have h : ¬ (x ∉ c.orientedChartTube ∨ c.ζ x = 0 ∨ k.δ' ≤ ‖c.ζ x‖) := fun h =>
      hZ (Or.inl (Or.inl ⟨hA, h⟩))
    push Not at h
    exact k.exists_lyapunovFunction_lt_of_mem_pClosedAnnulus hA h.1 h.2.1 h.2.2
  by_cases hR : x ∈ k.qPositiveRegion
  · have h : ¬ (c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) = 0 ∨ c.qNormProductSq (c.d.χ.symm x) = 0 ∨
        (βq c.d.hk c.hkq k.δ k.τ c.σ (c.d.χ.symm x) *
          ψq c.d.hk c.hkq c.uA c.uB (c.d.χ.symm x) = 0 ∧ k.qTransverseWeight (c.d.χ.symm x) = 0)) :=
      fun h => hZ (Or.inr ⟨hR, h⟩)
    push Not at h
    have hy := k.symm_mem_qPositiveCoordinateRegion_of_mem_qPositiveRegion hk hR
    have hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm x) := lt_of_le_of_ne hy.1 (Ne.symm h.1)
    have hQ : 0 < c.qNormProductSq (c.d.χ.symm x) := lt_of_le_of_ne (c.qNormProductSq_nonneg _) (Ne.symm h.2.1)
    refine k.exists_lyapunovFunction_lt_of_mem_qPositiveRegion hk hR hu hQ ?_
    by_cases hβ : βq c.d.hk c.hkq k.δ k.τ c.σ (c.d.χ.symm x) *
        ψq c.d.hk c.hkq c.uA c.uB (c.d.χ.symm x) = 0
    · exact Or.inr (h.2.2 hβ)
    · exact Or.inl hβ
  have hT : x ∈ k.middleTube := by
    rcases hx with (h | h) | h
    · exact absurd h hA
    · exact h
    · exact absurd h hR
  have hlo : c.lo₂ < f x := by
    rcases hT.2.1.eq_or_lt with h | h
    · exact absurd (c.mem_pClosedAnnulus_of_mem_middleTube_lo₂ k hk hT h.symm) hA
    · exact h
  have hhi : f x < c.hi₁ := by
    rcases hT.2.2.eq_or_lt with h | h
    · exact absurd (c.mem_qPositiveRegion_of_mem_middleTube_hi₁ k hk hT h) hR
    · exact h
  have h : ¬ (c.ζ x = 0 ∨ k.δ' ≤ ‖c.ζ x‖) := fun h => hZ (Or.inl (Or.inr ⟨hT, h⟩))
  push Not at h
  exact k.exists_lyapunovFunction_lt_of_mem_middleTube hk hcon hT hlo hhi h.1 h.2

theorem notMem_lyapunovExceptionalSet_of_lo₂ (hk : k.Good) {w : M} (hw : w ∈ k.middleTube) (hf : f w = c.lo₂)
    (hζ0 : c.ζ w ≠ 0) (hζ : ‖c.ζ w‖ < k.δ') : w ∉ k.lyapunovExceptionalSet := by
  have hT := k.middleTube_subset_orientedChartTube hw
  rintro ((⟨-, h⟩ | ⟨-, h⟩) | ⟨h, -⟩)
  · rcases h with h | h | h
    · exact h hT
    · exact hζ0 h
    · linarith
  · rcases h with h | h
    · exact hζ0 h
    · linarith
  · have := k.f_ge_lo₂_of_mem_qPositiveRegion hk h
    have := k.hi₁_le_f_of_mem_qRegion hk (k.qPositiveRegion_subset_qRegion h)
    linarith [c.lo₂_lt_hi₁]

theorem notMem_lyapunovExceptionalSet_of_hi₁ (hk : k.Good) {w : M} (hw : w ∈ k.middleTube) (hf : f w = c.hi₁)
    (hζ0 : c.ζ w ≠ 0) (hζ : ‖c.ζ w‖ < k.δ') : w ∉ k.lyapunovExceptionalSet := by
  have hT := k.middleTube_subset_orientedChartTube hw
  rintro ((⟨h, -⟩ | ⟨-, h⟩) | ⟨hR, h⟩)
  · have := c.f_le_lo₂_of_mem_pClosedAnnulus h
    linarith [c.lo₂_lt_hi₁]
  · rcases h with h | h
    · exact hζ0 h
    · linarith
  · have hq := k.qPositiveRegion_subset_qBall' hk hR
    have hχ : c.d.χ (c.d.χ.symm w) = w := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
    have hsq := c.symm_sq_lt_of_mem_qBall' hq
    have hu := k.σ_uq_pos_of_mem_middleTube hw hq
    rcases h with h | h | h
    · linarith
    · apply hζ0
      rw [← hχ, c.ζ_eq_ζhat hsq (by rw [hχ]; exact hT.1)]
      exact (c.ζhat_eq_zero_iff _).2 h
    · have hB : k.qTransverseWeight (c.d.χ.symm w) ≠ 0 := by
        rw [k.qTransverseWeight_of_mem (by rw [hχ]; exact hT), hχ]
        have hψ : c.ψm' w = 1 := c.ψm'_eq_one
          (by rw [hf]; linarith [c.lo₁_lt_lo₂, c.lo₂_lt_hi₁]) (by rw [hf]; exact c.hi₁_lt_hi₂.le)
        rw [hψ, mul_one]
        exact (cut_pos_of_lt k.two_δ_sq_lt_δ'_sq
          (pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero)).ne'
      exact hB h.2

def leaves (z : M) : Prop := ∃ t, 0 ≤ t ∧ k.cancellationFlow t z ∉ k.crossingRegion ∩ k.lyapunovExceptionalSet

theorem leaves_of_f_le (hk : k.Good) {z : M} {T : ℝ} (hT : 0 ≤ T) (hf : f (k.cancellationFlow T z) ≤ a') :
    k.leaves z :=
  ⟨T, hT, fun h => k.notMem_crossingRegion_of_f_le hk hf h.1⟩

theorem leaves_of_notMem_lyapunovExceptionalSet {z : M} {t : ℝ} (ht : 0 ≤ t) (hZ : k.cancellationFlow t z ∉ k.lyapunovExceptionalSet) : k.leaves z :=
  ⟨t, ht, fun h => hZ h.2⟩

theorem leaves_shift {z : M} {t : ℝ} (ht : 0 ≤ t) (h : k.leaves (k.cancellationFlow t z)) : k.leaves z := by
  obtain ⟨T, hT, hTz⟩ := h
  exact ⟨t + T, by linarith, by rw [k.cancellationFlow_add]; exact hTz⟩

theorem mem_qAxis_of_mem_middleTube_hi₁ (hk : k.Good) {z : M} (hz : z ∈ k.middleTube) (hf : f z = c.hi₁)
    (hζ : c.ζ z = 0) : z ∈ c.qAxis := by
  have hR := c.mem_qPositiveRegion_of_mem_middleTube_hi₁ k hk hz hf
  have hq := k.qPositiveRegion_subset_qBall' hk hR
  have hχ : c.d.χ (c.d.χ.symm z) = z := c.d.symm_image_eq (c.qBall'_subset_image_ball hq)
  have hsq := c.symm_sq_lt_of_mem_qBall' hq
  have hT := k.middleTube_subset_orientedChartTube hz
  refine k.mem_qAxis_of_mem_qPositiveRegion hk hR ?_
  have hQ : c.qNormProductSq (c.d.χ.symm z) = 0 := by
    rw [← c.ζhat_eq_zero_iff, ← c.ζ_eq_ζhat hsq (by rw [hχ]; exact hT.1), hχ]
    exact hζ
  have hu := k.σ_uq_pos_of_mem_middleTube hz hq
  rw [c.qNormProductSq_eq_uq] at hQ
  rcases mul_eq_zero.1 hQ with h | h
  · exfalso
    have : uq c.d.hk c.hkq (c.d.χ.symm z) = 0 := pow_eq_zero_iff two_ne_zero |>.1 h
    rw [this, mul_zero] at hu
    exact lt_irrefl _ hu
  · exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)

theorem leaves_of_mem_middleTube_ζ_zero (hk : k.Good) {z : M} (hz : z ∈ k.middleTube) (hζ : c.ζ z = 0) :
    k.leaves z := by
  obtain ⟨t, ht, hT, hf, hζ'⟩ := k.exists_reach_hi₁_of_ζ_eq_zero hz hζ
  refine k.leaves_shift ht ?_
  obtain ⟨T, hT', hfT⟩ := k.exists_f_le_a'_of_mem_qAxis hk (k.mem_qAxis_of_mem_middleTube_hi₁ hk hT hf hζ')
  exact k.leaves_of_f_le hk hT' hfT

theorem leaves_of_mem_pClosedBall (hk : k.Good) {z : M} (hz : z ∈ c.pClosedBall) : k.leaves z := by
  obtain ⟨t, ht, hW2, hT, hf⟩ := k.exists_reach_pAxialAnnulus_middleTube hk hz
  refine k.leaves_shift ht ?_
  set w := k.cancellationFlow t z with hw
  have hWb := k.pAxialAnnulus_subset_pClosedBall hW2
  obtain ⟨h1, h2, h3⟩ := (k.mem_pAxialAnnulus_iff (c.pClosedBall_subset_image_ball hWb)).1 hW2
  obtain ⟨hTσ, hζ⟩ := k.mem_tube_of_axialDefect_le h1 h2 h3
  rw [c.e.symm_image_eq (c.pClosedBall_subset_image_ball hWb)] at hTσ hζ
  by_cases hζ0 : c.ζ w = 0
  · exact k.leaves_of_mem_middleTube_ζ_zero hk hT hζ0
  · exact k.leaves_of_notMem_lyapunovExceptionalSet le_rfl (by rw [k.cancellationFlow_zero]; exact k.notMem_lyapunovExceptionalSet_of_lo₂ hk hT hf hζ0 hζ)

theorem leaves_of_mem_middleTube_δ' (hk : k.Good) {z : M} (hz : z ∈ k.middleTube) (hζ : k.δ' ≤ ‖c.ζ z‖) :
    k.leaves z := by
  rcases hz.2.1.eq_or_lt with hlo | hlo
  · exact k.leaves_of_mem_pClosedBall hk (c.pClosedAnnulus_subset_pClosedBall (c.mem_pClosedAnnulus_of_mem_middleTube_lo₂ k hk hz hlo.symm))
  obtain ⟨t₀, ht₀, hz₁, hf₁, hlo₁⟩ :=
    k.exists_pos_mem_middleTube_of_two_δ_le hz (by linarith [k.hδδ']) hlo
  refine k.leaves_shift ht₀.le ?_
  set z₁ := k.cancellationFlow t₀ z with hz₁def
  obtain ⟨t, ht, hall, -, hexit⟩ := k.exists_exit_mid_band hz₁
  refine k.leaves_shift ht ?_
  set z₂ := k.cancellationFlow t z₁ with hz₂def
  have hz₂ : z₂ ∈ k.middleTube := hall t (right_mem_Icc.2 ht)
  rcases hexit with ⟨hf, hζ2⟩ | hf
  · have htpos : 0 < t := by
      rcases ht.eq_or_lt with h | h
      · exfalso
        have hz₂₁ : z₂ = z₁ := by rw [hz₂def, ← h, k.cancellationFlow_zero]
        rw [hz₂₁] at hf
        linarith [hz.2.2]
      · exact h
    have hζ' : ‖c.ζ z₂‖ < k.δ' := (hζ2 htpos).trans (by linarith [k.hδδ'])
    by_cases hζ0 : c.ζ z₂ = 0
    · exact k.leaves_of_mem_middleTube_ζ_zero hk hz₂ hζ0
    · exact k.leaves_of_notMem_lyapunovExceptionalSet le_rfl
        (by rw [k.cancellationFlow_zero]; exact k.notMem_lyapunovExceptionalSet_of_hi₁ hk hz₂ hf hζ0 hζ')
  · exact k.leaves_of_mem_pClosedBall hk (c.pClosedAnnulus_subset_pClosedBall (c.mem_pClosedAnnulus_of_mem_middleTube_lo₂ k hk hz₂ hf))

theorem leaves_of_mem_qPositiveRegion (hk : k.Good) {z : M} (hz : z ∈ k.qPositiveRegion) : k.leaves z := by
  obtain ⟨t, ht, hall, hface⟩ := k.exists_exit_qPositiveRegion_face hk hz
  rcases hface with hu | ⟨hf, hT, -, -⟩
  · obtain ⟨T, hT, hfT⟩ :=
      k.exists_f_le_a'_of_mem_qRegion_face hk (hall t (right_mem_Icc.2 ht)) hu
    exact k.leaves_shift ht (k.leaves_of_f_le hk hT hfT)
  · refine k.leaves_shift ht ?_
    set z₂ := k.cancellationFlow t z with hz₂def
    by_cases hζ0 : c.ζ z₂ = 0
    · exact k.leaves_of_mem_middleTube_ζ_zero hk hT hζ0
    rcases (k.norm_ζ_le_of_mem_closedFlowTube hT.1).lt_or_eq with hlt | heq
    · exact k.leaves_of_notMem_lyapunovExceptionalSet le_rfl
        (by rw [k.cancellationFlow_zero]; exact k.notMem_lyapunovExceptionalSet_of_hi₁ hk hT hf hζ0 hlt)
    · exact k.leaves_of_mem_middleTube_δ' hk hT heq.ge

theorem leaves_of_mem_middleTube (hk : k.Good) {z : M} (hz : z ∈ k.middleTube) : k.leaves z := by
  by_cases hζ0 : c.ζ z = 0
  · exact k.leaves_of_mem_middleTube_ζ_zero hk hz hζ0
  rcases (k.norm_ζ_le_of_mem_closedFlowTube hz.1).lt_or_eq with hlt | heq
  · rcases hz.2.1.eq_or_lt with hlo | hlo
    · exact k.leaves_of_notMem_lyapunovExceptionalSet le_rfl
        (by rw [k.cancellationFlow_zero]; exact k.notMem_lyapunovExceptionalSet_of_lo₂ hk hz hlo.symm hζ0 hlt)
    rcases hz.2.2.eq_or_lt with hhi | hhi
    · exact k.leaves_of_notMem_lyapunovExceptionalSet le_rfl
        (by rw [k.cancellationFlow_zero]; exact k.notMem_lyapunovExceptionalSet_of_hi₁ hk hz hhi hζ0 hlt)
    refine k.leaves_of_notMem_lyapunovExceptionalSet le_rfl ?_
    rw [k.cancellationFlow_zero]
    rintro ((⟨h, -⟩ | ⟨-, h⟩) | ⟨h, -⟩)
    · exact absurd (c.f_le_lo₂_of_mem_pClosedAnnulus h) (not_le.2 hlo)
    · rcases h with h | h
      · exact hζ0 h
      · linarith
    · exact absurd (k.hi₁_le_f_of_mem_qRegion hk (k.qPositiveRegion_subset_qRegion h)) (not_le.2 hhi)
  · exact k.leaves_of_mem_middleTube_δ' hk hz heq.ge

theorem leaves_of_mem_crossingRegion (hk : k.Good) {z : M} (hz : z ∈ k.crossingRegion) : k.leaves z := by
  rcases hz with (h | h) | h
  · exact k.leaves_of_mem_pClosedBall hk (c.pClosedAnnulus_subset_pClosedBall h)
  · exact k.leaves_of_mem_middleTube hk h
  · exact k.leaves_of_mem_qPositiveRegion hk h

theorem exists_exit_crossingRegion (hk : k.Good) : ∀ x ∈ k.crossingRegion, ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∉ k.crossingRegion :=
  k.exists_exit_of_antitone_weak (k.isCompact_crossingRegion hk) (k.continuousOn_lyapunovFunction_crossingRegion hk)
    (Z := k.lyapunovExceptionalSet) (fun _ _ hT => k.antitoneOn_lyapunovFunction_cancellationFlow hk hT)
    (fun _ hx hcon => k.exists_lyapunovFunction_lt_of_notMem_lyapunovExceptionalSet hk hx.1 hx.2 hcon)
    (fun z hz => by
      obtain ⟨t, -, h⟩ := k.leaves_of_mem_crossingRegion hk hz.1
      exact ⟨t, h⟩)

def crossingExitSet : Set M := c.e.χ '' {y | morseNorm n y = c.ρs} ∪ (k.qPositiveRegion ∩ c.qNonpositiveChartRegion)

theorem isClosed_crossingExitSet (hk : k.Good) : IsClosed k.crossingExitSet :=
  (c.e.isCompact_image_of_subset ((isCompact_morseNorm_le c.ρs).of_isClosed_subset
    (isClosed_eq continuous_morseNorm continuous_const) fun _ hy => le_of_eq hy)
    (c.ρs_lt_ρB.trans c.ρB_lt_R') fun _ hy => le_of_eq hy).isClosed.union
    ((k.isCompact_qPositiveRegion hk).isClosed.inter c.isClosed_qNonpositiveChartRegion)

theorem ρs_sq_lt : c.ρs ^ 2 < 3 * c.ε :=
  (pow_lt_pow_left₀ c.ρs_lt_ρB c.ρs_pos.le two_ne_zero).trans c.ρB_sq_lt_three_ε

theorem isOpen_annulus_open :
    IsOpen (c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y < c.ρB}) := by
  refine (OpenPartialHomeomorph.isOpen_image_iff_of_subset_source c.e.χ fun y hy => ?_).2 ?_
  · exact c.e.hball (mem_ball_of_morseNorm_lt (hy.2.trans c.ρB_lt_R'))
  · exact (isOpen_lt continuous_const continuous_morseNorm).inter
      (isOpen_lt continuous_morseNorm continuous_const)

theorem exists_Ioc_of_eventually {P : ℝ → Prop} (h : ∀ᶠ u in 𝓝[>] (0 : ℝ), P u) :
    ∃ ε > 0, ∀ u ∈ Ioc 0 ε, P u := by
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 h
  exact ⟨ε, hε, fun u hu => hsub hu⟩

theorem local_pClosedAnnulus_open {z : M} (hz : z ∈ c.pClosedAnnulus) (h1 : c.ρs < morseNorm n (c.e.χ.symm z))
    (h2 : morseNorm n (c.e.χ.symm z) < c.ρB) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.cancellationFlow u z ∈ k.crossingRegion := by
  have hO : k.cancellationFlow 0 z ∈ c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y < c.ρB} := by
    rw [k.cancellationFlow_zero]
    exact c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball (c.pClosedAnnulus_subset_pBall' hz))
      ⟨h1, h2⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open (isOpen_annulus_open (c := c)) hO
  refine ⟨ε, hε, fun u hu => ?_⟩
  obtain ⟨y, hy, hyu⟩ := hεO u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  exact k.pClosedAnnulus_subset_crossingRegion ⟨y, ⟨hy.1.le, hy.2.le⟩, hyu⟩

theorem local_pClosedAnnulus_sphere_out {z : M} (hz : z ∈ c.pClosedAnnulus) (hr : morseNorm n (c.e.χ.symm z) = c.ρB)
    (hout : z ∈ c.orientedChartTube → 2 * k.δ ≤ ‖c.ζ z‖) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.cancellationFlow u z ∈ k.crossingRegion := by
  have hp := c.pClosedAnnulus_subset_pBall' hz
  set y := c.e.χ.symm z with hydef
  have hχ : c.e.χ y = z := c.e.symm_image_eq (c.pBall'_subset_image_ball hp)
  have hsq := c.symm_sq_lt_of_mem_pBall' hp
  have hdot : dot y (k.pCancellationField y) < 0 := by
    rw [k.dot_pCancellationField hsq, k.pReversalWeight_eq_zero_of_norm_ζ (by rw [hχ]; exact hout),
      ψp_eq_zero c.ρA_pos.le c.ρA_lt_ρB hr.ge]
    have hθ := ModelField.theta_pos c.e.hr₀ y
    have : 0 < morseNorm n y ^ 2 := by rw [hr]; exact pow_pos c.ρB_pos 2
    nlinarith [mul_pos hθ this]
  have hd := k.hasDerivAt_morseNormSq_cancellationFlow_p (x := z) (s := 0) (by rw [k.cancellationFlow_zero]; exact hp)
  rw [k.cancellationFlow_zero] at hd
  have hev := eventually_lt_of_hasDerivAt_neg (by linarith : 2 * dot y (k.pCancellationField y) < 0) hd
  have hO : k.cancellationFlow 0 z ∈ c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε} := by
    rw [k.cancellationFlow_zero]
    exact c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball hp)
      ⟨by rw [hr]; exact c.ρs_lt_ρB, hsq⟩
  obtain ⟨ε₁, hε₁, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open c.isOpen_annulus_gt hO
  obtain ⟨ε₂, hε₂, hsub⟩ := exists_Ioc_of_eventually hev
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun u hu => ?_⟩
  rcases hu.1.eq_or_lt with h | h
  · rw [← h, k.cancellationFlow_zero]; exact k.pClosedAnnulus_subset_crossingRegion hz
  · have hu1 : u ≤ ε₁ := hu.2.trans (min_le_left _ _)
    have hu2 : u ≤ ε₂ := hu.2.trans (min_le_right _ _)
    obtain ⟨y', hy', hy'u⟩ := hεO u ⟨by linarith, by linarith [hu1]⟩
    have hlt := hsub u ⟨h, hu2⟩
    have hy'eq : c.e.χ.symm (k.cancellationFlow u z) = y' := by rw [← hy'u, c.chart_p_symm_eq' hy'.2]
    rw [hy'eq, k.cancellationFlow_zero, ← hydef, hr] at hlt
    have hlt' : morseNorm n y' < c.ρB :=
      (pow_lt_pow_iff_left₀ (ModelField.morseNorm_nonneg _) c.ρB_pos.le two_ne_zero).1 hlt
    exact k.pClosedAnnulus_subset_crossingRegion ⟨y', ⟨hy'.1.le, hlt'.le⟩, hy'u⟩

theorem c₁_sub_half_lt_lo₂ : c.c₁ - c.η / 2 < c.lo₂ := by unfold lo₂; linarith [c.η_pos]

theorem local_pClosedAnnulus_sphere_tube (hk : k.Good) {z : M} (hz : z ∈ c.pClosedAnnulus)
    (hr : morseNorm n (c.e.χ.symm z) = c.ρB) (hT : z ∈ c.orientedChartTube) (hζ : ‖c.ζ z‖ < 2 * k.δ) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.cancellationFlow u z ∈ k.crossingRegion := by
  have hp := c.pClosedAnnulus_subset_pBall' hz
  have hfz : f z = c.lo₂ := by
    rw [c.f_eq_of_mem_pBall' hp, hr, c.ρB_sq_eq]; ring
  set O : Set M := c.orientedChartTube ∩ (c.openChartTube ∩ c.ζ ⁻¹' {v | ‖v‖ < k.δ'}) ∩
    {w | c.c₁ - c.η / 2 < f w ∧ f w < c.hi₁} ∩
    c.e.χ '' {y | c.ρs < morseNorm n y ∧ morseNorm n y ^ 2 < 3 * c.ε} with hOdef
  have hOo : IsOpen O :=
    ((c.isOpen_orientedChartTube.inter (c.continuousOn_ζ.isOpen_inter_preimage c.isOpen_openChartTube
      (isOpen_lt continuous_norm continuous_const))).inter
      ((isOpen_lt continuous_const c.hfs.continuous).inter
        (isOpen_lt c.hfs.continuous continuous_const))).inter c.isOpen_annulus_gt
  have hzO : k.cancellationFlow 0 z ∈ O := by
    rw [k.cancellationFlow_zero]
    refine ⟨⟨⟨hT, hT.1, hζ.trans (by linarith [k.hδδ'])⟩, ?_, ?_⟩, ?_⟩
    · rw [hfz]; exact (c₁_sub_half_lt_lo₂ (c := c))
    · rw [hfz]; exact c.lo₂_lt_hi₁
    · exact c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball hp)
        ⟨by rw [hr]; exact c.ρs_lt_ρB, c.symm_sq_lt_of_mem_pBall' hp⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open hOo hzO
  refine ⟨ε, hε, fun u hu => ?_⟩
  obtain ⟨⟨⟨hwT, -, hwζ⟩, hw1, hw2⟩, hwA⟩ := hεO u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hwζ' : ‖c.ζ (k.cancellationFlow u z)‖ < k.δ' := hwζ
  have hwS : k.cancellationFlow u z ∈ k.closedFlowTube :=
    k.mem_closedFlowTube_iff.2 ⟨hwT, ⟨hw1.le, hw2.le.trans c.hi₁_mem_levels⟩, hwζ'.le⟩
  rcases le_or_gt c.lo₂ (f (k.cancellationFlow u z)) with h | h
  · exact k.middleTube_subset_crossingRegion ⟨hwS, h, hw2.le⟩
  · have hW := hk.closedFlowTube_low_subset_pClosedBall ⟨hwS, h.le⟩
    obtain ⟨y', hy', hy'u⟩ := hwA
    refine k.pClosedAnnulus_subset_crossingRegion ⟨y', ⟨hy'.1.le, ?_⟩, hy'u⟩
    have := c.symm_mem_of_mem_pClosedBall hW
    rwa [← hy'u, c.chart_p_symm_eq' hy'.2] at this

theorem local_pClosedAnnulus (hk : k.Good) {z : M} (hz : z ∈ c.pClosedAnnulus) (hF : z ∉ k.crossingExitSet) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.cancellationFlow u z ∈ k.crossingRegion := by
  obtain ⟨h1, h2⟩ := c.symm_mem_of_mem_pClosedAnnulus hz
  have hp := c.pClosedAnnulus_subset_pBall' hz
  have h1' : c.ρs < morseNorm n (c.e.χ.symm z) := by
    rcases h1.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hF
      exact Or.inl (c.e.mem_image_of_symm_mem (c.pBall'_subset_image_ball hp) h.symm)
  rcases h2.lt_or_eq with h | h
  · exact k.local_pClosedAnnulus_open hz h1' h
  · by_cases hin : z ∈ c.orientedChartTube ∧ ‖c.ζ z‖ < 2 * k.δ
    · exact k.local_pClosedAnnulus_sphere_tube hk hz h hin.1 hin.2
    · refine k.local_pClosedAnnulus_sphere_out hz h fun hT => ?_
      by_contra hlt
      exact hin ⟨hT, not_le.1 hlt⟩

theorem local_middleTube_open {z : M} (hz : z ∈ k.middleTube) (hlo : c.lo₂ < f z) (hhi : f z < c.hi₁) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.cancellationFlow u z ∈ k.crossingRegion := by
  have hO : k.cancellationFlow 0 z ∈ c.orientedChartTube ∩ {w | c.lo₂ < f w ∧ f w < c.hi₁} := by
    rw [k.cancellationFlow_zero]; exact ⟨k.middleTube_subset_orientedChartTube hz, hlo, hhi⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open (c.isOpen_orientedChartTube.inter
    ((isOpen_lt continuous_const c.hfs.continuous).inter
      (isOpen_lt c.hfs.continuous continuous_const))) hO
  refine ⟨ε, hε, fun u hu => ?_⟩
  have hband : ∀ v ∈ Icc 0 u, k.cancellationFlow v z ∈ c.orientedChartTube ∧ c.lo₂ ≤ f (k.cancellationFlow v z) ∧
      f (k.cancellationFlow v z) ≤ c.hi₁ := fun v hv => by
    have := hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩
    exact ⟨this.1, this.2.1.le, this.2.2.le⟩
  exact k.middleTube_subset_crossingRegion
    (k.cancellationFlow_mem_middleTube_of_band (k.norm_ζ_le_of_mem_closedFlowTube hz.1) hband u (right_mem_Icc.2 hu.1))

theorem qPositiveRegion_conditions (hk : k.Good) {z : M} (hz : z ∈ k.qPositiveRegion) {u : ℝ}
    (hq : ∀ v ∈ Icc 0 u, k.cancellationFlow v z ∈ c.qBall')
    (hσ : ∀ v ∈ Icc 0 u, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow v z))) (hu : 0 ≤ u) :
    ‖posPart c.d.hk (c.d.χ.symm (k.cancellationFlow u z))‖ ≤ k.ν ∧ c.qNormProductSq (c.d.χ.symm (k.cancellationFlow u z)) ≤ k.qNormProductBound := by
  have hy := k.symm_mem_qPositiveCoordinateRegion_of_mem_qPositiveRegion hk hz
  constructor
  · have hanti := k.antitoneOn_normSq_posPart_cancellationFlow hq
    have h1 : ‖posPart c.d.hk (c.d.χ.symm (k.cancellationFlow u z))‖ ^ 2 ≤
        ‖posPart c.d.hk (c.d.χ.symm (k.cancellationFlow 0 z))‖ ^ 2 :=
      hanti (left_mem_Icc.2 hu) (right_mem_Icc.2 hu) hu
    rw [k.cancellationFlow_zero] at h1
    have h2 : ‖posPart c.d.hk (c.d.χ.symm z)‖ ^ 2 ≤ k.ν ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hy.2.2.1 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) k.ν_pos.le two_ne_zero).1 (h1.trans h2)
  · have hanti := k.antitoneOn_qNormProductSq_cancellationFlow hq hσ
    have h1 : c.qNormProductSq (c.d.χ.symm (k.cancellationFlow u z)) ≤ c.qNormProductSq (c.d.χ.symm (k.cancellationFlow 0 z)) :=
      hanti (left_mem_Icc.2 hu) (right_mem_Icc.2 hu) hu
    rw [k.cancellationFlow_zero] at h1
    exact h1.trans hy.2.2.2

theorem local_qPositiveRegion_open (hk : k.Good) {z : M} (hz : z ∈ k.qPositiveRegion)
    (hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm z)) (hf : c.hi₁ < f z) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.cancellationFlow u z ∈ k.crossingRegion := by
  have hO : k.cancellationFlow 0 z ∈ c.qBall' ∩ {w | 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm w)} ∩
      {w | c.hi₁ < f w} := by
    rw [k.cancellationFlow_zero]; exact ⟨⟨k.qPositiveRegion_subset_qBall' hk hz, hu⟩, hf⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open
    ((c.isOpen_qBall'_inter (P := fun r => 0 < r) (isOpen_lt continuous_const continuous_id)).inter
      (isOpen_lt continuous_const c.hfs.continuous)) hO
  refine ⟨ε, hε, fun u hu => ?_⟩
  have hq : ∀ v ∈ Icc 0 u, k.cancellationFlow v z ∈ c.qBall' := fun v hv =>
    (hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩).1.1
  have hσ : ∀ v ∈ Icc 0 u, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow v z)) := fun v hv =>
    (hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩).1.2.le
  obtain ⟨hν, hQ⟩ := k.qPositiveRegion_conditions hk hz hq hσ hu.1
  obtain ⟨⟨huq, huσ⟩, huf⟩ := hεO u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have huf' : c.hi₁ < f (k.cancellationFlow u z) := huf
  refine k.qPositiveRegion_subset_crossingRegion (k.mem_qPositiveRegion_of_symm huq ⟨huσ.le, ?_, hν, hQ⟩)
  rw [← c.hi₁_le_iff (c.morseNorm_le_R_of_sq_lt (c.symm_sq_lt_of_mem_qBall' huq)),
    c.d.symm_image_eq (c.qBall'_subset_image_ball huq)]
  exact huf'.le

theorem local_qPositiveRegion_hi₁ (hk : k.Good) {z : M} (hz : z ∈ k.qPositiveRegion)
    (hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm z)) (hf : f z = c.hi₁) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.cancellationFlow u z ∈ k.crossingRegion := by
  have hzq := k.qPositiveRegion_subset_qBall' hk hz
  have hχ : c.d.χ (c.d.χ.symm z) = z := c.d.symm_image_eq (c.qBall'_subset_image_ball hzq)
  obtain ⟨-, hT⟩ := k.hi₁_face hk (k.symm_mem_qCoordinateRegion_of_mem_qRegion hk (k.qPositiveRegion_subset_qRegion hz))
    (by rw [hχ]; exact hf)
  rw [hχ] at hT
  have hO : k.cancellationFlow 0 z ∈ c.qBall' ∩ {w | 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm w)} ∩
      c.orientedChartTube ∩ {w | c.lo₂ < f w} := by
    rw [k.cancellationFlow_zero]; exact ⟨⟨⟨hzq, hu⟩, hT⟩, show c.lo₂ < f z by rw [hf]; exact c.lo₂_lt_hi₁⟩
  obtain ⟨ε, hε, hεO⟩ := k.exists_Icc_cancellationFlow_mem_open
    (((c.isOpen_qBall'_inter (P := fun r => 0 < r)
      (isOpen_lt continuous_const continuous_id)).inter c.isOpen_orientedChartTube).inter
      (isOpen_lt continuous_const c.hfs.continuous)) hO
  refine ⟨ε, hε, fun u hu => ?_⟩
  have hq : ∀ v ∈ Icc 0 u, k.cancellationFlow v z ∈ c.qBall' := fun v hv =>
    (hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩).1.1.1
  have hσ : ∀ v ∈ Icc 0 u, 0 ≤ c.σ * uq c.d.hk c.hkq (c.d.χ.symm (k.cancellationFlow v z)) := fun v hv =>
    (hεO v ⟨by linarith [hv.1], by linarith [hv.2, hu.2]⟩).1.1.2.le
  obtain ⟨hν, hQ⟩ := k.qPositiveRegion_conditions hk hz hq hσ hu.1
  obtain ⟨⟨⟨huq, huσ⟩, huT⟩, hulo⟩ := hεO u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hulo' : c.lo₂ < f (k.cancellationFlow u z) := hulo
  have hχu : c.d.χ (c.d.χ.symm (k.cancellationFlow u z)) = k.cancellationFlow u z :=
    c.d.symm_image_eq (c.qBall'_subset_image_ball huq)
  have huR := c.morseNorm_le_R_of_sq_lt (c.symm_sq_lt_of_mem_qBall' huq)
  rcases le_or_gt c.hi₁ (f (k.cancellationFlow u z)) with h | h
  · refine k.qPositiveRegion_subset_crossingRegion (k.mem_qPositiveRegion_of_symm huq ⟨huσ.le, ?_, hν, hQ⟩)
    rw [← c.hi₁_le_iff huR, hχu]
    exact h
  · have hζ : ‖c.ζ (k.cancellationFlow u z)‖ ≤ k.δ' := by
      have := (c.norm_ζ_le_iff_qNormProductSq_le k (c.symm_sq_lt_of_mem_qBall' huq)
        (by rw [hχu]; exact huT.1)).2 hQ
      rwa [hχu] at this
    refine k.middleTube_subset_crossingRegion ⟨k.mem_closedFlowTube_iff.2 ⟨huT, ⟨?_, ?_⟩, hζ⟩, hulo'.le, h.le⟩
    · linarith [(c₁_sub_half_lt_lo₂ (c := c))]
    · linarith [c.hi₁_mem_levels]

theorem local_qPositiveRegion (hk : k.Good) {z : M} (hz : z ∈ k.qPositiveRegion) (hF : z ∉ k.crossingExitSet) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.cancellationFlow u z ∈ k.crossingRegion := by
  have hzq := k.qPositiveRegion_subset_qBall' hk hz
  have hu : 0 < c.σ * uq c.d.hk c.hkq (c.d.χ.symm z) := by
    by_contra h
    exact hF (Or.inr ⟨hz, c.mem_qNonpositiveChartRegion_of hzq (not_lt.1 h)⟩)
  rcases (k.hi₁_le_f_of_mem_qRegion hk (k.qPositiveRegion_subset_qRegion hz)).lt_or_eq with h | h
  · exact k.local_qPositiveRegion_open hk hz hu h
  · exact k.local_qPositiveRegion_hi₁ hk hz hu h.symm

theorem local_crossingRegion (hk : k.Good) {z : M} (hz : z ∈ k.crossingRegion) (hF : z ∉ k.crossingExitSet) :
    ∃ ε > 0, ∀ u ∈ Icc 0 ε, k.cancellationFlow u z ∈ k.crossingRegion := by
  rcases hz with (h | h) | h
  · exact k.local_pClosedAnnulus hk h hF
  · rcases h.2.1.eq_or_lt with hlo | hlo
    · exact k.local_pClosedAnnulus hk (c.mem_pClosedAnnulus_of_mem_middleTube_lo₂ k hk h hlo.symm) hF
    rcases h.2.2.eq_or_lt with hhi | hhi
    · exact k.local_qPositiveRegion hk (c.mem_qPositiveRegion_of_mem_middleTube_hi₁ k hk h hhi) hF
    exact k.local_middleTube_open h hlo hhi
  · exact k.local_qPositiveRegion hk h hF

theorem cancellationFlow_mem_crossingRegion_until (hk : k.Good) {x : M} (hx : x ∈ k.crossingRegion) {t : ℝ}
    (hF : ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∉ k.crossingExitSet) : ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ k.crossingRegion := by
  have hQ : IsClosed {s : ℝ | k.cancellationFlow s x ∈ k.crossingRegion} :=
    (k.isCompact_crossingRegion hk).isClosed.preimage (k.continuous_cancellationFlow_curve x)
  refine Icc_subset_of_isClosed_of_step hQ (by simp [hx]) fun s hs hIcc => ?_
  have hsC : k.cancellationFlow s x ∈ k.crossingRegion := hIcc (right_mem_Icc.2 hs.1)
  obtain ⟨ε, hε, hεC⟩ := k.local_crossingRegion hk hsC (hF s (Ico_subset_Icc_self hs))
  refine mem_nhdsGT_iff_exists_Ioc_subset.2 ⟨min (s + ε) t, lt_min (by linarith) hs.2,
    fun s' hs' => ?_⟩
  have hs'ε : s' ≤ s + ε := hs'.2.trans (min_le_left _ _)
  change k.cancellationFlow s' x ∈ k.crossingRegion
  have := hεC (s' - s) ⟨by linarith [hs'.1], by linarith⟩
  rwa [k.cancellationFlow_cancellationFlow, add_sub_cancel] at this

theorem exists_hit_crossingExitSet (hk : k.Good) {x : M} (hx : x ∈ k.crossingRegion) :
    ∃ t, 0 ≤ t ∧ k.cancellationFlow t x ∈ k.crossingExitSet ∧ ∀ s ∈ Icc 0 t, k.cancellationFlow s x ∈ k.crossingRegion := by
  obtain ⟨t, ht, hexit⟩ := k.exists_exit_crossingRegion hk x hx
  obtain ⟨t₁, ht₁, -, ht₁F, hall, -⟩ := k.exists_first_hit_face (k.isCompact_crossingRegion hk).isClosed
    (k.isClosed_crossingExitSet hk) hx (fun t hF => k.cancellationFlow_mem_crossingRegion_until hk hx hF) ht hexit
  exact ⟨t₁, ht₁, ht₁F, hall⟩

theorem exists_f_le_a'_of_mem_qPositiveRegion_qNonpositiveChartRegion (hk : k.Good) {z : M} (hz : z ∈ k.qPositiveRegion)
    (hF : z ∈ c.qNonpositiveChartRegion) : ∃ T, 0 ≤ T ∧ f (k.cancellationFlow T z) ≤ a' := by
  have hu : c.σ * uq c.d.hk c.hkq (c.d.χ.symm z) = 0 :=
    le_antisymm (c.σ_uq_le_of_mem_qNonpositiveChartRegion hF) (k.symm_mem_qPositiveCoordinateRegion_of_mem_qPositiveRegion hk hz).1
  exact k.exists_f_le_a'_of_mem_qNegativeRegion hk (k.mem_qNegativeRegion_of_mem_qPositiveRegion hk hz hu)

theorem exists_f_le_a'_of_mem_pAxialAnnulus_middleTube (hk : k.Good) {x : M} (hx2 : x ∈ k.pAxialAnnulus)
    (hxT : x ∈ k.middleTube) (hf : f x = c.lo₂) : ∃ T, 0 ≤ T ∧ f (k.cancellationFlow T x) ≤ a' := by
  obtain ⟨t, ht, htF, hall⟩ := k.exists_hit_crossingExitSet hk (k.middleTube_subset_crossingRegion hxT)
  rcases htF with hS | ⟨hR, hM⟩
  · exfalso
    obtain ⟨y₀, hy₀, hy₀t⟩ := hS
    have hy₀' : morseNorm n y₀ = c.ρs := hy₀
    have hy₀sq : morseNorm n y₀ ^ 2 < 3 * c.ε := by rw [hy₀']; exact ρs_sq_lt (c := c)
    have htp : k.cancellationFlow t x ∈ c.pBall' := ⟨y₀, hy₀sq, hy₀t⟩
    have hsymm : c.e.χ.symm (k.cancellationFlow t x) = y₀ := by
      rw [← hy₀t, c.chart_p_symm_eq' hy₀sq]
    have hxp := c.pClosedBall_subset_pBall' (k.pAxialAnnulus_subset_pClosedBall hx2)
    obtain ⟨-, -, hB⟩ := (k.mem_pAxialAnnulus_iff (c.pBall'_subset_image_ball hxp)).1 hx2
    have hmono := k.antitoneOn_lyapunovFunction_cancellationFlow hk hall
    have hL : c.lyapunovFunction (k.cancellationFlow t x) ≤ c.lyapunovFunction (k.cancellationFlow 0 x) := hmono (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
    rw [k.cancellationFlow_zero, c.lyapunovFunction_of_mem_pBall' hxp, c.lyapunovFunction_of_mem_pBall' htp, hsymm] at hL
    have hBy₀ : axialDefect c.e₁ y₀ ≤ k.b₀ := hL.trans hB
    have hdot := k.dot_pCancellationField_pos_of_inner_sphere hy₀' hBy₀
    have hd := k.hasDerivAt_morseNormSq_cancellationFlow_p htp
    rw [hsymm] at hd
    have hev := eventually_lt_left_of_hasDerivAt_pos (by linarith : 0 < 2 * dot y₀ (k.pCancellationField y₀)) hd
    have htpos : 0 < t := by
      rcases ht.eq_or_lt with h | h
      · exfalso
        have := hk.closedFlowTube_lo₂_radius hxT.1 hf
        rw [← h, k.cancellationFlow_zero] at hsymm
        rw [hsymm, hy₀'] at this
        exact c.ρs_lt_ρB.ne this.2
      · exact h
    have hflt : f (k.cancellationFlow t x) < c.lo₂ := by
      rw [c.f_eq_of_mem_pBall' htp, hsymm, hy₀']
      have := c.ρB_sq_eq
      have := pow_lt_pow_left₀ c.ρs_lt_ρB c.ρs_pos.le two_ne_zero
      linarith
    have hO : k.cancellationFlow t x ∈ c.pBall' ∩ {w | f w < c.lo₂} := ⟨htp, hflt⟩
    have hmem : ∀ᶠ s in 𝓝[<] t, k.cancellationFlow s x ∈ c.pBall' ∩ {w | f w < c.lo₂} :=
      nhdsWithin_le_nhds ((k.continuous_cancellationFlow_curve x).continuousAt.preimage_mem_nhds
        ((c.isOpen_pBall'.inter (isOpen_lt c.hfs.continuous continuous_const)).mem_nhds hO))
    obtain ⟨s, ⟨hlt, hsp, hsf⟩, hs⟩ := ((hev.and hmem).and (Ioo_mem_nhdsLT htpos)).exists
    have hsC := hall s ⟨hs.1.le, hs.2.le⟩
    have hsf' : f (k.cancellationFlow s x) < c.lo₂ := hsf
    rw [hsymm, hy₀'] at hlt
    rcases hsC with (hA | hT) | hR
    · have := (c.symm_mem_of_mem_pClosedAnnulus hA).1
      have h2 := pow_le_pow_left₀ c.ρs_pos.le this 2
      linarith
    · linarith [hT.2.1]
    · linarith [k.f_ge_lo₂_of_mem_qPositiveRegion hk hR]
  · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_qPositiveRegion_qNonpositiveChartRegion hk hR hM
    exact ⟨t + T, by linarith, by rw [k.cancellationFlow_add]; exact hfT⟩

theorem exists_f_le_a'_of_mem_pClosedBall (hk : k.Good) {x : M} (hx : x ∈ c.pClosedBall) :
    ∃ T, 0 ≤ T ∧ f (k.cancellationFlow T x) ≤ a' := by
  obtain ⟨t, ht, hW2, hT, hf⟩ := k.exists_reach_pAxialAnnulus_middleTube hk hx
  obtain ⟨T, hT', hfT⟩ := k.exists_f_le_a'_of_mem_pAxialAnnulus_middleTube hk hW2 hT hf
  exact ⟨t + T, by linarith, by rw [k.cancellationFlow_add]; exact hfT⟩

theorem exists_f_le_a'_of_mem_crossingRegion (hk : k.Good) {x : M} (hx : x ∈ k.crossingRegion) :
    ∃ T, 0 ≤ T ∧ f (k.cancellationFlow T x) ≤ a' := by
  obtain ⟨t, ht, htF, -⟩ := k.exists_hit_crossingExitSet hk hx
  rcases htF with hS | ⟨hR, hM⟩
  · obtain ⟨y₀, hy₀, hy₀t⟩ := hS
    have hy₀' : morseNorm n y₀ = c.ρs := hy₀
    have hy₀B : morseNorm n y₀ ≤ c.ρB := by rw [hy₀']; exact c.ρs_lt_ρB.le
    have hW : k.cancellationFlow t x ∈ c.pClosedBall := ⟨y₀, hy₀B, hy₀t⟩
    obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_pClosedBall hk hW
    exact ⟨t + T, by linarith, by rw [k.cancellationFlow_add]; exact hfT⟩
  · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_qPositiveRegion_qNonpositiveChartRegion hk hR hM
    exact ⟨t + T, by linarith, by rw [k.cancellationFlow_add]; exact hfT⟩

theorem hi₁_mem_Icc : c.hi₁ ∈ Icc a' b' := by
  have h1 := c.a'_lt_lo₂
  have h2 := c.lo₂_lt_hi₁
  have h3 := c.c₂_add_η_lt_b'
  have h4 := c.η_pos
  unfold hi₁ at *
  exact ⟨by linarith, by linarith⟩

theorem exists_f_le_a'_of_mem_qRegion (hk : k.Good) {x : M} (hx : x ∈ k.qRegion) :
    ∃ T, 0 ≤ T ∧ f (k.cancellationFlow T x) ≤ a' := by
  obtain ⟨t, ht, hall, -, hface⟩ := k.exists_exit_qRegion_face hk hx
  have htR := hall t (right_mem_Icc.2 ht)
  rcases hface with hu | hf
  · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_qRegion_face hk htR hu
    exact ⟨t + T, by linarith, by rw [k.cancellationFlow_add]; exact hfT⟩
  set z := k.cancellationFlow t x with hzdef
  suffices h : ∃ T, 0 ≤ T ∧ f (k.cancellationFlow T z) ≤ a' by
    obtain ⟨T, hT, hfT⟩ := h
    exact ⟨t + T, by linarith, by rw [k.cancellationFlow_add]; exact hfT⟩
  have hzq := k.qRegion_subset_qBall' hk htR
  have hχ : c.d.χ (c.d.χ.symm z) = z := c.d.symm_image_eq (c.qBall'_subset_image_ball hzq)
  have hy := k.symm_mem_qCoordinateRegion_of_mem_qRegion hk htR
  obtain ⟨huB, hT⟩ := k.hi₁_face hk hy (by rw [hχ]; exact hf)
  rw [hχ] at hT
  have hsq := c.symm_sq_lt_of_mem_qBall' hzq
  by_cases hQ : c.qNormProductSq (c.d.χ.symm z) ≤ k.qNormProductBound
  · have hζ : ‖c.ζ z‖ ≤ k.δ' := by
      have := (c.norm_ζ_le_iff_qNormProductSq_le k hsq (by rw [hχ]; exact hT.1)).2 hQ
      rwa [hχ] at this
    have hzT : z ∈ k.middleTube :=
      ⟨k.mem_closedFlowTube_iff.2 ⟨hT, ⟨by rw [hf]; linarith [c₁_sub_half_lt_lo₂ (c := c), c.lo₂_lt_hi₁],
        by rw [hf]; exact c.hi₁_mem_levels⟩, hζ⟩, by rw [hf]; exact c.lo₂_lt_hi₁.le, hf.le⟩
    exact k.exists_f_le_a'_of_mem_crossingRegion hk (k.middleTube_subset_crossingRegion hzT)
  push Not at hQ
  have hζ : k.δ' < ‖c.ζ z‖ := by
    by_contra h
    push Not at h
    have := (c.norm_ζ_le_iff_qNormProductSq_le k hsq (by rw [hχ]; exact hT.1)).1 (by rw [hχ]; exact h)
    linarith
  have hv : posPart c.d.hk (c.d.χ.symm z) ≠ 0 := by
    intro h
    have : c.qNormProductSq (c.d.χ.symm z) = 0 := by unfold qNormProductSq; rw [h, norm_zero]; ring
    linarith [k.qNormProductBound_pos]
  have hzK : z ∉ k.perturbationSupportRegion := by
    rintro ((hKp | hKq) | hS)
    · exact (c.D.disjoint p c.hp q c.hq c.p_ne_q).notMem_of_mem_left
        (image_mono k.pSupportRegion_subset_ball hKp) (c.qBall'_subset_image_ball hzq)
    · obtain ⟨y', hy', hy'z⟩ := hKq
      have hy'eq : c.d.χ.symm z = y' := by
        rw [← hy'z, c.d.χ.left_inv (c.d.hball (k.qSupportRegion_subset_ball hy'))]
      have h1 := hy'.1
      rw [← hy'eq] at h1
      have h2 : uq c.d.hk c.hkq (c.d.χ.symm z) ^ 2 =
          c.uB ^ 2 + ‖posPart c.d.hk (c.d.χ.symm z)‖ ^ 2 := by
        have := c.f_chart_q (c.morseNorm_le_R_of_sq_lt hsq)
        rw [hχ, hf] at this
        rw [c.uB_sq_eq]
        linarith
      have h3 : 0 < ‖posPart c.d.hk (c.d.χ.symm z)‖ ^ 2 := by positivity
      linarith
    · exact absurd (k.norm_ζ_le_of_mem_closedFlowTube hS) (not_le.2 hζ)
  obtain ⟨t₁, ht₁, hhit, hbefore⟩ := k.exists_hit_perturbationSupportRegion_or_bottom (x := z)
    (by rw [hf]; exact hi₁_mem_Icc (c := c))
  rcases hhit with hK | hle
  · have ht₁pos : 0 < t₁ := by
      rcases ht₁.eq_or_lt with h | h
      · exfalso; rw [← h, k.cancellationFlow_zero] at hK; exact hzK hK
      · exact h
    have hflow := k.flow_eq_cancellationFlow_of_avoid (fun s hs => (hbefore s hs).1)
    have hd : HasDerivAt (fun s => f (c.D.flow s z)) (dfV I f c.D.V (c.D.flow 0 z)) 0 :=
      hasDerivAt_df_comp_integralCurve f c.hfs c.D.V (c.D.isMIntegralCurve_flow z) 0
    have hfz : f z ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η) := by
      rw [hf]
      have h1 := c.lo₂_lt_hi₁
      have h2 := c.η_pos
      have h3 := c₁_sub_half_lt_lo₂ (c := c)
      unfold hi₁ at *
      exact ⟨by linarith, by linarith⟩
    rw [c.D.flow_zero, c.dfV_V_eq_neg_one_of_mem_tube hfz] at hd
    have hev := eventually_lt_of_hasDerivAt_neg (by norm_num : (-1 : ℝ) < 0) hd
    obtain ⟨s₁, hlt, hs₁⟩ := (hev.and (Ioc_mem_nhdsGT ht₁pos)).exists
    rw [c.D.flow_zero] at hlt
    have hfw : f (k.cancellationFlow t₁ z) < c.hi₁ := by
      rw [← hflow t₁ (right_mem_Icc.2 ht₁)]
      have := f_flow_le c.hfs (D := c.D) (c.D.flow s₁ z) (t := t₁ - s₁) (by linarith [hs₁.2])
      rw [flow_flow, add_sub_cancel] at this
      linarith
    rcases k.mem_perturbationSupportRegion_cases hk hK with hW | hT | hR
    · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_pClosedBall hk hW
      exact ⟨t₁ + T, by linarith, by rw [k.cancellationFlow_add]; exact hfT⟩
    · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_crossingRegion hk (k.middleTube_subset_crossingRegion hT)
      exact ⟨t₁ + T, by linarith, by rw [k.cancellationFlow_add]; exact hfT⟩
    · exact absurd (k.hi₁_le_f_of_mem_qRegion hk hR) (not_le.2 hfw)
  · exact ⟨t₁, ht₁, hle⟩

theorem exists_f_le_a'_of_mem_perturbationSupportRegion (hk : k.Good) {x : M} (hx : x ∈ k.perturbationSupportRegion) :
    ∃ T, 0 ≤ T ∧ f (k.cancellationFlow T x) ≤ a' := by
  rcases k.mem_perturbationSupportRegion_cases hk hx with hW | hT | hR
  · exact k.exists_f_le_a'_of_mem_pClosedBall hk hW
  · exact k.exists_f_le_a'_of_mem_crossingRegion hk (k.middleTube_subset_crossingRegion hT)
  · exact k.exists_f_le_a'_of_mem_qRegion hk hR

theorem exists_f_cancellationFlow_le_a' (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ T, 0 ≤ T ∧ f (k.cancellationFlow T x) ≤ a' := by
  obtain ⟨t, ht, hhit, -⟩ := k.exists_hit_perturbationSupportRegion_or_bottom hx
  rcases hhit with hK | hle
  · obtain ⟨T, hT, hfT⟩ := k.exists_f_le_a'_of_mem_perturbationSupportRegion hk hK
    exact ⟨t + T, by linarith, by rw [k.cancellationFlow_add]; exact hfT⟩
  · exact ⟨t, ht, hle⟩

theorem reaches_bottom (hk : k.Good) {x : M} (hx : f x ∈ Icc a' b') :
    ∃ t, 0 ≤ t ∧ f (k.cancellationFlow t x) = a' ∧ ∀ s ∈ Ico 0 t, a' < f (k.cancellationFlow s x) := by
  obtain ⟨T, hT, hfT⟩ := k.exists_f_cancellationFlow_le_a' hk hx
  have hcl : IsClosed (f ⁻¹' Iic a') := isClosed_Iic.preimage c.hfs.continuous
  obtain ⟨t, ht, htK, hmin⟩ := exists_first_time hcl (k.continuous_cancellationFlow_curve x) (t := T)
    ⟨T, ⟨hT, le_rfl⟩, hfT⟩
  have hgt : ∀ s ∈ Ico 0 t, a' < f (k.cancellationFlow s x) := fun s hs => not_le.1 (hmin s hs)
  refine ⟨t, ht.1, le_antisymm htK ?_, hgt⟩
  rcases ht.1.eq_or_lt with h | h
  · rw [← h, k.cancellationFlow_zero]; exact hx.1
  · have := k.mem_of_mem_Ico (A := f ⁻¹' Ici a') (isClosed_Ici.preimage c.hfs.continuous) h
      (fun s hs => (hgt s hs).le)
    exact this

end CancelConsts

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
