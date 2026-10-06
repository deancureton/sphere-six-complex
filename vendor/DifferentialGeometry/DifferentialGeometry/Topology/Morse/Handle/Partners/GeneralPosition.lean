module

public import DifferentialGeometry.Topology.Morse.Handle.Partners.PartnerMove

@[expose] public section

set_option autoImplicit false

open Set Filter Function

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart)

namespace IndexOnePartner

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

section Engines

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

theorem exists_small_cells {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {F : E → X} (hF : Continuous F)
    (G : X → Set X) (hG : ∀ x, IsOpen (G x) ∧ x ∈ G x) {K W : Set E} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (C N : Fin m → Set E) (x : Fin m → X), (∀ j, IsCompact (C j)) ∧
      (∀ j, IsOpen (N j)) ∧ (∀ j, C j ⊆ N j) ∧ (∀ j, IsCompact (closure (N j))) ∧
      (∀ j, closure (N j) ⊆ W) ∧ (∀ j, F '' closure (N j) ⊆ G (x j)) ∧
      (∀ j, ∀ z ∈ closure (N j), ∀ z' ∈ closure (N j), ‖z - z'‖ < δ) ∧
      (∀ j, x j ∈ F '' (K ∩ C j)) ∧ K ⊆ ⋃ j, interior (C j) := by
  classical
  have hr : ∀ z : E, ∃ r : ℝ, 0 < r ∧ (z ∈ K → r < δ / 4 ∧
      Metric.closedBall z (2 * r) ⊆ W ∩ F ⁻¹' G (F z)) := by
    intro z
    by_cases hz : z ∈ K
    · have hopen : IsOpen (W ∩ F ⁻¹' G (F z)) := hW.inter ((hG (F z)).1.preimage hF)
      obtain ⟨ε, hε, hball⟩ :=
        Metric.isOpen_iff.mp hopen z ⟨hKW hz, (hG (F z)).2⟩
      refine ⟨min (ε / 4) (δ / 8), lt_min (by linarith) (by linarith), fun _ => ⟨?_, ?_⟩⟩
      · have := min_le_right (ε / 4) (δ / 8); linarith
      · refine (Metric.closedBall_subset_ball ?_).trans hball
        have := min_le_left (ε / 4) (δ / 8); linarith
    · exact ⟨1, one_pos, fun h => absurd h hz⟩
  choose r hrpos hrK using hr
  obtain ⟨t, htK, hcover⟩ :=
    hK.elim_nhds_subcover (fun z => Metric.ball z (r z))
      (fun z _ => Metric.ball_mem_nhds z (hrpos z))
  let e : Fin t.card ≃ t := t.equivFin.symm
  let zc : Fin t.card → E := fun j => (e j : E)
  have hzcK : ∀ j, zc j ∈ K := fun j => htK _ (e j).2
  have hclN : ∀ j, closure (Metric.ball (zc j) (2 * r (zc j))) ⊆
      Metric.closedBall (zc j) (2 * r (zc j)) := fun j => Metric.closure_ball_subset_closedBall
  refine ⟨t.card, fun j => Metric.closedBall (zc j) (r (zc j)),
    fun j => Metric.ball (zc j) (2 * r (zc j)), fun j => F (zc j),
    fun j => isCompact_closedBall _ _, fun j => Metric.isOpen_ball, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact Metric.closedBall_subset_ball (by linarith [hrpos (zc j)])
  · intro j
    exact (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure (hclN j)
  · intro j
    exact ((hclN j).trans ((hrK _ (hzcK j)).2)).trans inter_subset_left
  · intro j
    rintro _ ⟨w, hw, rfl⟩
    exact ((hrK _ (hzcK j)).2 (hclN j hw)).2
  · intro j w hw w' hw'
    have h1 := hclN j hw
    have h2 := hclN j hw'
    rw [Metric.mem_closedBall, dist_eq_norm] at h1 h2
    have h3 : ‖w - w'‖ ≤ ‖w - zc j‖ + ‖w' - zc j‖ := by
      calc ‖w - w'‖ = ‖(w - zc j) - (w' - zc j)‖ := by congr 1; abel
        _ ≤ ‖w - zc j‖ + ‖w' - zc j‖ := norm_sub_le _ _
    have h4 := (hrK _ (hzcK j)).1
    linarith
  · intro j
    exact ⟨zc j, ⟨hzcK j, Metric.mem_closedBall_self (hrpos (zc j)).le⟩, rfl⟩
  · intro w hw
    have hw' := hcover hw
    simp only [mem_iUnion] at hw'
    obtain ⟨z, hzt, hwz⟩ := hw'
    refine mem_iUnion.mpr ⟨e.symm ⟨z, hzt⟩, ?_⟩
    have hz : zc (e.symm ⟨z, hzt⟩) = z := by simp [zc]
    change w ∈ interior (Metric.closedBall (zc (e.symm ⟨z, hzt⟩)) (r (zc (e.symm ⟨z, hzt⟩))))
    rw [hz]
    exact Metric.ball_subset_interior_closedBall hwz

theorem isOpen_periodic_imp {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {τ : E} (hτ : τ ≠ 0) {K : Set E} (hK : IsCompact K) {V : Set X}
    (hV : IsOpen V) :
    IsOpen {q : E × X | (∃ k : ℤ, q.1 + (k : ℝ) • τ ∈ K) → q.2 ∈ V} := by
  have hτn : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hK.isBounded
  have hLF : LocallyFinite (fun k : ℤ => (fun z : E => z + (k : ℝ) • τ) ⁻¹' K) := by
    intro x
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
    set N : ℤ := ⌈(R + ‖x‖ + 1) / ‖τ‖⌉
    refine (Set.finite_Icc (-N) N).subset ?_
    rintro k ⟨w, hwK, hwB⟩
    have h1 : ‖w + (k : ℝ) • τ‖ ≤ R := by
      simpa [dist_zero_right] using hR hwK
    have h2 : ‖w‖ < ‖x‖ + 1 := by
      have := norm_le_norm_add_norm_sub' w x
      rw [Metric.mem_ball, dist_eq_norm] at hwB
      linarith
    have h3 : |(k : ℝ)| * ‖τ‖ ≤ R + ‖x‖ + 1 := by
      have : ‖(k : ℝ) • τ‖ ≤ ‖w + (k : ℝ) • τ‖ + ‖w‖ := by
        have := norm_sub_le (w + (k : ℝ) • τ) w
        simpa using this
      rw [norm_smul, Real.norm_eq_abs] at this
      linarith
    have h4 : |(k : ℝ)| ≤ (N : ℝ) := by
      calc |(k : ℝ)| ≤ (R + ‖x‖ + 1) / ‖τ‖ := by rw [le_div_iff₀ hτn]; exact h3
        _ ≤ (N : ℝ) := Int.le_ceil _
    rw [abs_le] at h4
    constructor
    · have : ((-N : ℤ) : ℝ) ≤ (k : ℝ) := by push_cast; linarith [h4.1]
      exact_mod_cast this
    · exact_mod_cast h4.2
  have hS : IsClosed {z : E | ∃ k : ℤ, z + (k : ℝ) • τ ∈ K} := by
    have := hLF.isClosed_iUnion (fun k => hK.isClosed.preimage (continuous_id.add continuous_const))
    convert this using 1
    ext z; simp
  have : {q : E × X | (∃ k : ℤ, q.1 + (k : ℝ) • τ ∈ K) → q.2 ∈ V} =
      ({z : E | ∃ k : ℤ, z + (k : ℝ) • τ ∈ K}ᶜ ×ˢ (univ : Set X)) ∪ ((univ : Set E) ×ˢ V) := by
    ext ⟨z, y⟩
    simp only [mem_ofPred_eq, mem_union, mem_prod, mem_compl_iff, mem_univ, and_true, true_and]
    tauto
  rw [this]
  exact (hS.isOpen_compl.prod isOpen_univ).union (isOpen_univ.prod hV)

theorem exists_smooth_rel_euclid {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} (hg : Continuous g) {U : Set E} (hU : IsOpen U) (hgU : ContDiffOn ℝ ∞ g U)
    {P C N : Set E} (hP : IsClosed P) (hPU : P ⊆ U) (hC : IsCompact C) (hN : IsOpen N)
    (hCN : C ⊆ N) {η : ℝ} (hη : 0 < η) :
    ∃ g' : E → F, Continuous g' ∧
      (∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ ContDiffOn ℝ ∞ g' (U ∪ W)) ∧
      (∀ z ∈ P, g' z = g z) ∧ (∀ z, z ∉ N → g' z = g z) ∧ ∀ z, ‖g' z - g z‖ < η := by
  classical
  obtain ⟨h, hh⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const (𝓘(ℝ, E)) (n := (⊤ : ℕ∞))
    (t := fun z => Metric.ball (g z) η) (fun z => convex_ball _ _)
    (fun z => ⟨g z, (hg.continuousAt.eventually (Metric.ball_mem_nhds (g z) hη)).mono
      fun y hy => by simpa [Metric.mem_ball, dist_comm] using hy⟩)
  have hhs : ContDiff ℝ ∞ (h : E → F) := contMDiff_iff_contDiff.1 h.contMDiff
  have hK : IsClosed (C \ U) := (hC.diff hU).isClosed
  obtain ⟨χ, hχ1, hχ0, hχI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, E))
    (n := (⊤ : ℕ∞)) (s := C \ U) (t := N ∩ Pᶜ) hK
    (by
      rw [(hN.inter hP.isOpen_compl).interior_eq]
      exact fun z hz => ⟨hCN hz.1, fun hzP => hz.2 (hPU hzP)⟩)
  obtain ⟨O, hO, hKO, hOχ⟩ := mem_nhdsSet_iff_exists.1 hχ1
  have hχs : ContDiff ℝ ∞ (χ : E → ℝ) := contMDiff_iff_contDiff.1 χ.contMDiff
  refine ⟨fun z => g z + χ z • (h z - g z), ?_, ⟨U ∪ O, hU.union hO, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact hg.add (hχs.continuous.smul (hhs.continuous.sub hg))
  · intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · exact Or.inr (hKO ⟨hz, hzU⟩)
  · intro z hz
    apply ContDiffAt.contDiffWithinAt
    have hz' : z ∈ U ∨ z ∈ O := by
      rcases hz with hz | hz | hz
      · exact Or.inl hz
      · exact Or.inl hz
      · exact Or.inr hz
    rcases hz' with hz | hz
    · have hgz : ContDiffAt ℝ ∞ g z := hgU.contDiffAt (hU.mem_nhds hz)
      exact hgz.add (hχs.contDiffAt.smul (hhs.contDiffAt.sub hgz))
    · refine hhs.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [hO.mem_nhds hz] with y hy
      have : χ y = 1 := hOχ hy
      simp [this]
  · intro z hz
    have : χ z = 0 := hχ0 z (fun hz' => hz'.2 hz)
    simp [this]
  · intro z hz
    have : χ z = 0 := hχ0 z (fun hz' => hz hz'.1)
    simp [this]
  · intro z
    have h1 : ‖h z - g z‖ < η := by
      have := hh z
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have h2 : |χ z| ≤ 1 := abs_le.2 ⟨by linarith [(hχI z).1], (hχI z).2⟩
    calc ‖g z + χ z • (h z - g z) - g z‖ = |χ z| * ‖h z - g z‖ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖h z - g z‖ := by gcongr
      _ < η := by rwa [one_mul]

theorem dimH_affine_zeros_lt {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Submodule ℝ F}
    (hdim : Module.finrank ℝ E < Module.finrank ℝ S)
    (hSP : Module.finrank ℝ S ≤ Module.finrank ℝ P) {Z : Set E} (hZ : IsOpen Z)
    {Φ₀ : E → F} (hΦ₀ : ContDiffOn ℝ 1 Φ₀ Z) {L : E → P →L[ℝ] F} (hL : ContDiffOn ℝ 1 L Z)
    (hrange : ∀ z ∈ Z, LinearMap.range (L z : P →ₗ[ℝ] F) = S) :
    dimH {w : P | ∃ z ∈ Z, Φ₀ z + L z w = 0} < Module.finrank ℝ P := by
  classical
  set T : Set (E × P) := {x | x.1 ∈ Z ∧ Φ₀ x.1 + L x.1 x.2 = 0} with hT
  have hW : {w : P | ∃ z ∈ Z, Φ₀ z + L z w = 0} = Prod.snd '' T := by
    ext w
    constructor
    · rintro ⟨z, hz, h⟩
      exact ⟨(z, w), ⟨hz, h⟩, rfl⟩
    · rintro ⟨x, ⟨hz, h⟩, rfl⟩
      exact ⟨x.1, hz, h⟩
  set m : ℕ := Module.finrank ℝ E + (Module.finrank ℝ P - Module.finrank ℝ S) with hm
  have hmp : m < Module.finrank ℝ P := by omega
  have hTm : dimH T ≤ (m : ENNReal) := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨x, hxT, hx⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hcon
    obtain ⟨z₀, w₀⟩ := x
    obtain ⟨hz₀, -⟩ := hxT
    simp only at hz₀
    set K : Submodule ℝ P := LinearMap.ker (L z₀ : P →ₗ[ℝ] F) with hK
    have hrk : Module.finrank ℝ S + Module.finrank ℝ K = Module.finrank ℝ P := by
      have := LinearMap.finrank_range_add_finrank_ker (L z₀ : P →ₗ[ℝ] F)
      rw [hrange z₀ hz₀] at this
      exact this
    obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective K.subtype K.ker_subtype
    set Λ : P →ₗ[ℝ] K × F := π.prod (L z₀ : P →ₗ[ℝ] F) with hΛ
    have hΛker : LinearMap.ker Λ = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro v hv
      have h1 : π v = 0 := congrArg Prod.fst hv
      have h2 : (L z₀) v = 0 := congrArg Prod.snd hv
      have hvK : v ∈ K := h2
      have h3 : π (K.subtype ⟨v, hvK⟩) = ⟨v, hvK⟩ := LinearMap.congr_fun hπ ⟨v, hvK⟩
      simp only [Submodule.subtype_apply] at h3
      rw [h1] at h3
      exact (congrArg Subtype.val h3).symm
    obtain ⟨A, hA0, hA⟩ := Λ.exists_antilipschitzWith hΛker
    have hAv : ∀ v : P, ‖v‖ ≤ (A : ℝ) * (‖π v‖ + ‖L z₀ v‖) := by
      intro v
      have h := hA.le_mul_dist v 0
      rw [dist_zero_right, map_zero, dist_zero_right] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ A.2)
      refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
      · have := norm_nonneg (L z₀ v)
        change ‖π v‖ ≤ _
        linarith
      · have := norm_nonneg (π v)
        change ‖L z₀ v‖ ≤ _
        linarith
    obtain ⟨CΦ, UΦ, hUΦ, hΦlip⟩ := (hΦ₀.contDiffAt (hZ.mem_nhds hz₀)).exists_lipschitzOnWith
    obtain ⟨CL, UL, hUL, hLlip⟩ := (hL.contDiffAt (hZ.mem_nhds hz₀)).exists_lipschitzOnWith
    set ε : ℝ := 1 / (2 * ((A : ℝ) + 1)) with hε
    have hA0' : (0 : ℝ) ≤ A := A.2
    have hεpos : 0 < ε := by positivity
    have hAε : (A : ℝ) * ε ≤ 1 / 2 := by
      rw [hε, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hLcont : ∀ᶠ z in 𝓝 z₀, L z ∈ Metric.ball (L z₀) ε :=
      (hL.continuousOn.continuousAt (hZ.mem_nhds hz₀)).eventually (Metric.ball_mem_nhds _ hεpos)
    have hev : ∀ᶠ z in 𝓝 z₀, z ∈ Z ∧ z ∈ UΦ ∧ z ∈ UL ∧ L z ∈ Metric.ball (L z₀) ε :=
      Filter.Eventually.and (hZ.eventually_mem hz₀)
        (Filter.Eventually.and hUΦ (Filter.Eventually.and hUL hLcont))
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hev
    set r : ℝ := min δ 1 with hr
    have hr0 : 0 < r := lt_min hδ one_pos
    set t : Set (E × P) := T ∩ Metric.ball (z₀, w₀) r with ht
    have htn : t ∈ 𝓝[T] (z₀, w₀) := inter_mem_nhdsWithin T (Metric.ball_mem_nhds _ hr0)
    have hlt := hx t htn
    have hpt : ∀ x ∈ t, Φ₀ x.1 + L x.1 x.2 = 0 ∧ x.1 ∈ UΦ ∧ x.1 ∈ UL ∧
        ‖L x.1 - L z₀‖ < ε ∧ ‖x.2‖ ≤ ‖w₀‖ + 1 := by
      intro x hxt
      obtain ⟨⟨-, hx0⟩, hxb⟩ := hxt
      rw [Metric.mem_ball, Prod.dist_eq] at hxb
      have hd1 : dist x.1 z₀ < δ := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hxb (min_le_left _ _))
      have hd2 : dist x.2 w₀ < 1 := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hxb (min_le_right _ _))
      obtain ⟨-, h1, h2, h3⟩ := hδ' hd1
      refine ⟨hx0, h1, h2, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm] at h3
        exact h3
      · rw [dist_eq_norm] at hd2
        have := norm_le_insert' x.2 w₀
        linarith [norm_sub_norm_le x.2 w₀]
    set B : ℝ := (CL : ℝ) * (‖w₀‖ + 1) + CΦ with hB
    have hB0 : 0 ≤ B := by positivity
    have hkey : ∀ x ∈ t, ∀ y ∈ t,
        ‖x.2 - y.2‖ ≤ 2 * A * ‖π (x.2 - y.2)‖ + 2 * A * B * ‖x.1 - y.1‖ := by
      intro x hxt y hyt
      obtain ⟨hx0, hxΦ, hxL, hxε, hxw⟩ := hpt x hxt
      obtain ⟨hy0, hyΦ, hyL, hyε, hyw⟩ := hpt y hyt
      have e1 : L x.1 x.2 = -Φ₀ x.1 := eq_neg_of_add_eq_zero_right hx0
      have e2 : L y.1 y.2 = -Φ₀ y.1 := eq_neg_of_add_eq_zero_right hy0
      have hid : L z₀ (x.2 - y.2) = (L z₀ - L x.1) (x.2 - y.2) + (L y.1 - L x.1) y.2 +
          (Φ₀ y.1 - Φ₀ x.1) := by
        simp only [sub_apply, map_sub, e1, e2]
        abel
      have hn1 : ‖(L z₀ - L x.1) (x.2 - y.2)‖ ≤ ε * ‖x.2 - y.2‖ := by
        refine ((L z₀ - L x.1).le_opNorm _).trans ?_
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right hxε.le (norm_nonneg _)
      have hn2 : ‖(L y.1 - L x.1) y.2‖ ≤ (CL : ℝ) * ‖x.1 - y.1‖ * (‖w₀‖ + 1) := by
        refine ((L y.1 - L x.1).le_opNorm _).trans ?_
        have hl := hLlip.norm_sub_le hyL hxL
        rw [norm_sub_rev y.1 x.1] at hl
        exact mul_le_mul hl hyw (norm_nonneg _) (by positivity)
      have hn3 : ‖Φ₀ y.1 - Φ₀ x.1‖ ≤ (CΦ : ℝ) * ‖x.1 - y.1‖ := by
        have hl := hΦlip.norm_sub_le hyΦ hxΦ
        rwa [norm_sub_rev y.1 x.1] at hl
      have hLn : ‖L z₀ (x.2 - y.2)‖ ≤ ε * ‖x.2 - y.2‖ + B * ‖x.1 - y.1‖ := by
        rw [hid]
        refine (norm_add₃_le).trans ?_
        rw [hB]
        nlinarith
      have hv := hAv (x.2 - y.2)
      have h4 : (A : ℝ) * ‖L z₀ (x.2 - y.2)‖ ≤ (A : ℝ) * (ε * ‖x.2 - y.2‖ + B * ‖x.1 - y.1‖) :=
        mul_le_mul_of_nonneg_left hLn hA0'
      have h5 : (A : ℝ) * ε * ‖x.2 - y.2‖ ≤ 1 / 2 * ‖x.2 - y.2‖ :=
        mul_le_mul_of_nonneg_right hAε (norm_nonneg _)
      nlinarith
    have hdt : dimH t ≤ (m : ENNReal) := by
      set C : ℝ := 2 * A * (1 + B) + 1 with hC
      have hC0 : 0 ≤ C := by positivity
      let g : t → E × K := fun x => (x.1.1, π x.1.2)
      have hg : AntilipschitzWith C.toNNReal g := by
        refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
        rw [Real.coe_toNNReal _ hC0, Subtype.dist_eq, Prod.dist_eq, Prod.dist_eq]
        simp only [g, dist_eq_norm]
        have hk := hkey x.1 x.2 y.1 y.2
        rw [map_sub] at hk
        have ha : ‖x.1.1 - y.1.1‖ ≤ max ‖x.1.1 - y.1.1‖ ‖π x.1.2 - π y.1.2‖ := le_max_left _ _
        have hb : ‖π x.1.2 - π y.1.2‖ ≤ max ‖x.1.1 - y.1.1‖ ‖π x.1.2 - π y.1.2‖ :=
          le_max_right _ _
        have hm0 : 0 ≤ max ‖x.1.1 - y.1.1‖ ‖π x.1.2 - π y.1.2‖ :=
          le_trans (norm_nonneg _) ha
        have h2A : (0 : ℝ) ≤ 2 * A := by positivity
        have h2AB : (0 : ℝ) ≤ 2 * A * B := by positivity
        have hb' := mul_le_mul_of_nonneg_left hb h2A
        have ha' := mul_le_mul_of_nonneg_left ha h2AB
        refine max_le ?_ ?_
        · nlinarith
        · nlinarith
      have h1 : dimH t = dimH (univ : Set t) := by
        have hi := (isometry_subtype_coe (s := t)).dimH_image univ
        rw [Subtype.coe_image_univ] at hi
        exact hi
      rw [h1]
      refine (hg.le_dimH_image univ).trans ((dimH_mono (subset_univ _)).trans ?_)
      rw [Real.dimH_univ_eq_finrank, Module.finrank_prod]
      have hKr : Module.finrank ℝ K = Module.finrank ℝ P - Module.finrank ℝ S := by omega
      rw [hKr]
    exact absurd hlt (not_lt.mpr hdt)
  rw [hW]
  calc dimH (Prod.snd '' T) ≤ dimH T := LipschitzWith.prod_snd.dimH_image_le T
    _ ≤ (m : ENNReal) := hTm
    _ < (Module.finrank ℝ P : ENNReal) := by exact_mod_cast hmp

theorem exists_openPartialHomeomorph_of_inverse {Ψ : (Fin n → ℝ) → M} {Φ : M → (Fin n → ℝ)}
    {S : Set (Fin n → ℝ)} {T : Set M} (hS : IsOpen S) (hT : IsOpen T) (hΨS : MapsTo Ψ S T)
    (hΦT : MapsTo Φ T S) (hΦΨ : ∀ y ∈ S, Φ (Ψ y) = y) (hΨΦ : ∀ x ∈ T, Ψ (Φ x) = x)
    (hΨ : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ Ψ S) (hΦ : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ Φ T) :
    ∃ e : OpenPartialHomeomorph (Fin n → ℝ) M, e.source = S ∧ e.target = T ∧
      (∀ y ∈ S, e y = Ψ y) ∧ (∀ x ∈ T, e.symm x = Φ x) ∧
      ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ e e.source ∧
      ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ e.symm e.target := by
  let e : OpenPartialHomeomorph (Fin n → ℝ) M :=
    { toFun := Ψ
      invFun := Φ
      source := S
      target := T
      map_source' := hΨS
      map_target' := hΦT
      left_inv' := hΦΨ
      right_inv' := hΨΦ
      open_source := hS
      open_target := hT
      continuousOn_toFun := hΨ.continuousOn
      continuousOn_invFun := hΦ.continuousOn }
  have _hman : IsManifold I ∞ M := inferInstance
  have _hT2 : T2Space M := inferInstance
  have _hbd : I.Boundaryless := inferInstance
  exact ⟨e, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, hΨ, hΦ⟩

theorem exists_shrinkAll_factor (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {ρ : ℝ} (hρ : 0 < ρ)
    (hle : ∀ p hp, ρ ≤ (D.chart p hp).r₀) :
    ∃ E : GradientLikeStrip I f a b crit,
      (∀ p hp, (E.chart p hp).χ = (D.chart p hp).χ ∧ (E.chart p hp).k = (D.chart p hp).k ∧
        (E.chart p hp).R = (D.chart p hp).R ∧ (E.chart p hp).R' = (D.chart p hp).R') ∧
      (∀ p hp, (E.chart p hp).r₀ = ρ / 2) ∧ (∀ p hp, E.rm p hp = D.rm p hp) ∧
      (∀ x, (∀ p hp, x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}) →
        E.V x = D.V x) ∧
      ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ x, E.V x = φ x • D.V x := by
  classical
  have _hB : I.Boundaryless := inferInstance
  obtain ⟨E, hE1, hE2, hE3, hE4⟩ := GradientLikeStrip.exists_shrinkAll hf D hρ hle
  have hρ2 : (0 : ℝ) < ρ / 2 := by positivity
  set g : ∀ p ∈ crit, (Fin n → ℝ) → ℝ := fun p hp y =>
    ModelField.theta (ρ / 2) y / ModelField.theta (D.chart p hp).r₀ y - 1 with hg
  have hg_smooth : ∀ p hp, ContDiff ℝ ∞ (g p hp) := fun p hp =>
    ((ModelField.contDiff_theta hρ2).div (ModelField.contDiff_theta (D.chart p hp).hr₀)
      (fun y => (ModelField.theta_pos (D.chart p hp).hr₀ y).ne')).sub contDiff_const
  have hg_zero : ∀ p hp y, ¬ morseNorm n y ≤ (D.chart p hp).r₀ / 2 → g p hp y = 0 := by
    intro p hp y hy
    replace hy := not_le.1 hy
    have h1 := hle p hp
    have h2 := (D.chart p hp).hr₀
    simp only [hg]
    rw [ModelField.theta_eq hρ2 (by linarith), ModelField.theta_eq (D.chart p hp).hr₀ hy.le]
    have h3 : 0 < morseNorm n y := by linarith
    have h4 : (morseNorm n y ^ 2)⁻¹ ≠ 0 := by positivity
    rw [div_self h4, sub_self]
  have hKb : ∀ p hp, {y : Fin n → ℝ | morseNorm n y ≤ (D.chart p hp).r₀ / 2} ⊆
      Metric.ball 0 (D.chart p hp).R' := fun p hp y hy =>
    mem_ball_of_morseNorm_lt (lt_of_le_of_lt hy (by
      linarith [D.r₀_lt_rm p hp, D.rm_lt_R' p hp, (D.chart p hp).hr₀]))
  set φ : M → ℝ := fun x => ∏ p ∈ crit.attach, (1 + (D.chart p.1 p.2).pushFun (g p.1 p.2) x)
    with hφ
  have hφc : Continuous φ := continuous_finsetProd _ fun p _ =>
    continuous_const.add ((D.chart p.1 p.2).contMDiff_pushFun (hg_smooth _ _)
      (isCompact_morseNorm_le _) (hKb _ _) (fun y hy => hg_zero _ _ y hy)).continuous
  have hfac_pos : ∀ p hp x, 0 < 1 + (D.chart p hp).pushFun (g p hp) x := by
    intro p hp x
    by_cases hx : x ∈ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R'
    · obtain ⟨y, hy, rfl⟩ := hx
      rw [MorseNormalChart.pushFun_apply_chart _ hy]
      simp only [hg, add_sub_cancel]
      exact div_pos (ModelField.theta_pos hρ2 y) (ModelField.theta_pos (D.chart p hp).hr₀ y)
    · rw [MorseNormalChart.pushFun_apply_of_notMem _ hx]
      norm_num
  have hφpos : ∀ x, 0 < φ x := fun x => Finset.prod_pos fun p _ => hfac_pos p.1 p.2 x
  have hφone : ∀ x, (∀ p hp, x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}) →
      φ x = 1 := by
    intro x h
    refine Finset.prod_eq_one fun p _ => ?_
    rw [MorseNormalChart.pushFun_eq_zero_of_notMem_image (fun y hy => hg_zero _ _ y hy) (h p.1 p.2),
      add_zero]
  have hφhalf : ∀ p hp y, morseNorm n y ≤ (D.chart p hp).r₀ / 2 →
      φ ((D.chart p hp).χ y) = 1 + g p hp y := by
    intro p hp y hy
    have hyb := hKb p hp hy
    simp only [hφ]
    rw [Finset.prod_eq_single (⟨p, hp⟩ : {x // x ∈ crit})]
    · exact congrArg _ (MorseNormalChart.pushFun_apply_chart _ hyb)
    · intro q _ hqp
      have hne : p ≠ q.1 := fun h => hqp (Subtype.ext h.symm)
      rw [MorseNormalChart.pushFun_apply_of_notMem _
        (Set.disjoint_left.1 (D.disjoint p hp q.1 q.2 hne) (mem_image_of_mem _ hyb)), add_zero]
    · intro h
      exact absurd (Finset.mem_attach _ _) h
  refine ⟨E, hE1, hE2, hE3, hE4, φ, hφc, ?_, ?_⟩
  · set K : Set M := ⋃ p : {x // x ∈ crit},
      (D.chart p.1 p.2).χ '' {y | morseNorm n y ≤ (D.chart p.1 p.2).r₀ / 2} with hKdef
    have hK : IsCompact K := isCompact_iUnion fun p => D.isCompact_halfBall p.1 p.2
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφc.continuousOn
    obtain ⟨C', hC'⟩ := hK.exists_bound_of_continuousOn
      (hφc.inv₀ fun x => (hφpos x).ne').continuousOn
    refine ⟨(max C' 1)⁻¹, max C 1, by positivity, fun x => ?_⟩
    by_cases hx : x ∈ K
    · have h1 := hC x hx
      have h2 := hC' x hx
      rw [Real.norm_eq_abs] at h1 h2
      have h3 : (φ x)⁻¹ ≤ max C' 1 := (le_abs_self _).trans (h2.trans (le_max_left _ _))
      refine ⟨?_, (le_abs_self _).trans (h1.trans (le_max_left _ _))⟩
      exact inv_le_of_inv_le₀ (hφpos x) h3
    · have hx' : ∀ p hp, x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2} :=
        fun p hp hxp => hx (mem_iUnion.2 ⟨⟨p, hp⟩, hxp⟩)
      rw [hφone x hx']
      exact ⟨inv_le_one_of_one_le₀ (le_max_right _ _), le_max_right _ _⟩
  · intro x
    by_cases h : ∀ p hp, x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}
    · rw [hφone x h, one_smul]
      exact hE4 x h
    · simp only [not_forall, not_not] at h
      obtain ⟨p, hp, y, hy, rfl⟩ := h
      rw [hφhalf p hp y hy]
      have hy' : morseNorm n y ≤ (D.chart p hp).r₀ / 2 := hy
      have hymr : morseNorm n y < D.rm p hp := by
        linarith [D.r₀_lt_rm p hp, (D.chart p hp).hr₀]
      set d := D.chart p hp with hd
      have hyb : y ∈ Metric.ball (0 : Fin n → ℝ) d.R' := hKb p hp hy
      have hxb : d.χ y ∈ d.χ '' Metric.ball 0 d.R' := mem_image_of_mem _ hyb
      have hinv : ∀ v : TangentSpace I (d.χ y),
          mfderiv 𝓘(ℝ, Fin n → ℝ) I d.χ (d.χ.symm (d.χ y))
            (mfderiv I 𝓘(ℝ, Fin n → ℝ) d.χ.symm (d.χ y) v) = v := by
        intro v
        have hcomp := mfderiv_comp (I' := 𝓘(ℝ, Fin n → ℝ)) (d.χ y)
          (d.mdifferentiableAt_chart (d.symm_mem_ball hxb)) (d.mdifferentiableAt_symm hxb)
        have hev : (d.χ ∘ d.χ.symm) =ᶠ[𝓝 (d.χ y)] id :=
          eventuallyEq_of_mem (d.isOpen_image_ball.mem_nhds hxb) fun x hx => d.symm_image_eq hx
        have h1 := hev.mfderiv_eq (I := I) (I' := I)
        rw [mfderiv_id] at h1
        exact DFunLike.congr_fun (hcomp.symm.trans h1) v
      have hDm := D.model p hp y hymr
      have hEm := E.model p hp y (by rw [hE3 p hp]; exact hymr)
      rw [(hE1 p hp).1, (hE1 p hp).2.1, hE2 p hp] at hEm
      have key : ModelField.modelField d.k (ρ / 2) y =
          (1 + g p hp y) • ModelField.modelField d.k d.r₀ y := by
        rw [ModelField.modelField, ModelField.modelField, smul_smul]
        congr 1
        have := ModelField.theta_pos d.hr₀ y
        simp only [hg]
        rw [add_sub_cancel]
        exact (div_mul_cancel₀ _ this.ne').symm
      refine (hinv _).symm.trans (Eq.trans ?_ (hinv _))
      congr 1
      rw [map_smul, hEm, hDm]
      exact key

theorem exists_shrink_free (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {Kdn Kup : Set M} (hKdn : IsCompact Kdn) (hKup : IsCompact Kup) {Tdn Tup : ℝ}
    (hTdn : 0 ≤ Tdn) (hTup : 0 ≤ Tup)
    (hdn : ∀ x ∈ Kdn, a ≤ f x - Tdn ∧ f x ≤ b ∧ ∃ t, 0 ≤ t ∧ f (D.flow t x) < f x - Tdn)
    (hup : ∀ x ∈ Kup, a ≤ f x ∧ f x + Tup ≤ b ∧ ∃ t, t ≤ 0 ∧ f x + Tup < f (D.flow t x))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ D' : GradientLikeStrip I f a b crit,
      (∀ p hp, (D'.chart p hp).χ = (D.chart p hp).χ ∧ (D'.chart p hp).k = (D.chart p hp).k ∧
        (D'.chart p hp).R = (D.chart p hp).R ∧ (D'.chart p hp).R' = (D.chart p hp).R' ∧
        (D'.chart p hp).r₀ ≤ (D.chart p hp).r₀ ∧ (D'.chart p hp).r₀ ≤ ρ) ∧
      (∀ p hp, D'.rm p hp = D.rm p hp) ∧
      (∀ x, (∀ p hp, x ∉ D.closedSmallBall p hp) → D'.V x = D.V x) ∧
      (∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ x, D'.V x = φ x • D.V x) ∧
      (∀ x ∈ Kdn, descendsFreely D' Tdn x) ∧ ∀ x ∈ Kup, ascendsFreely D' Tup x := by
  classical
  have hfc : Continuous f := hf.continuous
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Kdn ⊆ {x | f (D.flow N x) < f x - Tdn} := by
    refine hKdn.elim_directed_cover (fun N : ℕ => {x | f (D.flow N x) < f x - Tdn})
      (fun N => ?_) ?_ ?_
    · exact isOpen_lt (hfc.comp (D.continuous_flow _)) (hfc.sub continuous_const)
    · intro x hx
      obtain ⟨-, -, t, -, ht⟩ := hdn x hx
      obtain ⟨N, hN⟩ := exists_nat_ge t
      exact mem_iUnion.2 ⟨N, show f (D.flow N x) < f x - Tdn from
        lt_of_le_of_lt (GradientLikeStrip.f_flow_antitone (D := D) hf x hN) ht⟩
    · refine Monotone.directed_le fun N N' hNN' x hx => ?_
      exact show f (D.flow N' x) < f x - Tdn from lt_of_le_of_lt
        (GradientLikeStrip.f_flow_antitone (D := D) hf x (Nat.cast_le.2 hNN')) hx
  obtain ⟨N', hN'⟩ : ∃ N : ℕ, Kup ⊆ {x | f x + Tup < f (D.flow (-(N : ℝ)) x)} := by
    refine hKup.elim_directed_cover (fun N : ℕ => {x | f x + Tup < f (D.flow (-(N : ℝ)) x)})
      (fun N => ?_) ?_ ?_
    · exact isOpen_lt (hfc.add continuous_const) (hfc.comp (D.continuous_flow _))
    · intro x hx
      obtain ⟨-, -, t, -, ht⟩ := hup x hx
      obtain ⟨N, hN⟩ := exists_nat_ge (-t)
      exact mem_iUnion.2 ⟨N, show f x + Tup < f (D.flow (-(N : ℝ)) x) from
        lt_of_lt_of_le ht (GradientLikeStrip.f_flow_antitone (D := D) hf x (by linarith))⟩
    · refine Monotone.directed_le fun N N' hNN' x hx => ?_
      have hc : ((N : ℕ) : ℝ) ≤ N' := Nat.cast_le.2 hNN'
      exact show f x + Tup < f (D.flow (-(N' : ℝ)) x) from lt_of_lt_of_le hx
        (GradientLikeStrip.f_flow_antitone (D := D) hf x (by linarith))
  set S : Set M := (fun q : ℝ × M => D.flow q.1 q.2) ''
    (Icc (0 : ℝ) N ×ˢ Kdn ∪ Icc (-(N' : ℝ)) 0 ×ˢ Kup) with hSdef
  have hS : IsCompact S :=
    ((isCompact_Icc.prod hKdn).union (isCompact_Icc.prod hKup)).image D.continuous_flow_joint
  have hScrit : ∀ p ∈ crit, p ∉ S := by
    rintro p hp ⟨⟨s, x⟩, hq, hfl⟩
    simp only at hfl
    have hxp : p = x := by
      have := D.flow_neg_flow x s
      rwa [hfl, D.flow_crit hp] at this
    subst hxp
    rcases hq with ⟨-, hx⟩ | ⟨-, hx⟩
    · have := hN hx
      simp only [mem_ofPred_eq, D.flow_crit hp] at this
      linarith
    · have := hN' hx
      simp only [mem_ofPred_eq, D.flow_crit hp] at this
      linarith
  have hloc : ∀ p (hp : p ∈ crit), ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ ρ ∧ δ ≤ (D.chart p hp).r₀ ∧
      ∀ y, morseNorm n y ≤ δ / 2 → (D.chart p hp).χ y ∉ S := by
    intro p hp
    have hR : 0 < (D.chart p hp).R := by linarith [(D.chart p hp).hr₀R, (D.chart p hp).hr₀]
    have h0src : (0 : Fin n → ℝ) ∈ (D.chart p hp).χ.source :=
      (D.chart p hp).hsrc 0 (by rw [morseNorm_zero]; exact hR.le)
    have hmem : (D.chart p hp).χ ⁻¹' Sᶜ ∈ 𝓝 (0 : Fin n → ℝ) := by
      refine ((D.chart p hp).χ.continuousAt h0src).preimage_mem_nhds
        (hS.isClosed.isOpen_compl.mem_nhds ?_)
      rw [(D.chart p hp).hχ0]
      exact hScrit p hp
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
    have hpos : 0 < min ε (min ρ (D.chart p hp).r₀) :=
      lt_min hε (lt_min hρ (D.chart p hp).hr₀)
    refine Filter.eventually_of_mem (Ioo_mem_nhdsGT hpos) fun δ hδ => ⟨?_, ?_, ?_⟩
    · exact hδ.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact hδ.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    · intro y hy
      have hδε : δ < ε := hδ.2.trans_le (min_le_left _ _)
      have hy' : morseNorm n y < ε := by linarith [hδ.1]
      exact hball (mem_ball_of_morseNorm_lt hy')
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ p ∈ crit, ∀ hp : p ∈ crit, δ ≤ ρ ∧
      δ ≤ (D.chart p hp).r₀ ∧ ∀ y, morseNorm n y ≤ δ / 2 → (D.chart p hp).χ y ∉ S :=
    (Filter.eventually_all_finset crit).2 fun p hp => (hloc p hp).mono fun δ hδ _ => hδ
  obtain ⟨ρ', hρ'all, hρ'pos⟩ := (hall.and self_mem_nhdsWithin).exists
  have hρ'0 : (0 : ℝ) < ρ' := hρ'pos
  obtain ⟨E, hEch, hEr₀, hErm, hEV, φ, hφc, ⟨m, M₀, hm, hφb⟩, hEφ⟩ :=
    exists_shrinkAll_factor hf D hρ'0 fun p hp => (hρ'all p hp hp).2.1
  have hnotS : ∀ z ∈ S, ∀ p (hp : p ∈ crit), z ∉ E.closedSmallBall p hp := by
    intro z hz p hp hmem
    obtain ⟨y, hy, hyeq⟩ := hmem
    have hy' : morseNorm n y ≤ ρ' / 2 := by rw [← hEr₀ p hp]; exact hy
    rw [(hEch p hp).1] at hyeq
    exact (hρ'all p hp hp).2.2 y hy' (hyeq ▸ hz)
  refine ⟨E, fun p hp => ⟨(hEch p hp).1, (hEch p hp).2.1, (hEch p hp).2.2.1,
    (hEch p hp).2.2.2, ?_, ?_⟩, hErm, ?_, ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hEφ⟩, ?_, ?_⟩
  · rw [hEr₀ p hp]; linarith [(hρ'all p hp hp).2.1]
  · rw [hEr₀ p hp]; linarith [(hρ'all p hp hp).1]
  · intro x hx
    refine hEV x fun p hp hmem => hx p hp ?_
    obtain ⟨y, hy, rfl⟩ := hmem
    exact ⟨y, le_trans (show morseNorm n y ≤ (D.chart p hp).r₀ / 2 from hy)
      (by linarith [(D.chart p hp).hr₀]), rfl⟩
  · intro x hx s hs p hp
    obtain ⟨σ, hσmono, hσ0, -, hσ⟩ := GradientLikeStrip.exists_reparam D E hφc hm hφb hEφ x
    have h0 : 0 ≤ σ s := hσ0 ▸ hσmono.monotone hs.1
    have hle : σ s ≤ N := by
      by_contra hlt
      rw [not_le] at hlt
      have h1 := GradientLikeStrip.f_flow_antitone (D := D) hf x hlt.le
      have h2 := GradientLikeStrip.sub_le_f_flow (D := E) hf x hs.1
      have h3 : f (D.flow N x) < f x - Tdn := hN hx
      rw [hσ] at h2
      simp only at h1
      linarith [hs.2]
    refine hnotS _ ?_ p hp
    rw [hσ]
    exact ⟨(σ s, x), Or.inl ⟨⟨h0, hle⟩, hx⟩, rfl⟩
  · intro x hx s hs p hp
    obtain ⟨σ, hσmono, hσ0, -, hσ⟩ := GradientLikeStrip.exists_reparam D E hφc hm hφb hEφ x
    have h0 : σ s ≤ 0 := hσ0 ▸ hσmono.monotone hs.2
    have hle : -(N' : ℝ) ≤ σ s := by
      by_contra hlt
      rw [not_le] at hlt
      have h1 := GradientLikeStrip.f_flow_antitone (D := D) hf x hlt.le
      have h2 := GradientLikeStrip.f_flow_le_sub_of_nonpos (D := E) hf x hs.2
      have h3 : f x + Tup < f (D.flow (-(N' : ℝ)) x) := hN' hx
      rw [hσ] at h2
      simp only at h1
      linarith [hs.1]
    refine hnotS _ ?_ p hp
    rw [hσ]
    exact ⟨(σ s, x), Or.inr ⟨⟨hle, h0⟩, hx⟩, rfl⟩

theorem exists_levelRetraction (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    {c : ℝ} (hc : c ∈ Ioo a b) (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c) :
    (∃ U : Set M, IsOpen U ∧
      {x | f x ∈ Icc a b ∧ ∃ t, f (D.flow t x) = c} = U ∩ f ⁻¹' Icc a b) ∧
    ∃ r : M → M, ContinuousOn r {x | f x ∈ Icc a b ∧ ∃ t, f (D.flow t x) = c} ∧
      (∀ x, f x ∈ Icc a b → (∃ t, f (D.flow t x) = c) →
        f (r x) = c ∧ ∃ t, r x = D.flow t x) ∧
      ∀ x, f x = c → r x = x := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hfc : Continuous f := hfs.continuous
  have hcI : c ∈ Icc a b := ⟨hc.1.le, hc.2.le⟩
  have hcS : ∀ p hp, ∀ y ∈ D.smallBall p hp, f y ≠ c := fun p hp y hy =>
    hcU p hp y (D.smallBall_subset_closedSmallBall p hp hy)
  have hcU' : ∀ y, f y = c → dfV I f D.V y = -1 := fun y hy =>
    D.dfV_eq_neg_one_of_level hcI hcS hy
  have huniq : ∀ {x : M} {t t' : ℝ}, f (D.flow t x) = c → f (D.flow t' x) = c → t = t' :=
    fun ht ht' => GradientLikeStrip.flow_level_unique hfs hcU' ht ht'
  have hlevelΩ : ∀ y, f y = c → y ∈ D.regularFlowDomain c := by
    intro y hy
    refine ⟨by rw [hy]; exact hc, fun s hs p hp => ?_⟩
    rw [hy, sub_self, uIcc_self, mem_singleton_iff] at hs
    rw [hs, GradientLikeStrip.flow_zero]
    exact fun hmem => hcU p hp y hmem hy
  have hΩreach : ∀ (x : M) (t : ℝ), D.flow t x ∈ D.regularFlowDomain c →
      f (D.flow (t + (f (D.flow t x) - c)) x) = c := by
    intro x t ht
    have h := GradientLikeStrip.f_π hfs hcI ht
    rw [GradientLikeStrip.π, GradientLikeStrip.flow_flow] at h
    exact h
  refine ⟨⟨⋃ t : ℝ, D.flow t ⁻¹' D.regularFlowDomain c,
    isOpen_iUnion fun t => (D.isOpen_regularFlowDomain hfc c).preimage (D.continuous_flow t), ?_⟩, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨hx, t, ht⟩
      exact ⟨⟨t, hlevelΩ _ ht⟩, hx⟩
    · rintro ⟨⟨t, ht⟩, hx⟩
      exact ⟨hx, _, hΩreach x t ht⟩
  classical
  let r : M → M := fun x =>
    if h : ∃ t, f (D.flow t x) = c then D.flow (Classical.choose h) x else x
  have hr : ∀ x t, f (D.flow t x) = c → r x = D.flow t x := by
    intro x t ht
    have h : ∃ t, f (D.flow t x) = c := ⟨t, ht⟩
    simp only [r, h, ↓reduceDIte]
    rw [huniq (Classical.choose_spec h) ht]
  refine ⟨r, ?_, ?_, ?_⟩
  · rintro x₀ ⟨-, t₀, ht₀⟩
    refine ContinuousAt.continuousWithinAt ?_
    have hg : Continuous (fun x => D.π c (D.flow t₀ x)) :=
      (D.continuous_π hfs c).comp (D.continuous_flow t₀)
    refine hg.continuousAt.congr ?_
    have hN : D.flow t₀ ⁻¹' D.regularFlowDomain c ∈ 𝓝 x₀ :=
      ((D.isOpen_regularFlowDomain hfc c).preimage (D.continuous_flow t₀)).mem_nhds (hlevelΩ _ ht₀)
    filter_upwards [hN] with x hx
    rw [hr x _ (hΩreach x t₀ hx), GradientLikeStrip.π, GradientLikeStrip.flow_flow]
  · intro x _ hx
    obtain ⟨t, ht⟩ := hx
    rw [hr x t ht]
    exact ⟨ht, t, rfl⟩
  · intro x hx
    rw [hr x 0 (by rw [GradientLikeStrip.flow_zero]; exact hx), GradientLikeStrip.flow_zero]

theorem exists_backward_capture (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {c : ℝ} (hcb : c < b) {x : M}
    (hx : a ≤ f x) (hbd : ∀ t, t ≤ 0 → f (D.flow t x) ≤ c) :
    ∃ r, ∃ hr : r ∈ crit, f r ≤ c ∧ ∃ T, T ≤ 0 ∧ D.flow T x ∈ (D.chart r hr).χ ''
      {y | morseNorm n y < D.rm r hr ∧ posPart (D.chart r hr).hk y = 0} := by
  classical
  have _ := hcrit
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hab : a < b := hf.lt
  set e : M → ℝ := fun p => if hp : p ∈ crit then
    (D.chart p hp).r₀ ^ 2 / 4 + D.rm p hp ^ 2 / 16 else 1 with hedef
  have he : ∀ p (hp : p ∈ crit), e p = (D.chart p hp).r₀ ^ 2 / 4 + D.rm p hp ^ 2 / 16 :=
    fun p hp => by simp only [hedef, hp, ↓reduceDIte]
  have hepos : ∀ p (hp : p ∈ crit), 0 < e p := fun p hp => by
    rw [he p hp]
    have := D.rm_pos p hp
    positivity
  have her : ∀ p (hp : p ∈ crit), (D.chart p hp).r₀ ^ 2 < 2 * e p ∧ 8 * e p < D.rm p hp ^ 2 := by
    intro p hp
    have h1 := (D.hrm p hp).1
    have h2 := (D.chart p hp).hr₀
    have h3 : 4 * (D.chart p hp).r₀ ^ 2 < D.rm p hp ^ 2 := by nlinarith
    rw [he p hp]
    constructor <;> linarith
  have hr'gt : ∀ p (hp : p ∈ crit), (D.chart p hp).r₀ < Real.sqrt (2 * e p) := fun p hp =>
    (Real.lt_sqrt (D.chart p hp).hr₀.le).2 (her p hp).1
  let P : M → Prop := fun z => ∃ r, ∃ hr : r ∈ crit, f r ≤ c ∧ ∃ T, T ≤ 0 ∧
    D.flow T z ∈ (D.chart r hr).χ ''
      {y | morseNorm n y < D.rm r hr ∧ posPart (D.chart r hr).hk y = 0}
  have hPshift : ∀ z s, s ≤ 0 → P (D.flow s z) → P z := by
    rintro z s hs ⟨r, hr, hfr, T, hT, hmem⟩
    refine ⟨r, hr, hfr, s + T, by linarith, ?_⟩
    rwa [D.flow_flow] at hmem
  have key : ∀ N : ℕ, ∀ z, a < f z → (∀ t, t ≤ 0 → f (D.flow t z) ≤ c) →
      (crit.filter (fun r => f z < f r + e r)).card = N → P z := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro z hz hbdz hN
    have hzc : f z ≤ c := by simpa using hbdz 0 le_rfl
    have hzb : f z < b := lt_of_le_of_lt hzc hcb
    rcases D.mem_regularFlowDomain_or_exists_throughBall (c := b) (fun p _ => Real.sqrt (2 * e p)) hr'gt
        ⟨hz, hzb⟩ with hΩ | ⟨r, hr, hthr⟩
    · exfalso
      have h1 := GradientLikeStrip.f_flow_eq_sub_of_mem_regularFlowDomain hfs (right_mem_Icc.2 hab.le) hΩ _
        right_mem_uIcc
      have h2 := hbdz (f z - b) (by linarith)
      rw [h1] at h2
      linarith
    · obtain ⟨-, s, hs, hmem⟩ := hthr
      rw [uIcc_of_ge (by linarith)] at hs
      obtain ⟨y, hy, hyx⟩ := hmem
      have hy' : morseNorm n y < Real.sqrt (2 * e r) := hy
      have hysq : morseNorm n y ^ 2 < 2 * e r :=
        (Real.lt_sqrt (ModelField.morseNorm_nonneg y)).1 hy'
      have hsq := DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
        (D.chart r hr).hk y
      have hrm0 := D.rm_pos r hr
      have hrm8 := (her r hr).2
      have he0 := hepos r hr
      have hyrm : morseNorm n y < D.rm r hr := by
        apply lt_of_pow_lt_pow_left₀ 2 hrm0.le
        linarith
      have hyR : morseNorm n y ≤ (D.chart r hr).R := hyrm.le.trans (D.hrm r hr).2
      have hfy : f (D.flow s z) = morseNormalForm (D.chart r hr).hk (f r) y := by
        rw [← hyx]; exact (D.chart r hr).hnorm y hyR
      have hfzs : f z ≤ f (D.flow s z) := GradientLikeStrip.le_f_flow_of_nonpos hfs z hs.2
      by_cases hv0 : posPart (D.chart r hr).hk y = 0
      · refine ⟨r, hr, ?_, s, hs.2, y, ⟨hyrm, hv0⟩, hyx⟩
        by_contra hlt
        push Not at hlt
        have hr₀ := (D.chart r hr).hr₀
        have hθ₀ : 0 < (morseNorm n y ^ 2 + (D.chart r hr).r₀ ^ 2)⁻¹ := by positivity
        set θ₀ := (morseNorm n y ^ 2 + (D.chart r hr).r₀ ^ 2)⁻¹ with hθ₀def
        have hcr : 0 < f r - c := by linarith
        set m := θ₀ * (2 * (f r - c)) with hmdef
        have hm0 : 0 < m := by positivity
        have har : 0 < f r - a + 1 := by linarith
        set T := (f r - a + 1) / m with hTdef
        have hT0 : 0 ≤ T := by positivity
        have hstay : ∀ u, u ≤ 0 → D.flow u (D.flow s z) ∈ (D.chart r hr).χ ''
            {w | morseNorm n w ≤ morseNorm n y ∧ posPart (D.chart r hr).hk w = 0} := by
          intro u hu
          rw [← hyx]
          exact GradientLikeStrip.flow_mem_of_posPart_eq_zero hr hyrm hv0 hu
        have hODE : ∀ u ∈ Icc (-T) 0, D.flow u (D.flow s z) ∈ (D.chart r hr).χ ''
            {w | morseNorm n w < D.rm r hr} :=
          fun u hu => image_mono (fun w hw => lt_of_le_of_lt hw.1 hyrm) (hstay u hu.2)
        have hγ := GradientLikeStrip.hasDerivAt_symm_flow_Icc hr hODE
        have hγeq : ∀ u, u ≤ 0 → ∃ w, morseNorm n w ≤ morseNorm n y ∧
            posPart (D.chart r hr).hk w = 0 ∧
            (D.chart r hr).χ.symm (D.flow u (D.flow s z)) = w ∧
            f (D.flow u (D.flow s z)) = morseNormalForm (D.chart r hr).hk (f r) w := by
          intro u hu
          obtain ⟨w, ⟨hw1, hw2⟩, hwx⟩ := hstay u hu
          refine ⟨w, hw1, hw2, ?_, ?_⟩
          · rw [← hwx, (D.chart r hr).χ.left_inv ((D.chart r hr).hsrc w (hw1.trans hyR))]
          · rw [← hwx]; exact (D.chart r hr).hnorm w (hw1.trans hyR)
        have hm : ∀ u ∈ Icc (-T) 0, m ≤ ModelField.theta (D.chart r hr).r₀
            ((D.chart r hr).χ.symm (D.flow u (D.flow s z))) *
            morseNorm n ((D.chart r hr).χ.symm (D.flow u (D.flow s z))) ^ 2 := by
          intro u hu
          obtain ⟨w, hw1, hw2, hwe, hwf⟩ := hγeq u hu.2
          rw [hwe]
          have hth := ModelField.theta_ge_of_le hr₀ hw1
          have hbu : f (D.flow u (D.flow s z)) ≤ c := by
            rw [D.flow_flow]; exact hbdz _ (by linarith [hu.2, hs.2])
          have hsqw :=
            DifferentialGeometry.Topology.Morse.CellAttachment.morseNorm_sq_eq_negPart_add_posPart
              (D.chart r hr).hk w
          rw [hw2, norm_zero] at hsqw
          rw [hwf, DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split, hw2,
            norm_zero] at hbu
          have hw2c : 2 * (f r - c) ≤ morseNorm n w ^ 2 := by nlinarith
          exact mul_le_mul hth hw2c (by linarith) (ModelField.theta_pos hr₀ w).le
        have hlin := ModelField.nf_le_linear_of_rate (D.chart r hr).hk (f r) hγ hm 0
          ⟨by linarith, le_rfl⟩
        obtain ⟨w0, -, -, hw0e, hw0f⟩ := hγeq 0 le_rfl
        obtain ⟨wT, -, -, hwTe, hwTf⟩ := hγeq (-T) (by linarith)
        rw [hw0e, hwTe, ← hw0f, ← hwTf, D.flow_zero] at hlin
        have hbT : f (D.flow (-T) (D.flow s z)) ≤ c := by
          rw [D.flow_flow]; exact hbdz _ (by linarith [hs.2])
        have hmT : m * (0 - -T) = f r - a + 1 := by
          rw [hTdef]; field_simp; ring
        rw [hmT] at hlin
        linarith
      · have hball : 2 * e r + 2 * ‖negPart (D.chart r hr).hk y‖ ^ 2 < D.rm r hr ^ 2 := by
          nlinarith [sq_nonneg ‖posPart (D.chart r hr).hk y‖]
        have hnfy : morseNormalForm (D.chart r hr).hk (f r) y < f r + e r := by
          rw [DifferentialGeometry.Topology.Morse.CellAttachment.morseNormalForm_split]
          nlinarith [sq_nonneg ‖negPart (D.chart r hr).hk y‖]
        obtain ⟨t, ht0, hft, -, -⟩ :=
          GradientLikeStrip.exists_exit_asc hfs hr (hepos r hr) hball hv0 hnfy.le
        rw [hyx, D.flow_flow] at hft
        have hst : s + -t ≤ 0 := by linarith [hs.2]
        have hz' : a < f (D.flow (s + -t) z) :=
          lt_of_lt_of_le hz (GradientLikeStrip.le_f_flow_of_nonpos hfs z hst)
        have hbd' : ∀ u, u ≤ 0 → f (D.flow u (D.flow (s + -t) z)) ≤ c := fun u hu => by
          rw [D.flow_flow]; exact hbdz _ (by linarith)
        have hsub : crit.filter (fun q => f (D.flow (s + -t) z) < f q + e q) ⊆
            crit.filter (fun q => f z < f q + e q) := by
          intro q
          simp only [Finset.mem_filter]
          rintro ⟨hq, hlt⟩
          exact ⟨hq, lt_of_le_of_lt (GradientLikeStrip.le_f_flow_of_nonpos hfs z hst) hlt⟩
        have hss : crit.filter (fun q => f (D.flow (s + -t) z) < f q + e q) ⊂
            crit.filter (fun q => f z < f q + e q) := by
          rw [Finset.ssubset_iff_of_subset hsub]
          refine ⟨r, ?_, ?_⟩
          · simp only [Finset.mem_filter]
            exact ⟨hr, by linarith⟩
          · simp only [Finset.mem_filter, not_and, not_lt]
            intro _
            rw [hft]
        have hlt := Finset.card_lt_card hss
        rw [hN] at hlt
        exact hPshift z _ hst (ih _ hlt _ hz' hbd' rfl)
  have hxc : f x ≤ c := by simpa using hbd 0 le_rfl
  rcases hx.lt_or_eq with hlt | heq
  · exact key _ x hlt hbd rfl
  · have hunit : dfV I f D.V x = -1 :=
      D.unit x ⟨hx, hxc.trans hcb.le⟩ fun p hp hmem =>
        (D.inStrip p hp (D.smallBall_subset_image_ball p hp hmem)).1.ne' heq.symm
    have hd : HasDerivAt (fun s => f (D.flow s x)) (-1) 0 := by
      have := GradientLikeStrip.hasDerivAt_f_flow (D := D) hfs x 0
      rwa [D.flow_zero, hunit] at this
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), slope (fun s => f (D.flow s x)) 0 t < 0 :=
      (tendsto_order.1 hd).2 0 (by norm_num)
    have h2 : ∀ᶠ t in 𝓝[<] (0 : ℝ), slope (fun s => f (D.flow s x)) 0 t < 0 :=
      h1.filter_mono (nhdsWithin_mono _ fun t (ht : t < 0) => ht.ne)
    obtain ⟨t, ht, ht0⟩ := (h2.and self_mem_nhdsWithin).exists
    have ht0' : t < 0 := ht0
    rw [slope_def_field, sub_zero, D.flow_zero] at ht
    have hft : f x < f (D.flow t x) := by
      have := (div_lt_iff_of_neg ht0').1 ht
      linarith
    have hbd' : ∀ u, u ≤ 0 → f (D.flow u (D.flow t x)) ≤ c := fun u hu => by
      rw [D.flow_flow]; exact hbd _ (by linarith)
    exact hPshift x t ht0'.le (key _ _ (lt_of_eq_of_lt heq hft) hbd' rfl)

theorem isThin_nonReaching_below (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {c : ℝ} (hc : c ∈ Ioo a b)
    (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c)
    {kdn : ℕ} (hdn : ∀ x hx, f x < c → (D.chart x hx).k ≤ kdn) :
    isThin I kdn {x | f x ∈ Icc a c ∧ ∀ t, f (D.flow t x) ≠ c} := by
  have hfc : Continuous f := hf.smooth.continuous
  let L : ℕ → (Fin kdn → ℝ) → (Fin n → ℝ) := fun k w i =>
    if h : (i : ℕ) < k ∧ (i : ℕ) < kdn then w ⟨i, h.2⟩ else 0
  have hL : ∀ k, ContDiff ℝ ∞ (L k) := by
    intro k
    refine contDiff_pi.2 fun i => ?_
    by_cases h : (i : ℕ) < k ∧ (i : ℕ) < kdn
    · simp only [L, dite_eq_left h]
      exact contDiff_apply ℝ ℝ (⟨i, h.2⟩ : Fin kdn)
    · simp only [L, dite_eq_right h]
      exact contDiff_const
  let e := crit.equivFin
  let ι : Type := Fin crit.card × ℕ
  let U : ι → Set (Fin kdn → ℝ) := fun q =>
    L (D.chart (e.symm q.1).1 (e.symm q.1).2).k ⁻¹'
      Metric.ball 0 (D.chart (e.symm q.1).1 (e.symm q.1).2).R'
  let g : ι → (Fin kdn → ℝ) → M := fun q w =>
    D.flow (q.2 : ℝ) ((D.chart (e.symm q.1).1 (e.symm q.1).2).χ
      (L (D.chart (e.symm q.1).1 (e.symm q.1).2).k w))
  refine ⟨ι, inferInstance, U, g, fun q => ?_, fun q => ?_, ?_⟩
  · exact Metric.isOpen_ball.preimage (hL _).continuous
  · have h1 : ContMDiffOn 𝓘(ℝ, Fin kdn → ℝ) I ∞
        (fun w => (D.chart (e.symm q.1).1 (e.symm q.1).2).χ
          (L (D.chart (e.symm q.1).1 (e.symm q.1).2).k w)) (U q) :=
      (D.chart (e.symm q.1).1 (e.symm q.1).2).hχ.comp (hL _).contMDiff.contMDiffOn fun w hw => hw
    exact ((D.contMDiff_flow (q.2 : ℝ)).comp_contMDiffOn h1).of_le (by norm_num)
  · rintro x ⟨hxI, hxc⟩
    have hbd : ∀ t, t ≤ 0 → f (D.flow t x) ≤ c := by
      intro t ht
      by_contra hlt
      push Not at hlt
      have hcont : ContinuousOn (fun s => f (D.flow s x)) (Icc t 0) :=
        (hfc.comp (D.continuous_flow_curve x)).continuousOn
      have hmem : c ∈ Icc (f (D.flow 0 x)) (f (D.flow t x)) := by
        rw [D.flow_zero]; exact ⟨hxI.2, hlt.le⟩
      obtain ⟨s, -, hs⟩ := intermediate_value_Icc' ht hcont hmem
      exact hxc s hs
    obtain ⟨r, hr, hfr, T, hT, hmem⟩ := exists_backward_capture hf D hcrit hc.2 hxI.1 hbd
    have hfrc : f r ≠ c := hcU r hr r
      (D.smallBall_subset_closedSmallBall r hr (D.p_mem_smallBall r hr))
    have hk : (D.chart r hr).k ≤ kdn := hdn r hr (lt_of_le_of_ne hfr hfrc)
    obtain ⟨y, ⟨hy, hyv⟩, hyx⟩ := hmem
    set m : ℕ := ⌈-T⌉₊ with hm
    have hmT : -T ≤ (m : ℝ) := Nat.le_ceil _
    obtain ⟨z, ⟨hz, hzv⟩, hzx⟩ :=
      D.flow_mem_of_posPart_eq_zero hr hy hyv (t := -(m : ℝ) - T) (by linarith)
    have hxz : x = D.flow (m : ℝ) ((D.chart r hr).χ z) := by
      rw [hzx, hyx, D.flow_flow, D.flow_flow, show T + (-(m : ℝ) - T + (m : ℝ)) = 0 by ring,
        D.flow_zero]
    set k := (D.chart r hr).k with hkdef
    let w : Fin kdn → ℝ := fun j =>
      if h : (j : ℕ) < k then z ⟨j, lt_of_lt_of_le h (D.chart r hr).hk⟩ else 0
    have hLw : L k w = z := by
      funext i
      by_cases hi : (i : ℕ) < k
      · have h2 : (i : ℕ) < k ∧ (i : ℕ) < kdn := ⟨hi, lt_of_lt_of_le hi hk⟩
        simp only [L, w, dite_eq_left h2, dite_eq_left hi]
      · have h2 : ¬ ((i : ℕ) < k ∧ (i : ℕ) < kdn) := fun h => hi h.1
        simp only [L, dite_eq_right h2]
        rw [← DifferentialGeometry.Topology.Morse.CellAttachment.recombine_decompose
          (D.chart r hr).hk z, hzv]
        simp only [DifferentialGeometry.Topology.Morse.CellAttachment.recombine, PiLp.zero_apply]
        split_ifs with h
        · exact False.elim (hi h)
        · rfl
    have he : e.symm (e ⟨r, hr⟩) = ⟨r, hr⟩ := e.symm_apply_apply _
    have hgen : ∀ q : {r // r ∈ crit}, q = ⟨r, hr⟩ →
        L (D.chart q.1 q.2).k w ∈ Metric.ball 0 (D.chart q.1 q.2).R' ∧
          D.flow (m : ℝ) ((D.chart q.1 q.2).χ (L (D.chart q.1 q.2).k w)) = x := by
      rintro q rfl
      refine ⟨?_, ?_⟩
      · change L k w ∈ Metric.ball 0 (D.chart r hr).R'
        rw [hLw]
        exact (D.chart r hr).mem_ball_of_le
          ((hz.trans hy.le).trans (D.hrm r hr).2)
      · change D.flow (m : ℝ) ((D.chart r hr).χ (L k w)) = x
        rw [hLw, hxz]
    obtain ⟨h1, h2⟩ := hgen _ he
    exact mem_iUnion.2 ⟨(e ⟨r, hr⟩, m), w, h1, h2⟩

theorem exists_forward_capture (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {c : ℝ} (hac : a < c) {x : M}
    (hx : f x ≤ b) (hbd : ∀ t, 0 ≤ t → c ≤ f (D.flow t x)) :
    ∃ r, ∃ hr : r ∈ crit, c ≤ f r ∧ ∃ T, 0 ≤ T ∧ D.flow T x ∈ (D.chart r hr).χ ''
      {y | morseNorm n y < D.rm r hr ∧ negPart (D.chart r hr).hk y = 0} := by
  classical
  have _hcrit := hcrit
  have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  set g : M → ℝ := fun p => if hp : p ∈ crit then min (D.chart p hp).r₀ (D.rm p hp / 2) else 1
    with hgdef
  have hgpos : ∀ p, 0 < g p := by
    intro p
    simp only [hgdef]
    split_ifs with hp
    · exact lt_min (D.chart p hp).hr₀ (half_pos (D.rm_pos p hp))
    · exact one_pos
  have hne : (insert (1 : ℝ) (crit.image g)).Nonempty := Finset.insert_nonempty _ _
  set ρ : ℝ := (insert (1 : ℝ) (crit.image g)).min' hne with hρdef
  have hρpos : 0 < ρ := by
    have hmem := Finset.min'_mem _ hne
    rw [← hρdef, Finset.mem_insert, Finset.mem_image] at hmem
    rcases hmem with h | ⟨p, -, hp⟩
    · rw [h]; exact one_pos
    · rw [← hp]; exact hgpos p
  have hρle : ∀ p hp, ρ ≤ (D.chart p hp).r₀ ∧ ρ ≤ D.rm p hp / 2 := by
    intro p hp
    have h1 : ρ ≤ g p := Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hp))
    have h2 : g p = min (D.chart p hp).r₀ (D.rm p hp / 2) := by simp [hgdef, hp]
    rw [h2] at h1
    exact ⟨h1.trans (min_le_left _ _), h1.trans (min_le_right _ _)⟩
  obtain ⟨E, hEchart, hEr₀, hErm, -, φ, hφc, ⟨m, M₀, hm, hφb⟩, hEV⟩ :=
    exists_shrinkAll_factor hsm D hρpos (fun p hp => (hρle p hp).1)
  have hε : (0 : ℝ) < ρ ^ 2 / 4 := by positivity
  have hεr : ∀ p hp, (E.chart p hp).r₀ ^ 2 < 2 * (ρ ^ 2 / 4) ∧ 8 * (ρ ^ 2 / 4) < E.rm p hp ^ 2 := by
    intro p hp
    rw [hEr₀ p hp, hErm p hp]
    have h1 := (hρle p hp).2
    have h2 := D.rm_pos p hp
    constructor
    · nlinarith
    · nlinarith
  have hfx0 : c ≤ f x := by simpa [GradientLikeStrip.flow_zero] using hbd 0 le_rfl
  have hxI : f x ∈ Icc a b := ⟨hac.le.trans hfx0, hx⟩
  obtain ⟨σ, hσm, hσ0, -, hσ⟩ := GradientLikeStrip.exists_reparam D E hφc hm hφb hEV x
  rcases GradientLikeStrip.trichotomy (D := E) hsm hε hεr hxI with hbot | ⟨r, hr, hcap⟩
  · exfalso
    obtain ⟨t, ht, hlt⟩ := hbot
    have hσt : 0 ≤ σ t := by rw [← hσ0]; exact hσm.monotone ht
    rw [hσ] at hlt
    have := hbd (σ t) hσt
    linarith
  · have hnp : ∀ {k k' : ℕ} (hk : k ≤ n) (hk' : k' ≤ n), k = k' → ∀ y : Fin n → ℝ,
        negPart hk y = 0 → negPart hk' y = 0 := by
      intro k k' hk hk' hkk' y h
      subst hkk'
      exact h
    have hDcap : x ∈ D.captured r hr := by
      obtain ⟨T, y, ⟨hy1, hy2⟩, hyT⟩ := hcap
      refine ⟨σ T, y, ⟨?_, ?_⟩, ?_⟩
      · rw [← hErm r hr]; exact hy1
      · exact hnp _ _ (hEchart r hr).2.1 y hy2
      · rw [← hσ, ← hyT, (hEchart r hr).1]
    refine ⟨r, hr, ?_, ?_⟩
    · refine le_of_forall_pos_lt_add fun η hη => ?_
      obtain ⟨T, hT⟩ := GradientLikeStrip.exists_f_flow_lt_of_mem_captured hDcap hη
      have h1 := GradientLikeStrip.f_flow_antitone (D := D) hsm x (le_max_left T 0)
      have h2 := hbd (max T 0) (le_max_right T 0)
      simp only at h1
      linarith
    · obtain ⟨T₀, hT₀⟩ := GradientLikeStrip.mem_captured_iff_eventually.1 hDcap
      exact ⟨max T₀ 0, le_max_right _ _, hT₀ _ (le_max_left _ _)⟩

theorem isThin_nonReaching_above (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {c : ℝ} (hc : c ∈ Ioo a b)
    (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c)
    {kup : ℕ} (hup : ∀ x hx, c < f x → kup ≤ (D.chart x hx).k) :
    isThin I (n - kup) {x | f x ∈ Icc c b ∧ ∀ t, f (D.flow t x) ≠ c} := by
  classical
  let Y : (Fin (n - kup) → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun i : Fin n =>
      if h : kup ≤ i.val then
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n - kup) => ℝ)
          (⟨i.val - kup, by have := i.isLt; omega⟩ : Fin (n - kup))
      else 0
  have hYapp : ∀ w i, Y w i =
      if h : kup ≤ i.val then w ⟨i.val - kup, by have := i.isLt; omega⟩ else 0 := by
    intro w i
    simp only [Y, ContinuousLinearMap.pi_apply]
    split_ifs <;> rfl
  let rr : Fin crit.card → {r // r ∈ crit} := crit.equivFin.symm
  refine ⟨Fin crit.card × ℕ, inferInstance,
    fun i => Y ⁻¹' Metric.ball 0 (D.chart (rr i.1).1 (rr i.1).2).R',
    fun i w => D.flow (-(i.2 : ℝ)) ((D.chart (rr i.1).1 (rr i.1).2).χ (Y w)), ?_, ?_, ?_⟩
  · intro i
    exact Metric.isOpen_ball.preimage Y.continuous
  · intro i
    have h1 : ContMDiffOn 𝓘(ℝ, Fin (n - kup) → ℝ) I ∞
        (fun w => (D.chart (rr i.1).1 (rr i.1).2).χ (Y w))
        (Y ⁻¹' Metric.ball 0 (D.chart (rr i.1).1 (rr i.1).2).R') :=
      (D.chart (rr i.1).1 (rr i.1).2).hχ.comp Y.contDiff.contMDiff.contMDiffOn
        (fun w hw => hw)
    exact ((D.contMDiff_flow _).comp_contMDiffOn h1).of_le (by norm_cast)
  · rintro x ⟨hx, hnever⟩
    have hcont : Continuous fun s => f (D.flow s x) :=
      hf.smooth.continuous.comp (D.continuous_flow_curve x)
    have hbd : ∀ t, 0 ≤ t → c ≤ f (D.flow t x) := by
      intro t ht
      by_contra hlt'
      have hlt : f (D.flow t x) < c := not_le.1 hlt'
      have h0 : f (D.flow 0 x) ∈ Icc (f (D.flow t x)) (f (D.flow 0 x)) :=
        ⟨by rw [D.flow_zero]; linarith [hx.1], le_rfl⟩
      have hcmem : c ∈ Icc (f (D.flow t x)) (f (D.flow 0 x)) :=
        ⟨hlt.le, by rw [D.flow_zero]; exact hx.1⟩
      obtain ⟨s, -, hs⟩ := intermediate_value_Icc' ht hcont.continuousOn hcmem
      exact hnever s hs
    obtain ⟨r, hr, hcr, T, hT, hmem⟩ := exists_forward_capture hf D hcrit hc.1 hx.2 hbd
    have hfr : f r ≠ c := by
      refine hcU r hr r ⟨0, ?_, (D.chart r hr).hχ0⟩
      change morseNorm n 0 ≤ (D.chart r hr).r₀
      rw [morseNorm_zero]
      exact (D.chart r hr).hr₀.le
    have hk : kup ≤ (D.chart r hr).k := hup r hr (lt_of_le_of_ne hcr (Ne.symm hfr))
    set m : ℕ := ⌈T⌉₊ with hmdef
    have hTm : T ≤ (m : ℝ) := Nat.le_ceil T
    obtain ⟨y, ⟨hy1, hy2⟩, hyx⟩ := hmem
    have hfl := D.flow_mem_of_negPart_eq_zero hr hy1 hy2 (t := (m : ℝ) - T) (by linarith)
    rw [hyx, D.flow_flow, add_sub_cancel] at hfl
    obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := hfl
    obtain ⟨j, hj⟩ : ∃ j, rr j = ⟨r, hr⟩ := crit.equivFin.symm.surjective _
    let w : Fin (n - kup) → ℝ := fun l => z ⟨l.val + kup, by have := l.isLt; omega⟩
    have hYw : Y w = z := by
      funext i
      rw [hYapp]
      split_ifs with h
      · change z _ = z i
        congr 1
        ext
        simp only
        omega
      · have hi : i.val < (D.chart r hr).k := by omega
        have := congrArg (fun v => v ⟨i.val, hi⟩) hz2
        simp only [DifferentialGeometry.Topology.Morse.CellAttachment.negPart,
          DifferentialGeometry.Topology.Morse.CellAttachment.negIdx] at this
        have hci : (Fin.castLE (D.chart r hr).hk ⟨i.val, hi⟩ : Fin n) = i := by ext; simp
        rw [hci] at this
        rw [this]
        rfl
    refine mem_iUnion.2 ⟨(j, m), w, ?_, ?_⟩
    · change Y w ∈ Metric.ball 0 (D.chart (rr j).1 (rr j).2).R'
      rw [hj, hYw, mem_ball_zero_iff]
      calc ‖z‖ ≤ morseNorm n z :=
            DifferentialGeometry.Topology.Morse.CellAttachment.supNorm_le_morseNorm z
        _ ≤ morseNorm n y := hz1
        _ < D.rm r hr := hy1
        _ < (D.chart r hr).R' := D.rm_lt_R' r hr
    · change D.flow (-(m : ℝ)) ((D.chart (rr j).1 (rr j).2).χ (Y w)) = x
      rw [hj, hYw]
      change D.flow (-(m : ℝ)) ((D.chart r hr).χ z) = x
      rw [hzx, D.flow_neg_flow]

omit [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] in
theorem isThin_union_of_le {d₁ d₂ d : ℕ} (h₁ : d₁ ≤ d) (h₂ : d₂ ≤ d) {T₁ T₂ : Set M}
    (hT₁ : isThin I d₁ T₁) (hT₂ : isThin I d₂ T₂) : isThin I d (T₁ ∪ T₂) := by
  have mono : ∀ (e : ℕ), e ≤ d → ∀ (T : Set M), isThin I e T → isThin I d T := by
    intro e he T hT
    obtain ⟨ι, hι, U, g, hU, hg, hTU⟩ := hT
    let p : (Fin d → ℝ) →L[ℝ] (Fin e → ℝ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castLE he i)
    have hp : ∀ v : Fin d → ℝ, p v = fun i => v (Fin.castLE he i) := fun v => rfl
    refine ⟨ι, hι, fun i => p ⁻¹' U i, fun i => g i ∘ p, fun i => (hU i).preimage p.continuous,
      fun i => ?_, ?_⟩
    · exact (hg i).comp p.contDiff.contMDiff.contMDiffOn (fun v hv => hv)
    · intro x hx
      obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.mp (hTU hx)
      refine mem_iUnion.mpr ⟨i, ?_⟩
      let v : Fin d → ℝ := fun j => if h : (j : ℕ) < e then u ⟨j, h⟩ else 0
      have hv : p v = u := by
        rw [hp]
        funext k
        simp [v, Fin.castLE]
      exact ⟨v, by simpa [hv] using hu, by simp [hv]⟩
  obtain ⟨ι₁, hι₁, U₁, g₁, hU₁, hg₁, hT₁U⟩ := mono d₁ h₁ T₁ hT₁
  obtain ⟨ι₂, hι₂, U₂, g₂, hU₂, hg₂, hT₂U⟩ := mono d₂ h₂ T₂ hT₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim U₁ U₂, Sum.elim g₁ g₂, ?_, ?_, ?_⟩
  · rintro (i | i)
    · exact hU₁ i
    · exact hU₂ i
  · rintro (i | i)
    · exact hg₁ i
    · exact hg₂ i
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hT₁U hx)
      exact mem_iUnion.mpr ⟨Sum.inl i, hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hT₂U hx)
      exact mem_iUnion.mpr ⟨Sum.inr i, hi⟩

theorem exists_levelChart (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x₀ : M}
    (hx₀ : ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x₀) :
    ∃ (ψ : OpenPartialHomeomorph (Fin n → ℝ) M) (i₀ : Fin n) (r : ℝ), 0 < r ∧
      Metric.ball 0 r ⊆ ψ.source ∧ ψ 0 = x₀ ∧
      ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source ∧
      ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target ∧
      ∀ y ∈ ψ.source, f (ψ y) = f x₀ + y i₀ := by
  classical
  set φ := extChartAt I x₀ with hφ
  set g : (Fin n → ℝ) → ℝ := f ∘ φ.symm with hg
  set z₀ := φ x₀ with hz₀
  have hφt : IsOpen φ.target := isOpen_extChartAt_target x₀
  have hz₀t : z₀ ∈ φ.target := mem_extChartAt_target x₀
  have hφz₀ : φ.symm z₀ = x₀ := extChartAt_to_inv x₀
  have hgs : ContDiffOn ℝ ∞ g φ.target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀))
  have hL : fderiv ℝ g z₀ ≠ 0 := by
    intro h0
    apply hx₀
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f x₀ :=
      (hf x₀).mdifferentiableAt (by simp)
    unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt mfderiv
    simp only [hmd, ↓reduceIte, writtenInExtChartAt, extChartAt_model_space_eq_id,
      ModelWithCorners.range_eq_univ, fderivWithin_univ]
    exact h0
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, fderiv ℝ g z₀ (Pi.single i₀ 1) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hL
    have hlin : (fderiv ℝ g z₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ) = 0 := by
      refine LinearMap.pi_ext fun i x => ?_
      have hx : (Pi.single i x : Fin n → ℝ) = x • Pi.single i 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [hx]
      simp [hall i]
    ext v
    exact congrArg (fun T : (Fin n → ℝ) →ₗ[ℝ] ℝ => T v) hlin
  set e₀ : Fin n → ℝ := Pi.single i₀ 1 with he₀
  set F : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun z => (z - z₀) + (g z - g z₀ - (z i₀ - z₀ i₀)) • e₀ with hF
  have hFs : ContDiffOn ℝ ∞ F φ.target := by
    refine (contDiffOn_id.sub contDiffOn_const).add ?_
    exact ((hgs.sub contDiffOn_const).sub
      (((contDiff_apply ℝ ℝ i₀).contDiffOn).sub contDiffOn_const)).smul contDiffOn_const
  have hFi₀ : ∀ z, F z i₀ = g z - g z₀ := by
    intro z
    simp [hF, he₀]
  have hFz₀ : F z₀ = 0 := by simp [hF]
  set D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.id ℝ _ +
      (fderiv ℝ g z₀ - ContinuousLinearMap.proj i₀).smulRight e₀ with hD
  have hFD : HasFDerivAt F D z₀ := by
    have hgd : HasFDerivAt g (fderiv ℝ g z₀) z₀ :=
      ((hgs.contDiffAt (hφt.mem_nhds hz₀t)).differentiableAt (by simp)).hasFDerivAt
    exact ((hasFDerivAt_id (𝕜 := ℝ) z₀).sub_const z₀).add
      (((hgd.sub_const (g z₀)).sub ((hasFDerivAt_apply i₀ z₀).sub_const (z₀ i₀))).smul_const e₀)
  have hDinj : Function.Injective D := by
    refine (injective_iff_map_eq_zero D).mpr ?_
    intro v hv
    have hv' : v + (fderiv ℝ g z₀ v - v i₀) • e₀ = 0 := by simpa [hD] using hv
    have hoff : ∀ j, j ≠ i₀ → v j = 0 := by
      intro j hj
      have := congrFun hv' j
      simpa [he₀, hj] using this
    have hvi : fderiv ℝ g z₀ v = 0 := by
      have := congrFun hv' i₀
      simpa [he₀] using this
    have hveq : v = v i₀ • e₀ := by
      funext j
      by_cases hj : j = i₀
      · subst hj; simp [he₀]
      · simp [he₀, hj, hoff j hj]
    have : v i₀ * fderiv ℝ g z₀ e₀ = 0 := by
      rw [← smul_eq_mul, ← map_smul, ← hveq, hvi]
    have hvi0 : v i₀ = 0 := (mul_eq_zero.mp this).resolve_right hi₀
    rw [hveq, hvi0, zero_smul]
  have hDsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective (f := (D : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))).mp hDinj
  set E₀ : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (LinearEquiv.ofBijective (D : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      ⟨hDinj, hDsurj⟩).toContinuousLinearEquiv with hE₀
  have hE₀D : (E₀ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = D := by
    ext v; rfl
  have hstrict : HasStrictFDerivAt F (E₀ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) z₀ := by
    have h1 := (hFs.contDiffAt (hφt.mem_nhds hz₀t)).hasStrictFDerivAt (by simp)
    rwa [hFD.fderiv, ← hE₀D] at h1
  set U : Set (Fin n → ℝ) := φ.target ∩ (fderiv ℝ F) ⁻¹'
    Set.range (ContinuousLinearEquiv.toContinuousLinearMap :
      ((Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) with hU
  have hUo : IsOpen U :=
    (hFs.continuousOn_fderiv_of_isOpen hφt (by simp)).isOpen_inter_preimage hφt
      ContinuousLinearEquiv.isOpen
  have hz₀U : z₀ ∈ U := ⟨hz₀t, E₀, by rw [hFD.fderiv, ← hE₀D]⟩
  set F₀ := hstrict.toOpenPartialHomeomorph F with hF₀
  set F' := F₀.restrOpen U hUo with hF'
  have hF'coe : (F' : (Fin n → ℝ) → (Fin n → ℝ)) = F := by
    rw [hF', OpenPartialHomeomorph.coe_restrOpen, hF₀,
      HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hF'src : F'.source = F₀.source ∩ U := OpenPartialHomeomorph.restrOpen_source _ _ _
  have hF'U : F'.source ⊆ U := by rw [hF'src]; exact inter_subset_right
  have hz₀F' : z₀ ∈ F'.source := by
    rw [hF'src]; exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀U⟩
  have hF'z : ∀ z, F' z = F z := fun z => by rw [hF'coe]
  have h0T : (0 : Fin n → ℝ) ∈ F'.target := by
    rw [← hFz₀, ← hF'z]; exact F'.map_source hz₀F'
  have hF'symm0 : F'.symm 0 = z₀ := by
    rw [← hFz₀, ← hF'z]; exact F'.left_inv hz₀F'
  have hF'symm : ContDiffOn ℝ ∞ F'.symm F'.target := by
    intro y hy
    have hzs : F'.symm y ∈ F'.source := F'.map_target hy
    obtain ⟨Ez, hEz⟩ := (hF'U hzs).2
    have hzt : F'.symm y ∈ φ.target := (hF'U hzs).1
    have hcd : ContDiffAt ℝ ∞ F (F'.symm y) := hFs.contDiffAt (hφt.mem_nhds hzt)
    have hder : HasFDerivAt F (Ez : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (F'.symm y) := by
      rw [hEz]; exact (hcd.differentiableAt (by simp)).hasFDerivAt
    rw [← hF'coe] at hder hcd
    exact (F'.contDiffAt_symm hy hder hcd).contDiffWithinAt
  set Ψ : (Fin n → ℝ) → M := φ.symm ∘ F'.symm with hΨ
  set Φ : M → (Fin n → ℝ) := F ∘ φ with hΦ
  set T : Set M := φ.source ∩ φ ⁻¹' F'.source with hT
  have hTo : IsOpen T := isOpen_extChartAt_preimage' x₀ F'.open_source
  have hΨS : MapsTo Ψ F'.target T := by
    intro y hy
    have hzs : F'.symm y ∈ F'.source := F'.map_target hy
    have hzt : F'.symm y ∈ φ.target := (hF'U hzs).1
    refine ⟨φ.map_target hzt, ?_⟩
    change φ (φ.symm (F'.symm y)) ∈ F'.source
    rw [φ.right_inv hzt]; exact hzs
  have hΦT : MapsTo Φ T F'.target := by
    intro x hx
    change F (φ x) ∈ F'.target
    rw [← hF'z]; exact F'.map_source hx.2
  have hΦΨ : ∀ y ∈ F'.target, Φ (Ψ y) = y := by
    intro y hy
    have hzs : F'.symm y ∈ F'.source := F'.map_target hy
    have hzt : F'.symm y ∈ φ.target := (hF'U hzs).1
    change F (φ (φ.symm (F'.symm y))) = y
    rw [φ.right_inv hzt, ← hF'z]; exact F'.right_inv hy
  have hΨΦ : ∀ x ∈ T, Ψ (Φ x) = x := by
    intro x hx
    change φ.symm (F'.symm (F (φ x))) = x
    rw [← hF'z, F'.left_inv hx.2]; exact φ.left_inv hx.1
  have hΨs : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ Ψ F'.target := by
    refine (contMDiffOn_extChartAt_symm x₀).comp
      (contMDiffOn_iff_contDiffOn.mpr hF'symm) ?_
    intro y hy
    exact (hF'U (F'.map_target hy)).1
  have hΦs : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ Φ T := by
    refine (contMDiffOn_iff_contDiffOn.mpr hFs).comp
      (contMDiffOn_extChartAt.mono ?_) ?_
    · intro x hx; rw [← extChartAt_source I]; exact hx.1
    · intro x hx; exact (hF'U hx.2).1
  obtain ⟨ψ, hψS, hψT, hψ, hψsymm, hψs, hψss⟩ :=
    exists_openPartialHomeomorph_of_inverse F'.open_target hTo hΨS hΦT hΦΨ hΨΦ hΨs hΦs
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp F'.open_target 0 h0T
  refine ⟨ψ, i₀, r, hr, hψS ▸ hrb, ?_, hψs, hψss, ?_⟩
  · rw [hψ 0 h0T]
    change φ.symm (F'.symm 0) = x₀
    rw [hF'symm0, hφz₀]
  · intro y hy
    rw [hψS] at hy
    rw [hψ y hy]
    have hzs : F'.symm y ∈ F'.source := F'.map_target hy
    have hy' : F (F'.symm y) = y := by rw [← hF'z]; exact F'.right_inv hy
    have h1 := hFi₀ (F'.symm y)
    rw [hy'] at h1
    change f (φ.symm (F'.symm y)) = f x₀ + y i₀
    have h2 : g (F'.symm y) = f (φ.symm (F'.symm y)) := rfl
    have h3 : g z₀ = f x₀ := by
      change f (φ.symm z₀) = f x₀
      rw [hφz₀]
    linarith

theorem isPathConnected_ball_diff_thin {m d : ℕ} (hdm : d + 2 ≤ m) {Z : Set (Fin m → ℝ)}
    (hZ : ∃ (ι : Type) (_ : Countable ι) (U : ι → Set (Fin d → ℝ))
      (g : ι → (Fin d → ℝ) → (Fin m → ℝ)),
      (∀ i, IsOpen (U i)) ∧ (∀ i, ContDiffOn ℝ 1 (g i) (U i)) ∧ Z ⊆ ⋃ i, g i '' U i)
    (x : Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball x r \ Z) := by
  obtain ⟨ι, hι, U, g, hU, hg, hZU⟩ := hZ
  let S : (Fin m → ℝ) → Set (Fin m → ℝ) := fun p =>
    ⋃ i, (fun q : (Fin d → ℝ) × ℝ => p + q.2 • (g i q.1 - p)) '' (U i ×ˢ univ)
  have hSdim : ∀ p, dimH (S p) ≤ ((d + 1 : ℕ) : ENNReal) := by
    intro p
    rw [dimH_iUnion]
    refine iSup_le fun i => ?_
    have hdiff : DifferentiableOn ℝ (fun q : (Fin d → ℝ) × ℝ => p + q.2 • (g i q.1 - p))
        (U i ×ˢ univ) := by
      have hgi : DifferentiableOn ℝ (g i) (U i) := (hg i).differentiableOn one_ne_zero
      have h1 : DifferentiableOn ℝ (fun q : (Fin d → ℝ) × ℝ => g i q.1) (U i ×ˢ univ) :=
        hgi.comp differentiableOn_fst (fun q hq => hq.1)
      exact (differentiableOn_const p).add (differentiableOn_snd.smul (h1.sub_const p))
    refine (hdiff.dimH_image_le).trans ((dimH_mono (subset_univ _)).trans ?_)
    rw [Real.dimH_univ_eq_finrank, Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_self]
  have hdense : ∀ p q, Dense (S p ∪ S q)ᶜ := by
    intro p q
    apply dense_compl_of_dimH_lt_finrank
    rw [dimH_union, Module.finrank_fin_fun]
    have hlt : ((d + 1 : ℕ) : ENNReal) < (m : ENNReal) := by
      exact_mod_cast (show d + 1 < m by omega)
    exact max_lt ((hSdim p).trans_lt hlt) ((hSdim q).trans_lt hlt)
  have hZS : ∀ p, Z ⊆ S p := by
    intro p z hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hZU hz)
    obtain ⟨u, hu, rfl⟩ := hi
    refine mem_iUnion.2 ⟨i, ⟨(u, 1), ⟨hu, mem_univ _⟩, ?_⟩⟩
    simp
  have hB : (Metric.ball x r).Nonempty := ⟨x, Metric.mem_ball_self hr⟩
  have hpick : ∀ p q, ∃ w ∈ Metric.ball x r, w ∉ S p ∧ w ∉ S q := by
    intro p q
    obtain ⟨w, hw, hwB⟩ := (hdense p q).exists_mem_open Metric.isOpen_ball hB
    simp only [mem_compl_iff, mem_union, not_or] at hw
    exact ⟨w, hwB, hw.1, hw.2⟩
  have hseg : ∀ p w, p ∈ Metric.ball x r \ Z → w ∈ Metric.ball x r → w ∉ S p →
      JoinedIn (Metric.ball x r \ Z) p w := by
    intro p w hp hw hwS
    apply JoinedIn.of_segment_subset
    intro y hy
    refine ⟨(convex_ball x r).segment_subset hp.1 hw hy, ?_⟩
    intro hyZ
    rw [segment_eq_image'] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hZU hyZ)
    obtain ⟨u, hu, hgu⟩ := hi
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hp.2
      simpa using hyZ
    apply hwS
    refine mem_iUnion.2 ⟨i, ⟨(u, t⁻¹), ⟨hu, mem_univ _⟩, ?_⟩⟩
    simp only
    rw [hgu, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht0, one_smul,
      add_sub_cancel]
  refine isPathConnected_iff.2 ⟨?_, ?_⟩
  · obtain ⟨w, hwB, hw, -⟩ := hpick x x
    exact ⟨w, hwB, fun hwZ => hw (hZS x hwZ)⟩
  · intro p hp q hq
    obtain ⟨w, hwB, hwp, hwq⟩ := hpick p q
    exact (hseg p w hp hwB hwp).trans (hseg q w hq hwB hwq).symm

theorem isPathConnected_level_diff_thin (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ x, f x = c → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) (hconn : IsConnected (f ⁻¹' {c}))
    {Z : Set M} (hZc : IsClosed Z) {d : ℕ} (hZ : isThin I d Z) (hd : d + 3 ≤ n) :
    IsPathConnected (f ⁻¹' {c} \ Z) := by
  have _hZc : IsClosed Z := hZc
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdm : d + 2 ≤ m := by omega
  obtain ⟨ι, hι, U, g, hUo, hg, hZU⟩ := hZ
  have loc : ∀ x, f x = c → ∀ N ∈ 𝓝 x, ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ O ⊆ N ∧
      IsPathConnected ((f ⁻¹' {c} ∩ O) \ Z) := by
    intro x hx N hN
    obtain ⟨ψ, i₀, r, hr, hball, hψ0, -, hsymm, hlev⟩ := exists_levelChart hf (hreg x hx)
    have h0src : (0 : Fin (m + 1) → ℝ) ∈ ψ.source := hball (Metric.mem_ball_self hr)
    have hNψ : ψ ⁻¹' N ∈ 𝓝 (0 : Fin (m + 1) → ℝ) := by
      apply ψ.continuousAt h0src
      rw [hψ0]; exact hN
    obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hNψ
    set δ := min ε r with hδdef
    have hδ : 0 < δ := lt_min hε hr
    have hδball : Metric.ball (0 : Fin (m + 1) → ℝ) δ ⊆ ψ.source :=
      (Metric.ball_subset_ball (min_le_right _ _)).trans hball
    have hδN : Metric.ball (0 : Fin (m + 1) → ℝ) δ ⊆ ψ ⁻¹' N :=
      (Metric.ball_subset_ball (min_le_left _ _)).trans hεN
    let e : (Fin m → ℝ) → (Fin (m + 1) → ℝ) := fun y => i₀.insertNth (0 : ℝ) y
    let pr : (Fin (m + 1) → ℝ) → (Fin m → ℝ) := fun w => i₀.removeNth w
    have he_cont : Continuous e := Continuous.finInsertNth i₀ continuous_const continuous_id
    have hpr_cd : ContDiff ℝ 1 pr := by
      apply contDiff_pi.2
      intro j
      exact contDiff_apply ℝ ℝ (i₀.succAbove j)
    have hpr_e : ∀ y, pr (e y) = y := fun y => Fin.removeNth_insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) y
    have he_ball : ∀ y ∈ Metric.ball (0 : Fin m → ℝ) δ, e y ∈ Metric.ball (0 : Fin (m + 1) → ℝ) δ := by
      intro y hy
      rw [mem_ball_zero_iff] at hy ⊢
      rw [pi_norm_lt_iff hδ]
      intro j
      rcases Fin.eq_self_or_eq_succAbove i₀ j with rfl | ⟨k, rfl⟩
      · simp only [e, Fin.insertNth_apply_same, norm_zero]; exact hδ
      · simp only [e, Fin.insertNth_apply_succAbove]
        exact lt_of_le_of_lt (norm_le_pi_norm y k) hy
    let Z' : Set (Fin m → ℝ) := {y | e y ∈ ψ.source ∧ ψ (e y) ∈ Z}
    have hZ' : ∃ (ι : Type) (_ : Countable ι) (U : ι → Set (Fin d → ℝ))
        (g : ι → (Fin d → ℝ) → (Fin m → ℝ)),
        (∀ i, IsOpen (U i)) ∧ (∀ i, ContDiffOn ℝ 1 (g i) (U i)) ∧ Z' ⊆ ⋃ i, g i '' U i := by
      refine ⟨ι, hι, fun i => U i ∩ g i ⁻¹' ψ.target, fun i => pr ∘ ψ.symm ∘ g i, ?_, ?_, ?_⟩
      · intro i
        exact (hg i).continuousOn.isOpen_inter_preimage (hUo i) ψ.open_target
      · intro i
        have h1 : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin (m + 1) → ℝ) 1 (ψ.symm ∘ g i)
            (U i ∩ g i ⁻¹' ψ.target) :=
          (hsymm.of_le (by exact_mod_cast le_top)).comp ((hg i).mono inter_subset_left)
            (fun u hu => hu.2)
        have h2 : ContDiffOn ℝ 1 (ψ.symm ∘ g i) (U i ∩ g i ⁻¹' ψ.target) :=
          contMDiffOn_iff_contDiffOn.1 h1
        exact hpr_cd.comp_contDiffOn h2
      · intro y hy
        obtain ⟨hysrc, hyZ⟩ := hy
        obtain ⟨i, u, hu, hgu⟩ : ∃ i, ∃ u ∈ U i, g i u = ψ (e y) := by
          simpa only [mem_iUnion, mem_image] using hZU hyZ
        refine mem_iUnion.2 ⟨i, u, ⟨hu, ?_⟩, ?_⟩
        · change g i u ∈ ψ.target
          rw [hgu]; exact ψ.map_source hysrc
        · simp only [Function.comp_apply, hgu, ψ.left_inv hysrc, hpr_e]
    have hG7 := isPathConnected_ball_diff_thin hdm hZ' 0 hδ
    refine ⟨ψ '' Metric.ball 0 δ, ψ.isOpen_image_of_subset_source Metric.isOpen_ball hδball,
      ⟨0, Metric.mem_ball_self hδ, hψ0⟩, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hδN hw
    · have hcont : ContinuousOn (fun y => ψ (e y)) (Metric.ball 0 δ \ Z') :=
        ψ.continuousOn.comp he_cont.continuousOn (fun y hy => hδball (he_ball y hy.1))
      have heq : (f ⁻¹' {c} ∩ ψ '' Metric.ball 0 δ) \ Z =
          (fun y => ψ (e y)) '' (Metric.ball 0 δ \ Z') := by
        ext z
        constructor
        · rintro ⟨⟨hzc, w, hw, rfl⟩, hzZ⟩
          have hwi : w i₀ = 0 := by
            have := hlev w (hδball hw)
            rw [mem_preimage, mem_singleton_iff] at hzc
            linarith
          have hew : e (pr w) = w := by
            simp only [e, pr]
            rw [← hwi]
            exact Fin.insertNth_self_removeNth i₀ w
          refine ⟨pr w, ⟨?_, ?_⟩, by simp only [hew]⟩
          · rw [mem_ball_zero_iff, pi_norm_lt_iff hδ]
            intro j
            exact lt_of_le_of_lt (norm_le_pi_norm w _) (mem_ball_zero_iff.1 hw)
          · rintro ⟨-, h⟩
            rw [hew] at h
            exact hzZ h
        · rintro ⟨y, ⟨hy, hyZ'⟩, rfl⟩
          have hsrc := hδball (he_ball y hy)
          refine ⟨⟨?_, e y, he_ball y hy, rfl⟩, fun h => hyZ' ⟨hsrc, h⟩⟩
          rw [mem_preimage, mem_singleton_iff, hlev _ hsrc, hx]
          simp [e]
      rw [heq]
      exact hG7.image' hcont
  obtain ⟨x₀, hx₀⟩ := hconn.nonempty
  obtain ⟨O₀, -, -, -, hP₀⟩ := loc x₀ hx₀ univ univ_mem
  obtain ⟨p, hp⟩ := hP₀.nonempty
  have hPsub : ∀ O : Set M, (f ⁻¹' {c} ∩ O) \ Z ⊆ f ⁻¹' {c} \ Z := fun O =>
    sdiff_subset_sdiff_left inter_subset_left
  let J : Set M := {x | ∃ O, IsOpen O ∧ x ∈ O ∧
    ∀ q ∈ (f ⁻¹' {c} ∩ O) \ Z, JoinedIn (f ⁻¹' {c} \ Z) p q}
  let K : Set M := {x | ∃ O, IsOpen O ∧ x ∈ O ∧
    ∀ q ∈ (f ⁻¹' {c} ∩ O) \ Z, ¬ JoinedIn (f ⁻¹' {c} \ Z) p q}
  have hJo : IsOpen J := isOpen_iff_forall_mem_open.2 fun x ⟨O, hO, hxO, hq⟩ =>
    ⟨O, fun y hy => ⟨O, hO, hy, hq⟩, hO, hxO⟩
  have hKo : IsOpen K := isOpen_iff_forall_mem_open.2 fun x ⟨O, hO, hxO, hq⟩ =>
    ⟨O, fun y hy => ⟨O, hO, hy, hq⟩, hO, hxO⟩
  have hsub : f ⁻¹' {c} ⊆ J ∪ K := by
    intro x hx
    obtain ⟨O, hO, hxO, -, hP⟩ := loc x hx univ univ_mem
    obtain ⟨q₀, hq₀⟩ := hP.nonempty
    by_cases hj : JoinedIn (f ⁻¹' {c} \ Z) p q₀
    · exact Or.inl ⟨O, hO, hxO, fun q hq => hj.trans ((hP.joinedIn q₀ hq₀ q hq).mono (hPsub O))⟩
    · exact Or.inr ⟨O, hO, hxO, fun q hq hjq =>
        hj (hjq.trans ((hP.joinedIn q hq q₀ hq₀).mono (hPsub O)))⟩
  have hdisj : ∀ x, f x = c → x ∈ J → x ∈ K → False := by
    rintro x hx ⟨O₁, hO₁, hx₁, h₁⟩ ⟨O₂, hO₂, hx₂, h₂⟩
    obtain ⟨O, -, -, hOsub, hP⟩ := loc x hx (O₁ ∩ O₂) ((hO₁.inter hO₂).mem_nhds ⟨hx₁, hx₂⟩)
    obtain ⟨q, ⟨hqc, hqO⟩, hqZ⟩ := hP.nonempty
    exact h₂ q ⟨⟨hqc, (hOsub hqO).2⟩, hqZ⟩ (h₁ q ⟨⟨hqc, (hOsub hqO).1⟩, hqZ⟩)
  have hpJ : p ∈ J := by
    obtain ⟨O, hO, hpO, -, hP⟩ := loc p hp.1.1 univ univ_mem
    exact ⟨O, hO, hpO, fun q hq => (hP.joinedIn p ⟨⟨hp.1.1, hpO⟩, hp.2⟩ q hq).mono (hPsub O)⟩
  have hKempty : ∀ x, f x = c → x ∉ K := by
    intro x hx hxK
    obtain ⟨y, hy, hyJ, hyK⟩ :=
      hconn.isPreconnected J K hJo hKo hsub ⟨p, hp.1.1, hpJ⟩ ⟨x, hx, hxK⟩
    exact hdisj y hy hyJ hyK
  refine ⟨p, ⟨hp.1.1, hp.2⟩, fun {q} hq => ?_⟩
  rcases hsub hq.1 with ⟨O, -, hqO, hJ⟩ | hqK
  · exact hJ q ⟨⟨hq.1, hqO⟩, hq.2⟩
  · exact absurd hqK (hKempty q hq.1)

omit [T2Space M] in
theorem exists_smooth_cell_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {τ : E} {F : E → M} (hF : Continuous F)
    (hper : ∀ z, F (z + τ) = F z) {U : Set E} (hU : IsOpen U) (hUper : ∀ z, z ∈ U ↔ z + τ ∈ U)
    (hFU : ContMDiffOn 𝓘(ℝ, E) I ∞ F U) {P : Set E} (hP : IsClosed P)
    (hPper : ∀ z, z ∈ P ↔ z + τ ∈ P) (hPU : P ⊆ U) {C N : Set E} (hC : IsCompact C)
    (hN : IsOpen N) (hCN : C ⊆ N) (hNc : IsCompact (closure N))
    (hdisj : ∀ k : ℤ, k ≠ 0 → ∀ z ∈ closure N, z + (k : ℝ) • τ ∉ closure N)
    {x₀ : M} (hNx₀ : F '' closure N ⊆ (chartAt H x₀).source)
    {𝒪 : Set (E × M)} (h𝒪 : IsOpen 𝒪) (h𝒪per : ∀ z y, (z, y) ∈ 𝒪 ↔ (z + τ, y) ∈ 𝒪)
    (hgraph : ∀ z, (z, F z) ∈ 𝒪) :
    ∃ F' : E → M, Continuous F' ∧ (∀ z, F' (z + τ) = F' z) ∧
      (∃ W : Set E, IsOpen W ∧ (∀ z, z ∈ W ↔ z + τ ∈ W) ∧ U ⊆ W ∧ C ⊆ W ∧
        ContMDiffOn 𝓘(ℝ, E) I ∞ F' W) ∧
      (∀ z ∈ P, F' z = F z) ∧ (∀ z, (∀ k : ℤ, z + (k : ℝ) • τ ∉ N) → F' z = F z) ∧
      ∀ z, (z, F' z) ∈ 𝒪 := by
  classical
  have hZ : ∀ p : E → Prop, (∀ z, p z ↔ p (z + τ)) →
      ∀ z (k : ℤ), p z ↔ p (z + (k : ℝ) • τ) := by
    intro p hp z k
    induction k using Int.induction_on with
    | zero => simp
    | succ i ih =>
      have he : z + ((i : ℤ) : ℝ) • τ + τ = z + (((i : ℤ) + 1 : ℤ) : ℝ) • τ := by
        push_cast; rw [add_smul, one_smul, add_assoc]
      rw [ih, hp (z + ((i : ℤ) : ℝ) • τ), he]
    | pred i ih =>
      have he : z + ((-(i : ℤ) - 1 : ℤ) : ℝ) • τ + τ = z + ((-(i : ℤ) : ℤ) : ℝ) • τ := by
        push_cast; rw [sub_smul, one_smul]; abel
      rw [ih, hp (z + ((-(i : ℤ) - 1 : ℤ) : ℝ) • τ), he]
  rcases eq_or_ne τ 0 with hτ | hτ
  · subst hτ
    have hNe : ∀ z, z ∉ closure N := by
      intro z hz
      exact hdisj 1 one_ne_zero z hz (by simpa using hz)
    refine ⟨F, hF, hper, ⟨U, hU, hUper, subset_rfl, fun z hz => ?_, hFU⟩, fun _ _ => rfl,
      fun _ _ => rfl, hgraph⟩
    exact absurd (subset_closure (hCN hz)) (hNe z)
  set φ := extChartAt I x₀ with hφ
  have hTo : IsOpen φ.target := isOpen_extChartAt_target x₀
  set V : Set E := F ⁻¹' (chartAt H x₀).source with hV
  have hVo : IsOpen V := (chartAt H x₀).open_source.preimage hF
  have hNV : closure N ⊆ V := fun z hz => hNx₀ ⟨z, hz, rfl⟩
  have hsrc : ∀ z ∈ V, F z ∈ φ.source := fun z hz => by rw [hφ, extChartAt_source]; exact hz
  obtain ⟨N₂, hN₂o, hNN₂, hN₂V, -⟩ := exists_open_between_and_isCompact_closure hNc hVo hNV
  obtain ⟨ψ, hψs, -, hψsupp, hψ1⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, E) (n := ⊤) hN₂o isClosed_closure hNN₂
  have hψc : ContDiff ℝ ∞ ψ := contMDiff_iff_contDiff.mp hψs
  have htsV : tsupport ψ ⊆ V := by
    change closure (support ψ) ⊆ V
    rw [hψsupp]; exact hN₂V
  set g : E → (Fin n → ℝ) := fun z => ψ z • φ (F z) with hg
  have hgzero : ∀ z, z ∉ V → g =ᶠ[𝓝 z] 0 := by
    intro z hz
    have : z ∉ tsupport ψ := fun h => hz (htsV h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp this] with w hw
    simp [hg, hw]
  have hgc : Continuous g := by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    by_cases hz : z ∈ V
    · exact hψc.continuous.continuousAt.smul
        ((continuousAt_extChartAt' (hsrc z hz)).comp hF.continuousAt)
    · exact continuousAt_const.congr (hgzero z hz).symm
  have hgU : ContDiffOn ℝ ∞ g U := by
    intro z hzU
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hz : z ∈ V
    · have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Fin n → ℝ) ∞ (φ ∘ F) z :=
        (contMDiffAt_extChartAt' hz).comp z (hFU.contMDiffAt (hU.mem_nhds hzU))
      exact hψc.contDiffAt.smul (contMDiffAt_iff_contDiffAt.mp h1)
    · exact contDiffAt_const.congr_of_eventuallyEq (hgzero z hz)
  have hgN : ∀ z ∈ closure N, g z = φ (F z) := fun z hz => by
    simp [hg, (hψ1 z).mp hz]
  set Ω : Set (E × (Fin n → ℝ)) :=
    (univ ×ˢ φ.target) ∩ (fun p => (p.1, φ.symm p.2)) ⁻¹' 𝒪 with hΩdef
  have hΩ : IsOpen Ω := by
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_univ.prod hTo) h𝒪
    exact continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt_symm x₀).comp continuous_snd.continuousOn fun p hp => hp.2)
  have hK₀ : IsCompact ((fun z => (z, g z)) '' closure N) :=
    hNc.image (continuous_id.prodMk hgc)
  have hK₀Ω : (fun z => (z, g z)) '' closure N ⊆ Ω := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨trivial, ?_⟩, ?_⟩
    · change g z ∈ φ.target
      rw [hgN z hz]; exact φ.map_source (hsrc z (hNV hz))
    · change (z, φ.symm (g z)) ∈ 𝒪
      rw [hgN z hz, φ.left_inv (hsrc z (hNV hz))]; exact hgraph z
  obtain ⟨δ, hδ, hδΩ⟩ := hK₀.exists_thickening_subset_open hΩ hK₀Ω
  obtain ⟨N₁, hN₁o, hCN₁, hN₁N, hN₁c⟩ := exists_open_between_and_isCompact_closure hC hN hCN
  obtain ⟨g', hg'c, ⟨W₀, hW₀o, hCW₀, hg'W⟩, hg'P, hg'N, hg'η⟩ :=
    exists_smooth_rel_euclid hgc hU hgU hP hPU hC hN₁o hCN₁ hδ
  have f1 : ∀ w ∈ closure N, g' w ∈ φ.target ∧ (w, φ.symm (g' w)) ∈ 𝒪 := by
    intro w hw
    have h : (w, g' w) ∈ Ω := hδΩ (Metric.mem_thickening_iff.mpr
      ⟨(w, g w), ⟨w, hw, rfl⟩, by rw [Prod.dist_eq, dist_self, dist_eq_norm]; exact max_lt hδ (hg'η w)⟩)
    exact ⟨h.1.2, h.2⟩
  have f2 : ∀ w ∈ closure N, w ∉ N₁ → φ.symm (g' w) = F w := by
    intro w hw hw'
    rw [hg'N w hw', hgN w hw, φ.left_inv (hsrc w (hNV hw))]
  have f3 : ∀ w ∈ closure N, w ∈ P → φ.symm (g' w) = F w := by
    intro w hw hw'
    rw [hg'P w hw', hgN w hw, φ.left_inv (hsrc w (hNV hw))]
  have huniq : ∀ z (k k' : ℤ), z + (k : ℝ) • τ ∈ closure N → z + (k' : ℝ) • τ ∈ closure N →
      k = k' := by
    intro z k k' hk hk'
    by_contra hne
    have he : z + (k : ℝ) • τ + ((k' - k : ℤ) : ℝ) • τ = z + (k' : ℝ) • τ := by
      push_cast; rw [sub_smul]; abel
    exact hdisj (k' - k) (sub_ne_zero.mpr (Ne.symm hne)) _ hk (he ▸ hk')
  let F' : E → M := fun z =>
    if h : ∃ k : ℤ, z + (k : ℝ) • τ ∈ closure N then φ.symm (g' (z + (h.choose : ℝ) • τ))
    else F z
  have hF'eq : ∀ z (k : ℤ), z + (k : ℝ) • τ ∈ closure N →
      F' z = φ.symm (g' (z + (k : ℝ) • τ)) := by
    intro z k hk
    change (if h : ∃ k : ℤ, z + (k : ℝ) • τ ∈ closure N then
      φ.symm (g' (z + (h.choose : ℝ) • τ)) else F z) = _
    split_ifs with h
    · rw [huniq z _ _ h.choose_spec hk]
    · exact absurd ⟨k, hk⟩ h
  have hF'else : ∀ z, (¬ ∃ k : ℤ, z + (k : ℝ) • τ ∈ closure N) → F' z = F z := by
    intro z h
    change (if h : ∃ k : ℤ, z + (k : ℝ) • τ ∈ closure N then
      φ.symm (g' (z + (h.choose : ℝ) • τ)) else F z) = _
    split_ifs
    rfl
  have hFk : ∀ z (k : ℤ), F (z + (k : ℝ) • τ) = F z := fun z k =>
    ((hZ (fun w => F w = F z) (fun w => by simp only [hper]) z k).mp rfl)
  have L1 : ∀ z (k : ℤ), z + (k : ℝ) • τ ∈ N →
      F' =ᶠ[𝓝 z] fun w => φ.symm (g' (w + (k : ℝ) • τ)) := by
    intro z k hk
    have ho : IsOpen ((fun w => w + (k : ℝ) • τ) ⁻¹' N) := hN.preimage (continuous_add_const _)
    filter_upwards [ho.mem_nhds hk] with w hw
    exact hF'eq w k (subset_closure hw)
  have hO₁ : IsOpen {z : E | ¬ ∃ k : ℤ, z + (k : ℝ) • τ ∈ closure N₁} := by
    have h := isOpen_periodic_imp (X := E) hτ hN₁c isOpen_empty
    have h2 := h.preimage (continuous_id.prodMk continuous_id)
    convert h2 using 1
    ext z; simp
  have L2 : ∀ z, (∀ k : ℤ, z + (k : ℝ) • τ ∉ N) → F' =ᶠ[𝓝 z] F := by
    intro z hz
    have hz1 : z ∈ {z : E | ¬ ∃ k : ℤ, z + (k : ℝ) • τ ∈ closure N₁} :=
      fun ⟨k, hk⟩ => hz k (hN₁N hk)
    filter_upwards [hO₁.mem_nhds hz1] with w hw
    by_cases h : ∃ k : ℤ, w + (k : ℝ) • τ ∈ closure N
    · obtain ⟨k, hk⟩ := h
      rw [hF'eq w k hk, f2 _ hk (fun h' => hw ⟨k, subset_closure h'⟩), hFk]
    · exact hF'else w h
  refine ⟨F', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.mpr fun z => ?_
    by_cases h : ∃ k : ℤ, z + (k : ℝ) • τ ∈ N
    · obtain ⟨k, hk⟩ := h
      refine ContinuousAt.congr ?_ (L1 z k hk).symm
      exact ContinuousAt.comp (g := φ.symm) (f := fun w => g' (w + (k : ℝ) • τ))
        (continuousAt_extChartAt_symm'' (f1 _ (subset_closure hk)).1)
        (hg'c.comp (continuous_add_const ((k : ℝ) • τ))).continuousAt
    · replace h := not_exists.mp h
      exact hF.continuousAt.congr (L2 z h).symm
  · intro z
    by_cases h : ∃ k : ℤ, z + (k : ℝ) • τ ∈ closure N
    · obtain ⟨k, hk⟩ := h
      have he : z + τ + ((k - 1 : ℤ) : ℝ) • τ = z + (k : ℝ) • τ := by
        push_cast; rw [sub_smul, one_smul]; abel
      rw [hF'eq z k hk, hF'eq (z + τ) (k - 1) (he ▸ hk), he]
    · have h' : ¬ ∃ k : ℤ, z + τ + (k : ℝ) • τ ∈ closure N := by
        rintro ⟨k, hk⟩
        have he : z + τ + (k : ℝ) • τ = z + ((k + 1 : ℤ) : ℝ) • τ := by
          push_cast; rw [add_smul, one_smul]; abel
        exact h ⟨k + 1, he ▸ hk⟩
      rw [hF'else z h, hF'else _ h', hper]
  · refine ⟨U ∪ ⋃ k : ℤ, (fun z => z + (k : ℝ) • τ) ⁻¹' (W₀ ∩ N), ?_, ?_,
      subset_union_left, ?_, ?_⟩
    · exact hU.union (isOpen_iUnion fun k => (hW₀o.inter hN).preimage (continuous_add_const _))
    · intro z
      simp only [mem_union, mem_iUnion, mem_preimage]
      refine or_congr (hUper z) ⟨fun ⟨k, hk⟩ => ⟨k - 1, ?_⟩, fun ⟨k, hk⟩ => ⟨k + 1, ?_⟩⟩
      · have he : z + τ + ((k - 1 : ℤ) : ℝ) • τ = z + (k : ℝ) • τ := by
          push_cast; rw [sub_smul, one_smul]; abel
        rwa [he]
      · have he : z + ((k + 1 : ℤ) : ℝ) • τ = z + τ + (k : ℝ) • τ := by
          push_cast; rw [add_smul, one_smul]; abel
        rwa [he]
    · intro z hz
      refine Or.inr (mem_iUnion.mpr ⟨0, ?_⟩)
      simp only [mem_preimage, Int.cast_zero, zero_smul, add_zero]
      exact ⟨hCW₀ hz, hCN hz⟩
    · intro z hz
      refine ContMDiffAt.contMDiffWithinAt ?_
      by_cases h : ∃ k : ℤ, z + (k : ℝ) • τ ∈ N
      · obtain ⟨k, hk⟩ := h
        have hkUW : z + (k : ℝ) • τ ∈ U ∪ W₀ := by
          rcases hz with hzU | hz
          · exact Or.inl ((hZ (· ∈ U) hUper z k).mp hzU)
          · obtain ⟨k', hk'⟩ := mem_iUnion.mp hz
            have : k' = k := huniq z k' k (subset_closure hk'.2) (subset_closure hk)
            subst this
            exact Or.inr hk'.1
        have hgd : ContDiffAt ℝ ∞ (fun w => g' (w + (k : ℝ) • τ)) z :=
          (hg'W.contDiffAt ((hU.union hW₀o).mem_nhds hkUW)).comp z
            (contDiffAt_id.add contDiffAt_const)
        have hsym : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ φ.symm (g' (z + (k : ℝ) • τ)) :=
          (contMDiffOn_extChartAt_symm x₀).contMDiffAt
            (hTo.mem_nhds (f1 _ (subset_closure hk)).1)
        exact (hsym.comp z hgd.contMDiffAt).congr_of_eventuallyEq (L1 z k hk)
      · replace h := not_exists.mp h
        have hzU : z ∈ U := by
          rcases hz with hzU | hz
          · exact hzU
          · obtain ⟨k', hk'⟩ := mem_iUnion.mp hz
            exact absurd hk'.2 (h k')
        exact (hFU.contMDiffAt (hU.mem_nhds hzU)).congr_of_eventuallyEq (L2 z h)
  · intro z hz
    by_cases h : ∃ k : ℤ, z + (k : ℝ) • τ ∈ closure N
    · obtain ⟨k, hk⟩ := h
      rw [hF'eq z k hk, f3 _ hk ((hZ (· ∈ P) hPper z k).mp hz), hFk]
    · exact hF'else z h
  · intro z hz
    exact (L2 z hz).eq_of_nhds
  · intro z
    by_cases h : ∃ k : ℤ, z + (k : ℝ) • τ ∈ closure N
    · obtain ⟨k, hk⟩ := h
      rw [hF'eq z k hk]
      exact (hZ (fun w => (w, φ.symm (g' (z + (k : ℝ) • τ))) ∈ 𝒪)
        (fun w => h𝒪per w _) z k).mpr (f1 _ hk).2
    · rw [hF'else z h]; exact hgraph z

omit [T2Space M] in
theorem exists_smooth_loop_approx {γ₀ : ℝ → M} (hγ : Continuous γ₀) (hper : Periodic γ₀ 1)
    {U P : Set ℝ} (hU : IsOpen U) (hUper : ∀ t, t ∈ U ↔ t + 1 ∈ U)
    (hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ₀ U) (hP : IsClosed P) (hPper : ∀ t, t ∈ P ↔ t + 1 ∈ P)
    (hPU : P ⊆ U) {O : Set (M × M)} (hO : IsOpen O) (hdiag : ∀ x, (x, x) ∈ O) :
    ∃ γ₁ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ₁ ∧ Periodic γ₁ 1 ∧ (∀ t ∈ P, γ₁ t = γ₀ t) ∧
      ∀ t, (γ₀ t, γ₁ t) ∈ O := by
  have hZper : ∀ S : Set ℝ, (∀ z, z ∈ S ↔ z + 1 ∈ S) → ∀ (k : ℤ) (z : ℝ), z ∈ S ↔ z + k ∈ S := by
    intro S hS k
    induction k using Int.induction_on with
    | zero => intro z; simp
    | succ i ih =>
      intro z
      rw [ih z, hS (z + (i : ℤ))]
      push_cast; ring_nf
    | pred i ih =>
      intro z
      rw [ih z, hS (z + ((-(i : ℤ) - 1 : ℤ) : ℝ))]
      push_cast; ring_nf
  obtain ⟨m, C, N, x, hCc, hNo, hCN, hNc, -, hNG, hNdiam, -, hKcov⟩ :=
    exists_small_cells (E := ℝ) (X := M) hγ (fun y => (chartAt H y).source)
      (fun y => ⟨(chartAt H y).open_source, mem_chart_source H y⟩)
      (isCompact_Icc.diff hU) isOpen_univ (subset_univ _) (by norm_num : (0 : ℝ) < 1 / 2)
  set 𝒪₀ : Set (ℝ × M) := {q | (γ₀ q.1, q.2) ∈ O} ∩
    ⋂ j : Fin m, {q : ℝ × M | (∃ k : ℤ, q.1 + (k : ℝ) • (1 : ℝ) ∈ closure (N j)) →
      q.2 ∈ (chartAt H (x j)).source} with h𝒪₀def
  have h𝒪₀ : IsOpen 𝒪₀ := by
    refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun j => ?_)
    · exact hO.preimage ((hγ.comp continuous_fst).prodMk continuous_snd)
    · exact isOpen_periodic_imp (E := ℝ) (X := M) (τ := (1 : ℝ)) one_ne_zero (hNc j)
        (chartAt H (x j)).open_source
  have h𝒪₀per : ∀ z y, (z, y) ∈ 𝒪₀ ↔ (z + 1, y) ∈ 𝒪₀ := by
    intro z y
    simp only [h𝒪₀def, mem_inter_iff, mem_ofPred_eq, mem_iInter, smul_eq_mul, mul_one]
    rw [hper z]
    refine and_congr Iff.rfl (forall_congr' fun j => imp_congr ?_ Iff.rfl)
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k - 1, by push_cast; convert hk using 1; ring⟩
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, by push_cast; convert hk using 1; ring⟩
  have hγ₀𝒪 : ∀ z, (z, γ₀ z) ∈ 𝒪₀ := by
    intro z
    refine ⟨hdiag _, ?_⟩
    simp only [mem_iInter, mem_ofPred_eq]
    rintro j ⟨k, hk⟩
    have h1 : γ₀ (z + (k : ℝ) • (1 : ℝ)) = γ₀ z := by
      simpa [smul_eq_mul, mul_one] using hper.int_mul k z
    rw [← h1]
    exact hNG j ⟨_, hk, rfl⟩
  have key : ∀ j : ℕ, j ≤ m → ∃ γ : ℝ → M, Continuous γ ∧ (∀ z, γ (z + 1) = γ z) ∧
      (∃ W : Set ℝ, IsOpen W ∧ (∀ z, z ∈ W ↔ z + 1 ∈ W) ∧ U ⊆ W ∧
        (∀ i : Fin m, (i : ℕ) < j → C i ⊆ W) ∧ ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ W) ∧
      (∀ z ∈ P, γ z = γ₀ z) ∧ ∀ z, (z, γ z) ∈ 𝒪₀ := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨γ₀, hγ, hper, ⟨U, hU, hUper, subset_rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
        hsm⟩, fun z _ => rfl, hγ₀𝒪⟩
    | succ j ih =>
      intro hj
      obtain ⟨γ, hγc, hγper, ⟨W, hWo, hWper, hUW, hCW, hγW⟩, hγP, hγ𝒪⟩ := ih (by omega)
      set j' : Fin m := ⟨j, by omega⟩ with hj'
      have hdisj : ∀ k : ℤ, k ≠ 0 → ∀ z ∈ closure (N j'),
          z + (k : ℝ) • (1 : ℝ) ∉ closure (N j') := by
        intro k hk z hz hz'
        have h1 := hNdiam j' z hz _ hz'
        have h2 : (1 : ℝ) ≤ |(k : ℝ)| := by
          have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
          exact_mod_cast this
        rw [smul_eq_mul, mul_one, sub_add_cancel_left, Real.norm_eq_abs, abs_neg] at h1
        linarith
      have hNx : γ '' closure (N j') ⊆ (chartAt H (x j')).source := by
        rintro _ ⟨z, hz, rfl⟩
        have := (hγ𝒪 z).2
        simp only [mem_iInter, mem_ofPred_eq] at this
        exact this j' ⟨0, by simpa using hz⟩
      obtain ⟨γ', hγ'c, hγ'per, ⟨W', hW'o, hW'per, hWW', hCW', hγ'W'⟩, hγ'P, -, hγ'𝒪⟩ :=
        exists_smooth_cell_step (I := I) (τ := (1 : ℝ)) hγc hγper hWo hWper hγW hP hPper
          (hPU.trans hUW) (hCc j') (hNo j') (hCN j') (hNc j') hdisj hNx h𝒪₀ h𝒪₀per hγ𝒪
      refine ⟨γ', hγ'c, hγ'per, ⟨W', hW'o, hW'per, hUW.trans hWW', fun i hi => ?_, hγ'W'⟩,
        fun z hz => (hγ'P z hz).trans (hγP z hz), hγ'𝒪⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact (hCW i hi).trans hWW'
      · have : i = j' := Fin.ext hi
        rw [this]; exact hCW'
  obtain ⟨γ₁, -, hγ₁per, ⟨W, -, hWper, hUW, hCW, hγ₁W⟩, hγ₁P, hγ₁𝒪⟩ := key m le_rfl
  have hWuniv : W = univ := by
    refine eq_univ_of_forall fun t => ?_
    have ht : t = Int.fract t + (⌊t⌋ : ℝ) := by rw [← Int.self_sub_floor]; ring
    rw [ht, ← hZper W hWper ⌊t⌋ (Int.fract t)]
    by_cases hfU : Int.fract t ∈ U
    · exact hUW hfU
    · have hK : Int.fract t ∈ Icc (0 : ℝ) 1 \ U :=
        ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, hfU⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hKcov hK)
      exact hCW i i.isLt (interior_subset hi)
  refine ⟨γ₁, ?_, hγ₁per, hγ₁P, fun t => (hγ₁𝒪 t).1⟩
  rw [← contMDiffOn_univ, ← hWuniv]
  exact hγ₁W

omit [T2Space M] in
theorem exists_smooth_approx {F : ℝ → ℝ → M} (hF : Continuous (uncurry F))
    (hper : ∀ θ s, F (θ + 1) s = F θ s) {U P : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hUper : ∀ θ s, (θ, s) ∈ U ↔ (θ + 1, s) ∈ U) (hFU : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry F) U)
    (hP : IsClosed P) (hPper : ∀ θ s, (θ, s) ∈ P ↔ (θ + 1, s) ∈ P) (hPU : P ⊆ U)
    (hPs : ∀ θ s, s ∉ Ioo (0 : ℝ) 1 → (θ, s) ∈ P)
    {O : Set (M × M)} (hO : IsOpen O) (hdiag : ∀ x, (x, x) ∈ O) :
    ∃ F' : ℝ → ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry F') ∧
      (∀ θ s, F' (θ + 1) s = F' θ s) ∧ (∀ θ s, (θ, s) ∈ P → F' θ s = F θ s) ∧
      ∀ θ s, (F θ s, F' θ s) ∈ O := by
  classical
  set τ : ℝ × ℝ := ((1 : ℝ), (0 : ℝ)) with hτdef
  have hτ : ∀ z : ℝ × ℝ, z + τ = (z.1 + 1, z.2) := by
    intro z; rw [hτdef]; ext <;> simp
  have hkτ : ∀ (z : ℝ × ℝ) (k : ℤ), z + (k : ℝ) • τ = (z.1 + k, z.2) := by
    intro z k; rw [hτdef]; ext <;> simp
  have hFper : ∀ z : ℝ × ℝ, uncurry F (z + τ) = uncurry F z := by
    intro z; rw [hτ z]; exact hper z.1 z.2
  have hsetZ : ∀ S : Set (ℝ × ℝ), (∀ z, z ∈ S ↔ z + τ ∈ S) →
      ∀ (z : ℝ × ℝ) (k : ℤ), z + (k : ℝ) • τ ∈ S ↔ z ∈ S := by
    intro S hS z k
    have hp : Function.Periodic (fun w : ℝ × ℝ => w ∈ S) τ :=
      fun w => propext (hS w).symm
    have := (hp.zsmul k) z
    rw [← Int.cast_smul_eq_zsmul ℝ] at this
    rw [this]
  have hfunZ : ∀ g : ℝ × ℝ → M, (∀ z, g (z + τ) = g z) →
      ∀ (z : ℝ × ℝ) (k : ℤ), g (z + (k : ℝ) • τ) = g z := by
    intro g hg z k
    have hp : Function.Periodic g τ := hg
    have := (hp.zsmul k) z
    rw [← Int.cast_smul_eq_zsmul ℝ] at this
    exact this
  obtain ⟨m, C, N, x, hCc, hNo, hCN, hNc, hNW, hNF, hNdiam, -, hKcov⟩ :=
    exists_small_cells (E := ℝ × ℝ) (X := M) (F := uncurry F) hF
      (fun y => (chartAt H y).source) (fun y => ⟨(chartAt H y).open_source, mem_chart_source H y⟩)
      (K := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ U) (W := Pᶜ)
      ((isCompact_Icc.prod isCompact_Icc).diff hU) hP.isOpen_compl
      (fun z hz => fun hzP => hz.2 (hPU hzP)) (δ := 1 / 2) (by norm_num)
  set 𝒪₀ : Set ((ℝ × ℝ) × M) := {q | (uncurry F q.1, q.2) ∈ O} ∩
    ⋂ j : Fin m, {q | (∃ k : ℤ, q.1 + (k : ℝ) • τ ∈ closure (N j)) →
      q.2 ∈ (chartAt H (x j)).source} with h𝒪₀def
  have h𝒪₀ : IsOpen 𝒪₀ := by
    refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun j => ?_)
    · exact hO.preimage ((hF.comp continuous_fst).prodMk continuous_snd)
    · exact isOpen_periodic_imp (by simp [hτdef]) (hNc j) (chartAt H (x j)).open_source
  have h𝒪₀per : ∀ z y, (z, y) ∈ 𝒪₀ ↔ (z + τ, y) ∈ 𝒪₀ := by
    intro z y
    simp only [h𝒪₀def, mem_inter_iff, mem_ofPred_eq, mem_iInter, hFper z]
    refine and_congr Iff.rfl (forall_congr' fun j => ?_)
    refine imp_congr_left ⟨fun ⟨k, hk⟩ => ⟨k - 1, ?_⟩, fun ⟨k, hk⟩ => ⟨k + 1, ?_⟩⟩
    · convert hk using 1; push_cast; rw [sub_smul, one_smul]; abel
    · convert hk using 1; push_cast; rw [add_smul, one_smul]; abel
  have hgraph₀ : ∀ z, (z, uncurry F z) ∈ 𝒪₀ := by
    intro z
    refine ⟨hdiag _, mem_iInter.2 fun j => ?_⟩
    rintro ⟨k, hk⟩
    have h1 := hNF j (mem_image_of_mem _ hk)
    rwa [hfunZ _ hFper z k] at h1
  have hind : ∀ j : ℕ, j ≤ m → ∃ G : ℝ × ℝ → M, Continuous G ∧ (∀ z, G (z + τ) = G z) ∧
      (∃ W : Set (ℝ × ℝ), IsOpen W ∧ (∀ z, z ∈ W ↔ z + τ ∈ W) ∧ U ⊆ W ∧
        (∀ i : Fin m, (i : ℕ) < j → C i ⊆ W) ∧ ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ G W) ∧
      (∀ z ∈ P, G z = uncurry F z) ∧ ∀ z, (z, G z) ∈ 𝒪₀ := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨uncurry F, hF, hFper, ⟨U, hU, fun z => ?_, subset_rfl, fun i hi => absurd hi
        (Nat.not_lt_zero _), hFU⟩, fun _ _ => rfl, hgraph₀⟩
      rw [hτ z]; exact hUper z.1 z.2
    | succ j ih =>
      intro hj
      obtain ⟨G, hGc, hGper, ⟨W, hWo, hWper, hUW, hCW, hGW⟩, hGP, hG𝒪⟩ := ih (by omega)
      set j' : Fin m := ⟨j, by omega⟩ with hj'
      have hdisj : ∀ k : ℤ, k ≠ 0 → ∀ z ∈ closure (N j'), z + (k : ℝ) • τ ∉ closure (N j') := by
        intro k hk z hz hz'
        have hd := hNdiam j' z hz _ hz'
        have h1 : ‖z - (z + (k : ℝ) • τ)‖ = ‖(k : ℝ) • τ‖ := by
          rw [sub_add_cancel_left, norm_neg]
        have h2 : (1 : ℝ) ≤ ‖(k : ℝ) • τ‖ := by
          refine le_trans ?_ (norm_fst_le _)
          have : ((k : ℝ) • τ).1 = (k : ℝ) := by simp [hτdef]
          rw [this, Real.norm_eq_abs, ← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hk
        linarith
      have hNx : G '' closure (N j') ⊆ (chartAt H (x j')).source := by
        rintro _ ⟨z, hz, rfl⟩
        have := mem_iInter.1 (hG𝒪 z).2 j'
        exact this ⟨0, by simpa using hz⟩
      obtain ⟨G', hG'c, hG'per, ⟨W', hW'o, hW'per, hWW', hCW', hG'W'⟩, hG'P, -, hG'𝒪⟩ :=
        exists_smooth_cell_step (I := I) hGc hGper hWo hWper hGW hP
          (fun z => by rw [hτ z]; exact hPper z.1 z.2) (hPU.trans hUW) (hCc j') (hNo j')
          (hCN j') (hNc j') hdisj hNx h𝒪₀ h𝒪₀per hG𝒪
      refine ⟨G', hG'c, hG'per, ⟨W', hW'o, hW'per, hUW.trans hWW', fun i hi => ?_, hG'W'⟩,
        fun z hz => (hG'P z hz).trans (hGP z hz), hG'𝒪⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact (hCW i hi).trans hWW'
      · have : i = j' := Fin.ext hi
        rw [this]; exact hCW'
  obtain ⟨G, hGc, hGper, ⟨W, hWo, hWper, hUW, hCW, hGW⟩, hGP, hG𝒪⟩ := hind m le_rfl
  have hWuniv : ∀ z, z ∈ W := by
    intro z
    by_cases hs : z.2 ∈ Ioo (0 : ℝ) 1
    · rw [← hsetZ W hWper z (-⌊z.1⌋)]
      set z' := z + ((-⌊z.1⌋ : ℤ) : ℝ) • τ with hz'
      have hz'1 : z' = (Int.fract z.1, z.2) := by
        rw [hz', hkτ]; simp [Int.fract, sub_eq_add_neg]
      by_cases hU' : z' ∈ U
      · exact hUW hU'
      · have hK : z' ∈ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ U := by
          refine ⟨?_, hU'⟩
          rw [hz'1]
          exact ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ⟨hs.1.le, hs.2.le⟩⟩
        obtain ⟨i, hi⟩ := mem_iUnion.1 (hKcov hK)
        exact hCW i i.2 (interior_subset hi)
    · exact hUW (hPU (hPs z.1 z.2 hs))
  refine ⟨curry G, ?_, fun θ s => ?_, fun θ s hθs => ?_, fun θ s => ?_⟩
  · rw [uncurry_curry]
    exact fun z => hGW.contMDiffAt (hWo.mem_nhds (hWuniv z))
  · have := hGper (θ, s)
    rw [hτ] at this
    exact this
  · exact hGP (θ, s) hθs
  · exact (hG𝒪 (θ, s)).1

theorem exists_smooth_level_loop (hf : MorseStrip I f a b) (D : GradientLikeStrip I f a b crit)
    {c : ℝ} (hc : c ∈ Ioo a b) (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c)
    {γ₀ : ℝ → M} (hγ : Continuous γ₀) (hper : Periodic γ₀ 1) (hlev : ∀ t, f (γ₀ t) = c)
    {U P : Set ℝ} (hU : IsOpen U) (hUper : ∀ t, t ∈ U ↔ t + 1 ∈ U)
    (hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ₀ U) (hP : IsClosed P) (hPper : ∀ t, t ∈ P ↔ t + 1 ∈ P)
    (hPU : P ⊆ U) {O : Set (M × M)} (hO : IsOpen O) (hdiag : ∀ x, (x, x) ∈ O) :
    ∃ γ₁ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ₁ ∧ Periodic γ₁ 1 ∧ (∀ t, f (γ₁ t) = c) ∧
      (∀ t ∈ P, γ₁ t = γ₀ t) ∧ ∀ t, (γ₀ t, γ₁ t) ∈ O := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hfc : Continuous f := hfs.continuous
  have hcI : c ∈ Icc a b := ⟨hc.1.le, hc.2.le⟩
  have hlevΩ : ∀ x, f x = c → x ∈ D.regularFlowDomain c := by
    intro x hx
    refine ⟨by rw [hx]; exact hc, fun s hs p hp hmem => ?_⟩
    rw [hx, sub_self, uIcc_self, mem_singleton_iff] at hs
    subst hs
    rw [GradientLikeStrip.flow_zero] at hmem
    exact hcU p hp x hmem hx
  set O' : Set (M × M) := {q | f q.1 ≠ c} ∪ {q | q.2 ∈ D.regularFlowDomain c ∧ (q.1, D.π c q.2) ∈ O} with hO'def
  have hO' : IsOpen O' := by
    refine IsOpen.union (isOpen_ne_fun (hfc.comp continuous_fst) continuous_const) ?_
    exact ((D.isOpen_regularFlowDomain hfc c).preimage continuous_snd).inter
      (hO.preimage (continuous_fst.prodMk ((D.continuous_π hfs c).comp continuous_snd)))
  have hdiag' : ∀ x, (x, x) ∈ O' := by
    intro x
    by_cases hx : f x = c
    · right
      exact ⟨hlevΩ x hx, by rw [GradientLikeStrip.π_eq_self_of_level hx]; exact hdiag x⟩
    · left
      exact hx
  obtain ⟨γ₁, hγ₁, hper₁, hP₁, hO₁⟩ :=
    exists_smooth_loop_approx (I := I) hγ hper hU hUper hsm hP hPper hPU hO' hdiag'
  have hmem : ∀ t, γ₁ t ∈ D.regularFlowDomain c ∧ (γ₀ t, D.π c (γ₁ t)) ∈ O := by
    intro t
    rcases hO₁ t with h | h
    · exact absurd (hlev t) h
    · exact h
  refine ⟨fun t => D.π c (γ₁ t), (D.contMDiff_π hfs c).comp hγ₁, fun t => ?_,
    fun t => GradientLikeStrip.f_π hfs hcI (hmem t).1, fun t ht => ?_, fun t => (hmem t).2⟩
  · simp only [hper₁ t]
  · simp only [hP₁ t ht, GradientLikeStrip.π_eq_self_of_level (hlev t)]

theorem exists_smooth_level_family (hf : MorseStrip I f a b)
    (D : GradientLikeStrip I f a b crit) {c : ℝ} (hc : c ∈ Ioo a b)
    (hcU : ∀ x hx, ∀ y ∈ D.closedSmallBall x hx, f y ≠ c) {F : ℝ → ℝ → M}
    (hF : Continuous (uncurry F)) (hper : ∀ θ s, F (θ + 1) s = F θ s)
    (hlev : ∀ θ s, f (F θ s) = c) {U P : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hUper : ∀ θ s, (θ, s) ∈ U ↔ (θ + 1, s) ∈ U) (hFU : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry F) U)
    (hP : IsClosed P) (hPper : ∀ θ s, (θ, s) ∈ P ↔ (θ + 1, s) ∈ P) (hPU : P ⊆ U)
    (hPs : ∀ θ s, s ∉ Ioo (0 : ℝ) 1 → (θ, s) ∈ P)
    {O : Set (M × M)} (hO : IsOpen O) (hdiag : ∀ x, (x, x) ∈ O) :
    ∃ F' : ℝ → ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry F') ∧
      (∀ θ s, F' (θ + 1) s = F' θ s) ∧ (∀ θ s, f (F' θ s) = c) ∧
      (∀ θ s, (θ, s) ∈ P → F' θ s = F θ s) ∧ ∀ θ s, (F θ s, F' θ s) ∈ O := by
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hcI : c ∈ Icc a b := ⟨hc.1.le, hc.2.le⟩
  set O' : Set (M × M) :=
    {q | f q.1 ≠ c} ∪ {q | q.2 ∈ D.regularFlowDomain c ∧ (q.1, D.π c q.2) ∈ O} with hO'def
  have hO' : IsOpen O' := by
    refine IsOpen.union ?_ (IsOpen.inter ?_ ?_)
    · exact isOpen_ne_fun (hfs.continuous.comp continuous_fst) continuous_const
    · exact (D.isOpen_regularFlowDomain hfs.continuous c).preimage continuous_snd
    · exact hO.preimage (continuous_fst.prodMk ((D.continuous_π hfs c).comp continuous_snd))
  have hdiag' : ∀ x, (x, x) ∈ O' := by
    intro x
    by_cases hx : f x = c
    · right
      refine ⟨⟨by rw [hx]; exact hc, fun s hs p hp => ?_⟩, ?_⟩
      · rw [hx, sub_self, uIcc_self, mem_singleton_iff] at hs
        rw [hs, D.flow_zero]
        exact fun hmem => hcU p hp x hmem hx
      · change (x, D.π c x) ∈ O
        rw [GradientLikeStrip.π_eq_self_of_level hx]
        exact hdiag x
    · left
      exact hx
  obtain ⟨F', hF'sm, hF'per, hF'P, hF'O⟩ :=
    exists_smooth_approx hF hper hU hUper hFU hP hPper hPU hPs hO' hdiag'
  have hmem : ∀ θ s, F' θ s ∈ D.regularFlowDomain c ∧ (F θ s, D.π c (F' θ s)) ∈ O := by
    intro θ s
    rcases hF'O θ s with h | h
    · exact absurd (hlev θ s) h
    · exact h
  refine ⟨fun θ s => D.π c (F' θ s), ?_, ?_, ?_, ?_, ?_⟩
  · exact (D.contMDiff_π hfs c).comp hF'sm
  · intro θ s
    simp only [hF'per θ s]
  · intro θ s
    exact GradientLikeStrip.f_π hfs hcI (hmem θ s).1
  · intro θ s hθs
    simp only [hF'P θ s hθs]
    exact GradientLikeStrip.π_eq_self_of_level (hlev θ s)
  · intro θ s
    exact (hmem θ s).2

theorem exists_avoid_cell_step {G : ℝ × ℝ → M} (hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ G)
    (hper : ∀ z : ℝ × ℝ, G (z + ((1 : ℝ), (0 : ℝ))) = G z) {T : Set M} {d : ℕ}
    (hT : isThin I d T) (hd : d + 2 < n) {C N : Set (ℝ × ℝ)} (hC : IsCompact C)
    (hN : IsOpen N) (hCN : C ⊆ N) (hNc : IsCompact (closure N))
    (hdisj : ∀ k : ℤ, k ≠ 0 → ∀ z ∈ closure N, z + ((k : ℝ), (0 : ℝ)) ∉ closure N)
    {x₀ : M} (hNx₀ : G '' closure N ⊆ (chartAt H x₀).source)
    {𝒪 : Set ((ℝ × ℝ) × M)} (h𝒪 : IsOpen 𝒪)
    (h𝒪per : ∀ z y, (z, y) ∈ 𝒪 ↔ (z + ((1 : ℝ), (0 : ℝ)), y) ∈ 𝒪)
    (hgraph : ∀ z, (z, G z) ∈ 𝒪) :
    ∃ G' : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ G' ∧
      (∀ z, G' (z + ((1 : ℝ), (0 : ℝ))) = G' z) ∧
      (∀ z, (∀ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∉ N) → G' z = G z) ∧
      (∀ z, (z, G' z) ∈ 𝒪) ∧ ∀ z ∈ C, G' z ∉ T := by
  classical
  have _hT2 : T2Space M := inferInstance
  set φ := extChartAt I x₀ with hφ
  have hτk : ∀ k : ℤ, k • ((1 : ℝ), (0 : ℝ)) = ((k : ℝ), (0 : ℝ)) := by
    intro k; ext <;> simp
  have hGk : ∀ z (k : ℤ), G (z + ((k : ℝ), (0 : ℝ))) = G z := by
    intro z k
    have hP : Function.Periodic G ((1 : ℝ), (0 : ℝ)) := hper
    have := hP.zsmul k z
    rwa [hτk] at this
  have h𝒪k : ∀ z y (k : ℤ), (z + ((k : ℝ), (0 : ℝ)), y) ∈ 𝒪 ↔ (z, y) ∈ 𝒪 := by
    intro z y k
    have hP : Function.Periodic (fun z : ℝ × ℝ => {y : M | (z, y) ∈ 𝒪}) ((1 : ℝ), (0 : ℝ)) := by
      intro z; ext y; exact (h𝒪per z y).symm
    have := congrArg (fun s : Set M => y ∈ s) (hP.zsmul k z)
    simp only [hτk, Set.mem_ofPred_eq] at this
    exact Iff.of_eq this
  have hdisjN : ∀ z (j k : ℤ), z + ((j : ℝ), (0 : ℝ)) ∈ N → z + ((k : ℝ), (0 : ℝ)) ∈ N → j = k := by
    intro z j k hj hk
    by_contra hne
    have hne' : k - j ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    apply hdisj (k - j) hne' (z + ((j : ℝ), (0 : ℝ))) (subset_closure hj)
    have : z + ((j : ℝ), (0 : ℝ)) + (((k - j : ℤ) : ℝ), (0 : ℝ)) = z + ((k : ℝ), (0 : ℝ)) := by
      ext <;> simp
    rw [this]; exact subset_closure hk
  have hsrc : ∀ z ∈ closure N, G z ∈ φ.source := by
    intro z hz; rw [hφ, extChartAt_source]; exact hNx₀ (mem_image_of_mem G hz)
  obtain ⟨V₁, hV₁o, hCV₁, hV₁N, -⟩ := exists_open_between_and_isCompact_closure hC hN hCN
  obtain ⟨b, hb0, hb1, hb01⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℝ × ℝ) (n := ⊤)
    hV₁o.isClosed_compl hC.isClosed (Set.disjoint_compl_left_iff_subset.mpr hCV₁)
  have hbsupp : tsupport b ⊆ N := by
    refine (closure_mono ?_).trans hV₁N
    intro z hz
    by_contra hzV
    exact hz (hb0 hzV)
  have hbK : IsCompact (tsupport b) :=
    hNc.of_isClosed_subset (isClosed_tsupport _) (hbsupp.trans subset_closure)
  have htube : ∀ᶠ w in 𝓝 (0 : Fin n → ℝ), ∀ z ∈ closure N,
      φ (G z) + w ∈ φ.target ∧ (z, φ.symm (φ (G z) + w)) ∈ 𝒪 := by
    refine hNc.eventually_forall_of_forall_eventually (fun z hz => ?_)
    have hs := hsrc z hz
    have hc1a : ContinuousAt (fun q : (Fin n → ℝ) × (ℝ × ℝ) => φ (G q.2)) (0, z) :=
      (continuousAt_extChartAt' hs).comp (f := fun q : (Fin n → ℝ) × (ℝ × ℝ) => G q.2)
        (hG.continuous.comp continuous_snd).continuousAt
    have hc1 : ContinuousAt (fun q : (Fin n → ℝ) × (ℝ × ℝ) => φ (G q.2) + q.1) (0, z) :=
      hc1a.add continuousAt_fst
    have hy : φ (G z) + 0 ∈ φ.target := by rw [add_zero]; exact φ.map_source hs
    have e1 : ∀ᶠ q in 𝓝 ((0 : Fin n → ℝ), z), φ (G q.2) + q.1 ∈ φ.target :=
      hc1.eventually_mem ((isOpen_extChartAt_target x₀).mem_nhds hy)
    have hc2 : ContinuousAt (fun q : (Fin n → ℝ) × (ℝ × ℝ) => (q.2, φ.symm (φ (G q.2) + q.1)))
        (0, z) :=
      continuousAt_snd.prodMk ((continuousAt_extChartAt_symm'' hy).comp
        (f := fun q : (Fin n → ℝ) × (ℝ × ℝ) => φ (G q.2) + q.1) hc1)
    have hval : ((z, φ.symm (φ (G z) + 0)) : (ℝ × ℝ) × M) ∈ 𝒪 := by
      rw [add_zero, φ.left_inv hs]; exact hgraph z
    have e2 := hc2.eventually_mem (h𝒪.mem_nhds hval)
    exact e1.and e2
  obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff.mp htube
  obtain ⟨ι, hι, U, g, hUo, hg, hTsub⟩ := hT
  have := hι
  let W : ι → Set ((Fin d → ℝ) × (ℝ × ℝ)) :=
    fun i => {p | p.1 ∈ U i ∧ g i p.1 ∈ φ.source ∧ G p.2 ∈ φ.source}
  let F : ι → (Fin d → ℝ) × (ℝ × ℝ) → (Fin n → ℝ) := fun i p => φ (g i p.1) - φ (G p.2)
  have h1le : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hFsm : ∀ i, ∀ p ∈ W i, ContDiffAt ℝ 1 (F i) p := by
    intro i p hp
    rw [← contMDiffAt_iff_contDiffAt]
    have h1 : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) I 1 (g i) p.1 :=
      (hg i).contMDiffAt ((hUo i).mem_nhds hp.1)
    have h2 : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) 1 φ (g i p.1) := by
      have := hp.2.1; rw [hφ, extChartAt_source] at this
      exact (contMDiffAt_extChartAt' (n := ∞) this).of_le h1le
    have h3 : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) 1 φ (G p.2) := by
      have := hp.2.2; rw [hφ, extChartAt_source] at this
      exact (contMDiffAt_extChartAt' (n := ∞) this).of_le h1le
    have hfst : ContMDiffAt 𝓘(ℝ, (Fin d → ℝ) × (ℝ × ℝ)) 𝓘(ℝ, Fin d → ℝ) 1
        (fun p : (Fin d → ℝ) × (ℝ × ℝ) => p.1) p := (contDiff_fst.contMDiff).contMDiffAt
    have hsnd : ContMDiffAt 𝓘(ℝ, (Fin d → ℝ) × (ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ) 1
        (fun p : (Fin d → ℝ) × (ℝ × ℝ) => p.2) p := (contDiff_snd.contMDiff).contMDiffAt
    have hGp : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 1 G p.2 := (hG p.2).of_le h1le
    exact (h2.comp p (h1.comp p hfst)).sub (h3.comp p (hGp.comp p hsnd))
  have hFdim : ∀ i, dimH (F i '' W i) ≤ ((d + 2 : ℕ) : ENNReal) := by
    intro i
    calc dimH (F i '' W i) ≤ dimH (W i) := by
          refine dimH_image_le_of_locally_lipschitzOn (fun p hp => ?_)
          obtain ⟨K, t, ht, hL⟩ := (hFsm i p hp).exists_lipschitzOnWith
          exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
      _ ≤ dimH (univ : Set ((Fin d → ℝ) × (ℝ × ℝ))) := dimH_mono (subset_univ _)
      _ = ((d + 2 : ℕ) : ENNReal) := by
          rw [Real.dimH_univ_eq_finrank, Module.finrank_prod, Module.finrank_fin_fun,
            Module.finrank_prod, Module.finrank_self]
  have hBlt : dimH (⋃ i, F i '' W i) < (Module.finrank ℝ (Fin n → ℝ) : ENNReal) := by
    rw [dimH_iUnion, Module.finrank_fin_fun]
    refine lt_of_le_of_lt (iSup_le hFdim) ?_
    exact_mod_cast hd
  obtain ⟨v, hvB, hv⟩ := (dense_compl_of_dimH_lt_finrank hBlt).exists_mem_open
    Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε0⟩
  have hvε : ‖v‖ < ε := by simpa using hv
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ × ℝ → ℝ, β = fun z => ∑ᶠ k : ℤ, b (z + ((k : ℝ), (0 : ℝ))) :=
    ⟨_, rfl⟩
  have hβ : ∀ z (k : ℤ), z + ((k : ℝ), (0 : ℝ)) ∈ N → β z = b (z + ((k : ℝ), (0 : ℝ))) := by
    intro z k hk
    rw [hβdef]
    refine finsum_eq_single _ k (fun j hj => ?_)
    by_contra hne
    exact hj (hdisjN z j k (hbsupp (subset_tsupport _ hne)) hk)
  have hβnorm : ∀ z (k : ℤ), z + ((k : ℝ), (0 : ℝ)) ∈ N → ‖β z • v‖ < ε := by
    intro z k hk
    rw [norm_smul, hβ z k hk, Real.norm_eq_abs, abs_of_nonneg (hb01 _).1]
    calc b (z + ((k : ℝ), (0 : ℝ))) * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right (hb01 _).2 (norm_nonneg _)
      _ < ε := by rw [one_mul]; exact hvε
  obtain ⟨G', hG'def⟩ : ∃ G' : ℝ × ℝ → M, G' = fun z =>
      if (∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ N) then φ.symm (φ (G z) + β z • v) else G z :=
    ⟨_, rfl⟩
  have hAo : IsOpen {w : ℝ × ℝ | ∀ k : ℤ, w + ((k : ℝ), (0 : ℝ)) ∉ tsupport b} := by
    have h := isOpen_periodic_imp (X := Unit) (τ := ((1 : ℝ), (0 : ℝ))) (by simp) hbK
      (isOpen_empty (X := Unit))
    have h2 := h.preimage (continuous_id.prodMk continuous_const :
      Continuous fun w : ℝ × ℝ => (w, ()))
    convert h2 using 1
    ext w
    simp [Prod.smul_mk]
  refine ⟨G', fun z => ?_, fun z => ?_, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩
  · by_cases h : ∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ N
    · obtain ⟨k, hk⟩ := h
      have hzs : G z ∈ φ.source := by rw [← hGk z k]; exact hsrc _ (subset_closure hk)
      have hy : φ (G z) + b (z + ((k : ℝ), (0 : ℝ))) • v ∈ φ.target := by
        have := (hε (by rw [dist_zero_right]; exact hβnorm z k hk) _ (subset_closure hk)).1
        rwa [hGk, hβ z k hk] at this
      have hev : G' =ᶠ[𝓝 z] fun w => φ.symm (φ (G w) + b (w + ((k : ℝ), (0 : ℝ))) • v) := by
        have hopen : IsOpen {w : ℝ × ℝ | w + ((k : ℝ), (0 : ℝ)) ∈ N} :=
          hN.preimage (continuous_id.add continuous_const)
        filter_upwards [hopen.mem_nhds hk] with w hw
        rw [hG'def]
        simp only
        rw [ite_eq_left ⟨k, hw⟩, hβ w k hw]
      refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
      have hin : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
          (fun w => φ (G w) + b (w + ((k : ℝ), (0 : ℝ))) • v) z := by
        have hφG : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (fun w => φ (G w)) z := by
          have hz' := hzs; rw [hφ, extChartAt_source] at hz'
          exact (contMDiffAt_extChartAt' (n := ∞) hz').comp z (hG z)
        have hbt : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
            (fun w => b (w + ((k : ℝ), (0 : ℝ)))) z :=
          (b.contMDiff.comp ((contDiff_id.add contDiff_const).contMDiff)).contMDiffAt
        exact hφG.add (hbt.smul contMDiffAt_const)
      exact ((contMDiffOn_extChartAt_symm x₀).contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds hy)).comp z hin
    · have hzA : z ∈ {w : ℝ × ℝ | ∀ k : ℤ, w + ((k : ℝ), (0 : ℝ)) ∉ tsupport b} :=
        fun k hk => h ⟨k, hbsupp hk⟩
      have hev : G' =ᶠ[𝓝 z] G := by
        filter_upwards [hAo.mem_nhds hzA] with w hw
        rw [hG'def]
        simp only
        split_ifs with hw'
        · obtain ⟨k, hk⟩ := hw'
          rw [hβ w k hk, image_eq_zero_of_notMem_tsupport (hw k), zero_smul, add_zero,
            φ.left_inv]
          rw [← hGk w k]; exact hsrc _ (subset_closure hk)
        · rfl
      exact (hG z).congr_of_eventuallyEq hev
  · rw [hG'def]
    simp only
    by_cases h : ∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ N
    · obtain ⟨k, hk⟩ := h
      have heq : z + ((1 : ℝ), (0 : ℝ)) + (((k - 1 : ℤ) : ℝ), (0 : ℝ)) =
          z + ((k : ℝ), (0 : ℝ)) := by
        ext <;> simp
      have hk' : z + ((1 : ℝ), (0 : ℝ)) + (((k - 1 : ℤ) : ℝ), (0 : ℝ)) ∈ N := by
        rw [heq]; exact hk
      rw [ite_eq_left ⟨_, hk'⟩, ite_eq_left ⟨k, hk⟩, hβ _ _ hk', hβ _ _ hk, heq, hper]
    · have h' : ¬ ∃ k : ℤ, z + ((1 : ℝ), (0 : ℝ)) + ((k : ℝ), (0 : ℝ)) ∈ N := by
        rintro ⟨k, hk⟩
        refine h ⟨k + 1, ?_⟩
        have heq : z + ((1 : ℝ), (0 : ℝ)) + ((k : ℝ), (0 : ℝ)) =
            z + ((((k + 1 : ℤ)) : ℝ), (0 : ℝ)) := by
          ext <;> simp; ring
        rwa [heq] at hk
      rw [ite_eq_right h, ite_eq_right h', hper]
  · rw [hG'def]
    simp only
    rw [ite_eq_right (fun ⟨k, hk⟩ => hz k hk)]
  · rw [hG'def]
    simp only
    split_ifs with h
    · obtain ⟨k, hk⟩ := h
      have := (hε (by rw [dist_zero_right]; exact hβnorm z k hk) _ (subset_closure hk)).2
      rw [hGk, h𝒪k] at this
      exact this
    · exact hgraph z
  · have hz0 : z + (((0 : ℤ) : ℝ), (0 : ℝ)) ∈ N := by
      rw [Int.cast_zero, Prod.mk_zero_zero, add_zero]; exact hCN hz
    rw [hG'def]
    simp only
    rw [ite_eq_left ⟨0, hz0⟩, hβ z 0 hz0]
    have hb1z : b (z + (((0 : ℤ) : ℝ), (0 : ℝ))) = 1 := by
      rw [Int.cast_zero, Prod.mk_zero_zero, add_zero]; exact hb1 hz
    rw [hb1z, one_smul]
    intro hmem
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hTsub hmem)
    obtain ⟨u, hu, hgu⟩ := hi
    have hzN : z ∈ closure N := subset_closure (hCN hz)
    have hy : φ (G z) + v ∈ φ.target :=
      (hε (by rw [dist_zero_right]; exact hvε) z hzN).1
    have hgus : g i u ∈ φ.source := by rw [hgu]; exact φ.map_target hy
    have hφg : φ (g i u) = φ (G z) + v := by rw [hgu]; exact φ.right_inv hy
    apply hvB
    refine mem_iUnion.mpr ⟨i, (u, z), ⟨hu, hgus, hsrc z hzN⟩, ?_⟩
    change φ (g i u) - φ (G z) = v
    rw [hφg]; abel

theorem exists_avoid_thin {G : ℝ → ℝ → M} (hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry G))
    (hper : ∀ θ s, G (θ + 1) s = G θ s) {T : Set M} (hTc : IsClosed T) {d : ℕ}
    (hT : isThin I d T) (hd : d + 2 < n) {P : Set (ℝ × ℝ)} (hP : IsClosed P)
    (hPper : ∀ θ s, (θ, s) ∈ P ↔ (θ + 1, s) ∈ P) (hPs : ∀ θ s, s ∉ Ioo (0 : ℝ) 1 → (θ, s) ∈ P)
    (hPT : ∀ θ s, (θ, s) ∈ P → G θ s ∉ T)
    {O : Set (M × M)} (hO : IsOpen O) (hdiag : ∀ x, (x, x) ∈ O) :
    ∃ G' : ℝ → ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry G') ∧
      (∀ θ s, G' (θ + 1) s = G' θ s) ∧ (∀ θ s, (θ, s) ∈ P → G' θ s = G θ s) ∧
      (∀ θ s, G' θ s ∉ T) ∧ ∀ θ s, (G θ s, G' θ s) ∈ O := by
  have hadd : ∀ (z : ℝ × ℝ) (a b : ℝ), z + (a, (0 : ℝ)) + (b, (0 : ℝ)) = z + (a + b, (0 : ℝ)) := by
    intro z a b
    ext <;> simp [add_assoc]
  have hshift : ∀ (S : Set (ℝ × ℝ)) (z : ℝ × ℝ),
      (∃ k : ℤ, z + ((1 : ℝ), (0 : ℝ)) + ((k : ℝ), (0 : ℝ)) ∈ S) ↔
        (∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ S) := by
    intro S z
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [hadd] at hk
      convert hk using 3
      push_cast
      ring
    · rintro ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      rw [hadd]
      convert hk using 3
      push_cast
      ring
  have hperZ : ∀ (p : ℝ × ℝ → Prop), (∀ z, p (z + ((1 : ℝ), (0 : ℝ))) ↔ p z) →
      ∀ (k : ℤ) (z : ℝ × ℝ), p (z + ((k : ℝ), (0 : ℝ))) ↔ p z := by
    intro p hp k
    refine Int.induction_on (motive := fun k : ℤ => ∀ z, p (z + ((k : ℝ), (0 : ℝ))) ↔ p z)
      k ?_ ?_ ?_
    · intro z
      simp only [Int.cast_zero, Prod.mk_zero_zero, add_zero]
    · intro i ih z
      have h1 := hadd z (i : ℝ) 1
      have ih' := ih z
      push_cast at ih' ⊢
      rw [← h1, hp, ih']
    · intro i ih z
      have h1 := hadd z (((-(i : ℤ) - 1 : ℤ)) : ℝ) 1
      rw [← hp, h1]
      have h2 : ((((-(i : ℤ) - 1 : ℤ)) : ℝ) + 1) = (((-(i : ℤ) : ℤ)) : ℝ) := by
        push_cast
        ring
      rw [h2]
      exact ih z
  have hfunZ : ∀ (g : ℝ × ℝ → M), (∀ z, g (z + ((1 : ℝ), (0 : ℝ))) = g z) →
      ∀ (k : ℤ) (z : ℝ × ℝ), g (z + ((k : ℝ), (0 : ℝ))) = g z := by
    intro g hg k z
    exact (hperZ (fun w => g w = g z) (fun w => by simp only [hg]) k z).2 rfl
  have hGc : Continuous (uncurry G) := hG.continuous
  have hGper1 : ∀ z : ℝ × ℝ, uncurry G (z + ((1 : ℝ), (0 : ℝ))) = uncurry G z := by
    rintro ⟨θ, s⟩
    simp [hper]
  have hP1 : ∀ z : ℝ × ℝ, z + ((1 : ℝ), (0 : ℝ)) ∈ P ↔ z ∈ P := by
    rintro ⟨θ, s⟩
    simp only [Prod.mk_add_mk, add_zero]
    exact (hPper θ s).symm
  have hPZ := hperZ (fun z => z ∈ P) hP1
  have hτ : ((1 : ℝ), (0 : ℝ)) ≠ 0 := fun h => by simpa using congrArg Prod.fst h
  have hsm : ∀ k : ℤ, (k : ℝ) • ((1 : ℝ), (0 : ℝ)) = ((k : ℝ), (0 : ℝ)) := by
    intro k
    ext <;> simp
  have hG0b : ∀ (K : Set (ℝ × ℝ)) (V : Set M), IsCompact K → IsOpen V →
      IsOpen {q : (ℝ × ℝ) × M | (∃ k : ℤ, q.1 + ((k : ℝ), (0 : ℝ)) ∈ K) → q.2 ∈ V} := by
    intro K V hK hV
    have := isOpen_periodic_imp (X := M) hτ hK hV
    simpa only [hsm] using this
  set K : Set (ℝ × ℝ) := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ uncurry G ⁻¹' T with hKdef
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right (hTc.preimage hGc)
  have hKP : K ⊆ Pᶜ := by
    rintro ⟨θ, s⟩ ⟨-, hz⟩ hzP
    exact hPT θ s hzP hz
  obtain ⟨m, C, N, x, hCc, hNo, hCN, hNc, hNW, hNG, hNdiam, -, hKcov⟩ :=
    exists_small_cells (F := uncurry G) hGc (fun y => (chartAt H y).source)
      (fun y => ⟨(chartAt H y).open_source, mem_chart_source H y⟩) hKc hP.isOpen_compl hKP
      (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨S1, hS1o, hS1⟩ : ∃ S : Set ((ℝ × ℝ) × M), IsOpen S ∧
      ∀ z y, (z, y) ∈ S ↔ (uncurry G z, y) ∈ O :=
    ⟨{q | (uncurry G q.1, q.2) ∈ O},
      hO.preimage ((hGc.comp continuous_fst).prodMk continuous_snd), fun _ _ => Iff.rfl⟩
  obtain ⟨S2, hS2o, hS2⟩ : ∃ S : Set ((ℝ × ℝ) × M), IsOpen S ∧
      ∀ z y, (z, y) ∈ S ↔
        (y ∈ T → ∃ (i : Fin m) (k : ℤ), z + ((k : ℝ), (0 : ℝ)) ∈ interior (C i)) := by
    refine ⟨(Prod.snd ⁻¹' Tᶜ) ∪ (Prod.fst ⁻¹'
      (⋃ (i : Fin m), ⋃ (k : ℤ), (fun z : ℝ × ℝ => z + ((k : ℝ), (0 : ℝ))) ⁻¹' interior (C i))),
      ?_, ?_⟩
    · refine (hTc.isOpen_compl.preimage continuous_snd).union ((isOpen_iUnion fun i =>
        isOpen_iUnion fun k => ?_).preimage continuous_fst)
      exact isOpen_interior.preimage (continuous_id.add continuous_const)
    · intro z y
      simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_iUnion]
      tauto
  obtain ⟨S3, hS3o, hS3⟩ : ∃ S : Set ((ℝ × ℝ) × M), IsOpen S ∧
      ∀ z y, (z, y) ∈ S ↔ ∀ i : Fin m,
        (∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ closure (N i)) → y ∈ (chartAt H (x i)).source := by
    refine ⟨⋂ i : Fin m, {q : (ℝ × ℝ) × M |
      (∃ k : ℤ, q.1 + ((k : ℝ), (0 : ℝ)) ∈ closure (N i)) → q.2 ∈ (chartAt H (x i)).source},
      isOpen_iInter_of_finite fun i => hG0b _ _ (hNc i) (chartAt H (x i)).open_source, ?_⟩
    intro z y
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  obtain ⟨S4, hS4o, hS4⟩ : ∃ S : ℕ → Set ((ℝ × ℝ) × M), (∀ j, IsOpen (S j)) ∧
      ∀ j z y, (z, y) ∈ S j ↔ ∀ i : Fin m, i.val < j →
        (∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ C i) → y ∉ T := by
    refine ⟨fun j => ⋂ i : Fin m, {q : (ℝ × ℝ) × M | i.val < j →
      (∃ k : ℤ, q.1 + ((k : ℝ), (0 : ℝ)) ∈ C i) → q.2 ∈ Tᶜ}, fun j => ?_, ?_⟩
    · refine isOpen_iInter_of_finite fun i => ?_
      by_cases hij : i.val < j
      · simp only [hij, true_imp_iff]
        exact hG0b _ _ (hCc i) hTc.isOpen_compl
      · simp only [hij, false_imp_iff, Set.ofPred_true]
        exact isOpen_univ
    · intro j z y
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_compl_iff]
  set 𝒪 : ℕ → Set ((ℝ × ℝ) × M) := fun j => S1 ∩ (S2 ∩ (S3 ∩ S4 j)) with h𝒪def
  have h𝒪 : ∀ j z y, (z, y) ∈ 𝒪 j ↔ ((uncurry G z, y) ∈ O ∧
      (y ∈ T → ∃ (i : Fin m) (k : ℤ), z + ((k : ℝ), (0 : ℝ)) ∈ interior (C i)) ∧
      (∀ i : Fin m,
        (∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ closure (N i)) → y ∈ (chartAt H (x i)).source) ∧
      ∀ i : Fin m, i.val < j → (∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ C i) → y ∉ T) := by
    intro j z y
    simp only [h𝒪def, Set.mem_inter_iff, hS1, hS2, hS3, hS4]
  have h𝒪open : ∀ j, IsOpen (𝒪 j) := fun j =>
    hS1o.inter (hS2o.inter (hS3o.inter (hS4o j)))
  have h𝒪per : ∀ j z y, (z, y) ∈ 𝒪 j ↔ (z + ((1 : ℝ), (0 : ℝ)), y) ∈ 𝒪 j := by
    intro j z y
    rw [h𝒪, h𝒪]
    simp only [hGper1, hshift]
  have key : ∀ j ≤ m, ∃ g : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ g ∧
      (∀ z, g (z + ((1 : ℝ), (0 : ℝ))) = g z) ∧ (∀ z ∈ P, g z = uncurry G z) ∧
      ∀ z, (z, g z) ∈ 𝒪 j := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨uncurry G, hG, hGper1, fun _ _ => rfl, fun z => ?_⟩
      rw [h𝒪]
      refine ⟨hdiag _, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      · intro hzT
        obtain ⟨θ, s⟩ := z
        have hs : s ∈ Ioo (0 : ℝ) 1 := by
          by_contra hs
          exact hPT θ s (hPs θ s hs) hzT
        have hmem : (θ, s) + (((-⌊θ⌋ : ℤ) : ℝ), (0 : ℝ)) ∈ K := by
          have he : (θ, s) + (((-⌊θ⌋ : ℤ) : ℝ), (0 : ℝ)) = (Int.fract θ, s) := by
            rw [← Int.self_sub_floor]
            ext <;> simp [sub_eq_add_neg]
          refine ⟨?_, ?_⟩
          · rw [he]
            exact ⟨⟨Int.fract_nonneg θ, (Int.fract_lt_one θ).le⟩, ⟨hs.1.le, hs.2.le⟩⟩
          · change uncurry G _ ∈ T
            rw [hfunZ _ hGper1]
            exact hzT
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKcov hmem)
        exact ⟨i, -⌊θ⌋, hi⟩
      · rintro i ⟨k, hk⟩
        rw [← hfunZ _ hGper1 k z]
        exact hNG i ⟨_, hk, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨g, hgs, hgper, hgP, hg𝒪⟩ := ih (by omega)
      set i : Fin m := ⟨j, by omega⟩ with hidef
      have hdisj : ∀ k : ℤ, k ≠ 0 → ∀ z ∈ closure (N i),
          z + ((k : ℝ), (0 : ℝ)) ∉ closure (N i) := by
        intro k hk z hz hz'
        have h1 := hNdiam i z hz _ hz'
        have h2 : ‖z - (z + ((k : ℝ), (0 : ℝ)))‖ = |(k : ℝ)| := by
          rw [sub_add_cancel_left, norm_neg, Prod.norm_mk]
          simp
        have h3 : (1 : ℝ) ≤ |(k : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hk
        linarith
      have hNx : g '' closure (N i) ⊆ (chartAt H (x i)).source := by
        rintro _ ⟨w, hw, rfl⟩
        exact ((h𝒪 j w (g w)).1 (hg𝒪 w)).2.2.1 i ⟨0, by rw [Int.cast_zero, Prod.mk_zero_zero, add_zero]; exact hw⟩
      obtain ⟨g', hg's, hg'per, hg'fix, hg'𝒪, hg'C⟩ :=
        exists_avoid_cell_step hgs hgper hT hd (hCc i) (hNo i) (hCN i) (hNc i) hdisj hNx
          (h𝒪open j) (h𝒪per j) hg𝒪
      refine ⟨g', hg's, hg'per, ?_, ?_⟩
      · intro z hz
        rw [hg'fix z ?_]
        · exact hgP z hz
        · intro k hk
          exact hNW i (subset_closure hk) ((hPZ k z).2 hz)
      · intro z
        obtain ⟨h1, h2, h3, h4⟩ := (h𝒪 j z (g' z)).1 (hg'𝒪 z)
        rw [h𝒪]
        refine ⟨h1, h2, h3, fun i' hi' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | heq
        · exact h4 i' hlt
        · have hii : i' = i := Fin.ext heq
          rintro ⟨k, hk⟩
          rw [hii] at hk
          rw [← hfunZ _ hg'per k z]
          exact hg'C _ hk
  obtain ⟨g, hgs, hgper, hgP, hg𝒪⟩ := key m le_rfl
  refine ⟨fun θ s => g (θ, s), hgs, ?_, fun θ s h => hgP _ h, ?_, ?_⟩
  · intro θ s
    have := hgper (θ, s)
    simpa only [Prod.mk_add_mk, add_zero] using this
  · intro θ s hT'
    obtain ⟨-, h2, -, h4⟩ := (h𝒪 m (θ, s) (g (θ, s))).1 (hg𝒪 (θ, s))
    obtain ⟨i, k, hk⟩ := h2 hT'
    exact h4 i i.isLt ⟨k, interior_subset hk⟩ hT'
  · intro θ s
    exact ((h𝒪 m (θ, s) (g (θ, s))).1 (hg𝒪 (θ, s))).1

theorem exists_periodic_closed_nhds {P U : Set (ℝ × ℝ)} (hP : IsClosed P) (hU : IsOpen U)
    (hPU : P ⊆ U) (hPper : ∀ θ s, (θ, s) ∈ P ↔ (θ + 1, s) ∈ P)
    (hUper : ∀ θ s, (θ, s) ∈ U ↔ (θ + 1, s) ∈ U) :
    ∃ Q : Set (ℝ × ℝ), IsClosed Q ∧ (∀ θ s, (θ, s) ∈ Q ↔ (θ + 1, s) ∈ Q) ∧ Q ⊆ U ∧
      Q ⊆ (univ : Set ℝ) ×ˢ Icc (-1 : ℝ) 2 ∧
      P ∩ (univ : Set ℝ) ×ˢ Icc (-(1 / 2) : ℝ) (3 / 2) ⊆ interior Q ∧
      IsCompact (Q ∩ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  have hint : ∀ A : Set (ℝ × ℝ), (∀ θ s, (θ, s) ∈ A ↔ (θ + 1, s) ∈ A) →
      ∀ k : ℤ, ∀ θ s, (θ, s) ∈ A ↔ (θ + (k : ℝ), s) ∈ A := by
    intro A hA k
    induction k using Int.induction_on with
    | zero => intro θ s; simp
    | succ i ih =>
      intro θ s
      have he : θ + ((i : ℤ) : ℝ) + 1 = θ + (((i : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [ih θ s, hA (θ + ((i : ℤ) : ℝ)) s, he]
    | pred i ih =>
      intro θ s
      have he : θ + ((-(i : ℤ) - 1 : ℤ) : ℝ) + 1 = θ + ((-(i : ℤ) : ℤ) : ℝ) := by push_cast; ring
      rw [ih θ s, ← he, ← hA (θ + ((-(i : ℤ) - 1 : ℤ) : ℝ)) s]
  set P₀ : Set (ℝ × ℝ) := P ∩ (univ : Set ℝ) ×ˢ Icc (-(1 / 2) : ℝ) (3 / 2) with hP₀
  set K : Set (ℝ × ℝ) := P ∩ Icc (0 : ℝ) 1 ×ˢ Icc (-(1 / 2) : ℝ) (3 / 2) with hK
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_left hP
  have hKU : K ⊆ U := fun z hz => hPU hz.1
  obtain ⟨δ, hδ, hδU⟩ := hKc.exists_cthickening_subset_open hU hKU
  have hP₀per : ∀ θ s, (θ, s) ∈ P₀ ↔ (θ + 1, s) ∈ P₀ := by
    intro θ s
    simp only [hP₀, mem_inter_iff, mem_prod, mem_univ, true_and]
    rw [hPper θ s]
  have himg : (fun x : ℝ × ℝ => x + ((1 : ℝ), (0 : ℝ))) '' P₀ = P₀ := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨⟨c, d⟩, h, hcd⟩
      simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq] at hcd
      obtain ⟨rfl, rfl⟩ := hcd
      exact (hP₀per c d).1 h
    · intro h
      refine ⟨(a - 1, b), ?_, ?_⟩
      · rw [hP₀per (a - 1) b, sub_add_cancel]; exact h
      · simp
  have hcper : ∀ θ s, (θ, s) ∈ Metric.cthickening (δ / 2) P₀ ↔
      (θ + 1, s) ∈ Metric.cthickening (δ / 2) P₀ := by
    intro θ s
    have hiso : Isometry (fun x : ℝ × ℝ => x + ((1 : ℝ), (0 : ℝ))) :=
      isometry_add_right _
    have h1 := Metric.infEDist_image (x := (θ, s)) (t := P₀) hiso
    rw [himg] at h1
    simp only [Prod.mk_add_mk, add_zero] at h1
    rw [Metric.mem_cthickening_iff, Metric.mem_cthickening_iff, h1]
  refine ⟨Metric.cthickening (δ / 2) P₀ ∩ (univ : Set ℝ) ×ˢ Icc (-1 : ℝ) 2,
    Metric.isClosed_cthickening.inter (isClosed_univ.prod isClosed_Icc), ?_, ?_, ?_, ?_, ?_⟩
  · intro θ s
    simp only [mem_inter_iff, mem_prod, mem_univ, true_and]
    rw [hcper θ s]
  · rintro ⟨z1, z2⟩ ⟨hz, -⟩
    have hz' := Metric.cthickening_subset_thickening' hδ (half_lt_self hδ) P₀ hz
    obtain ⟨⟨θ, s⟩, hp, hd⟩ := Metric.mem_thickening_iff.1 hz'
    have hpP : (θ - (⌊θ⌋ : ℝ), s) ∈ P := by
      rw [hint P hPper ⌊θ⌋ (θ - (⌊θ⌋ : ℝ)) s, sub_add_cancel]; exact hp.1
    have hpK : (θ - (⌊θ⌋ : ℝ), s) ∈ K := by
      refine ⟨hpP, ⟨?_, ?_⟩, hp.2.2⟩
      · linarith [Int.floor_le θ]
      · linarith [Int.lt_floor_add_one θ]
    have hdist : dist (z1 - (⌊θ⌋ : ℝ), z2) (θ - (⌊θ⌋ : ℝ), s) ≤ δ := by
      rw [Prod.dist_eq, dist_sub_right]
      rw [Prod.dist_eq] at hd
      exact hd.le
    have hzU : (z1 - (⌊θ⌋ : ℝ), z2) ∈ U :=
      hδU (Metric.mem_cthickening_of_dist_le _ _ _ _ hpK hdist)
    rw [hint U hUper ⌊θ⌋ (z1 - (⌊θ⌋ : ℝ)) z2, sub_add_cancel] at hzU
    exact hzU
  · exact inter_subset_right
  · intro p hp
    rw [mem_interior]
    refine ⟨Metric.ball p (δ / 2) ∩ (univ : Set ℝ) ×ˢ Ioo (-1 : ℝ) 2, ?_,
      Metric.isOpen_ball.inter (isOpen_univ.prod isOpen_Ioo), ?_⟩
    · rintro x ⟨hx1, hx2⟩
      refine ⟨Metric.mem_cthickening_of_dist_le x p _ _ hp (Metric.mem_ball.1 hx1).le, ?_⟩
      exact ⟨mem_univ _, Ioo_subset_Icc_self hx2.2⟩
    · refine ⟨Metric.mem_ball_self (half_pos hδ), mem_univ _, ?_, ?_⟩
      · linarith [hp.2.2.1]
      · linarith [hp.2.2.2]
  · refine ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
      (isCompact_Icc (a := (-1 : ℝ)) (b := 2))).of_isClosed_subset
      ((Metric.isClosed_cthickening.inter (isClosed_univ.prod isClosed_Icc)).inter
        (isClosed_Icc.prod isClosed_univ)) ?_
    rintro ⟨a, b⟩ ⟨⟨-, -, hb⟩, ha, -⟩
    exact ⟨ha, hb⟩

theorem eventually_locallyInjective {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Hf : ℝ × ℝ → P → M}
    (hH : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × P) I ∞ (fun q : (ℝ × ℝ) × P => Hf q.1 q.2))
    (hper : ∀ θ s w, Hf (θ + 1, s) w = Hf (θ, s) w) {Q : Set (ℝ × ℝ)}
    (hQper : ∀ θ s, (θ, s) ∈ Q ↔ (θ + 1, s) ∈ Q)
    (hQb : IsCompact (Q ∩ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)))
    (himm : ∀ z ∈ Q, mfderiv 𝓘(ℝ, ℝ) I (fun θ => Hf (θ, z.2) 0) z.1 (1 : ℝ) ≠ 0) :
    ∃ r > 0, ∃ δ > 0, ∀ w : P, ‖w‖ < r → ∀ z ∈ Q,
      mfderiv 𝓘(ℝ, ℝ) I (fun θ => Hf (θ, z.2) w) z.1 (1 : ℝ) ≠ 0 ∧
      ∀ θ', |θ' - z.1| < δ → Hf (θ', z.2) w = Hf z w → θ' = z.1 := by
  classical
  have _hB : I.Boundaryless := inferInstance
  have _hT : T2Space M := inferInstance
  have hgd : ∀ (s : ℝ) (w : P) (θ : ℝ),
      MDifferentiableAt 𝓘(ℝ, ℝ) I (fun θ => Hf (θ, s) w) θ := by
    intro s w θ
    have h1 : MDifferentiableAt 𝓘(ℝ, (ℝ × ℝ) × P) I (fun q : (ℝ × ℝ) × P => Hf q.1 q.2)
        ((θ, s), w) := (hH.mdifferentiable (by simp)) _
    have h2 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, (ℝ × ℝ) × P)
        (fun θ : ℝ => (((θ, s), w) : (ℝ × ℝ) × P)) θ :=
      mdifferentiableAt_iff_differentiableAt.2 (by fun_prop)
    exact h1.comp θ h2
  have hper' : ∀ (θ s : ℝ) (w : P) (m : ℤ), Hf (θ - m, s) w = Hf (θ, s) w := by
    intro θ s w m
    have hp : Function.Periodic (fun θ : ℝ => Hf (θ, s) w) 1 := fun θ => hper θ s w
    simpa using hp.sub_int_mul_eq (x := θ) m
  have hQper' : ∀ (θ s : ℝ) (m : ℤ), (θ - m, s) ∈ Q ↔ (θ, s) ∈ Q := by
    intro θ s m
    have hp : Function.Periodic (fun θ : ℝ => (θ, s) ∈ Q) 1 :=
      fun θ => propext (hQper θ s).symm
    exact Iff.of_eq (by simpa using hp.sub_int_mul_eq (x := θ) m)
  let Good : (P × ℝ) → (ℝ × ℝ) → Prop := fun y z =>
    0 < y.2 → (mfderiv 𝓘(ℝ, ℝ) I (fun θ => Hf (θ, z.2) y.1) z.1 (1 : ℝ) ≠ 0 ∧
      ∀ θ', |θ' - z.1| < y.2 → Hf (θ', z.2) y.1 = Hf z y.1 → θ' = z.1)
  have hloc : ∀ z₀ ∈ Q ∩ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
      ∀ᶠ p : (P × ℝ) × (ℝ × ℝ) in 𝓝 ((0, 0), z₀), Good p.1 p.2 := by
    intro z₀ hz₀
    have hz₀Q : z₀ ∈ Q := hz₀.1
    set F : (ℝ × ℝ) × P → M := fun q => Hf q.1 q.2 with hFdef
    set q₀ : (ℝ × ℝ) × P := (z₀, 0) with hq₀
    set x₀ : M := F q₀ with hx₀
    have hFc : Continuous F := hH.continuous
    set V : Set ((ℝ × ℝ) × P) := F ⁻¹' (chartAt H x₀).source with hV
    have hVo : IsOpen V := (chartAt H x₀).open_source.preimage hFc
    have hq₀V : q₀ ∈ V := mem_chart_source H x₀
    set G : (ℝ × ℝ) × P → (Fin n → ℝ) := fun q => extChartAt I x₀ (F q) with hGdef
    have hG : ContDiffOn ℝ ∞ G V := by
      have := (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x₀)).comp hH.contMDiffOn
        (fun q hq => hq)
      exact this.contDiffOn
    set D := fderiv ℝ G with hD
    have hDc : ContinuousOn D V := hG.continuousOn_fderiv_of_isOpen hVo (by simp)
    have hGd : ∀ q ∈ V, HasFDerivAt G (D q) q := fun q hq =>
      ((hG.differentiableOn (by simp)).differentiableAt (hVo.mem_nhds hq)).hasFDerivAt
    set e : (ℝ × ℝ) × P := ((1, 0), 0) with he
    have hθ : ∀ q ∈ V, HasDerivAt (fun θ : ℝ => G ((θ, q.1.2), q.2)) (D q e) q.1.1 := by
      intro q hq
      have hl : HasDerivAt (fun θ : ℝ => (((θ, q.1.2), q.2) : (ℝ × ℝ) × P)) e q.1.1 :=
        ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _)).prodMk (hasDerivAt_const _ _)
      exact (hGd q hq).comp_hasDerivAt q.1.1 hl
    have hu₀ : D q₀ e ≠ 0 := by
      intro h0
      apply himm z₀ hz₀Q
      have h1 := (hgd z₀.2 0 z₀.1).hasMFDerivAt
      have h2 := h1.2
      simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
        PartialEquiv.refl_coe, CompTriple.comp_eq, modelWithCornersSelf_coe, range_id,
        hasFDerivWithinAt_univ, id] at h2
      have h4 := (hθ q₀ hq₀V).hasFDerivAt
      have h5 := h2.unique h4
      have h6 : (ContinuousLinearMap.toSpanSingleton ℝ (D q₀ e)) (1 : ℝ) = D q₀ e := by
        simp
      rw [← h5] at h6
      exact h6.trans h0
    obtain ⟨i, hi⟩ : ∃ i, D q₀ e i ≠ 0 := Function.ne_iff.1 hu₀
    have hkc : ContinuousAt (fun q => D q e i * D q₀ e i) q₀ := by
      have hDq : ContinuousAt D q₀ := hDc.continuousAt (hVo.mem_nhds hq₀V)
      have hDe : ContinuousAt (fun q => D q e) q₀ := hDq.clm_apply continuousAt_const
      exact ((continuous_apply i).continuousAt.comp hDe).mul continuousAt_const
    have hkpos : ∀ᶠ q in 𝓝 q₀, 0 < D q e i * D q₀ e i :=
      hkc.eventually (lt_mem_nhds (mul_self_pos.2 hi))
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 (hkpos.and (hVo.mem_nhds hq₀V))
    have hballmem : ∀ (t s : ℝ) (w : P), |t - z₀.1| < ε → |s - z₀.2| < ε → ‖w‖ < ε →
        (((t, s), w) : (ℝ × ℝ) × P) ∈ Metric.ball q₀ ε := by
      intro t s w h1 h2 h3
      rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq]
      simp only [hq₀, Real.dist_eq, dist_zero_right]
      exact max_lt (max_lt h1 h2) h3
    rw [Metric.eventually_nhds_iff]
    refine ⟨ε / 2, by positivity, ?_⟩
    rintro ⟨⟨w, δ⟩, ⟨t, s⟩⟩ hp hδ
    have hp' : max (max ‖w‖ |δ|) (max |t - z₀.1| |s - z₀.2|) < ε / 2 := by
      simpa [Prod.dist_eq, Real.dist_eq] using hp
    simp only [max_lt_iff] at hp'
    obtain ⟨⟨hw, hδ'⟩, ht, hs⟩ := hp'
    simp only at hδ ⊢
    have hmono : StrictMonoOn (fun θ => G ((θ, s), w) i * D q₀ e i) (Metric.ball z₀.1 ε) := by
      have hmem : ∀ θ ∈ Metric.ball z₀.1 ε, (((θ, s), w) : (ℝ × ℝ) × P) ∈
          {x | 0 < D x e i * D q₀ e i} ∩ V := by
        intro θ hθb
        rw [Metric.mem_ball, Real.dist_eq] at hθb
        exact hεs (hballmem θ s w hθb (by linarith) (by linarith))
      apply strictMonoOn_of_deriv_pos (convex_ball _ _)
      · intro θ hθb
        exact ((hasDerivAt_pi.1 (hθ _ (hmem θ hθb).2) i).mul_const _).continuousAt.continuousWithinAt
      · intro θ hθb
        rw [Metric.isOpen_ball.interior_eq] at hθb
        rw [((hasDerivAt_pi.1 (hθ _ (hmem θ hθb).2) i).mul_const _).deriv]
        exact (hmem θ hθb).1
    refine ⟨?_, ?_⟩
    · have hq : (((t, s), w) : (ℝ × ℝ) × P) ∈ Metric.ball q₀ ε :=
        hballmem t s w (by linarith) (by linarith) (by linarith)
      obtain ⟨hk, hqV⟩ := hεs hq
      intro h0
      have hφ : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) (Hf (t, s) w) :=
        mdifferentiableAt_extChartAt hqV
      have hc := mfderiv_comp t hφ (hgd s w t)
      have hcf : fderiv ℝ (⇑(extChartAt I x₀) ∘ fun θ => Hf (θ, s) w) t =
          (mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) (Hf (t, s) w)).comp
            (mfderiv 𝓘(ℝ, ℝ) I (fun θ => Hf (θ, s) w) t) := by
        rw [mfderiv_eq_fderiv] at hc
        apply ContinuousLinearMap.ext
        intro v
        exact DFunLike.congr_fun hc v
      have h4 := (hθ ((t, s), w) hqV).hasFDerivAt
      have h5 : fderiv ℝ (⇑(extChartAt I x₀) ∘ fun θ => Hf (θ, s) w) t =
          ContinuousLinearMap.toSpanSingleton ℝ (D ((t, s), w) e) := h4.fderiv
      have h7 : (ContinuousLinearMap.toSpanSingleton ℝ (D ((t, s), w) e)) (1 : ℝ) =
          D ((t, s), w) e := by simp
      rw [← h5, hcf] at h7
      have h8 : D ((t, s), w) e = 0 := by
        rw [← h7]
        change (mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) (Hf (t, s) w))
          ((mfderiv 𝓘(ℝ, ℝ) I (fun θ => Hf (θ, s) w) t) (1 : ℝ)) = 0
        rw [h0, map_zero]
      simp only [h8] at hk
      simp at hk
    · intro θ' hθ'lt heq
      have hθ'b : θ' ∈ Metric.ball z₀.1 ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        rw [abs_lt] at hθ'lt ht hδ' ⊢
        constructor <;> linarith
      have htb : t ∈ Metric.ball z₀.1 ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        linarith
      apply hmono.injOn hθ'b htb
      change extChartAt I x₀ (Hf (θ', s) w) i * D q₀ e i =
        extChartAt I x₀ (Hf (t, s) w) i * D q₀ e i
      rw [heq]
  have hunif := hQb.eventually_forall_of_forall_eventually hloc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hunif
  refine ⟨ε / 2, by positivity, ε / 2, by positivity, ?_⟩
  intro w hw z hz
  have hy : dist ((w, ε / 2) : P × ℝ) 0 < ε := by
    rw [Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, dist_zero_right]
    rw [Real.norm_of_nonneg (by positivity)]
    exact max_lt (by linarith) (by linarith)
  set k : ℤ := ⌊z.1⌋ with hk
  have hz' : ((z.1 - k, z.2) : ℝ × ℝ) ∈ Q ∩ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    refine ⟨(hQper' z.1 z.2 k).2 hz, ?_, trivial⟩
    rw [hk, Int.self_sub_floor]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  obtain ⟨ha, hb⟩ := hball hy _ hz' (by positivity)
  simp only at ha hb
  refine ⟨?_, ?_⟩
  · have hfun : (fun θ => Hf (θ, z.2) w) = (fun θ => Hf (θ, z.2) w) ∘ (fun θ : ℝ => θ - k) := by
      funext θ
      simp only [Function.comp_apply]
      exact (hper' θ z.2 w k).symm
    have h1 := (hgd z.2 w (z.1 - k)).hasMFDerivAt
    have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun θ : ℝ => θ - k) z.1
        (ContinuousLinearMap.id ℝ ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id _).sub_const _)
    have h3 := h1.comp z.1 h2
    rw [← hfun] at h3
    rw [h3.mfderiv]
    exact ha
  · intro θ' hθ' heq
    have := hb (θ' - k) (by rw [show θ' - k - (z.1 - k) = θ' - z.1 by ring]; exact hθ') (by
      rw [hper', hper']
      exact heq)
    linarith

theorem eventually_isEmbeddedOn {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Hf : ℝ × ℝ → P → M}
    (hH : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × P) I ∞ (fun q : (ℝ × ℝ) × P => Hf q.1 q.2))
    (hper : ∀ θ s w, Hf (θ + 1, s) w = Hf (θ, s) w) {Q : Set (ℝ × ℝ)} (hQ : IsClosed Q)
    (hQper : ∀ θ s, (θ, s) ∈ Q ↔ (θ + 1, s) ∈ Q)
    (hQb : IsCompact (Q ∩ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)))
    (hemb : isEmbeddedOn I (fun θ s => Hf (θ, s) 0) Q) :
    ∀ᶠ w in 𝓝 (0 : P), isEmbeddedOn I (fun θ s => Hf (θ, s) w) Q := by
  obtain ⟨r, hr, δ, hδ, hloc⟩ := eventually_locallyInjective hH hper hQper hQb hemb.1
  have hcont : Continuous (fun q : (ℝ × ℝ) × P => Hf q.1 q.2) := hH.continuous
  have hQk : ∀ (k : ℤ) (θ s : ℝ), ((θ + k, s) ∈ Q ↔ (θ, s) ∈ Q) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro θ s; simp
    | succ i ih =>
      intro θ s
      rw [show θ + (((i : ℤ) + 1 : ℤ) : ℝ) = (θ + ((i : ℤ) : ℝ)) + 1 by push_cast; ring,
        ← hQper, ih]
    | pred i ih =>
      intro θ s
      rw [hQper, show θ + ((-(i : ℤ) - 1 : ℤ) : ℝ) + 1 = θ + ((-(i : ℤ) : ℤ) : ℝ) by
        push_cast; ring, ih]
  have hHk : ∀ (k : ℤ) (θ s : ℝ) (w : P), Hf (θ + k, s) w = Hf (θ, s) w := by
    intro k
    induction k using Int.induction_on with
    | zero => intro θ s w; simp
    | succ i ih =>
      intro θ s w
      rw [show θ + (((i : ℤ) + 1 : ℤ) : ℝ) = (θ + ((i : ℤ) : ℝ)) + 1 by push_cast; ring,
        hper, ih]
    | pred i ih =>
      intro θ s w
      rw [← hper, show θ + ((-(i : ℤ) - 1 : ℤ) : ℝ) + 1 = θ + ((-(i : ℤ) : ℤ) : ℝ) by
        push_cast; ring, ih]
  set K : Set ((ℝ × ℝ) × ℝ) :=
    ((Q ∩ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ×ˢ Icc δ (1 - δ)) ∩
      {y | (y.1.1 + y.2, y.1.2) ∈ Q} with hKdef
  have hKc : IsCompact K := by
    refine (hQb.prod isCompact_Icc).inter_right ?_
    exact hQ.preimage (by fun_prop)
  have hev : ∀ᶠ w in 𝓝 (0 : P), ∀ y ∈ K, Hf y.1 w ≠ Hf (y.1.1 + y.2, y.1.2) w := by
    apply hKc.eventually_forall_of_forall_eventually
    intro y hy
    have hopen : IsOpen {z : P × ((ℝ × ℝ) × ℝ) |
        Hf z.2.1 z.1 ≠ Hf (z.2.1.1 + z.2.2, z.2.1.2) z.1} :=
      isOpen_ne_fun
        (hcont.comp (f := fun z : P × ((ℝ × ℝ) × ℝ) => (z.2.1, z.1)) (by fun_prop))
        (hcont.comp (f := fun z : P × ((ℝ × ℝ) × ℝ) => ((z.2.1.1 + z.2.2, z.2.1.2), z.1))
          (by fun_prop))
    apply hopen.mem_nhds
    intro heq
    obtain ⟨k, hk⟩ := hemb.2 y.1.1 (y.1.1 + y.2) y.1.2 hy.1.1.1 hy.2 heq
    have hy2 := hy.1.2
    have h1 : (0 : ℝ) < k := by rw [mem_Icc] at hy2; linarith
    have h2 : (k : ℝ) < 1 := by rw [mem_Icc] at hy2; linarith
    have h1' : (0 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < 1 := by exact_mod_cast h2
    omega
  filter_upwards [hev, Metric.ball_mem_nhds (0 : P) hr] with w hw hwr
  have hwr' : ‖w‖ < r := by simpa using hwr
  refine ⟨fun z hz => (hloc w hwr' z hz).1, ?_⟩
  intro θ θ' s hθ hθ' heq
  by_contra hne
  push Not at hne
  set d := Int.fract (θ' - θ) with hd
  set θ₀ := Int.fract θ with hθ₀def
  have hθeq : θ = θ₀ + ((⌊θ⌋ : ℤ) : ℝ) := by rw [hθ₀def, Int.fract]; ring
  have hθ'eq : θ' = (θ₀ + d) + ((⌊θ⌋ + ⌊θ' - θ⌋ : ℤ) : ℝ) := by
    rw [hθ₀def, hd, Int.fract, Int.fract]; push_cast; ring
  have hQ₀ : (θ₀, s) ∈ Q := by rw [← hQk ⌊θ⌋, ← hθeq]; exact hθ
  have hQ₀' : (θ₀ + d, s) ∈ Q := by rw [← hQk (⌊θ⌋ + ⌊θ' - θ⌋), ← hθ'eq]; exact hθ'
  have heq₀ : Hf (θ₀, s) w = Hf (θ₀ + d, s) w := by
    have e1 := hHk ⌊θ⌋ θ₀ s w
    have e2 := hHk (⌊θ⌋ + ⌊θ' - θ⌋) (θ₀ + d) s w
    rw [← hθeq] at e1
    rw [← hθ'eq] at e2
    rw [← e1, ← e2]; exact heq
  have hd0 : 0 ≤ d := Int.fract_nonneg _
  have hd1 : d < 1 := Int.fract_lt_one _
  have hθ₀0 : 0 ≤ θ₀ := Int.fract_nonneg _
  have hθ₀1 : θ₀ < 1 := Int.fract_lt_one _
  have hdne : d ≠ 0 := by
    intro hd0'
    apply hne ⌊θ' - θ⌋
    have : θ' - θ - ⌊θ' - θ⌋ = 0 := by rw [← Int.fract]; exact hd0'
    linarith
  by_cases hsmall : d < δ
  · have := (hloc w hwr' (θ₀, s) hQ₀).2 (θ₀ + d)
      (by simp only; rw [add_sub_cancel_left, abs_of_nonneg hd0]; exact hsmall) heq₀.symm
    exact hdne (by simpa using this)
  by_cases hbig : 1 - δ < d
  · have e1 : Hf (θ₀ + 1, s) w = Hf (θ₀ + d, s) w := by rw [hper]; exact heq₀
    have := (hloc w hwr' (θ₀ + d, s) hQ₀').2 (θ₀ + 1)
      (by simp only; rw [abs_lt]; constructor <;> linarith) e1
    have : d = 1 := by linarith
    linarith
  push Not at hsmall hbig
  apply hw ((θ₀, s), d) ⟨⟨⟨hQ₀, ⟨hθ₀0, hθ₀1.le⟩, mem_univ _⟩, ⟨hsmall, hbig⟩⟩, hQ₀'⟩
  exact heq₀

theorem exists_level_perturbation_family (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    {h : ℝ → ℝ → M} (hsm : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry h))
    (hper : ∀ θ s, h (θ + 1) s = h θ s) (hlev : ∀ θ s, f (h θ s) = c)
    (ψ : OpenPartialHomeomorph (Fin n → ℝ) M) (i₀ : Fin n)
    (hψ : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source)
    (hψs : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target)
    (hψf : ∀ y ∈ ψ.source, f (ψ y) = c + y i₀)
    {C N : Set (ℝ × ℝ)} (hC : IsCompact C) (hN : IsOpen N) (hCN : C ⊆ N)
    (hNc : IsCompact (closure N))
    (hNθ : ∀ z ∈ closure N, ∀ z' ∈ closure N, |z.1 - z'.1| < 1 / 2)
    (hNψ : ∀ z ∈ closure N, h z.1 z.2 ∈ ψ.target)
    {𝒪 : Set ((ℝ × ℝ) × M)} (h𝒪 : IsOpen 𝒪)
    (h𝒪per : ∀ z y, (z, y) ∈ 𝒪 ↔ (z + ((1 : ℝ), (0 : ℝ)), y) ∈ 𝒪)
    (hgraph : ∀ z : ℝ × ℝ, (z, h z.1 z.2) ∈ 𝒪) :
    ∃ (Hf : ℝ × ℝ → (Fin n → ℝ) × (Fin n → ℝ) → M) (β τ : ℝ × ℝ → ℝ) (A : Set (ℝ × ℝ))
      (r : ℝ), 0 < r ∧
      ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))) I ∞
        (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => Hf q.1 q.2) ∧
      (∀ θ s w, Hf (θ + 1, s) w = Hf (θ, s) w) ∧ (∀ z, Hf z 0 = h z.1 z.2) ∧
      (∀ z w, f (Hf z w) = c) ∧
      (∀ z w, (∀ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∉ N) → Hf z w = h z.1 z.2) ∧
      (∀ w : (Fin n → ℝ) × (Fin n → ℝ), ‖w‖ < r → ∀ z, (z, Hf z w) ∈ 𝒪) ∧
      (∀ w : (Fin n → ℝ) × (Fin n → ℝ), ‖w‖ < r → ∀ z, h z.1 z.2 ∈ ψ.target →
        Hf z w ∈ ψ.target ∧
        ψ.symm (Hf z w) = ψ.symm (h z.1 z.2) +
          β z • ((w.1 - w.1 i₀ • Pi.single i₀ (1 : ℝ)) +
            τ z • (w.2 - w.2 i₀ • Pi.single i₀ (1 : ℝ)))) ∧
      ContDiff ℝ ∞ β ∧ ContDiff ℝ ∞ τ ∧
      IsOpen A ∧ C ⊆ A ∧ A ⊆ N ∧ EqOn β 1 A ∧
      (∀ z ∈ A, deriv (fun θ => τ (θ, z.2)) z.1 ≠ 0) ∧
      (∀ z ∈ A, ∀ z' : ℝ × ℝ, β z' = 1 → τ z' = τ z → ∃ k : ℤ, z'.1 = z.1 + k) := by
  classical
  have _hf := hf
  have _i₁ : IsManifold I ∞ M := inferInstance
  have _i₂ : T2Space M := inferInstance
  have _i₃ : I.Boundaryless := inferInstance
  have hshift : ∀ P : ℝ × ℝ → Prop, (∀ z, P z ↔ P (z + ((1 : ℝ), (0 : ℝ)))) →
      ∀ (k : ℤ) (z : ℝ × ℝ), P z ↔ P (z + ((k : ℝ), (0 : ℝ))) := by
    intro P hP k
    induction k using Int.induction_on with
    | zero => intro z; rw [Int.cast_zero, Prod.mk_zero_zero, add_zero]
    | succ i ih =>
      intro z
      rw [ih z, hP]
      have e : z + (((i : ℤ) : ℝ), (0 : ℝ)) + ((1 : ℝ), (0 : ℝ)) =
          z + ((((i : ℤ) + 1 : ℤ) : ℝ), (0 : ℝ)) := by
        ext <;> simp [add_assoc]
      rw [e]
    | pred i ih =>
      intro z
      rw [ih z, hP (z + (((-(i : ℤ) - 1 : ℤ) : ℝ), (0 : ℝ)))]
      have e : z + (((-(i : ℤ) - 1 : ℤ) : ℝ), (0 : ℝ)) + ((1 : ℝ), (0 : ℝ)) =
          z + (((-(i : ℤ) : ℤ) : ℝ), (0 : ℝ)) := by
        ext <;> simp
        ring
      rw [e]
  have hh_int : ∀ (k : ℤ) (z : ℝ × ℝ),
      h (z + ((k : ℝ), (0 : ℝ))).1 (z + ((k : ℝ), (0 : ℝ))).2 = h z.1 z.2 := by
    intro k z
    exact ((hshift (fun x => h x.1 x.2 = h z.1 z.2) (fun x => by simp [hper]) k z).mp rfl)
  obtain ⟨θC, hθC⟩ : ∃ θC : ℝ, ∀ z ∈ closure N, |z.1 - θC| < 1 / 4 := by
    rcases (closure N).eq_empty_or_nonempty with he | hne
    · exact ⟨0, by simp [he]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hNc.exists_isMinOn hne continuous_fst.continuousOn
      obtain ⟨z₂, hz₂, hmax⟩ := hNc.exists_isMaxOn hne continuous_fst.continuousOn
      refine ⟨(z₁.1 + z₂.1) / 2, fun z hz => ?_⟩
      have h1 : z₁.1 ≤ z.1 := hmin hz
      have h2 : z.1 ≤ z₂.1 := hmax hz
      have h3 := hNθ z₂ hz₂ z₁ hz₁
      rw [abs_lt] at h3 ⊢
      constructor <;> linarith
  have huniq : ∀ (z : ℝ × ℝ) (k k' : ℤ), z + ((k : ℝ), (0 : ℝ)) ∈ closure N →
      z + ((k' : ℝ), (0 : ℝ)) ∈ closure N → k = k' := by
    intro z k k' hk hk'
    have h3 := hNθ _ hk _ hk'
    simp only [Prod.fst_add] at h3
    have h4 : |((k - k' : ℤ) : ℝ)| < 1 := by
      push_cast
      have : z.1 + (k : ℝ) - (z.1 + (k' : ℝ)) = (k : ℝ) - k' := by ring
      rw [this] at h3
      linarith
    have h5 : |k - k'| < 1 := by
      rw [← Int.cast_abs] at h4
      exact_mod_cast h4
    have := Int.abs_lt_one_iff.mp h5
    omega
  have hlf : LocallyFinite
      (fun k : ℤ => (fun z : ℝ × ℝ => z + ((k : ℝ), (0 : ℝ))) ⁻¹' closure N) := by
    intro z₀
    obtain ⟨R, hR⟩ := hNc.isBounded.subset_closedBall 0
    refine ⟨Metric.ball z₀ 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
    apply (Set.finite_Icc (⌊-R - z₀.1 - 1⌋) (⌈R - z₀.1 + 1⌉)).subset
    rintro k ⟨z, hz1, hz2⟩
    have a1 : ‖(z + ((k : ℝ), (0 : ℝ))).1‖ ≤ R :=
      (norm_fst_le _).trans (mem_closedBall_zero_iff.mp (hR hz1))
    have a2 : ‖(z - z₀).1‖ < 1 :=
      (norm_fst_le _).trans_lt (by rw [← dist_eq_norm]; exact hz2)
    simp only [Prod.fst_add, Prod.fst_sub, Real.norm_eq_abs] at a1 a2
    rw [abs_le] at a1
    rw [abs_lt] at a2
    constructor
    · exact Int.floor_le_iff.mpr (by linarith)
    · exact Int.le_ceil_iff.mpr (by linarith)
  obtain ⟨f₀, hf₀s, hf₀t, hf₀I⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (n := (⊤ : ℕ∞)) 𝓘(ℝ, ℝ × ℝ)
      hN.isClosed_compl hC.isClosed (disjoint_compl_left_iff_subset.mpr hCN)
  obtain ⟨V₀, hV₀o, hV₀s, hV₀⟩ := eventually_nhdsSet_iff_exists.mp hf₀s
  obtain ⟨A₀, hA₀o, hA₀s, hA₀⟩ := eventually_nhdsSet_iff_exists.mp hf₀t
  obtain ⟨β₀, hβ₀def⟩ : ∃ β₀ : ℝ × ℝ → ℝ, β₀ = fun z => f₀ z := ⟨_, rfl⟩
  have hβ₀sm : ContDiff ℝ ∞ β₀ := by
    rw [hβ₀def]; exact contMDiff_iff_contDiff.mp f₀.contMDiff
  have hβ₀T : ∀ x, β₀ x ≠ 0 → x ∈ V₀ᶜ := by
    intro x hx hxV
    exact hx (by rw [hβ₀def]; exact hV₀ x hxV)
  have hV₀N : V₀ᶜ ⊆ N := by
    intro x hx
    by_contra hxN
    exact hx (hV₀s hxN)
  have hβ₀I : ∀ x, β₀ x ∈ Icc (0 : ℝ) 1 := by intro x; rw [hβ₀def]; exact hf₀I x
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ × ℝ → ℝ,
      β = fun z => ∑ᶠ k : ℤ, β₀ (z + ((k : ℝ), (0 : ℝ))) := ⟨_, rfl⟩
  have hβ_eq : ∀ (z : ℝ × ℝ) (k : ℤ), z + ((k : ℝ), (0 : ℝ)) ∈ N →
      β z = β₀ (z + ((k : ℝ), (0 : ℝ))) := by
    intro z k hk
    rw [hβdef]
    refine finsum_eq_single _ k fun k' hk' => ?_
    by_contra hne
    exact hk' (huniq z k' k (subset_closure (hV₀N (hβ₀T _ hne))) (subset_closure hk))
  have hβ_zero : ∀ z : ℝ × ℝ, (∀ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∉ N) → β z = 0 := by
    intro z hz
    rw [hβdef]
    refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
    by_contra hne
    exact hz k (hV₀N (hβ₀T _ hne))
  have hβI : ∀ z, β z ∈ Icc (0 : ℝ) 1 := by
    intro z
    by_cases hz : ∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ N
    · obtain ⟨k, hk⟩ := hz
      rw [hβ_eq z k hk]; exact hβ₀I _
    · simp only [not_exists] at hz
      rw [hβ_zero z hz]; exact ⟨le_rfl, zero_le_one⟩
  have hβ_ne : ∀ z, β z ≠ 0 → ∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ V₀ᶜ := by
    intro z hz
    by_contra hcon
    simp only [not_exists] at hcon
    apply hz
    rw [hβdef]
    refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
    by_contra hne
    exact hcon k (hβ₀T _ hne)
  have hβsm : ContDiff ℝ ∞ β := by
    rw [hβdef, ← contMDiff_iff_contDiff]
    refine contMDiff_finsum (fun k => ?_) (hlf.subset fun k => ?_)
    · rw [contMDiff_iff_contDiff]
      exact hβ₀sm.comp (contDiff_id.add contDiff_const)
    · intro x hx
      exact subset_closure (hV₀N (hβ₀T _ hx))
  have hβper : ∀ z : ℝ × ℝ, β (z + ((1 : ℝ), (0 : ℝ))) = β z := by
    intro z
    rw [hβdef]
    simp only
    conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
    refine finsum_congr fun k => ?_
    congr 1
    ext <;> simp
    ring
  have hβA : ∀ z ∈ A₀ ∩ N, β z = 1 := by
    intro z hz
    have := hβ_eq z 0 (by rw [Int.cast_zero, Prod.mk_zero_zero, add_zero]; exact hz.2)
    rw [this]
    simp only [Int.cast_zero, Prod.mk_zero_zero, add_zero]
    rw [hβ₀def]; exact hA₀ z hz.1
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ × ℝ → ℝ,
      τ = fun z => Real.sin (2 * Real.pi * (z.1 - θC)) := ⟨_, rfl⟩
  have hτsm : ContDiff ℝ ∞ τ := by
    rw [hτdef]; fun_prop
  have hτper : ∀ z : ℝ × ℝ, τ (z + ((1 : ℝ), (0 : ℝ))) = τ z := by
    intro z
    rw [hτdef]
    simp only [Prod.fst_add]
    have := Real.sin_add_int_mul_two_pi (2 * Real.pi * (z.1 - θC)) 1
    rw [← this]; congr 1; push_cast; ring
  have hτI : ∀ z, |τ z| ≤ 1 := by intro z; rw [hτdef]; exact Real.abs_sin_le_one _
  have hτderiv : ∀ z ∈ A₀ ∩ N, deriv (fun θ => τ (θ, z.2)) z.1 ≠ 0 := by
    intro z hz
    have hd : HasDerivAt (fun θ => τ (θ, z.2))
        (Real.cos (2 * Real.pi * (z.1 - θC)) * (2 * Real.pi * 1)) z.1 := by
      rw [hτdef]
      exact (((hasDerivAt_id z.1).sub_const θC).const_mul (2 * Real.pi)).sin
    rw [hd.deriv]
    have hb := hθC z (subset_closure hz.2)
    rw [abs_lt] at hb
    have hcos : 0 < Real.cos (2 * Real.pi * (z.1 - θC)) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos]
    have := Real.pi_pos
    positivity
  have hτinj : ∀ z ∈ A₀ ∩ N, ∀ z' : ℝ × ℝ, β z' = 1 → τ z' = τ z →
      ∃ k : ℤ, z'.1 = z.1 + k := by
    intro z hz z' hβ1 hτe
    obtain ⟨k, hk⟩ := hβ_ne z' (by rw [hβ1]; exact one_ne_zero)
    have hb := hθC z (subset_closure hz.2)
    have hb' := hθC _ (subset_closure (hV₀N hk))
    simp only [Prod.fst_add] at hb'
    rw [abs_lt] at hb hb'
    have e1 : τ z' = Real.sin (2 * Real.pi * (z'.1 + k - θC)) := by
      rw [hτdef]
      dsimp only
      have := Real.sin_add_int_mul_two_pi (2 * Real.pi * (z'.1 - θC)) k
      rw [← this]; congr 1; ring
    rw [e1, hτdef] at hτe
    have := Real.injOn_sin ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ hτe
    refine ⟨-k, ?_⟩
    have hpi := Real.pi_pos
    have : z'.1 + k - θC = z.1 - θC := by
      have h2 : (2 * Real.pi) * (z'.1 + k - θC) = (2 * Real.pi) * (z.1 - θC) := by
        simpa [mul_assoc] using this
      exact mul_left_cancel₀ (by positivity) h2
    push_cast; linarith
  have hhc : Continuous (fun z : ℝ × ℝ => h z.1 z.2) := hsm.continuous
  have hK : IsCompact (ψ.symm '' ((fun z : ℝ × ℝ => h z.1 z.2) '' closure N)) := by
    refine (hNc.image hhc).image_of_continuousOn (hψs.continuousOn.mono ?_)
    rintro _ ⟨z, hz, rfl⟩; exact hNψ z hz
  have hKs : ψ.symm '' ((fun z : ℝ × ℝ => h z.1 z.2) '' closure N) ⊆ ψ.source := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩; exact ψ.map_target (hNψ z hz)
  obtain ⟨δ, hδ, hδs⟩ := hK.exists_thickening_subset_open ψ.open_source hKs
  set r₀ : ℝ := δ / 8 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  let lam : ContDiffBump (0 : (Fin n → ℝ) × (Fin n → ℝ)) :=
    ⟨r₀, 2 * r₀, hr₀pos, by linarith⟩
  have hlamsm : ContDiff ℝ ∞ (fun w => lam w) := lam.contDiff
  have hlamI : ∀ w, lam w ∈ Icc (0 : ℝ) 1 := fun w => ⟨lam.nonneg, lam.le_one⟩
  have hlam0 : ∀ w, lam w ≠ 0 → ‖w‖ < 2 * r₀ := by
    intro w hw
    have : w ∈ Function.support (fun w => lam w) := hw
    rw [lam.support_eq] at this
    simpa using this
  have hlam1 : ∀ w : (Fin n → ℝ) × (Fin n → ℝ), ‖w‖ ≤ r₀ → lam w = 1 := by
    intro w hw
    exact lam.one_of_mem_closedBall (by simpa using hw)
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ × ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ),
      V = fun z w => (w.1 - w.1 i₀ • Pi.single i₀ (1 : ℝ)) +
        τ z • (w.2 - w.2 i₀ • Pi.single i₀ (1 : ℝ)) := ⟨_, rfl⟩
  have hVi₀ : ∀ z w, V z w i₀ = 0 := by
    intro z w; rw [hVdef]; simp
  have hVper : ∀ z w, V (z + ((1 : ℝ), (0 : ℝ))) w = V z w := by
    intro z w; rw [hVdef]; simp only [hτper]
  have hpr : ∀ y : Fin n → ℝ, ‖y - y i₀ • Pi.single i₀ (1 : ℝ)‖ ≤ 2 * ‖y‖ := by
    intro y
    calc ‖y - y i₀ • Pi.single i₀ (1 : ℝ)‖ ≤ ‖y‖ + ‖y i₀ • Pi.single i₀ (1 : ℝ)‖ :=
          norm_sub_le _ _
      _ = ‖y‖ + ‖y i₀‖ := by rw [norm_smul, Pi.norm_single, norm_one, mul_one]
      _ ≤ ‖y‖ + ‖y‖ := by gcongr; exact norm_le_pi_norm y i₀
      _ = 2 * ‖y‖ := by ring
  have hVb : ∀ z w, ‖V z w‖ ≤ 4 * ‖w‖ := by
    intro z w
    rw [hVdef]
    calc ‖(w.1 - w.1 i₀ • Pi.single i₀ (1 : ℝ)) + τ z • (w.2 - w.2 i₀ • Pi.single i₀ (1 : ℝ))‖
        ≤ ‖w.1 - w.1 i₀ • Pi.single i₀ (1 : ℝ)‖ +
          ‖τ z • (w.2 - w.2 i₀ • Pi.single i₀ (1 : ℝ))‖ := norm_add_le _ _
      _ ≤ 2 * ‖w.1‖ + 1 * (2 * ‖w.2‖) := by
          rw [norm_smul]
          gcongr
          · exact hpr _
          · rw [Real.norm_eq_abs]; exact hτI z
          · exact hpr _
      _ ≤ 4 * ‖w‖ := by
          have := norm_fst_le w
          have := norm_snd_le w
          linarith
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ),
      G = fun z w => ψ.symm (h z.1 z.2) + (β z * lam w) • V z w := ⟨_, rfl⟩
  have hGper : ∀ z w, G (z + ((1 : ℝ), (0 : ℝ))) w = G z w := by
    intro z w
    rw [hGdef]
    simp only [hVper, hβper]
    have := hh_int 1 z
    simp only [Int.cast_one] at this
    rw [this]
  obtain ⟨U, hUdef⟩ : ∃ U : Set (ℝ × ℝ),
      U = {z | ∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ N} := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    have : U = ⋃ k : ℤ, (fun z : ℝ × ℝ => z + ((k : ℝ), (0 : ℝ))) ⁻¹' N := by
      rw [hUdef]; ext z; simp
    rw [this]
    exact isOpen_iUnion fun k => hN.preimage (continuous_id.add continuous_const)
  have hUper : ∀ z, z ∈ U ↔ z + ((1 : ℝ), (0 : ℝ)) ∈ U := by
    intro z
    rw [hUdef]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      convert hk using 1
      ext <;> simp
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      convert hk using 1
      ext <;> simp
      ring
  have hUt : ∀ z ∈ U, h z.1 z.2 ∈ ψ.target := by
    intro z hz
    rw [hUdef] at hz
    obtain ⟨k, hk⟩ := hz
    rw [← hh_int k z]
    exact hNψ _ (subset_closure hk)
  have hGs : ∀ z ∈ U, ∀ w, G z w ∈ ψ.source := by
    intro z hz w
    have hz' := hz
    rw [hUdef] at hz'
    obtain ⟨k, hk⟩ := hz'
    apply hδs
    rw [Metric.mem_thickening_iff]
    refine ⟨ψ.symm (h z.1 z.2), ⟨_, ⟨_, subset_closure hk, rfl⟩, by dsimp only; rw [hh_int k z]⟩, ?_⟩
    rw [hGdef, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_smul]
    by_cases hl : lam w = 0
    · rw [hl, mul_zero, norm_zero, zero_mul]; exact hδ
    · have h1 : ‖β z * lam w‖ ≤ 1 := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hβI z).1,
          abs_of_nonneg (hlamI w).1]
        calc β z * lam w ≤ 1 * 1 :=
              mul_le_mul (hβI z).2 (hlamI w).2 (hlamI w).1 zero_le_one
          _ = 1 := mul_one 1
      have h2 := hlam0 w hl
      calc ‖β z * lam w‖ * ‖V z w‖ ≤ 1 * (4 * ‖w‖) :=
            mul_le_mul h1 (hVb z w) (norm_nonneg _) zero_le_one
        _ < δ := by rw [hr₀] at h2; linarith
  have hβU : ∀ z, z ∉ U → β z = 0 := by
    intro z hz
    exact hβ_zero z (fun k hk => hz (by rw [hUdef]; exact ⟨k, hk⟩))
  obtain ⟨Hf, hHfdef⟩ : ∃ Hf : ℝ × ℝ → (Fin n → ℝ) × (Fin n → ℝ) → M,
      Hf = fun z w => if z ∈ U then ψ (G z w) else h z.1 z.2 := ⟨_, rfl⟩
  have hHfper : ∀ z w, Hf (z + ((1 : ℝ), (0 : ℝ))) w = Hf z w := by
    intro z w
    rw [hHfdef]
    have := hh_int 1 z
    simp only [Int.cast_one] at this
    dsimp only
    rw [this, hGper]
    by_cases hz : z ∈ U
    · have hz' := (hUper z).mp hz
      simp only [hz, hz', ↓reduceIte]
    · have hz' : z + ((1 : ℝ), (0 : ℝ)) ∉ U := fun h' => hz ((hUper z).mpr h')
      simp only [hz, hz', ↓reduceIte]
  have hHf0 : ∀ z, Hf z 0 = h z.1 z.2 := by
    intro z
    rw [hHfdef]
    by_cases hz : z ∈ U
    · simp only [hz, ↓reduceIte]
      rw [hGdef]
      have : V z 0 = 0 := by rw [hVdef]; simp
      simp only [this, smul_zero, add_zero]
      exact ψ.right_inv (hUt z hz)
    · simp only [hz, ↓reduceIte]
  have hHfU : ∀ z w, z ∈ U → Hf z w = ψ (G z w) := by
    intro z w hz; rw [hHfdef]; simp only [hz, ↓reduceIte]
  have hHfnU : ∀ z w, z ∉ U → Hf z w = h z.1 z.2 := by
    intro z w hz; rw [hHfdef]; simp only [hz, ↓reduceIte]
  have hlevel : ∀ z w, f (Hf z w) = c := by
    intro z w
    by_cases hz : z ∈ U
    · rw [hHfU z w hz, hψf _ (hGs z hz w)]
      have h0 : (ψ.symm (h z.1 z.2)) i₀ = 0 := by
        have := hψf _ (ψ.map_target (hUt z hz))
        rw [ψ.right_inv (hUt z hz), hlev] at this
        linarith
      rw [hGdef]
      simp only [Pi.add_apply, Pi.smul_apply, hVi₀, h0, smul_zero, add_zero]
    · rw [hHfnU z w hz, hlev]
  obtain ⟨T, hTdef⟩ : ∃ T : Set (ℝ × ℝ),
      T = ⋃ k : ℤ, (fun z : ℝ × ℝ => z + ((k : ℝ), (0 : ℝ))) ⁻¹' V₀ᶜ := ⟨_, rfl⟩
  have hTc : IsClosed T := by
    rw [hTdef]
    refine (hlf.subset fun k => ?_).isClosed_iUnion fun k =>
      hV₀o.isClosed_compl.preimage (continuous_id.add continuous_const)
    intro x hx
    exact subset_closure (hV₀N hx)
  have hTU : ∀ z, z ∉ T → β z = 0 := by
    intro z hz
    by_contra hne
    obtain ⟨k, hk⟩ := hβ_ne z hne
    exact hz (by rw [hTdef]; exact Set.mem_iUnion.mpr ⟨k, hk⟩)
  have hUT : ∀ z, z ∉ U → z ∉ T := by
    intro z hz hzT
    rw [hTdef] at hzT
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hzT
    exact hz (by rw [hUdef]; exact ⟨k, hV₀N hk⟩)
  have hsmooth : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))) I ∞
      (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => Hf q.1 q.2) := by
    intro q₀
    by_cases hq : q₀.1 ∈ U
    · have hev : ∀ᶠ q in 𝓝 q₀, q.1 ∈ U :=
        continuous_fst.continuousAt.preimage_mem_nhds (hUo.mem_nhds hq)
      have hg0 : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
          (fun z : ℝ × ℝ => ψ.symm (h z.1 z.2)) q₀.1 :=
        (hψs.contMDiffAt (ψ.open_target.mem_nhds (hUt _ hq))).comp q₀.1 hsm.contMDiffAt
      have hg0' : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => ψ.symm (h z.1 z.2)) q₀.1 :=
        contMDiffAt_iff_contDiffAt.mp hg0
      have hGat : ContDiffAt ℝ ∞
          (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => G q.1 q.2) q₀ := by
        rw [hGdef, hVdef]
        have e1 : ContDiffAt ℝ ∞
            (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => ψ.symm (h q.1.1 q.1.2)) q₀ :=
          hg0'.comp q₀ contDiffAt_fst
        have e2 : ContDiff ℝ ∞ (fun y : Fin n → ℝ => y i₀) := contDiff_apply ℝ ℝ i₀
        have e3 : ContDiff ℝ ∞
            (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
              (β q.1 * lam q.2) •
                ((q.2.1 - q.2.1 i₀ • Pi.single i₀ (1 : ℝ)) +
                  τ q.1 • (q.2.2 - q.2.2 i₀ • Pi.single i₀ (1 : ℝ)))) := by
          have b1 : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => β q.1) :=
            hβsm.comp contDiff_fst
          have b2 : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => lam q.2) :=
            hlamsm.comp contDiff_snd
          have b3 : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => τ q.1) :=
            hτsm.comp contDiff_fst
          have b4 : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => q.2.1) :=
            contDiff_fst.comp contDiff_snd
          have b5 : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => q.2.2) :=
            contDiff_snd.comp contDiff_snd
          exact (b1.mul b2).smul ((b4.sub ((e2.comp b4).smul contDiff_const)).add
            (b3.smul (b5.sub ((e2.comp b5).smul contDiff_const))))
        exact e1.add e3.contDiffAt
      have hψat : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ ψ (G q₀.1 q₀.2) :=
        hψ.contMDiffAt (ψ.open_source.mem_nhds (hGs _ hq _))
      have hcomp : ContMDiffAt 𝓘(ℝ, (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))) I ∞
          (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => ψ (G q.1 q.2)) q₀ :=
        hψat.comp q₀ (contMDiffAt_iff_contDiffAt.mpr hGat)
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [hev] with q hq'
      exact hHfU _ _ hq'
    · have hev : ∀ᶠ q in 𝓝 q₀, q.1 ∉ T :=
        continuous_fst.continuousAt.preimage_mem_nhds (hTc.isOpen_compl.mem_nhds (hUT _ hq))
      have hcomp : ContMDiffAt 𝓘(ℝ, (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))) I ∞
          (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => h q.1.1 q.1.2) q₀ :=
        (hsm.comp (contMDiff_iff_contDiff.mpr contDiff_fst)).contMDiffAt
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [hev] with q hq'
      by_cases hqU : q.1 ∈ U
      · rw [hHfU _ _ hqU, hGdef]
        simp only [hTU _ hq', zero_mul, zero_smul, add_zero]
        exact ψ.right_inv (hUt _ hqU)
      · exact hHfnU _ _ hqU
  have hFc : Continuous (fun q : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => (q.1, Hf q.1 q.2)) :=
    continuous_fst.prodMk hsmooth.continuous
  obtain ⟨u, v, -, hvo, hNu, h0v, huv⟩ :=
    generalized_tube_lemma (s := closure N) (t := {(0 : (Fin n → ℝ) × (Fin n → ℝ))}) hNc
      isCompact_singleton (h𝒪.preimage hFc) (by
        rintro ⟨z, w⟩ ⟨_, hw⟩
        rw [Set.mem_singleton_iff] at hw
        subst hw
        change (z, Hf z 0) ∈ 𝒪
        rw [hHf0]; exact hgraph z)
  obtain ⟨ε, hε, hεv⟩ := Metric.isOpen_iff.mp hvo 0 (h0v rfl)
  refine ⟨Hf, β, τ, A₀ ∩ N, min r₀ ε, lt_min hr₀pos hε, hsmooth, ?_, hHf0, hlevel, ?_, ?_, ?_,
    hβsm, hτsm, hA₀o.inter hN, subset_inter hA₀s hCN, inter_subset_right,
    fun z hz => hβA z hz, hτderiv, hτinj⟩
  · intro θ s w
    simpa only [Prod.mk_add_mk, add_zero] using hHfper (θ, s) w
  · intro z w hzN
    refine hHfnU z w fun hz => ?_
    rw [hUdef] at hz
    obtain ⟨k, hk⟩ := hz
    exact hzN k hk
  · intro w hw z
    by_cases hz : z ∈ U
    · have hz' := hz
      rw [hUdef] at hz'
      obtain ⟨k, hk⟩ := hz'
      have key : (z + ((k : ℝ), (0 : ℝ)), Hf (z + ((k : ℝ), (0 : ℝ))) w) ∈ 𝒪 := by
        have hwv : w ∈ v := hεv (mem_ball_zero_iff.mpr (hw.trans_le (min_le_right _ _)))
        exact huv (Set.mk_mem_prod (hNu (subset_closure hk)) hwv)
      exact (hshift (fun x => (x, Hf x w) ∈ 𝒪)
        (fun x => by rw [h𝒪per x (Hf x w), hHfper]) k z).mpr key
    · rw [hHfnU z w hz]; exact hgraph z
  · intro w hw z hz
    have hl1 : lam w = 1 := hlam1 w (hw.le.trans (min_le_left _ _))
    by_cases hzU : z ∈ U
    · rw [hHfU z w hzU]
      refine ⟨ψ.map_source (hGs z hzU w), ?_⟩
      rw [ψ.left_inv (hGs z hzU w), hGdef, hVdef]
      simp only [hl1, mul_one]
    · rw [hHfnU z w hzU]
      refine ⟨hz, ?_⟩
      rw [hβU z hzU]
      simp

theorem dimH_bad_params_lt (h5 : 5 ≤ n) (i₀ : Fin n) {Y A : Set (ℝ × ℝ)} (hY : IsOpen Y)
    (hA : IsOpen A) (hAY : A ⊆ Y) {G₀ : ℝ × ℝ → (Fin n → ℝ)} (hG₀ : ContDiffOn ℝ ∞ G₀ Y)
    {β τ : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hτ : ContDiff ℝ ∞ τ) (hβA : EqOn β 1 A)
    (hτA : ∀ z ∈ A, deriv (fun θ => τ (θ, z.2)) z.1 ≠ 0)
    (hτinj : ∀ z ∈ A, ∀ z' ∈ Y, z'.2 = z.2 → β z' = 1 → τ z' = τ z →
      ∃ k : ℤ, z'.1 = z.1 + k) :
    dimH ({w : (Fin n → ℝ) × (Fin n → ℝ) | ∃ z ∈ A,
        deriv (fun θ => G₀ (θ, z.2) + β (θ, z.2) • ((w.1 - w.1 i₀ • Pi.single i₀ (1 : ℝ)) +
          τ (θ, z.2) • (w.2 - w.2 i₀ • Pi.single i₀ (1 : ℝ)))) z.1 = 0} ∪
      {w : (Fin n → ℝ) × (Fin n → ℝ) | ∃ z ∈ A, ∃ z' ∈ Y, z'.2 = z.2 ∧
        (∀ k : ℤ, z'.1 ≠ z.1 + k) ∧
        G₀ z + β z • ((w.1 - w.1 i₀ • Pi.single i₀ (1 : ℝ)) +
            τ z • (w.2 - w.2 i₀ • Pi.single i₀ (1 : ℝ))) =
          G₀ z' + β z' • ((w.1 - w.1 i₀ • Pi.single i₀ (1 : ℝ)) +
            τ z' • (w.2 - w.2 i₀ • Pi.single i₀ (1 : ℝ)))}) <
      Module.finrank ℝ ((Fin n → ℝ) × (Fin n → ℝ)) := by
  classical
  set e : Fin n → ℝ := Pi.single i₀ (1 : ℝ) with he
  have hei : e i₀ = 1 := by simp [he]
  let πL : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.id ℝ (Fin n → ℝ) - (ContinuousLinearMap.proj i₀).smulRight e
  have hπL : ∀ u, πL u = u - u i₀ • e := fun u => by simp [πL]
  let S : Submodule ℝ (Fin n → ℝ) :=
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i₀)
  have hmemS : ∀ y, y ∈ S ↔ y i₀ = 0 := fun y => by simp [S]
  have hSrank : Module.finrank ℝ S = n - 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i₀)
    have h2 : LinearMap.range (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i₀) = ⊤ :=
      LinearMap.range_eq_top.2 (fun t => ⟨fun _ => t, rfl⟩)
    rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
    change Module.finrank ℝ (LinearMap.ker _) = n - 1
    omega
  have hPrank : Module.finrank ℝ ((Fin n → ℝ) × (Fin n → ℝ)) = n + n := by
    simp [Module.finrank_prod]
  have hSP : Module.finrank ℝ S ≤ Module.finrank ℝ ((Fin n → ℝ) × (Fin n → ℝ)) := by
    rw [hSrank, hPrank]; omega
  let L₀ : ℝ → ℝ → ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) := fun c₁ c₂ =>
    c₁ • πL.comp (ContinuousLinearMap.fst ℝ _ _) + c₂ • πL.comp (ContinuousLinearMap.snd ℝ _ _)
  have hL₀ : ∀ c₁ c₂ w, L₀ c₁ c₂ w = c₁ • (w.1 - w.1 i₀ • e) + c₂ • (w.2 - w.2 i₀ • e) := by
    intro c₁ c₂ w; simp [L₀, hπL]
  have hrangeS : ∀ c₁ c₂ : ℝ, (c₁ ≠ 0 ∨ c₂ ≠ 0) →
      LinearMap.range (L₀ c₁ c₂ : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] (Fin n → ℝ)) = S := by
    intro c₁ c₂ hc
    ext y
    simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, hmemS]
    constructor
    · rintro ⟨w, rfl⟩
      simp [hL₀, hei]
    · intro hy
      rcases hc with hc | hc
      · refine ⟨(c₁⁻¹ • y, 0), ?_⟩
        simp [hL₀, hy, hc]
      · refine ⟨(0, c₂⁻¹ • y), ?_⟩
        simp [hL₀, hy, hc]
  have hderivτ : ∀ z : ℝ × ℝ, HasDerivAt (fun θ => τ (θ, z.2)) (fderiv ℝ τ z (1, 0)) z.1 := by
    intro z
    have h1 : HasDerivAt (fun θ : ℝ => (θ, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
      (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
    have h2 : HasFDerivAt τ (fderiv ℝ τ z) z :=
      ((hτ.differentiable (by simp)) z).hasFDerivAt
    exact h2.comp_hasDerivAt z.1 h1
  have hderivG : ∀ z ∈ Y, HasDerivAt (fun θ => G₀ (θ, z.2)) (fderiv ℝ G₀ z (1, 0)) z.1 := by
    intro z hz
    have h1 : HasDerivAt (fun θ : ℝ => (θ, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
      (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
    have h2 : HasFDerivAt G₀ (fderiv ℝ G₀ z) z :=
      ((hG₀.differentiableOn (by simp)).differentiableAt (hY.mem_nhds hz)).hasFDerivAt
    exact h2.comp_hasDerivAt z.1 h1
  have hB1 : dimH {w : (Fin n → ℝ) × (Fin n → ℝ) | ∃ z ∈ A,
      fderiv ℝ G₀ z (1, 0) + L₀ 0 (fderiv ℝ τ z (1, 0)) w = 0} <
      Module.finrank ℝ ((Fin n → ℝ) × (Fin n → ℝ)) := by
    refine dimH_affine_zeros_lt (E := ℝ × ℝ) (S := S) ?_ hSP hA ?_ ?_ ?_
    · rw [hSrank]; simp [Module.finrank_prod]; omega
    · exact (((hG₀.fderiv_of_isOpen hY (m := 1) (by simp)).clm_apply contDiffOn_const)).mono hAY
    · have hτ' : ContDiff ℝ 1 (fderiv ℝ τ) := hτ.fderiv_right (by simp)
      have : ContDiff ℝ 1 (fun z : ℝ × ℝ => L₀ 0 (fderiv ℝ τ z (1, 0))) := by
        simp only [L₀, zero_smul, zero_add]
        exact (hτ'.clm_apply contDiff_const).smul contDiff_const
      exact this.contDiffOn
    · intro z hz
      refine hrangeS _ _ (Or.inr ?_)
      rw [← (hderivτ z).deriv]
      exact hτA z hz
  let Z₂ : Set ((ℝ × ℝ) × ℝ) := {p | p.1 ∈ A ∧ (p.2, p.1.2) ∈ Y ∧ ∀ k : ℤ, p.2 ≠ p.1.1 + k}
  have hZ₂ : IsOpen Z₂ := by
    have hcl : IsClosed (range ((↑) : ℤ → ℝ)) := Int.isClosedEmbedding_coe_real.isClosed_range
    have hEq : Z₂ = (Prod.fst ⁻¹' A ∩ (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.2)) ⁻¹' Y) ∩
        (fun p : (ℝ × ℝ) × ℝ => p.2 - p.1.1) ⁻¹' (range ((↑) : ℤ → ℝ))ᶜ := by
      ext p
      simp only [Z₂, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, mem_range,
        not_exists]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, fun k hk => h3 k (by linarith)⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, fun k hk => h3 k (by linarith)⟩
    rw [hEq]
    exact ((hA.preimage continuous_fst).inter (hY.preimage (by fun_prop))).inter
      (hcl.isOpen_compl.preimage (by fun_prop))
  have hsw : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.2)) := by fun_prop
  have hB2 : dimH {w : (Fin n → ℝ) × (Fin n → ℝ) | ∃ p ∈ Z₂,
      (G₀ p.1 - G₀ (p.2, p.1.2)) +
        L₀ (1 - β (p.2, p.1.2)) (τ p.1 - β (p.2, p.1.2) * τ (p.2, p.1.2)) w = 0} <
      Module.finrank ℝ ((Fin n → ℝ) × (Fin n → ℝ)) := by
    refine dimH_affine_zeros_lt (E := (ℝ × ℝ) × ℝ) (S := S) ?_ hSP hZ₂ ?_ ?_ ?_
    · rw [hSrank]; simp [Module.finrank_prod]; omega
    · have h1 : ContDiffOn ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => G₀ p.1) Z₂ :=
        hG₀.comp contDiffOn_fst (fun p hp => hAY hp.1)
      have h2 : ContDiffOn ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => G₀ (p.2, p.1.2)) Z₂ :=
        hG₀.comp hsw.contDiffOn (fun p hp => hp.2.1)
      exact (h1.sub h2).of_le (by simp)
    · have h1 : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ =>
          L₀ (1 - β (p.2, p.1.2)) (τ p.1 - β (p.2, p.1.2) * τ (p.2, p.1.2))) := by
        simp only [L₀]
        exact ((contDiff_const.sub (hβ.comp hsw)).smul contDiff_const).add
          (((hτ.comp contDiff_fst).sub ((hβ.comp hsw).mul (hτ.comp hsw))).smul contDiff_const)
      exact (h1.of_le (by simp)).contDiffOn
    · rintro ⟨z, θ'⟩ ⟨hz, hz', hk⟩
      refine hrangeS _ _ ?_
      by_contra hcon
      push Not at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      have hb : β (θ', z.2) = 1 := by linarith
      rw [hb, one_mul, sub_eq_zero] at hc2
      obtain ⟨k, hk'⟩ := hτinj z hz (θ', z.2) hz' rfl hb hc2.symm
      exact hk k hk'
  refine lt_of_le_of_lt ?_ (max_lt hB1 hB2)
  rw [← dimH_union]
  refine dimH_mono (union_subset_union ?_ ?_)
  · rintro w ⟨z, hz, hw⟩
    refine ⟨z, hz, ?_⟩
    have hev : (fun θ => G₀ (θ, z.2) + β (θ, z.2) • ((w.1 - w.1 i₀ • e) +
          τ (θ, z.2) • (w.2 - w.2 i₀ • e))) =ᶠ[𝓝 z.1]
        (fun θ => G₀ (θ, z.2) + ((w.1 - w.1 i₀ • e) + τ (θ, z.2) • (w.2 - w.2 i₀ • e))) := by
      have hopen : IsOpen {θ : ℝ | (θ, z.2) ∈ A} :=
        hA.preimage (continuous_id.prodMk continuous_const)
      filter_upwards [hopen.mem_nhds (show (z.1, z.2) ∈ A from hz)] with θ hθ
      rw [hβA hθ, Pi.one_apply, one_smul]
    have hd : HasDerivAt (fun θ => G₀ (θ, z.2) + ((w.1 - w.1 i₀ • e) +
        τ (θ, z.2) • (w.2 - w.2 i₀ • e)))
        (fderiv ℝ G₀ z (1, 0) + fderiv ℝ τ z (1, 0) • (w.2 - w.2 i₀ • e)) z.1 :=
      (hderivG z (hAY hz)).add (((hderivτ z).smul_const _).const_add _)
    rw [(hd.congr_of_eventuallyEq hev).deriv] at hw
    rw [hL₀, ← hw]
    simp
  · rintro w ⟨z, hz, z', hz', hz2, hk, heq⟩
    have hz'e : (z'.1, z.2) = z' := Prod.ext rfl hz2.symm
    refine ⟨(z, z'.1), ⟨hz, by rw [hz'e]; exact hz', hk⟩, ?_⟩
    simp only [hz'e, hL₀]
    rw [hβA hz, Pi.one_apply, one_smul] at heq
    linear_combination (norm := module) heq

theorem exists_embedded_cell_step (h5 : 5 ≤ n) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    {h : ℝ → ℝ → M} (hsm : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry h))
    (hper : ∀ θ s, h (θ + 1) s = h θ s) (hlev : ∀ θ s, f (h θ s) = c)
    {Q : Set (ℝ × ℝ)} (hQ : IsClosed Q) (hQper : ∀ θ s, (θ, s) ∈ Q ↔ (θ + 1, s) ∈ Q)
    (hQb : IsCompact (Q ∩ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ))) (hemb : isEmbeddedOn I h Q)
    (ψ : OpenPartialHomeomorph (Fin n → ℝ) M) (i₀ : Fin n)
    (hψ : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source)
    (hψs : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target)
    (hψf : ∀ y ∈ ψ.source, f (ψ y) = c + y i₀)
    {C N : Set (ℝ × ℝ)} (hC : IsCompact C) (hN : IsOpen N) (hCN : C ⊆ N)
    (hNc : IsCompact (closure N))
    (hNθ : ∀ z ∈ closure N, ∀ z' ∈ closure N, |z.1 - z'.1| < 1 / 2)
    (hNψ : ∀ z ∈ closure N, h z.1 z.2 ∈ ψ.target)
    {𝒪 : Set ((ℝ × ℝ) × M)} (h𝒪 : IsOpen 𝒪)
    (h𝒪per : ∀ z y, (z, y) ∈ 𝒪 ↔ (z + ((1 : ℝ), (0 : ℝ)), y) ∈ 𝒪)
    (hgraph : ∀ z : ℝ × ℝ, (z, h z.1 z.2) ∈ 𝒪) :
    ∃ h' : ℝ → ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry h') ∧
      (∀ θ s, h' (θ + 1) s = h' θ s) ∧ (∀ θ s, f (h' θ s) = c) ∧
      (∀ z : ℝ × ℝ, (∀ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∉ N) → h' z.1 z.2 = h z.1 z.2) ∧
      (∀ z : ℝ × ℝ, (z, h' z.1 z.2) ∈ 𝒪) ∧
      isEmbeddedOn I h' (Q ∪ {z | ∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ C}) := by
  obtain ⟨Hf, β, τ, A, r, hr, hHsm, hHper, hH0, hHlev, hHoff, hH𝒪, hHch, hβ, hτ, hA, hCA, hAN,
    hβA, hτA, hτinj⟩ := exists_level_perturbation_family hf hsm hper hlev ψ i₀ hψ hψs hψf hC hN
      hCN hNc hNθ hNψ h𝒪 h𝒪per hgraph
  have hperZ : ∀ (k : ℤ) (θ s : ℝ), h (θ + k) s = h θ s := by
    intro k θ s
    have := (show Function.Periodic (fun t => h t s) 1 from fun t => hper t s).int_mul k θ
    simpa using this
  have hHperZ : ∀ (k : ℤ) (θ s : ℝ) (w : (Fin n → ℝ) × (Fin n → ℝ)),
      Hf (θ + k, s) w = Hf (θ, s) w := by
    intro k θ s w
    have := (show Function.Periodic (fun t => Hf (t, s) w) 1 from
      fun t => hHper t s w).int_mul k θ
    simpa using this
  have hemb0 : isEmbeddedOn I (fun θ s => Hf (θ, s) 0) Q := by
    have : (fun θ s => Hf (θ, s) 0) = h := by
      funext θ s
      exact hH0 (θ, s)
    rw [this]
    exact hemb
  have hev := eventually_isEmbeddedOn hHsm hHper hQ hQper hQb hemb0
  obtain ⟨ε, hε, hεemb⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set Y : Set (ℝ × ℝ) := {z | h z.1 z.2 ∈ ψ.target} with hYdef
  have hY : IsOpen Y := ψ.open_target.preimage hsm.continuous
  have hAY : A ⊆ Y := fun z hz => hNψ z (subset_closure (hAN hz))
  have hG₀ : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => ψ.symm (h z.1 z.2)) Y := by
    have := hψs.comp hsm.contMDiffOn (fun z hz => hz)
    exact contMDiffOn_iff_contDiffOn.1 this
  have hdim := dimH_bad_params_lt h5 i₀ hY hA hAY hG₀ hβ hτ hβA hτA
    (fun z hz z' _ _ hb ht => hτinj z hz z' hb ht)
  obtain ⟨w, hwB, hwb⟩ := (dense_compl_of_dimH_lt_finrank hdim).exists_mem_open
    Metric.isOpen_ball (Metric.nonempty_ball.2 (lt_min hr hε) :
      (Metric.ball (0 : (Fin n → ℝ) × (Fin n → ℝ)) (min r ε)).Nonempty)
  have hwn : ‖w‖ < min r ε := mem_ball_zero_iff.1 hwb
  have hwr : ‖w‖ < r := lt_of_lt_of_le hwn (min_le_left _ _)
  have hembw : isEmbeddedOn I (fun θ s => Hf (θ, s) w) Q :=
    hεemb w (mem_ball_zero_iff.2 (lt_of_lt_of_le hwn (min_le_right _ _)))
  have hw1 := fun hh => hwB (Or.inl hh)
  have hw2 := fun hh => hwB (Or.inr hh)
  have hsm' : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry fun θ s => Hf (θ, s) w) :=
    hHsm.comp ((contDiff_id.prodMk contDiff_const).contMDiff)
  refine ⟨fun θ s => Hf (θ, s) w, hsm', fun θ s => hHper θ s w, fun θ s => hHlev _ w,
    fun z hz => hHoff z w hz, fun z => hH𝒪 w hwr z, ?_⟩
  have himmC : ∀ z : ℝ × ℝ, (∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ C) →
      mfderiv 𝓘(ℝ, ℝ) I (fun θ => Hf (θ, z.2) w) z.1 (1 : ℝ) ≠ 0 := by
    rintro z ⟨k, hk⟩
    have hk' : ((z.1 + k, z.2) : ℝ × ℝ) ∈ C := by
      have e : z + ((k : ℝ), (0 : ℝ)) = (z.1 + k, z.2) := by
        rw [← Prod.mk.eta (p := z), Prod.mk_add_mk, add_zero]
      rw [← e]
      exact hk
    have hz0A : ((z.1 + k, z.2) : ℝ × ℝ) ∈ A := hCA hk'
    have hz0Y : h (z.1 + k) z.2 ∈ ψ.target := hNψ _ (subset_closure (hCN hk'))
    have hzY : h z.1 z.2 ∈ ψ.target := by
      rw [← hperZ k]
      exact hz0Y
    have hmem : Hf (z.1, z.2) w ∈ ψ.target := (hHch w hwr (z.1, z.2) hzY).1
    have hgood : deriv (fun θ => ψ.symm (h θ z.2) + β (θ, z.2) •
        ((w.1 - w.1 i₀ • Pi.single i₀ (1 : ℝ)) +
          τ (θ, z.2) • (w.2 - w.2 i₀ • Pi.single i₀ (1 : ℝ)))) (z.1 + k) ≠ 0 :=
      fun h0 => hw1 ⟨(z.1 + k, z.2), hz0A, h0⟩
    have hopen : IsOpen {θ : ℝ | h (θ + k) z.2 ∈ ψ.target} :=
      ψ.open_target.preimage (hsm.continuous.comp
        (by fun_prop : Continuous fun θ : ℝ => ((θ + (k : ℝ), z.2) : ℝ × ℝ)))
    have heq : (fun θ => ψ.symm (Hf (θ, z.2) w)) =ᶠ[𝓝 z.1]
        fun θ => (fun θ => ψ.symm (h θ z.2) + β (θ, z.2) •
          ((w.1 - w.1 i₀ • Pi.single i₀ (1 : ℝ)) +
            τ (θ, z.2) • (w.2 - w.2 i₀ • Pi.single i₀ (1 : ℝ)))) (θ + k) := by
      filter_upwards [hopen.mem_nhds (show z.1 ∈ {θ : ℝ | h (θ + k) z.2 ∈ ψ.target} from hz0Y)]
        with θ hθ
      rw [← hHperZ k θ z.2 w]
      exact (hHch w hwr (θ + k, z.2) hθ).2
    have hderiv : deriv (fun θ => ψ.symm (Hf (θ, z.2) w)) z.1 ≠ 0 := by
      rw [heq.deriv_eq]
      intro h0
      exact hgood ((deriv_comp_add_const _ _ _).symm.trans h0)
    intro h0
    have hSd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun θ => Hf (θ, z.2) w) z.1 :=
      ((hHsm.comp (((contDiff_id.prodMk contDiff_const).prodMk contDiff_const).contMDiff :
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))) ∞
          (fun θ : ℝ => ((θ, z.2), w)))).contMDiffAt).mdifferentiableAt (by simp)
    have hψd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) ψ.symm (Hf (z.1, z.2) w) :=
      ((hψs _ hmem).contMDiffAt (ψ.open_target.mem_nhds hmem)).mdifferentiableAt (by simp)
    have hc := mfderiv_comp_apply (g := ψ.symm) z.1 hψd hSd (1 : ℝ)
    rw [h0, map_zero, mfderiv_eq_fderiv] at hc
    exact hderiv hc
  have hinjC : ∀ θ θ' s : ℝ, (∃ k : ℤ, ((θ, s) : ℝ × ℝ) + ((k : ℝ), (0 : ℝ)) ∈ C) →
      Hf (θ, s) w = Hf (θ', s) w → ∃ k : ℤ, θ' = θ + k := by
    rintro θ θ' s ⟨k, hk⟩ hθθ'
    have hk' : ((θ + k, s) : ℝ × ℝ) ∈ C := by
      rw [Prod.mk_add_mk, add_zero] at hk
      exact hk
    have hz0A : ((θ + k, s) : ℝ × ℝ) ∈ A := hCA hk'
    have hz0Y : h (θ + k) s ∈ ψ.target := hNψ _ (subset_closure (hCN hk'))
    by_cases hY' : h θ' s ∈ ψ.target
    · by_contra hne
      rw [not_exists] at hne
      apply hw2
      refine ⟨(θ + k, s), hz0A, (θ', s), hY', rfl, ?_, ?_⟩
      · intro j hj
        apply hne (k + j)
        have hj' : θ' = θ + k + j := hj
        rw [hj']
        push_cast
        ring
      · have e1 := (hHch w hwr (θ + k, s) hz0Y).2
        have e2 := (hHch w hwr (θ', s) hY').2
        dsimp only at e1 e2 ⊢
        rw [← e1, ← e2, hHperZ]
        exact congrArg ψ.symm hθθ'
    · exfalso
      have hoff : Hf (θ', s) w = h θ' s := by
        apply hHoff (θ', s) w
        intro j hj
        apply hY'
        have := hNψ _ (subset_closure hj)
        rw [Prod.mk_add_mk, add_zero] at this
        rw [← hperZ j]
        exact this
      have hin : Hf (θ, s) w ∈ ψ.target := by
        rw [← hHperZ k]
        exact (hHch w hwr (θ + k, s) hz0Y).1
      rw [hθθ', hoff] at hin
      exact hY' hin
  change isEmbeddedOn I (fun θ s => Hf (θ, s) w) (Q ∪ {z | ∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ C})
  refine ⟨?_, ?_⟩
  · rintro z (hzQ | hzC)
    · exact hembw.1 z hzQ
    · exact himmC z hzC
  · intro θ θ' s h1 h2 hθθ'
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact hembw.2 θ θ' s h1 h2 hθθ'
      · obtain ⟨k, hk⟩ := hinjC θ' θ s h2 hθθ'.symm
        exact ⟨-k, by rw [hk]; push_cast; ring⟩
    · exact hinjC θ θ' s h1 hθθ'

theorem exists_embedded_slices (h5 : 5 ≤ n) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ x, f x = c → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {h : ℝ → ℝ → M}
    (hsm : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry h)) (hper : ∀ θ s, h (θ + 1) s = h θ s)
    (hlev : ∀ θ s, f (h θ s) = c) {U P : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hUper : ∀ θ s, (θ, s) ∈ U ↔ (θ + 1, s) ∈ U) (hP : IsClosed P)
    (hPper : ∀ θ s, (θ, s) ∈ P ↔ (θ + 1, s) ∈ P) (hPU : P ⊆ U)
    (himm : ∀ z ∈ U, mfderiv 𝓘(ℝ, ℝ) I (fun θ => h θ z.2) z.1 (1 : ℝ) ≠ 0)
    (hinj : ∀ θ θ' s, (θ, s) ∈ U → (θ', s) ∈ U → h θ s = h θ' s → ∃ k : ℤ, θ' = θ + k)
    {O : Set (M × M)} (hO : IsOpen O) (hdiag : ∀ x, (x, x) ∈ O) :
    ∃ h' : ℝ → ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry h') ∧
      (∀ θ s, h' (θ + 1) s = h' θ s) ∧ (∀ θ s, f (h' θ s) = c) ∧
      (∀ θ s, (θ, s) ∈ P → h' θ s = h θ s) ∧ (∀ θ s, (h θ s, h' θ s) ∈ O) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, isEmbeddedSlice I h' s := by
  have hIntPer : ∀ S : Set (ℝ × ℝ), (∀ θ s, (θ, s) ∈ S ↔ (θ + 1, s) ∈ S) →
      ∀ (k : ℤ) (θ s : ℝ), (θ, s) ∈ S ↔ (θ + (k : ℝ), s) ∈ S := by
    intro S hS k
    induction k using Int.induction_on with
    | zero => intro θ s; simp
    | succ i ih =>
      intro θ s
      rw [ih θ s, hS (θ + ((i : ℤ) : ℝ)) s]
      push_cast
      rw [add_assoc]
    | pred i ih =>
      intro θ s
      rw [ih θ s, hS (θ + ((-(i : ℤ) - 1 : ℤ) : ℝ)) s]
      push_cast
      ring_nf
  have hhInt : ∀ (k : ℤ) (θ s : ℝ), h (θ + (k : ℝ)) s = h θ s := by
    intro k θ s
    have hp : Function.Periodic (fun θ => h θ s) 1 := fun θ => hper θ s
    have := hp.int_mul k θ
    simpa using this
  have hcont : Continuous (uncurry h) := hsm.continuous
  obtain ⟨Q₀, hQ₀c, hQ₀per, hQ₀U, -, hPQ₀, hQ₀b⟩ :=
    exists_periodic_closed_nhds hP hU hPU hPper hUper
  have hembQ₀ : isEmbeddedOn I h Q₀ :=
    ⟨fun z hz => himm z (hQ₀U hz), fun θ θ' s hθ hθ' he => hinj θ θ' s (hQ₀U hθ) (hQ₀U hθ') he⟩
  have hch : ∀ x : M, ∀ _hx : f x = c, ∃ ψ : OpenPartialHomeomorph (Fin n → ℝ) M,
      ∃ i₀ : Fin n, x ∈ ψ.target ∧ ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source ∧
        ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target ∧
        ∀ y ∈ ψ.source, f (ψ y) = c + y i₀ := by
    intro x hx
    obtain ⟨ψ, i₀, r, hr, hball, hψ0, hψ, hψs, hψf⟩ := exists_levelChart hf (hreg x hx)
    refine ⟨ψ, i₀, ?_, hψ, hψs, ?_⟩
    · rw [← hψ0]
      exact ψ.map_source (hball (Metric.mem_ball_self hr))
    · intro y hy
      rw [hψf y hy, hx]
  choose ψ i₀ hψx hψ hψs hψf using hch
  let G : M → Set M := fun x => if hx : f x = c then (ψ x hx).target else univ
  have hG : ∀ x, IsOpen (G x) ∧ x ∈ G x := by
    intro x
    by_cases hx : f x = c
    · simp only [G, hx, ↓reduceDIte]
      exact ⟨(ψ x hx).open_target, hψx x hx⟩
    · simp only [G, hx, ↓reduceDIte]
      exact ⟨isOpen_univ, mem_univ x⟩
  let K : Set (ℝ × ℝ) := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ interior Q₀
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).diff isOpen_interior
  have hKW : K ⊆ Pᶜ := by
    rintro z ⟨⟨hz1, hz2⟩, hzQ⟩ hzP
    apply hzQ
    apply hPQ₀
    refine ⟨hzP, mem_univ _, ?_, ?_⟩
    · linarith [hz2.1]
    · linarith [hz2.2]
  obtain ⟨m, C, N, x, hCc, hNo, hCN, hNc, hNW, hNG, hNdiam, hxK, hKcov⟩ :=
    exists_small_cells hcont G hG hK hP.isOpen_compl hKW (by norm_num : (0 : ℝ) < 1 / 2)
  have hxlev : ∀ j, f (x j) = c := by
    intro j
    obtain ⟨z, -, hz⟩ := hxK j
    rw [← hz]
    exact hlev z.1 z.2
  have hGx : ∀ j, G (x j) = (ψ (x j) (hxlev j)).target := by
    intro j
    simp only [G, hxlev j, ↓reduceDIte]
  set τ : ℝ × ℝ := ((1 : ℝ), (0 : ℝ)) with hτdef
  have hτ : τ ≠ 0 := by
    intro h0
    have := congrArg Prod.fst h0
    simp [τ] at this
  have hkτ : ∀ k : ℤ, (k : ℝ) • τ = ((k : ℝ), (0 : ℝ)) := by
    intro k
    simp [τ]
  let T : Fin m → Set (ℝ × ℝ) := fun j => {z | ∃ k : ℤ, z + ((k : ℝ), (0 : ℝ)) ∈ C j}
  have hTc : ∀ j, IsClosed (T j) := by
    intro j
    have ho := isOpen_periodic_imp (X := Unit) hτ (hCc j) (isOpen_empty : IsOpen (∅ : Set Unit))
    have ho' := ho.preimage (continuous_id.prodMk continuous_const : Continuous
      (fun z : ℝ × ℝ => (z, ())))
    rw [← isOpen_compl_iff]
    convert ho' using 1
    ext z
    simp [T, hkτ]
  have hTper : ∀ j, ∀ θ s, (θ, s) ∈ T j ↔ (θ + 1, s) ∈ T j := by
    intro j θ s
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      convert hk using 1
      ext <;> simp
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      convert hk using 1
      ext <;> simp
      ring
  have hTb : ∀ j, IsCompact (T j ∩ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    intro j
    refine IsCompact.of_isClosed_subset ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod ((hCc j).image continuous_snd))
      ((hTc j).inter (isClosed_Icc.prod isClosed_univ)) ?_
    rintro z ⟨⟨k, hk⟩, hz1, -⟩
    refine ⟨hz1, z + ((k : ℝ), (0 : ℝ)), hk, ?_⟩
    simp
  let 𝒪₀ : Set ((ℝ × ℝ) × M) := {q | (h q.1.1 q.1.2, q.2) ∈ O} ∩
    ⋂ j : Fin m, {q | (∃ k : ℤ, q.1 + (k : ℝ) • τ ∈ closure (N j)) →
      q.2 ∈ (ψ (x j) (hxlev j)).target}
  have h𝒪₀ : IsOpen 𝒪₀ := by
    refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun j => ?_)
    · exact hO.preimage ((hcont.comp continuous_fst).prodMk continuous_snd)
    · exact isOpen_periodic_imp hτ (hNc j) (ψ (x j) (hxlev j)).open_target
  have h𝒪₀per : ∀ z y, (z, y) ∈ 𝒪₀ ↔ (z + ((1 : ℝ), (0 : ℝ)), y) ∈ 𝒪₀ := by
    intro z y
    have hshift : ∀ K' : Set (ℝ × ℝ), (∃ k : ℤ, z + (k : ℝ) • τ ∈ K') ↔
        (∃ k : ℤ, z + ((1 : ℝ), (0 : ℝ)) + (k : ℝ) • τ ∈ K') := by
      intro K'
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        convert hk using 1
        ext <;> simp [τ]
      · rintro ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        convert hk using 1
        ext <;> simp [τ]
        ring
    have hh1 : h (z + ((1 : ℝ), (0 : ℝ))).1 (z + ((1 : ℝ), (0 : ℝ))).2 = h z.1 z.2 := by
      simpa using hper z.1 z.2
    simp only [𝒪₀, mem_inter_iff, mem_ofPred_eq, mem_iInter, hh1, ← hshift]
  have hgraph₀ : ∀ z : ℝ × ℝ, (z, h z.1 z.2) ∈ 𝒪₀ := by
    intro z
    refine ⟨hdiag _, mem_iInter.2 fun j => ?_⟩
    rintro ⟨k, hk⟩
    have hmem := hNG j (mem_image_of_mem (uncurry h) hk)
    rw [hGx j] at hmem
    have he : uncurry h (z + (k : ℝ) • τ) = h z.1 z.2 := by
      have hz' : z + (k : ℝ) • τ = (z.1 + (k : ℝ), z.2) := by
        rw [hkτ k]
        ext <;> simp
      rw [hz']
      exact hhInt k z.1 z.2
    rwa [he] at hmem
  have main : ∀ j : ℕ, j ≤ m → ∃ h' : ℝ → ℝ → M, ∃ Q : Set (ℝ × ℝ),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry h') ∧ (∀ θ s, h' (θ + 1) s = h' θ s) ∧
      (∀ θ s, f (h' θ s) = c) ∧ (∀ θ s, (θ, s) ∈ P → h' θ s = h θ s) ∧
      (∀ z : ℝ × ℝ, (z, h' z.1 z.2) ∈ 𝒪₀) ∧ IsClosed Q ∧
      (∀ θ s, (θ, s) ∈ Q ↔ (θ + 1, s) ∈ Q) ∧
      IsCompact (Q ∩ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧ Q₀ ⊆ Q ∧
      (∀ i : Fin m, i.val < j → T i ⊆ Q) ∧ isEmbeddedOn I h' Q := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨h, Q₀, hsm, hper, hlev, fun _ _ _ => rfl, hgraph₀, hQ₀c, hQ₀per, hQ₀b,
        subset_rfl, fun i hi => absurd hi (Nat.not_lt_zero _), hembQ₀⟩
    | succ j ih =>
      intro hj
      obtain ⟨hj', Q, hsmj, hperj, hlevj, hPj, hgrj, hQc, hQper, hQb, hQ₀Q, hTQ, hembj⟩ :=
        ih (Nat.le_of_succ_le hj)
      let i : Fin m := ⟨j, hj⟩
      have hNψ : ∀ z ∈ closure (N i), hj' z.1 z.2 ∈ (ψ (x i) (hxlev i)).target := by
        intro z hz
        have hm := (hgrj z).2
        rw [mem_iInter] at hm
        exact hm i ⟨0, by simpa using hz⟩
      have hNθ : ∀ z ∈ closure (N i), ∀ z' ∈ closure (N i), |z.1 - z'.1| < 1 / 2 := by
        intro z hz z' hz'
        have h1 := hNdiam i z hz z' hz'
        have h2 := norm_fst_le (z - z')
        rw [Prod.fst_sub, Real.norm_eq_abs] at h2
        linarith
      obtain ⟨h'', hsm'', hper'', hlev'', hoff'', hgr'', hemb''⟩ :=
        exists_embedded_cell_step h5 hf hsmj hperj hlevj hQc hQper hQb hembj
          (ψ (x i) (hxlev i)) (i₀ (x i) (hxlev i)) (hψ (x i) (hxlev i)) (hψs (x i) (hxlev i))
          (hψf (x i) (hxlev i)) (hCc i) (hNo i) (hCN i) (hNc i) hNθ hNψ h𝒪₀ h𝒪₀per hgrj
      refine ⟨h'', Q ∪ T i, hsm'', hper'', hlev'', ?_, hgr'', hQc.union (hTc i), ?_, ?_,
        subset_union_of_subset_left hQ₀Q _, ?_, hemb''⟩
      · intro θ s hθs
        rw [← hPj θ s hθs]
        refine hoff'' (θ, s) fun k hk => ?_
        have hPk : (θ + (k : ℝ), s) ∈ P := (hIntPer P hPper k θ s).1 hθs
        have he : (θ, s) + ((k : ℝ), (0 : ℝ)) = (θ + (k : ℝ), s) := by
          ext <;> simp
        rw [he] at hk
        exact hNW i (subset_closure hk) hPk
      · intro θ s
        rw [mem_union, mem_union, hQper θ s, hTper i θ s]
      · rw [union_inter_distrib_right]
        exact hQb.union (hTb i)
      · intro i' hi'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | heq
        · exact subset_union_of_subset_left (hTQ i' hlt) _
        · have : i' = i := Fin.ext heq
          rw [this]
          exact subset_union_right
  obtain ⟨h', Q, hsm', hper', hlev', hP', hgr', -, hQper, -, hQ₀Q, hTQ, hemb'⟩ := main m le_rfl
  have hcov : ∀ θ s, s ∈ Icc (0 : ℝ) 1 → (θ, s) ∈ Q := by
    intro θ s hs
    have hfr : (Int.fract θ, s) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
      ⟨⟨Int.fract_nonneg θ, (Int.fract_lt_one θ).le⟩, hs⟩
    have hθ : Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ) = θ := by
      rw [← Int.self_sub_floor]
      ring
    by_cases hint : (Int.fract θ, s) ∈ interior Q₀
    · apply hQ₀Q
      have := (hIntPer Q₀ hQ₀per ⌊θ⌋ (Int.fract θ) s).1 (interior_subset hint)
      rwa [hθ] at this
    · have hK' : (Int.fract θ, s) ∈ K := ⟨hfr, hint⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hKcov hK')
      apply hTQ j j.isLt
      refine ⟨-⌊θ⌋, ?_⟩
      have he : (θ, s) + (((-⌊θ⌋ : ℤ) : ℝ), (0 : ℝ)) = (Int.fract θ, s) := by
        ext
        · simp only [Prod.fst_add, Int.cast_neg]
          rw [← Int.self_sub_floor]
          ring
        · simp
      rw [he]
      exact interior_subset hj
  refine ⟨h', hsm', hper', hlev', hP', fun θ s => (hgr' (θ, s)).1, fun s hs => ⟨?_, ?_⟩⟩
  · intro θ
    exact hemb'.1 (θ, s) (hcov θ s hs)
  · intro θ θ' he
    exact hemb'.2 θ θ' s (hcov θ s hs) (hcov θ' s hs) he

end Engines

end

end IndexOnePartner

end DifferentialGeometry.Topology
