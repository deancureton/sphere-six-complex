module

public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.IntegralCurveFromJointC1
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldFlowFamily
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.BanachIC
public import DifferentialGeometry.Analysis.ODE.Flow.Defs
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section


noncomputable section
open Set Function Filter Metric Bundle
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.Analysis.ODE

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
theorem manifoldFlow_contMDiffOn_of_jointContDiffOn
    (p₀ : M) (Φ_E : E × ℝ → E) {ρ T t₀ : ℝ}
    (U : Set M) (hUsub : U ⊆ (chartAt H p₀).source)
    (hUball : ∀ p ∈ U, I ((chartAt H p₀) p) ∈ Metric.ball (I ((chartAt H p₀) p₀)) ρ)
    (hΦE_smooth : ContDiffOn ℝ ∞ Φ_E
      (Metric.ball (I ((chartAt H p₀) p₀)) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)))
    (htgt : ∀ p ∈ U, ∀ s ∈ Set.Ioo (t₀ - T) (t₀ + T),
      Φ_E (I ((chartAt H p₀) p), s) ∈ (extChartAt I p₀).target) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (extChartAt I p₀).symm (Φ_E (I ((chartAt H p₀) q.2), q.1)))
      (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) := by
  set s : Set (ℝ × M) := Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U with hs
  have hcoord : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => I ((chartAt H p₀) q.2)) s := by
    have hext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I p₀) (chartAt H p₀).source :=
      contMDiffOn_extChartAt
    have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
        ((extChartAt I p₀) ∘ Prod.snd) s :=
      hext.comp contMDiffOn_snd (fun q hq => hUsub hq.2)
    refine hcomp.congr ?_
    intro q _
    simp only [Function.comp_apply, extChartAt_coe, Function.comp_apply]
  have hh : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E × ℝ) ∞
      (fun q : ℝ × M => (I ((chartAt H p₀) q.2), q.1)) s :=
    hcoord.prodMk_space contMDiffOn_fst
  have hΦ : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞ Φ_E
      (Metric.ball (I ((chartAt H p₀) p₀)) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) :=
    hΦE_smooth.contMDiffOn
  have hΦh : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Φ_E (I ((chartAt H p₀) q.2), q.1)) s := by
    have hsub : s ⊆ (fun q : ℝ × M => (I ((chartAt H p₀) q.2), q.1)) ⁻¹'
        (Metric.ball (I ((chartAt H p₀) p₀)) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := by
      intro q hq
      rw [hs] at hq
      exact Set.mk_mem_prod (hUball q.2 hq.2) hq.1
    exact hΦ.comp hh hsub
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I p₀).symm (extChartAt I p₀).target :=
    contMDiffOn_extChartAt_symm p₀
  have hsubtgt : s ⊆ (fun q : ℝ × M => Φ_E (I ((chartAt H p₀) q.2), q.1)) ⁻¹'
      (extChartAt I p₀).target := by
    intro q hq
    rw [hs] at hq
    exact htgt q.2 hq.2 q.1 hq.1
  exact hsymm.comp hΦh hsubtgt

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
theorem chart_pushforward_field_jointContDiff
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (p₀ : M) {ρ : ℝ}
    (hρ_sub : Metric.ball (extChartAt I p₀ p₀) ρ ⊆ (extChartAt I p₀).target) :
    ContDiffOn ℝ ∞
      (Function.uncurry (fun (s : ℝ) (c : E) =>
        ((trivializationAt E (TangentSpace I) p₀)
          (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2))
      ((Set.univ : Set ℝ) ×ˢ Metric.ball (extChartAt I p₀ p₀) ρ) := by
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  set e := trivializationAt E (TangentSpace I) p₀ with he
  set f : ℝ × M → TangentBundle I M :=
    fun q => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M) with hf
  set S : Set (ℝ × M) :=
    (Set.univ : Set ℝ) ×ˢ ((extChartAt I p₀).symm '' Metric.ball x₀ ρ) with hS
  have hX_on : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ f S := hX.contMDiffOn
  have hmaps : Set.MapsTo f S e.source := by
    rintro ⟨s, p⟩ hq
    obtain ⟨-, c, hc, rfl⟩ := hq
    have hcsrc : (extChartAt I p₀).symm c ∈ (chartAt H p₀).source := by
      have hmem : (extChartAt I p₀).symm c ∈ (extChartAt I p₀).source :=
        (extChartAt I p₀).map_target (hρ_sub hc)
      rwa [extChartAt_source] at hmem
    rw [he, TangentBundle.trivializationAt_source]
    exact hcsrc
  have hreading : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => (e (f q)).2) S :=
    ((e.contMDiffOn_iff hmaps).mp hX_on).2
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I p₀).symm (Metric.ball x₀ ρ) :=
    (contMDiffOn_extChartAt_symm p₀).mono hρ_sub
  have hreindex :
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (Prod.map (id : ℝ → ℝ) (extChartAt I p₀).symm)
        ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) :=
    (contMDiffOn_id (I := 𝓘(ℝ, ℝ))).prodMap hsymm
  have hsub :
      ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) ⊆
        Prod.map (id : ℝ → ℝ) (extChartAt I p₀).symm ⁻¹' S := by
    rintro ⟨s, c⟩ ⟨-, hc⟩
    exact ⟨Set.mem_univ _, Set.mem_image_of_mem _ hc⟩
  have hcomp :
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        ((fun q : ℝ × M => (e (f q)).2) ∘ Prod.map (id : ℝ → ℝ) (extChartAt I p₀).symm)
        ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) :=
    hreading.comp hreindex hsub
  have hfun :
      ((fun q : ℝ × M => (e (f q)).2) ∘ Prod.map (id : ℝ → ℝ) (extChartAt I p₀).symm)
        = Function.uncurry (fun (s : ℝ) (c : E) =>
            (e (TotalSpace.mk' E ((extChartAt I p₀).symm c)
                (X s ((extChartAt I p₀).symm c)))).2) := by
    funext q
    rfl
  rw [hfun] at hcomp
  rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp

omit [BoundarylessManifold I M] [T2Space M] in
theorem chart_pushforward_field_cutoff_globalContDiff
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (p₀ : M) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ_sub : Metric.ball (extChartAt I p₀ p₀) ρ ⊆ (extChartAt I p₀).target) :
    ∃ (G : ℝ → E → E) (ρ' : ℝ), 0 < ρ' ∧ ρ' ≤ ρ ∧
      ContDiff ℝ ∞ (Function.uncurry G) ∧
      ∀ (s : ℝ), ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ',
        G s c = ((trivializationAt E (TangentSpace I) p₀)
          (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2 := by
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  set F : ℝ → E → E := fun (s : ℝ) (c : E) =>
    ((trivializationAt E (TangentSpace I) p₀)
      (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2 with hF
  have hFsmooth : ContDiffOn ℝ ∞ (Function.uncurry F)
      ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) :=
    chart_pushforward_field_jointContDiff X hX p₀ hρ_sub
  set b : ContDiffBump x₀ :=
    { rIn := ρ / 4, rOut := ρ / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith } with hb
  have hb_rIn : b.rIn = ρ / 4 := rfl
  have hb_rOut : b.rOut = ρ / 2 := rfl
  have hclosed_sub : Metric.closedBall x₀ b.rOut ⊆ Metric.ball x₀ ρ := by
    rw [hb_rOut]; exact Metric.closedBall_subset_ball (by linarith)
  refine ⟨fun (s : ℝ) (c : E) => (b c) • F s c, b.rIn, b.rIn_pos, ?_, ?_, ?_⟩
  · rw [hb_rIn]; linarith
  · have huncurry : Function.uncurry (fun (s : ℝ) (c : E) => (b c) • F s c)
        = fun q : ℝ × E => (b : E → ℝ) q.2 • F q.1 q.2 := by
      funext q; rfl
    rw [huncurry, contDiff_iff_contDiffAt]
    rintro ⟨s, c⟩
    by_cases hc : c ∈ Metric.closedBall x₀ b.rOut
    · have hc_ball : c ∈ Metric.ball x₀ ρ := hclosed_sub hc
      have hmem : ((s, c) : ℝ × E) ∈ (Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ :=
        ⟨Set.mem_univ _, hc_ball⟩
      have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) :=
        isOpen_univ.prod Metric.isOpen_ball
      have hF_at : ContDiffAt ℝ ∞ (Function.uncurry F) (s, c) :=
        hFsmooth.contDiffAt (hopen.mem_nhds hmem)
      have hb_at : ContDiffAt ℝ ∞ (fun q : ℝ × E => (b : E → ℝ) q.2) (s, c) :=
        (b.contDiff.comp_contDiffAt (s, c) contDiffAt_snd)
      exact hb_at.smul hF_at
    · rw [Metric.mem_closedBall] at hc
      have hdist : b.rOut < dist c x₀ := not_le.mp hc
      have hopen : IsOpen {q : ℝ × E | b.rOut < dist q.2 x₀} := by
        have hcont : Continuous (fun q : ℝ × E => dist q.2 x₀) :=
          (continuous_snd.dist continuous_const)
        exact hcont.isOpen_preimage _ isOpen_Ioi
      have hmem : ((s, c) : ℝ × E) ∈ {q : ℝ × E | b.rOut < dist q.2 x₀} := hdist
      refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : ℝ × E => (0 : E))
        contDiffAt_const ?_
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
      intro q hq
      have hq' : b.rOut ≤ dist q.2 x₀ := le_of_lt hq
      have hb0 : (b : E → ℝ) q.2 = 0 := b.zero_of_le_dist hq'
      change (b : E → ℝ) q.2 • F q.1 q.2 = 0
      rw [hb0, zero_smul]
  · intro s c hc
    have hc_closed : c ∈ Metric.closedBall x₀ b.rIn :=
      Metric.ball_subset_closedBall hc
    have hb1 : (b : E → ℝ) c = 1 := b.one_of_mem_closedBall hc_closed
    change (b c) • F s c = F s c
    rw [hb1, one_smul]

omit [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] in
theorem chartflow_confined_to_agreementBall
    (p₀ : M) (Φ_E : E × ℝ → E) {ρ ρ' T t₀ : ℝ} (hρ' : 0 < ρ') (hρ'_le : ρ' ≤ ρ)
    (hT : 0 < T)
    (hΦE_cont : ContinuousOn Φ_E
      (Metric.ball (extChartAt I p₀ p₀) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)))
    (hinit : ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ, Φ_E (c, t₀) = c) :
    ∃ (ρ'' T' : ℝ), 0 < ρ'' ∧ 0 < T' ∧ ρ'' ≤ ρ' ∧ T' ≤ T ∧
      ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ'', ∀ s ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        Φ_E (c, s) ∈ Metric.ball (extChartAt I p₀ p₀) ρ' := by
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  set D : Set (E × ℝ) := Metric.ball x₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T) with hD
  have hD_open : IsOpen D := (Metric.isOpen_ball).prod isOpen_Ioo
  set ρseed : ℝ := ρ' / 2 with hρseed
  have hρseed_pos : 0 < ρseed := by rw [hρseed]; linarith
  have hρseed_lt : ρseed < ρ' := by rw [hρseed]; linarith
  have hseed_sub_ball' : Metric.closedBall x₀ ρseed ⊆ Metric.ball x₀ ρ' :=
    Metric.closedBall_subset_ball hρseed_lt
  have hseed_sub_ballρ : Metric.closedBall x₀ ρseed ⊆ Metric.ball x₀ ρ :=
    Metric.closedBall_subset_ball (lt_of_lt_of_le hρseed_lt hρ'_le)
  set O : Set (E × ℝ) := D ∩ Φ_E ⁻¹' Metric.ball x₀ ρ' with hO
  have hO_open : IsOpen O :=
    hΦE_cont.isOpen_inter_preimage hD_open Metric.isOpen_ball
  have ht₀_mem : t₀ ∈ Set.Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  have hslice_sub : Metric.closedBall x₀ ρseed ×ˢ ({t₀} : Set ℝ) ⊆ O := by
    rw [Set.prod_subset_iff]
    intro c hc s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have hc_ballρ : c ∈ Metric.ball x₀ ρ := hseed_sub_ballρ hc
    have hc_ball' : c ∈ Metric.ball x₀ ρ' := hseed_sub_ball' hc
    refine ⟨⟨hc_ballρ, ht₀_mem⟩, ?_⟩
    rw [Set.mem_preimage, hinit c hc_ballρ]
    exact hc_ball'
  obtain ⟨u, v, hu_open, hv_open, hseed_u, ht₀_v, huv_sub⟩ :=
    generalized_tube_lemma (isCompact_closedBall x₀ ρseed) isCompact_singleton
      hO_open hslice_sub
  have hx₀_u : x₀ ∈ u := hseed_u (Metric.mem_closedBall_self hρseed_pos.le)
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp hu_open x₀ hx₀_u
  have ht₀_v' : t₀ ∈ v := ht₀_v (Set.mem_singleton t₀)
  obtain ⟨l, w, ht₀_lw, hlw_sub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hv_open.mem_nhds ht₀_v')
  set δ : ℝ := min (t₀ - l) (w - t₀) with hδ
  have hδ_pos : 0 < δ := lt_min (by linarith [ht₀_lw.1]) (by linarith [ht₀_lw.2])
  have hIoo_δ_sub_v : Set.Ioo (t₀ - δ) (t₀ + δ) ⊆ v := by
    refine subset_trans (fun t ht => ?_) hlw_sub
    refine ⟨lt_of_le_of_lt ?_ ht.1, lt_of_lt_of_le ht.2 ?_⟩
    · have hle : δ ≤ t₀ - l := min_le_left _ _
      linarith
    · have hle : δ ≤ w - t₀ := min_le_right _ _
      linarith
  refine ⟨min ε ρ', min δ T, ?_, ?_, min_le_right _ _, min_le_right _ _, ?_⟩
  · exact lt_min hε_pos hρ'
  · exact lt_min hδ_pos hT
  intro c hc s hs
  have hc_u : c ∈ u := by
    apply hε_sub
    rw [Metric.mem_ball] at hc ⊢
    exact lt_of_lt_of_le hc (min_le_left _ _)
  have hs_v : s ∈ v := by
    apply hIoo_δ_sub_v
    refine ⟨?_, ?_⟩
    · have hle : min δ T ≤ δ := min_le_left _ _
      have := hs.1; linarith
    · have hle : min δ T ≤ δ := min_le_left _ _
      have := hs.2; linarith
  have hcs_O : (c, s) ∈ O := huv_sub (Set.mk_mem_prod hc_u hs_v)
  exact hcs_O.2

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] in
theorem chartODE_genuineF_on_Ioo
    (p₀ : M) (G F : ℝ → E → E) (Φ_E : E × ℝ → E) {ρ'' ρ' T' t₀ : ℝ} (r : ℝ≥0) {tmin tmax : ℝ}
    (hρ''_le : ρ'' ≤ ρ')
    (hflow : IsLocalFlow G t₀ (extChartAt I p₀ p₀) r tmin tmax Φ_E)
    (hIoo_sub : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Icc tmin tmax)
    (hball_sub : Metric.ball (extChartAt I p₀ p₀) ρ' ⊆ Metric.closedBall (extChartAt I p₀ p₀)
      (r : ℝ))
    (hGF : ∀ (s : ℝ), ∀ y ∈ Metric.ball (extChartAt I p₀ p₀) ρ', G s y = F s y)
    (hconf : ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ'', ∀ s ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        Φ_E (c, s) ∈ Metric.ball (extChartAt I p₀ p₀) ρ') :
    ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ'', ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
      HasDerivWithinAt (fun s => Φ_E (c, s)) (F t (Φ_E (c, t))) (Set.Ioo (t₀ - T') (t₀ + T'))
        t := by
  intro c hc t ht
  have hc_closed : c ∈ Metric.closedBall (extChartAt I p₀ p₀) (r : ℝ) :=
    hball_sub (Metric.ball_subset_ball hρ''_le hc)
  have hderiv_Icc :
      HasDerivWithinAt (fun s => Φ_E (c, s)) (G t (Φ_E (c, t)))
        (Set.Icc tmin tmax) t :=
    hflow.hasDerivWithinAt c hc_closed t (hIoo_sub ht)
  have hderiv_Ioo :
      HasDerivWithinAt (fun s => Φ_E (c, s)) (G t (Φ_E (c, t)))
        (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    hderiv_Icc.mono hIoo_sub
  have hGF_pt : G t (Φ_E (c, t)) = F t (Φ_E (c, t)) :=
    hGF t (Φ_E (c, t)) (hconf c hc t ht)
  exact hGF_pt ▸ hderiv_Ioo

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
theorem field_form_identity_trivreading_eq_chartvelocity
    (X : ℝ → ∀ x : M, TangentSpace I x) (p₀ : M) (s : ℝ) (c : E) :
    ((trivializationAt E (TangentSpace I) p₀)
        (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2
      = tangentCoordChange I ((extChartAt I p₀).symm c) p₀ ((extChartAt I p₀).symm c)
          (X s ((extChartAt I p₀).symm c)) := rfl

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
theorem pushforward_velocity_cancellation (p₀ q : M)
    (hq : q ∈ (extChartAt I p₀).source) (v : E) :
    (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (extChartAt I p₀ q))
        (tangentCoordChange I q p₀ q v) = v := by
  have hqq : q ∈ (extChartAt I q).source := mem_extChartAt_source q
  have hTc₀ : (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm) (extChartAt I q q) = extChartAt I p₀
    q := by
    simp only [Function.comp_apply, (extChartAt I q).left_inv hqq]
  have hg : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I)
      (extChartAt I p₀ q) := mdifferentiableWithinAt_extChartAt_symm
        ((extChartAt I p₀).map_source hq)
  have hfd : HasFDerivWithinAt (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm)
      (tangentCoordChange I q p₀ q) (Set.range I) (extChartAt I q q) :=
    hasFDerivWithinAt_tangentCoordChange (I := I) (x := q) (y := p₀) (z := q) ⟨hqq, hq⟩
  have hf : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm) (Set.range I) (extChartAt I q q) :=
    hfd.differentiableWithinAt.mdifferentiableWithinAt
  have hpre : Set.range I ⊆ (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm) ⁻¹' Set.range I := by
    intro y _
    simp only [Set.mem_preimage, Function.comp_apply, extChartAt_coe]
    exact Set.mem_range_self _
  have hU : UniqueMDiffWithinAt 𝓘(ℝ, E) (Set.range I) (extChartAt I q q) :=
    (I.uniqueMDiffOn) _ (extChartAt_target_subset_range q (mem_extChartAt_target q))
  have hchain := mfderivWithin_comp_of_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := I)
    (g := (extChartAt I p₀).symm) (f := extChartAt I p₀ ∘ ⇑(extChartAt I q).symm)
    (s := Set.range I) (u := Set.range I) (x := extChartAt I q q)
    (y := extChartAt I p₀ q) hg hf hpre hU hTc₀
  have hAmem : (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' (extChartAt I p₀).source
      ∈ 𝓝[Set.range I] (extChartAt I q q) := by
    refine Filter.inter_mem (extChartAt_target_mem_nhdsWithin q) ?_
    have hsrc : (extChartAt I p₀).source ∈ 𝓝 q :=
      (isOpen_extChartAt_source p₀).mem_nhds hq
    have hpre' := extChartAt_preimage_mem_nhdsWithin' (I := I) (x := q) (x' := q)
      (s := Set.univ) (t := (extChartAt I p₀).source) (mem_extChartAt_source q)
      (by simpa using hsrc)
    simpa only [Set.preimage_univ, Set.univ_inter] using hpre'
  have heqOn : ⇑(extChartAt I q).symm
      =ᶠ[𝓝[Set.range I] (extChartAt I q q)]
        ((extChartAt I p₀).symm ∘ (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm)) := by
    filter_upwards [hAmem] with y hy
    obtain ⟨_, hy₂⟩ := hy
    simp only [Set.mem_preimage] at hy₂
    simp only [Function.comp_apply, (extChartAt I p₀).left_inv hy₂]
  have heqDeriv :
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I q).symm (Set.range I) (extChartAt I q q)
        = mfderivWithin 𝓘(ℝ, E) I
            ((extChartAt I p₀).symm ∘ (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm))
            (Set.range I) (extChartAt I q q) :=
    heqOn.mfderivWithin_eq
      (by simp only [Function.comp_apply, (extChartAt I q).left_inv hqq,
        (extChartAt I p₀).left_inv hq])
  have hid := mfderivWithin_range_extChartAt_symm (𝕜 := ℝ) (I := I) (x := q)
  have hTderiv :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm)
        (Set.range I) (extChartAt I q q) = tangentCoordChange I q p₀ q := by
    rw [mfderivWithin_eq_fderivWithin]
    exact hfd.fderivWithin (hU.uniqueDiffWithinAt)
  rw [heqDeriv, hchain, hTderiv] at hid
  rw [(extChartAt I q).left_inv hqq, (extChartAt I p₀).left_inv hq] at hid
  have hv := congrArg (fun L => L v) hid
  rw [(extChartAt I p₀).left_inv hq]
  let h :
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm
        (Set.range I) (extChartAt I p₀ q))
          (tangentCoordChange I q p₀ q v) = v := hv
  exact h

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
theorem chartFlow_eq_integralCurve_on
    (X : ℝ → ∀ x : M, TangentSpace I x) (p₀ : M)
    (F : ℝ → E → E) (ΦE : E × ℝ → E) (U : Set M) {a b : ℝ}
    (hchartODE : ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt (fun s => ΦE (extChartAt I p₀ p, s))
        (F t (ΦE (extChartAt I p₀ p, t))) (Set.Ioo a b) t)
    (hF : ∀ (s : ℝ) (c : E), F s c =
        tangentCoordChange I ((extChartAt I p₀).symm c) p₀
          ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))
    (hconf : ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo a b,
      ΦE (extChartAt I p₀ p, t) ∈ (extChartAt I p₀).target)
    :
    ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)))
        (Set.Ioo a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (X t ((extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t))))) := by
  intro p hp t ht
  set u : ℝ → E := fun s => ΦE (extChartAt I p₀ p, s) with hu
  have htgt_t : u t ∈ (extChartAt I p₀).target := hconf p hp t ht
  set q : M := (extChartAt I p₀).symm (u t) with hq_def
  have hq_source : q ∈ (extChartAt I p₀).source := (extChartAt I p₀).map_target htgt_t
  have hq_round : extChartAt I p₀ q = u t := (extChartAt I p₀).right_inv htgt_t
  have hconf_range : u ⁻¹' (Set.range I) ∈ 𝓝[Set.Ioo a b] t := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro s hs
    exact extChartAt_target_subset_range p₀ (hconf p hp s hs)
  have hd : HasDerivWithinAt u (F t (u t)) (Set.Ioo a b) t := hchartODE p hp t ht
  have hbridge :
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => (extChartAt I p₀).symm (u s)) (Set.Ioo a b) t
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (u t)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (F t (u t)))) :=
    chartCoord_hasDerivWithinAt_to_manifold_hasMFDerivWithinAt
      (I := I) p₀ u (Set.Ioo a b) t (F t (u t)) htgt_t hconf_range hd
  have hcancel :
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (u t)) (F t (u t))
        = X t q := by
    rw [hF t (u t)]
    rw [← hq_def, ← hq_round]
    exact pushforward_velocity_cancellation (I := I) p₀ q hq_source (X t q)
  let w : TangentSpace 𝓘(ℝ, E) (u t) := F t (u t)
  have hw :
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (u t)) w =
        X t q := hcancel
  have hvel :
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (u t)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).smulRight w)
        = (1 : ℝ →L[ℝ] ℝ).smulRight (X t q) :=
    ContinuousLinearMap.ext fun r => by
      change (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm
        (Set.range I) (u t)) (r • w) = r • X t q
      rw [map_smul, hw]
  change HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
    (fun s => (extChartAt I p₀).symm (u s)) (Set.Ioo a b) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t q))
  rw [← hvel]
  let h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s => (extChartAt I p₀).symm (u s)) (Set.Ioo a b) t
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (u t)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).smulRight w)) := hbridge
  exact h

omit [BoundarylessManifold I M] [T2Space M] in
theorem local_flow_jointSmooth_and_integralCurve [CompleteSpace E] [I.Boundaryless]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (t₀ : ℝ) (p₀ : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hp₀ : p₀ ∈ U) (T : ℝ) (_hT : 0 < T)
      (Φ : M → ℝ → M),
      (∀ p ∈ U, Φ p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) ∧
      (∀ p ∈ U, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t)))) := by
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  have hx₀_target : x₀ ∈ (extChartAt I p₀).target := by
    rw [hx₀]; exact (extChartAt I p₀).map_source (mem_extChartAt_source p₀)
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_extChartAt_target p₀) x₀ hx₀_target
  obtain ⟨G, ρ', hρ'_pos, hρ'_le, hG_smooth, hGF⟩ :=
    chart_pushforward_field_cutoff_globalContDiff X hX p₀ hρ_pos hρ_sub
  obtain ⟨r, ε, hr_pos, hε_pos, ΦE, hflow, ρ_E, T_E, hρE_pos, hTE_pos, hρE_le_r, hTE_le_ε,
      hΦE_smooth⟩ :=
    exists_isLocalFlow_contDiffOn_top (f := G) (t₀ := t₀) (x₀ := x₀) hG_smooth
  set ρ'ₒₚ : ℝ := min ρ' ρ_E with hρ'ₒₚ
  have hρ'ₒₚ_pos : 0 < ρ'ₒₚ := lt_min hρ'_pos hρE_pos
  have hρ'ₒₚ_le_ρ' : ρ'ₒₚ ≤ ρ' := min_le_left _ _
  have hρ'ₒₚ_le_ρE : ρ'ₒₚ ≤ ρ_E := min_le_right _ _
  have hρ'ₒₚ_le_r : ρ'ₒₚ ≤ (r : ℝ) := le_trans hρ'ₒₚ_le_ρE hρE_le_r
  have hΦE_cont : ContinuousOn ΦE
      (Metric.ball x₀ ρ_E ×ˢ Set.Ioo (t₀ - T_E) (t₀ + T_E)) :=
    hΦE_smooth.continuousOn
  have hinit_ρE : ∀ c ∈ Metric.ball x₀ ρ_E, ΦE (c, t₀) = c := by
    intro c hc
    have hc_cb : c ∈ Metric.closedBall x₀ (r : ℝ) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hρE_le_r hc)
    exact hflow.apply_initial c hc_cb
  obtain ⟨ρ'', T', hρ''_pos, hT'_pos, hρ''_le, hT'_le, hconf⟩ :=
    chartflow_confined_to_agreementBall (I := I) p₀ ΦE
      (ρ := ρ_E) (ρ' := ρ'ₒₚ) (T := T_E) (t₀ := t₀)
      hρ'ₒₚ_pos hρ'ₒₚ_le_ρE hTE_pos hΦE_cont hinit_ρE
  have hρ''_le_r : ρ'' ≤ (r : ℝ) := le_trans hρ''_le hρ'ₒₚ_le_r
  set F : ℝ → E → E := fun (s : ℝ) (c : E) =>
    ((trivializationAt E (TangentSpace I) p₀)
      (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2 with hF
  have hGF_op : ∀ (s : ℝ), ∀ y ∈ Metric.ball x₀ ρ'ₒₚ, G s y = F s y := by
    intro s y hy
    have hy' : y ∈ Metric.ball x₀ ρ' := Metric.ball_subset_ball hρ'ₒₚ_le_ρ' hy
    exact hGF s y hy'
  have hball_sub : Metric.ball x₀ ρ'ₒₚ ⊆ Metric.closedBall x₀ (r : ℝ) := by
    intro y hy
    exact Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ'ₒₚ_le_r hy)
  have hT'_le_ε : T' ≤ ε := le_trans hT'_le hTE_le_ε
  have hIoo_sub : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Icc (t₀ - ε) (t₀ + ε) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hchartODE_raw :
      ∀ c ∈ Metric.ball x₀ ρ'', ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasDerivWithinAt (fun s => ΦE (c, s)) (F t (ΦE (c, t)))
          (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    chartODE_genuineF_on_Ioo (I := I) p₀ G F ΦE r
      (hρ''_le := hρ''_le) (hflow := hflow) (hIoo_sub := hIoo_sub)
      (hball_sub := hball_sub) (hGF := hGF_op) (hconf := hconf)
  set U : Set M := (extChartAt I p₀).source ∩ (extChartAt I p₀) ⁻¹' (Metric.ball x₀ ρ'') with hU
  set Φ : M → ℝ → M := fun p s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)) with hΦ
  have hU_open : IsOpen U :=
    (continuousOn_extChartAt p₀).isOpen_inter_preimage
      (isOpen_extChartAt_source p₀) Metric.isOpen_ball
  have hp₀_U : p₀ ∈ U := by
    refine ⟨mem_extChartAt_source p₀, ?_⟩
    rw [Set.mem_preimage, ← hx₀]
    exact Metric.mem_ball_self hρ''_pos
  have hU_source : U ⊆ (extChartAt I p₀).source := Set.inter_subset_left
  have hU_ball : ∀ p ∈ U, extChartAt I p₀ p ∈ Metric.ball x₀ ρ'' := fun p hp => hp.2
  have hchartODE :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasDerivWithinAt (fun s => ΦE (extChartAt I p₀ p, s))
          (F t (ΦE (extChartAt I p₀ p, t))) (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    fun p hp t ht => hchartODE_raw (extChartAt I p₀ p) (hU_ball p hp) t ht
  have hconf_target :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        ΦE (extChartAt I p₀ p, t) ∈ (extChartAt I p₀).target := by
    intro p hp t ht
    have hmem : ΦE (extChartAt I p₀ p, t) ∈ Metric.ball x₀ ρ'ₒₚ :=
      hconf (extChartAt I p₀ p) (hU_ball p hp) t ht
    have hsub_ρ : Metric.ball x₀ ρ'ₒₚ ⊆ Metric.ball x₀ ρ :=
      Metric.ball_subset_ball (le_trans hρ'ₒₚ_le_ρ' hρ'_le)
    exact hρ_sub (hsub_ρ hmem)
  have hF_id : ∀ (s : ℝ) (c : E), F s c =
      tangentCoordChange I ((extChartAt I p₀).symm c) p₀
        ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)) := by
    intro s c
    rw [hF]
    exact field_form_identity_trivreading_eq_chartvelocity X p₀ s c
  have hcoe : ∀ p : M, I ((chartAt H p₀) p) = extChartAt I p₀ p := by
    intro p; rw [extChartAt_coe]; rfl
  have hcoe₀ : I ((chartAt H p₀) p₀) = x₀ := by rw [hcoe, hx₀]
  have hContMDiffOn :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => (extChartAt I p₀).symm (ΦE (I ((chartAt H p₀) q.2), q.1)))
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ U) := by
    refine manifoldFlow_contMDiffOn_of_jointContDiffOn (I := I) p₀ ΦE
      (ρ := ρ'ₒₚ) (T := T') (t₀ := t₀) U ?_ ?_ ?_ ?_
    · rw [← extChartAt_source (I := I)]; exact hU_source
    · intro p hp
      rw [hcoe p, hcoe₀]
      exact Metric.ball_subset_ball hρ''_le (hU_ball p hp)
    · rw [hcoe₀]
      refine hΦE_smooth.mono (Set.prod_mono ?_ ?_)
      · exact Metric.ball_subset_ball hρ'ₒₚ_le_ρE
      · exact Set.Ioo_subset_Ioo (by linarith [hT'_le]) (by linarith [hT'_le])
    · intro p hp s hs
      rw [hcoe p]
      exact hconf_target p hp s hs
  have hContMDiffOn' :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ U) := by
    refine hContMDiffOn.congr ?_
    intro q _
    rw [hΦ, hcoe q.2]
  have hbare_within :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
          (fun s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)))
          (Set.Ioo (t₀ - T') (t₀ + T')) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (X t ((extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t))))) :=
    chartFlow_eq_integralCurve_on (I := I) X p₀ F ΦE U hchartODE hF_id hconf_target
  have hbare :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t))) := by
    intro p hp t ht
    have hnhds : Set.Ioo (t₀ - T') (t₀ + T') ∈ 𝓝 t :=
      isOpen_Ioo.mem_nhds ht
    have := (hbare_within p hp t ht).hasMFDerivAt hnhds
    rw [hΦ]; exact this
  have hΦinitial : ∀ p ∈ U, Φ p t₀ = p := by
    intro p hp
    have hcb : extChartAt I p₀ p ∈ Metric.closedBall x₀ (r : ℝ) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ''_le_r (hU_ball p hp))
    change (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t₀)) = p
    rw [hflow.apply_initial (extChartAt I p₀ p) hcb]
    exact (extChartAt I p₀).left_inv (hU_source hp)
  exact ⟨U, hU_open, hp₀_U, T', hT'_pos, Φ, hΦinitial, hContMDiffOn', hbare⟩

omit [BoundarylessManifold I M] [T2Space M] in
theorem local_flow_chartIsLocalFlow_and_realisation [CompleteSpace E] [I.Boundaryless]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (t₀ : ℝ) (p₀ : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hp₀ : p₀ ∈ U) (T : ℝ) (_hT : 0 < T)
      (Φ : M → ℝ → M)
      (f : ℝ → E → E) (x₀ : E) (r : ℝ≥0) (ε : ℝ) (ΦE : E × ℝ → E),
      ContDiff ℝ ∞ (Function.uncurry f) ∧
      x₀ = extChartAt I p₀ p₀ ∧
      0 < (r : ℝ) ∧ 0 < ε ∧
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) ΦE ∧
      (∃ (ρE TE : ℝ), 0 < ρE ∧ 0 < TE ∧
        ContDiffOn ℝ ∞ ΦE (Metric.ball x₀ ρE ×ˢ Set.Ioo (t₀ - TE) (t₀ + TE))) ∧
      (∀ p ∈ U, Φ p t₀ = p) ∧
      (∀ p ∈ U, ∀ s : ℝ,
        Φ p s = (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s))) ∧
      (∀ p ∈ U, ∀ s ∈ Set.Ioo (t₀ - T) (t₀ + T),
        ΦE (extChartAt I p₀ p, s) ∈ (extChartAt I p₀).target) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) ∧
      (∀ p ∈ U, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t)))) := by
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  have hx₀_target : x₀ ∈ (extChartAt I p₀).target := by
    rw [hx₀]; exact (extChartAt I p₀).map_source (mem_extChartAt_source p₀)
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_extChartAt_target p₀) x₀ hx₀_target
  obtain ⟨G, ρ', hρ'_pos, hρ'_le, hG_smooth, hGF⟩ :=
    chart_pushforward_field_cutoff_globalContDiff X hX p₀ hρ_pos hρ_sub
  obtain ⟨r, ε, hr_pos, hε_pos, ΦE, hflow, ρ_E, T_E, hρE_pos, hTE_pos, hρE_le_r, hTE_le_ε,
      hΦE_smooth⟩ :=
    exists_isLocalFlow_contDiffOn_top (f := G) (t₀ := t₀) (x₀ := x₀) hG_smooth
  set ρ'ₒₚ : ℝ := min ρ' ρ_E with hρ'ₒₚ
  have hρ'ₒₚ_pos : 0 < ρ'ₒₚ := lt_min hρ'_pos hρE_pos
  have hρ'ₒₚ_le_ρ' : ρ'ₒₚ ≤ ρ' := min_le_left _ _
  have hρ'ₒₚ_le_ρE : ρ'ₒₚ ≤ ρ_E := min_le_right _ _
  have hρ'ₒₚ_le_r : ρ'ₒₚ ≤ (r : ℝ) := le_trans hρ'ₒₚ_le_ρE hρE_le_r
  have hΦE_cont : ContinuousOn ΦE
      (Metric.ball x₀ ρ_E ×ˢ Set.Ioo (t₀ - T_E) (t₀ + T_E)) :=
    hΦE_smooth.continuousOn
  have hinit_ρE : ∀ c ∈ Metric.ball x₀ ρ_E, ΦE (c, t₀) = c := by
    intro c hc
    have hc_cb : c ∈ Metric.closedBall x₀ (r : ℝ) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hρE_le_r hc)
    exact hflow.apply_initial c hc_cb
  obtain ⟨ρ'', T', hρ''_pos, hT'_pos, hρ''_le, hT'_le, hconf⟩ :=
    chartflow_confined_to_agreementBall (I := I) p₀ ΦE
      (ρ := ρ_E) (ρ' := ρ'ₒₚ) (T := T_E) (t₀ := t₀)
      hρ'ₒₚ_pos hρ'ₒₚ_le_ρE hTE_pos hΦE_cont hinit_ρE
  have hρ''_le_r : ρ'' ≤ (r : ℝ) := le_trans hρ''_le hρ'ₒₚ_le_r
  set F : ℝ → E → E := fun (s : ℝ) (c : E) =>
    ((trivializationAt E (TangentSpace I) p₀)
      (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2 with hF
  have hGF_op : ∀ (s : ℝ), ∀ y ∈ Metric.ball x₀ ρ'ₒₚ, G s y = F s y := by
    intro s y hy
    exact hGF s y (Metric.ball_subset_ball hρ'ₒₚ_le_ρ' hy)
  have hball_sub : Metric.ball x₀ ρ'ₒₚ ⊆ Metric.closedBall x₀ (r : ℝ) :=
    fun y hy => Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ'ₒₚ_le_r hy)
  have hT'_le_ε : T' ≤ ε := le_trans hT'_le hTE_le_ε
  have hIoo_sub : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Icc (t₀ - ε) (t₀ + ε) :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hchartODE_raw :
      ∀ c ∈ Metric.ball x₀ ρ'', ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasDerivWithinAt (fun s => ΦE (c, s)) (F t (ΦE (c, t)))
          (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    chartODE_genuineF_on_Ioo (I := I) p₀ G F ΦE r
      (hρ''_le := hρ''_le) (hflow := hflow) (hIoo_sub := hIoo_sub)
      (hball_sub := hball_sub) (hGF := hGF_op) (hconf := hconf)
  set U : Set M := (extChartAt I p₀).source ∩ (extChartAt I p₀) ⁻¹' (Metric.ball x₀ ρ'') with hU
  set Φ : M → ℝ → M := fun p s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)) with hΦ
  have hU_open : IsOpen U :=
    (continuousOn_extChartAt p₀).isOpen_inter_preimage
      (isOpen_extChartAt_source p₀) Metric.isOpen_ball
  have hp₀_U : p₀ ∈ U := by
    refine ⟨mem_extChartAt_source p₀, ?_⟩
    rw [Set.mem_preimage, ← hx₀]
    exact Metric.mem_ball_self hρ''_pos
  have hU_source : U ⊆ (extChartAt I p₀).source := Set.inter_subset_left
  have hU_ball : ∀ p ∈ U, extChartAt I p₀ p ∈ Metric.ball x₀ ρ'' := fun p hp => hp.2
  have hchartODE :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasDerivWithinAt (fun s => ΦE (extChartAt I p₀ p, s))
          (F t (ΦE (extChartAt I p₀ p, t))) (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    fun p hp t ht => hchartODE_raw (extChartAt I p₀ p) (hU_ball p hp) t ht
  have hconf_target :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        ΦE (extChartAt I p₀ p, t) ∈ (extChartAt I p₀).target := by
    intro p hp t ht
    have hmem : ΦE (extChartAt I p₀ p, t) ∈ Metric.ball x₀ ρ'ₒₚ :=
      hconf (extChartAt I p₀ p) (hU_ball p hp) t ht
    exact hρ_sub (Metric.ball_subset_ball (le_trans hρ'ₒₚ_le_ρ' hρ'_le) hmem)
  have hF_id : ∀ (s : ℝ) (c : E), F s c =
      tangentCoordChange I ((extChartAt I p₀).symm c) p₀
        ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)) := by
    intro s c
    rw [hF]
    exact field_form_identity_trivreading_eq_chartvelocity X p₀ s c
  have hcoe : ∀ p : M, I ((chartAt H p₀) p) = extChartAt I p₀ p := by
    intro p; rw [extChartAt_coe]; rfl
  have hcoe₀ : I ((chartAt H p₀) p₀) = x₀ := by rw [hcoe, hx₀]
  have hContMDiffOn :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => (extChartAt I p₀).symm (ΦE (I ((chartAt H p₀) q.2), q.1)))
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ U) := by
    refine manifoldFlow_contMDiffOn_of_jointContDiffOn (I := I) p₀ ΦE
      (ρ := ρ'ₒₚ) (T := T') (t₀ := t₀) U ?_ ?_ ?_ ?_
    · rw [← extChartAt_source (I := I)]; exact hU_source
    · intro p hp
      rw [hcoe p, hcoe₀]
      exact Metric.ball_subset_ball hρ''_le (hU_ball p hp)
    · rw [hcoe₀]
      refine hΦE_smooth.mono (Set.prod_mono ?_ ?_)
      · exact Metric.ball_subset_ball hρ'ₒₚ_le_ρE
      · exact Set.Ioo_subset_Ioo (by linarith [hT'_le]) (by linarith [hT'_le])
    · intro p hp s hs
      rw [hcoe p]
      exact hconf_target p hp s hs
  have hContMDiffOn' :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ U) := by
    refine hContMDiffOn.congr ?_
    intro q _
    rw [hΦ, hcoe q.2]
  have hbare_within :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
          (fun s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)))
          (Set.Ioo (t₀ - T') (t₀ + T')) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (X t ((extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t))))) :=
    chartFlow_eq_integralCurve_on (I := I) X p₀ F ΦE U hchartODE hF_id hconf_target
  have hbare :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t))) := by
    intro p hp t ht
    have hnhds : Set.Ioo (t₀ - T') (t₀ + T') ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    have := (hbare_within p hp t ht).hasMFDerivAt hnhds
    rw [hΦ]; exact this
  have hΦinitial : ∀ p ∈ U, Φ p t₀ = p := by
    intro p hp
    have hcb : extChartAt I p₀ p ∈ Metric.closedBall x₀ (r : ℝ) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ''_le_r (hU_ball p hp))
    change (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t₀)) = p
    rw [hflow.apply_initial (extChartAt I p₀ p) hcb]
    exact (extChartAt I p₀).left_inv (hU_source hp)
  have hreal : ∀ p ∈ U, ∀ s : ℝ,
      Φ p s = (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)) := fun p _ s => rfl
  exact ⟨U, hU_open, hp₀_U, T', hT'_pos, Φ, G, x₀, r, ε, ΦE, hG_smooth, rfl, hr_pos, hε_pos,
    hflow, ⟨ρ_E, T_E, hρE_pos, hTE_pos, hΦE_smooth⟩, hΦinitial, hreal, hconf_target, hContMDiffOn',
    hbare⟩

end Manifold

end DifferentialGeometry.Analysis.ODE
