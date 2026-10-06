module

public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.Hartman
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

namespace DifferentialGeometry.Analysis.ODE

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem chartCoord_hasDerivWithinAt_to_manifold_hasMFDerivWithinAt
    (α : M) (u : ℝ → E) (s : Set ℝ) (t : ℝ) (velocity : E)
    (htgt_t : u t ∈ (extChartAt I α).target)
    (hconf : u ⁻¹' (Set.range I) ∈ 𝓝[s] t)
    (hd : HasDerivWithinAt u velocity s t) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s' : ℝ => (extChartAt I α).symm (u s')) s t
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I) (u t)) ∘L
        ((ContinuousLinearMap.id ℝ ℝ).smulRight velocity)) := by
  set s' : Set ℝ := s ∩ u ⁻¹' (Set.range I) with hs'
  have hu_mf : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) u s' t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight velocity) := by
    have h0 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) u s t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight velocity) := by
      let hfd : HasFDerivWithinAt u
          ((ContinuousLinearMap.id ℝ ℝ).smulRight velocity) s t :=
        hd.hasFDerivWithinAt
      exact hfd.hasMFDerivWithinAt
    exact h0.mono Set.inter_subset_left
  have hsymm_mf : HasMFDerivWithinAt 𝓘(ℝ, E) I (extChartAt I α).symm
      (Set.range I) (u t)
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I) (u t)) :=
    (mdifferentiableWithinAt_extChartAt_symm htgt_t).hasMFDerivWithinAt
  have hcomp : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      ((extChartAt I α).symm ∘ u) s' t
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I) (u t)) ∘L
        ((ContinuousLinearMap.id ℝ ℝ).smulRight velocity)) :=
    HasMFDerivWithinAt.comp t hsymm_mf hu_mf Set.inter_subset_right
  exact (hasMFDerivWithinAt_inter' (I := 𝓘(ℝ, ℝ)) (I' := I)
    (f := (extChartAt I α).symm ∘ u) (s := s)
    (t := u ⁻¹' Set.range I) hconf).mp hcomp

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem exists_manifoldFlowFamily
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (hLocalFwd : ∀ (Φ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
        ∀ s : ℝ, Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hLocalRev : ∀ (Ψ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧
        ∀ s : ℝ, Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Ψ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hBijPerChart : ∀ (Φ Ψ : ℝ → M → M),
      (∀ x, Φ 0 x = x) → (∀ x, Ψ 0 x = x) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ α : M,
        ∃ S_α : ℝ, 0 < S_α ∧
          ∀ x ∈ (hper α).U ∩ (hperNeg α).U,
            ∀ s ∈ Set.Ico (0 : ℝ) S_α,
              Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ (T : ℝ) (_ : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M),
        Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
        (∀ x : M, Φ 0 x = x) ∧
        (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) := by
  classical
  obtain ⟨T, hT, Φ, hΦ_initial, _hΦ_repr_simple, hdiffeo⟩ :=
    time_dependent_vf_flow_diffeomorph_on_closed_manifold X hper hperNeg
      hLocalFwd hLocalRev hBijPerChart
  refine ⟨T, hT, fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    Φ, ?_, hΦ_initial, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dite_eq_right, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dite_eq_left, and_self]
    exact (hdiffeo t ht htT).choose_spec x

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem exists_manifoldFlowFamily_chartRepr
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (hLocalFwd : ∀ (Φ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
        ∀ s : ℝ, Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hLocalRev : ∀ (Ψ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧
        ∀ s : ℝ, Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Ψ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hBijPerChart : ∀ (Φ Ψ : ℝ → M → M),
      (∀ x, Φ 0 x = x) → (∀ x, Ψ 0 x = x) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ α : M,
        ∃ S_α : ℝ, 0 < S_α ∧
          ∀ x ∈ (hper α).U ∩ (hperNeg α).U,
            ∀ s ∈ Set.Ico (0 : ℝ) S_α,
              Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ (T : ℝ) (_ : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M),
        Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
        (∀ x : M, Φ 0 x = x) ∧
        (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Φ s x = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        (∀ t : ℝ, 0 < t → t < T → ∀ x : M, ∃ α : M,
          (Φ_fam t x : M) = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) t))) := by
  classical
  obtain ⟨T, hT, Φ, hΦ_initial, hΦ_repr_simple, hdiffeo⟩ :=
    time_dependent_vf_flow_diffeomorph_on_closed_manifold X hper hperNeg
      hLocalFwd hLocalRev hBijPerChart
  refine ⟨T, hT, fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    Φ, ?_, hΦ_initial, ?_, hΦ_repr_simple, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dite_eq_right, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dite_eq_left, and_self]
    exact (hdiffeo t ht htT).choose_spec x
  · intro t ht htT x
    obtain ⟨α, hαrepr⟩ := hΦ_repr_simple x
    refine ⟨α, ?_⟩
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    have hfam_eq : ((if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose
        else Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) : M → M) x = Φ t x := by
      simp only [hguard, dite_eq_left, and_self]
      exact (hdiffeo t ht htT).choose_spec x
    rw [hfam_eq, hαrepr t]

omit [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem manifoldFlow_hasMFDerivWithinAt_of_chartLocal
    (X : ℝ → ∀ x : M, TangentSpace I x) (α x : M)
    (hper : ChartLocalPicardData X α)
    (hxU : x ∈ hper.U)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) hper.T)
    (hconf : (hper.flow (I ((chartAt H α) x))) ⁻¹' (Set.range I) ∈
      𝓝[Set.Icc (0 : ℝ) hper.T] t)
    (htgt_t :
      hper.flow (I ((chartAt H α) x)) t ∈ (extChartAt I α).target) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s : ℝ => (chartAt H α).symm
        (I.symm (hper.flow (I ((chartAt H α) x)) s)))
      (Set.Icc 0 hper.T) t
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
          (hper.flow (I ((chartAt H α) x)) t)) ∘L
        ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (X t ((chartAt H α).symm
            (I.symm (hper.flow (I ((chartAt H α) x)) t)))))) := by
  set y : E := I ((chartAt H α) x) with hy
  set u : ℝ → E := hper.flow y with hu
  have hball : y ∈ Metric.closedBall (I ((chartAt H α) α)) hper.r :=
    ChartLocalPicardData.chart_coord_mem_closedBall X α hper x hxU
  obtain ⟨_hinit, hode⟩ := hper.flow_spec y hball
  have hd : HasDerivWithinAt u
      (X t ((chartAt H α).symm (I.symm (u t))))
      (Set.Icc (0 : ℝ) hper.T) t := hode t ht
  have hrealise : (fun s : ℝ => (chartAt H α).symm (I.symm (u s))) =
      fun s : ℝ => (extChartAt I α).symm (u s) := by
    funext s; rw [extChartAt_coe_symm]; rfl
  rw [hrealise]
  exact chartCoord_hasDerivWithinAt_to_manifold_hasMFDerivWithinAt
    (I := I) α u (Set.Icc 0 hper.T) t
    (X t ((chartAt H α).symm (I.symm (u t)))) htgt_t hconf hd

end DifferentialGeometry.Analysis.ODE
