module

public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Autonomization
public import Mathlib.Geometry.Manifold.Diffeomorph

@[expose] public section


namespace DifferentialGeometry.Analysis.ODE

open Set Function Manifold Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

variable [CompactSpace M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M] in
theorem time_dependent_vf_manifold_integral_flow_family
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ : ℝ → M → M)
    (hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x)
    (hflow : ∀ t, 0 < t → t < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Ici 0) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    ∃ (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)),
      Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) ∧
      (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) := by
  classical
  refine ⟨fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    ?_, ?_, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dite_eq_right, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dite_eq_left, and_self]
    exact (hdiffeo t ht htT).choose_spec x
  · intro s hs hsT x
    have hagree : ∀ t : ℝ, 0 < t → t < T → ∀ y : M,
        (if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose
          else Diffeomorph.refl I M ∞) y = Φ t y := by
      intro t ht htT y
      have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
      simp only [hguard, dite_eq_left, and_self]
      exact (hdiffeo t ht htT).choose_spec y
    have hbase : (if h : 0 < s ∧ s < T then (hdiffeo s h.1 h.2).choose
        else Diffeomorph.refl I M ∞) x = Φ s x := hagree s hs hsT x
    have hcurve_eq : (fun u : ℝ =>
          (if h : 0 < u ∧ u < T then (hdiffeo u h.1 h.2).choose
            else Diffeomorph.refl I M ∞) x) =ᶠ[𝓝[Ici 0] s]
        (fun u : ℝ => Φ u x) := by
      have hopen : Ioo (0 : ℝ) T ∈ 𝓝[Ici 0] s :=
        mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hs hsT)
      filter_upwards [hopen] with u hu
      exact hagree u hu.1 hu.2 x
    have hbase_flow := hflow s hs hsT x
    rw [← hbase] at hbase_flow
    exact hbase_flow.congr_of_eventuallyEq hcurve_eq hbase

end DifferentialGeometry.Analysis.ODE
