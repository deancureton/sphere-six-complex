module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


namespace DifferentialGeometry.Analysis.ODE

open Set Function Manifold Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

noncomputable def autonomizedFlowVF (X : ℝ → ∀ x : M, TangentSpace I x) :
    (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p :=
  fun p => ((1 : ℝ), X p.1 p.2)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in
theorem autonomizedFlow_snd_hasMFDerivAt (X : ℝ → ∀ x : M, TangentSpace I x)
    (c : ℝ → ℝ × M) (t : ℝ)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t)))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (c s).2) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c t).1 (c t).2)) := by
  have h := (hasMFDerivAt_snd (c t)).comp t hc
  have hmap : (ContinuousLinearMap.snd ℝ
      (TangentSpace 𝓘(ℝ, ℝ) (c t).1) (TangentSpace I (c t).2)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (X (c t).1 (c t).2) := by
    apply ContinuousLinearMap.ext
    intro s
    change (s • ((1 : ℝ), X (c t).1 (c t).2)).2 = s • X (c t).1 (c t).2
    rfl
  change HasMFDerivAt 𝓘(ℝ, ℝ) I (Prod.snd ∘ c) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c t).1 (c t).2))
  exact h.congr_mfderiv hmap

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in
theorem autonomizedFlow_fst_hasDerivAt (X : ℝ → ∀ x : M, TangentSpace I x)
    (c : ℝ → ℝ × M) (t : ℝ)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t)))) :
    HasDerivAt (fun s => (c s).1) (1 : ℝ) t := by
  have h := (hasMFDerivAt_fst (c t)).comp t hc
  rw [hasMFDerivAt_iff_hasFDerivAt] at h
  have hmap : (ContinuousLinearMap.fst ℝ
      (TangentSpace 𝓘(ℝ, ℝ) (c t).1) (TangentSpace I (c t).2)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t))) =
      (1 : ℝ →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro s
    change (s • ((1 : ℝ), X (c t).1 (c t).2)).1 = s
    simp
  have h' := h.congr_fderiv hmap
  change HasDerivAt (Prod.fst ∘ c) 1 t
  have hone : (1 : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ 1 := by
    ext
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  exact hasDerivAt_iff_hasFDerivAt.mpr (h'.congr_fderiv hone)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in
theorem hasDerivAt_one_eq_self_on_Ioo (φ : ℝ → ℝ) {a b : ℝ}
    (h0mem : (0 : ℝ) ∈ Ioo a b)
    (hφ : ∀ s ∈ Ioo a b, HasDerivAt φ 1 s) (hval : φ 0 = 0) :
    ∀ s ∈ Ioo a b, φ s = s := by
  have hconst : ∀ s ∈ Ioo a b, HasDerivAt (fun u => φ u - u) (0 : ℝ) s := by
    intro u hu
    change HasDerivAt (φ - id) 0 u
    simpa only [sub_self] using (hφ u hu).sub (hasDerivAt_id u)
  intro s hs
  have hkey : (fun u => φ u - u) s = (fun u => φ u - u) 0 := by
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (convex_Ioo a b)
      (f := fun u => φ u - u) (s := Ioo a b)
    · intro u hu
      exact (hconst u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      have huniq : UniqueDiffWithinAt ℝ (Ioo a b) u :=
        isOpen_Ioo.uniqueDiffWithinAt hu
      have hfd : HasFDerivWithinAt (fun u => φ u - u)
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (0 : ℝ)) (Ioo a b) u :=
        ((hconst u hu).hasDerivWithinAt).hasFDerivWithinAt
      rw [hfd.fderivWithin huniq]; ext; simp
    · exact hs
    · exact h0mem
  simp only at hkey; rw [hval] at hkey; linarith

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem exists_local_integral_curve_of_contMDiffAt_autonomizedField [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (x : M)
    (hX : ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M)))
      (0, x)) :
    ∃ (ε : ℝ) (_ : 0 < ε) (γ : ℝ → M), γ 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
  obtain ⟨c, hc0, hcurve⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0 hX
  rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at hcurve
  obtain ⟨S, hS, hSon⟩ := hcurve
  rw [Metric.mem_nhds_iff] at hS
  obtain ⟨ε, hε, hball⟩ := hS
  refine ⟨ε, hε, fun s => (c s).2, by change (c 0).2 = x; rw [hc0], ?_⟩
  intro t ht
  have htS : t ∈ S := by
    apply hball
    rw [Real.ball_eq_Ioo]
    constructor
    · simpa using ht.1
    · simpa using ht.2
  have hct : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t))) := hSon t htS
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> simp [hε]
  have htime : ∀ s ∈ Ioo (-ε) ε, (c s).1 = s := by
    apply hasDerivAt_one_eq_self_on_Ioo (fun s => (c s).1) h0mem
    · intro u hu
      have huS : u ∈ S := by
        apply hball
        rw [Real.ball_eq_Ioo]
        constructor
        · simpa using hu.1
        · simpa using hu.2
      exact autonomizedFlow_fst_hasDerivAt X c u (hSon u huS)
    · rw [hc0]
  have hsnd := autonomizedFlow_snd_hasMFDerivAt X c t hct
  rw [htime t ht] at hsnd
  exact hsnd

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem exists_local_integral_curve_of_contMDiff_autonomizedField [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ∀ p : ℝ × M,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
        (fun p : ℝ × M =>
          (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M)))
        p)
    (x : M) :
    ∃ (ε : ℝ) (_ : 0 < ε) (γ : ℝ → M), γ 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) :=
  exists_local_integral_curve_of_contMDiffAt_autonomizedField X x (hX (0, x))

end DifferentialGeometry.Analysis.ODE
