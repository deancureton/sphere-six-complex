module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import DifferentialGeometry.Analysis.ODE.Flow.IntegralCurveTransport
public import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.Manifold

@[expose] public section

noncomputable section

open Bundle
open Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable {v : (x : M) → TangentSpace I x}

theorem curveAt_add [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (x : M) (s t : ℝ) :
    curveAt v hcomplete x (s + t) = curveAt v hcomplete (curveAt v hcomplete x s) t := by
  have hEq := integralCurve_eq_of_agree (t₀ := 0) v hv
    (IsMIntegralCurve.comp_add (curveAt_integralCurve v hcomplete x) s)
    (curveAt_integralCurve v hcomplete (curveAt v hcomplete x s)) (by
      simp [curveAt_zero v hcomplete (curveAt v hcomplete x s)])
  have hmain : curveAt v hcomplete x (t + s) = curveAt v hcomplete (curveAt v hcomplete x s) t := by
    have hh := congrFun hEq t
    simpa [Function.comp_def] using hh
  simpa [add_comm] using hmain

theorem curveAt_injective [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) (t : ℝ) :
    Function.Injective (fun x : M => curveAt v hcomplete x t) := by
  intro x y h
  have hx : curveAt v hcomplete (curveAt v hcomplete x t) (-t) = curveAt v hcomplete (curveAt v hcomplete y t) (-t) := by
    exact congrArg (fun z : M => curveAt v hcomplete z (-t)) h
  have h1 : curveAt v hcomplete (curveAt v hcomplete x t) (-t) = curveAt v hcomplete x (t + (-t)) := by
    exact (curveAt_add v hv hcomplete x t (-t)).symm
  have h2 : curveAt v hcomplete (curveAt v hcomplete y t) (-t) = curveAt v hcomplete y (t + (-t)) := by
    exact (curveAt_add v hv hcomplete y t (-t)).symm
  have hz : t + (-t) = 0 := by ring
  rw [h1, h2, hz, curveAt_zero v hcomplete x, curveAt_zero v hcomplete y] at hx
  exact hx

theorem exists_uniform_localFlow_on_compact [FiniteDimensional ℝ E] [CompleteSpace E]
    [I.Boundaryless]
    [IsManifold I ∞ M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ K,
      ∃ U : Set M, y ∈ U ∧ IsOpen U ∧
      ∃ Ψ : M → ℝ → M,
        (∀ p ∈ U, Ψ p 0 = p) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
          (fun q : ℝ × M => Ψ q.2 q.1) (Ioo (-ε) ε ×ˢ U) ∧
        (∀ p ∈ U, ∀ t ∈ Ioo (-ε) ε,
          HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Ψ p s) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Ψ p t)))) := by
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (v q.2) : TangentBundle I M)) := by
    have hproj : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (Prod.snd : ℝ × M → M) :=
      contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I) (n := ∞)
    have hcomp : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        ((fun x : M => (⟨x, v x⟩ : TangentBundle I M)) ∘ (Prod.snd : ℝ × M → M)) :=
      hv.comp hproj
    simpa [Function.comp_def] using hcomp
  have hlocal : ∀ y : K,
      ∃ U : Set M, y.1 ∈ U ∧ IsOpen U ∧ ∃ T : ℝ, 0 < T ∧
        ∃ Ψ : M → ℝ → M,
          (∀ p ∈ U, Ψ p 0 = p) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
            (fun q : ℝ × M => Ψ q.2 q.1) (Ioo (-T) T ×ˢ U) ∧
          (∀ p ∈ U, ∀ t ∈ Ioo (-T) T,
            HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Ψ p s) t
              ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Ψ p t)))) :=
    fun y => by
      rcases DifferentialGeometry.Analysis.ODE.local_flow_jointSmooth_and_integralCurve
        (E := E) (I := I) (M := M)
        (X := fun _ : ℝ => v) hX (0 : ℝ) y.1 with
        ⟨U, hUopen, hyU, T, hT, Ψ, hinit, hsm, hbare⟩
      exact ⟨U, hyU, hUopen, T, hT, Ψ, hinit, by simpa [sub_eq_add_neg] using hsm,
        by simpa [sub_eq_add_neg] using hbare⟩
  choose U hUmem hUopen T hTpos Ψ hΨinitial hΨsm hΨbare using hlocal
  by_cases hKempty : K = ∅
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    simp [hKempty] at hy
  · have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    have hcov : K ⊆ ⋃ y : K, U y := fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hUmem ⟨y, hy⟩⟩
    rcases hK.elim_finite_subcover (ι := K) (fun y : K => U y) (fun y => hUopen y) hcov with
      ⟨sf, hsf⟩
    have hsf_ne : sf.Nonempty := by
      rcases hKne with ⟨y, hy⟩
      have hycov : y ∈ ⋃ i ∈ sf, U i := hsf hy
      rcases Set.mem_iUnion₂.mp hycov with ⟨i, hi, _⟩
      exact ⟨i, hi⟩
    let ε : ℝ := sf.inf' hsf_ne T
    have hε : 0 < ε := by
      dsimp [ε]
      exact (Finset.lt_inf'_iff (a := (0 : ℝ)) (s := sf) (H := hsf_ne) (f := T)).mpr
        (fun i hi => hTpos i)
    have hεT : ∀ i ∈ sf, ε ≤ T i := fun i hi => by
      dsimp [ε]
      exact Finset.inf'_le _ hi
    refine ⟨ε, hε, ?_⟩
    intro y hy
    have hycov : y ∈ ⋃ i ∈ sf, U i := hsf hy
    rcases Set.mem_iUnion₂.mp hycov with ⟨i, hi, hyU⟩
    refine ⟨U i, hyU, hUopen i, Ψ i, hΨinitial i, ?_, ?_⟩
    · exact (hΨsm i).mono (Set.prod_mono
        (by intro t ht; constructor <;> linarith [hεT i hi, ht.1, ht.2]) (subset_rfl))
    · intro p hp t ht
      exact hΨbare i p hp t (by
        constructor <;> linarith [hεT i hi, ht.1, ht.2])

theorem isMIntegralCurveOn_const_of_eq_zero (x : M) (hvx : v x = 0) :
    IsMIntegralCurveOn (fun _ : ℝ => x) v Set.univ :=
  (isMIntegralCurve_const hvx).isMIntegralCurveOn Set.univ

theorem curveAt_eq_self_of_not_mem_tsupport [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    {x : M} (hx : x ∉ tsupport v) (t : ℝ) :
    curveAt v hcomplete x t = x := by
  have hxnot : x ∉ Function.support v := fun hs => hx (subset_closure hs)
  have hvx : v x = 0 := by
    by_contra h
    exact hxnot h
  have hconstOn : IsMIntegralCurveOn (fun _ : ℝ => x) v Set.univ :=
    isMIntegralCurveOn_const_of_eq_zero x hvx
  have hconst : IsMIntegralCurve (fun _ : ℝ => x) v := isMIntegralCurve_const hvx
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hIsM1 : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hγt : ∀ t : ℝ, I.IsInteriorPoint (curveAt v hcomplete x t) := by
    intro t
    exact BoundarylessManifold.isInteriorPoint (x := curveAt v hcomplete x t)
  have heq : curveAt v hcomplete x = (fun _ : ℝ => x) :=
    isMIntegralCurve_eq_of_contMDiff (t₀ := 0) hγt hv1
      (curveAt_integralCurve v hcomplete x) hconst (curveAt_zero v hcomplete x)
  exact congrFun heq t

theorem exists_uniform_localIntegralCurveOn_of_compactSupport [FiniteDimensional ℝ E]
    [CompleteSpace E] [I.Boundaryless]
    [IsManifold I ∞ M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : M,
      ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  rcases exists_uniform_localFlow_on_compact v hv hsupp with ⟨ε, hε, hflow⟩
  refine ⟨ε, hε, ?_⟩
  intro x
  by_cases hxK : x ∈ tsupport v
  · rcases hflow x hxK with ⟨U, hxU, hUopen, Ψ, hinit, hsm, hbare⟩
    refine ⟨Ψ x, hinit x hxU, ?_⟩
    intro t ht
    exact (hbare x hxU t ht).hasMFDerivWithinAt
  · have hxnot : x ∉ Function.support v := fun hs => hxK (subset_closure hs)
    have hvx : v x = 0 := by
      by_contra h
      exact hxnot h
    refine ⟨fun _ : ℝ => x, rfl, ?_⟩
    exact (isMIntegralCurveOn_const_of_eq_zero x hvx).mono (fun t ht => Set.mem_univ t)

theorem exists_globalIntegralCurve_of_compactSupport [FiniteDimensional ℝ E] [CompleteSpace E]
    [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) :
    ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  rcases exists_uniform_localIntegralCurveOn_of_compactSupport v hv hsupp with ⟨ε, hε, hlocal⟩
  have hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  exact fun x => exists_isMIntegralCurve_of_isMIntegralCurveOn hv1 hε hlocal x

lemma portPrivate_c55af3af_contMDiffAt_globalFlow_step [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    {ε : ℝ} (hε : 0 < ε)
    {K : Set M}
    (hflow : ∀ y ∈ K, ∃ U : Set M, y ∈ U ∧ IsOpen U ∧
      ∃ Ψ : M → ℝ → M,
        (∀ p ∈ U, Ψ p 0 = p) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
          (fun q : ℝ × M => Ψ q.2 q.1) (Ioo (-ε) ε ×ˢ U) ∧
        (∀ p ∈ U, ∀ t ∈ Ioo (-ε) ε,
          HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Ψ p s) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Ψ p t)))))
    {s : ℝ} {x₀ : M}
    (hP : ContMDiffAt I I ∞ (fun x : M => curveAt v hcomplete x s) x₀)
    (hγs : curveAt v hcomplete x₀ s ∈ K)
    {σ : ℝ} (hσ : |σ| < ε) :
    ContMDiffAt I I ∞ (fun x : M => curveAt v hcomplete x (s + σ)) x₀ := by
  rcases hflow (curveAt v hcomplete x₀ s) hγs with ⟨U, hyU, hUopen, Ψ, hΨinitial, hΨsm, hΨbare⟩
  have hσmem : σ ∈ Ioo (-ε) ε := by
    constructor
    · exact (abs_lt.mp hσ).1
    · exact (abs_lt.mp hσ).2
  have hγOn : ∀ p : M, IsMIntegralCurveOn (curveAt v hcomplete p) v (Ioo (-ε) ε) := fun p =>
    (curveAt_integralCurve v hcomplete p).isMIntegralCurveOn _
  have hΨOn : ∀ p ∈ U, IsMIntegralCurveOn (Ψ p) v (Ioo (-ε) ε) := fun p hp =>
    fun t ht => (hΨbare p hp t ht).hasMFDerivWithinAt
  have hagree : ∀ p ∈ U, ∀ t ∈ Ioo (-ε) ε, curveAt v hcomplete p t = Ψ p t := by
    intro p hp t ht
    have ht₀ : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> linarith
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0)
      (a := -ε) (b := ε) ht₀ hv1 (hγOn p) (hΨOn p hp) (by
        rw [curveAt_zero v hcomplete p]
        exact (hΨinitial p hp).symm)
    exact heq ht
  let z : M → M := fun x => curveAt v hcomplete x s
  have hz₀ : z x₀ = curveAt v hcomplete x₀ s := rfl
  have hcontz : ContinuousAt z x₀ := hP.continuousAt
  have hnbd : {x : M | z x ∈ U} ∈ 𝓝 x₀ :=
    hcontz.preimage_mem_nhds (hUopen.mem_nhds hyU)
  have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞
      (fun x : M => (σ, x)) (z x₀) :=
    ContMDiffAt.prodMk (contMDiffAt_const (c := σ) (x := z x₀)) (contMDiffAt_id (x := z x₀))
  have hjoint : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => Ψ q.2 q.1) (σ, z x₀) := by
    apply (hΨsm (σ, z x₀) (by constructor <;> [exact hσmem; exact hyU])).contMDiffAt
    exact prod_mem_nhds (isOpen_Ioo.mem_nhds hσmem) (hUopen.mem_nhds hyU)
  have hΨσ : ContMDiffAt I I ∞ (fun p : M => Ψ p σ) (z x₀) := by
    have hc := hjoint.comp (z x₀) hpair
    simpa [Function.comp_def] using hc
  have hcomp : ContMDiffAt I I ∞ (fun x : M => Ψ (z x) σ) x₀ := by
    have hc := hΨσ.comp x₀ hP
    simpa [Function.comp_def] using hc
  have heqev : (fun x : M => curveAt v hcomplete x (s + σ)) =ᶠ[𝓝 x₀]
      (fun x : M => Ψ (curveAt v hcomplete x s) σ) := by
    exact Filter.eventuallyEq_of_mem hnbd (fun x hx => by
      rw [curveAt_add v hv1 hcomplete x s σ]
      exact hagree (curveAt v hcomplete x s) hx σ hσmem)
  exact hcomp.congr_of_eventuallyEq heqev

theorem portPrivate_c55af3af_contMDiffAt_curveAt_slice_nonneg [FiniteDimensional ℝ E]
    [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x₀ : M) :
    ContMDiffAt I I ∞
      (fun x : M => curveAt v hcomplete x t₀) x₀ := by
  let γ : ℝ → M := curveAt v hcomplete x₀
  let K : Set M := γ '' Set.Icc (0 : ℝ) t₀
  have hK : IsCompact K := by
    exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) t₀)).image
      (curveAt_integralCurve v hcomplete x₀).continuous
  rcases exists_uniform_localFlow_on_compact v hv hK with ⟨ε, hε, hflow⟩
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by dsimp [δ]; linarith
  rcases exists_nat_gt (t₀ / δ) with ⟨n, hn⟩
  have hnt : t₀ < (n : ℝ) * δ := by
    have hn' : t₀ / δ < (n : ℝ) := hn
    exact (div_lt_iff₀ hδ).mp hn'
  let s : ℕ → ℝ := fun i => min ((i : ℝ) * δ) t₀
  have hs0 : s 0 = 0 := by
    dsimp [s]
    simpa using (min_eq_left ht₀)
  have hsn : s n = t₀ := by
    dsimp [s]
    exact min_eq_right (le_of_lt hnt)
  have hsIcc : ∀ i, s i ∈ Set.Icc (0 : ℝ) t₀ := by
    intro i
    dsimp [s]
    constructor
    · exact (le_min_iff.mpr ⟨mul_nonneg (Nat.cast_nonneg i) (le_of_lt hδ), ht₀⟩)
    · exact min_le_right (a := (i : ℝ) * δ) (b := t₀)
  have hstep : ∀ i, |s (i + 1) - s i| < ε := by
    intro i
    have hnonneg : 0 ≤ s (i + 1) - s i := by
      dsimp [s]
      have hm : min ((i : ℝ) * δ) t₀ ≤ min (((i + 1 : ℕ) : ℝ) * δ) t₀ := by
        have hi' : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ i
        exact min_le_min (mul_le_mul_of_nonneg_right hi' (le_of_lt hδ)) le_rfl
      linarith
    have hleδ : s (i + 1) - s i ≤ δ := by
      dsimp [s]
      have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_num
      by_cases h1 : t₀ ≤ ((i + 1 : ℕ) : ℝ) * δ
      · by_cases h2 : t₀ ≤ (i : ℝ) * δ
        · rw [min_eq_right h1, min_eq_right h2]
          nlinarith [hδ]
        · have h3 : (i : ℝ) * δ < t₀ := lt_of_not_ge h2
          rw [min_eq_right h1, min_eq_left (le_of_lt h3)]
          have h1' : t₀ ≤ (i : ℝ) * δ + δ := by
            have h1'' : t₀ ≤ ((i : ℝ) + 1) * δ := by simpa [hcast] using h1
            rw [add_mul, one_mul] at h1''
            exact h1''
          nlinarith [h1']
      · have h3 : ((i + 1 : ℕ) : ℝ) * δ < t₀ := lt_of_not_ge h1
        have h4 : (i : ℝ) * δ < t₀ := by
          have h3' : ((i : ℝ) + 1) * δ < t₀ := by simpa [hcast] using h3
          rw [add_mul, one_mul] at h3'
          linarith
        rw [min_eq_left (le_of_lt h3), min_eq_left (le_of_lt h4)]
        rw [hcast]
        ring_nf
        exact le_rfl
    rw [abs_of_nonneg hnonneg]
    linarith
  let hP : ℕ → Prop := fun i =>
    ContMDiffAt I I ∞ (fun x : M => curveAt v hcomplete x (s i)) x₀
  have hP0 : hP 0 := by
    have hfun : (fun x : M => curveAt v hcomplete x (s 0)) = id := by
      funext x
      simp [hs0, curveAt_zero v hcomplete x]
    simpa [hP, hfun] using (contMDiffAt_id (x := x₀))
  have hPsucc : ∀ i, hP i → hP (i + 1) := by
    intro i hPi
    by_cases hin : i < n
    · have hγs : curveAt v hcomplete x₀ (s i) ∈ K := by
        dsimp [K, γ]
        exact ⟨s i, hsIcc i, rfl⟩
      have hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
        hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
      have hstep' := portPrivate_c55af3af_contMDiffAt_globalFlow_step v hv1 hcomplete hε hflow
        (s := s i) (x₀ := x₀) (hP := hPi) (hγs := hγs) (σ := s (i + 1) - s i) (hstep i)
      simpa [hP, add_comm, sub_add_cancel] using hstep'
    · have hge : (n : ℝ) ≤ (i : ℝ) := by exact_mod_cast (le_of_not_gt hin)
      have hs : s (i + 1) = s i := by
        dsimp [s]
        have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_num
        have h1 : t₀ ≤ ((i + 1 : ℕ) : ℝ) * δ := by nlinarith [hnt, hge, hcast, hδ]
        have h2 : t₀ ≤ (i : ℝ) * δ := by nlinarith [hnt, hge, hδ]
        rw [min_eq_right h1, min_eq_right h2]
      simpa [hP, hs] using hPi
  have hPle : ∀ i : ℕ, 0 ≤ i → hP i :=
    Nat.le_induction (m := 0) (P := fun i _ => hP i) hP0 (fun i _ hPi => hPsucc i hPi)
  have hPn : hP n := hPle n (Nat.zero_le n)
  simpa [hP, hsn] using hPn

theorem portPrivate_c55af3af_contMDiffAt_curveAt_slice [FiniteDimensional ℝ E] [CompleteSpace E]
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff ∞ (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (t₀ : ℝ) (x₀ : M) :
    ContMDiffAt I I ∞ (fun x => curveAt v hcomplete x t₀) x₀ := by
  by_cases ht₀ : 0 ≤ t₀
  · exact portPrivate_c55af3af_contMDiffAt_curveAt_slice_nonneg v hv hcomplete ht₀ x₀
  · have hvneg : CMDiff ∞ (fun x : M => (⟨x, -v x⟩ : TangentBundle I M)) :=
      hv.neg_section
    have hrev : ∀ x : M, IsMIntegralCurve (fun t => curveAt v hcomplete x (-t)) (-v) := by
      intro x
      simpa only [Function.comp_def, mul_neg_one, neg_one_smul] using
        (curveAt_integralCurve v hcomplete x).comp_mul (-1)
    let hn : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ (-v) :=
      fun x => ⟨fun t => curveAt v hcomplete x (-t), by simp [curveAt_zero], hrev x⟩
    have heq : ∀ x : M, curveAt (-v) hn x = fun t => curveAt v hcomplete x (-t) := by
      intro x
      exact integralCurve_eq_of_agree (t₀ := 0) (-v) (hvneg.of_le (by simp))
        (curveAt_integralCurve (-v) hn x) (hrev x) (by simp [curveAt_zero])
    have h := portPrivate_c55af3af_contMDiffAt_curveAt_slice_nonneg (-v) hvneg hn (neg_nonneg.mpr (le_of_not_ge ht₀)) x₀
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x => by simpa using (congrFun (heq x) (-t₀)).symm

theorem contMDiffAt_globalFlow_of_complete [FiniteDimensional ℝ E]
    [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (t₀ : ℝ) (x₀ : M) :
    ContMDiffAt I I ∞ (fun x : M => curveAt v hcomplete x t₀) x₀ := by
  by_cases ht₀ : 0 ≤ t₀
  · exact portPrivate_c55af3af_contMDiffAt_curveAt_slice_nonneg v hv hcomplete ht₀ x₀
  · have hneg : 0 ≤ -t₀ := by linarith
    have hvneg : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => (⟨x, -v x⟩ : TangentBundle I M)) :=
      ContMDiff.neg_section hv
    have hcompleteNeg : ∀ x : M, ∃ γ : ℝ → M,
        γ 0 = x ∧ IsMIntegralCurve γ (-v) := by
      intro x
      obtain ⟨γ, hγ0, hγ⟩ := hcomplete x
      refine ⟨fun s : ℝ => γ (-s), by simp [hγ0], ?_⟩
      have hc := IsMIntegralCurve.comp_mul hγ (-1)
      have hcurve : (γ ∘ fun s : ℝ => s * (-1)) = fun s : ℝ => γ (-s) := by
        funext s
        exact congrArg γ (mul_neg_one s)
      have hfield : (-1 : ℝ) • v = -v := by
        funext y
        exact neg_one_smul ℝ (v y)
      rw [hcurve, hfield] at hc
      exact hc
    have hnonneg := portPrivate_c55af3af_contMDiffAt_curveAt_slice_nonneg
      (-v) hvneg hcompleteNeg hneg x₀
    have hrefl : ∀ x : M, ∀ t : ℝ,
        curveAt v hcomplete x t = curveAt (-v) hcompleteNeg x (-t) := by
      intro x t
      have hvneg1 : CMDiff 1 (fun x : M => (⟨x, -v x⟩ : TangentBundle I M)) :=
        hvneg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
      have hγ : IsMIntegralCurve (curveAt v hcomplete x) v :=
        curveAt_integralCurve v hcomplete x
      have hrev : IsMIntegralCurve (fun s : ℝ => curveAt v hcomplete x (-s)) (-v) := by
        have hc := IsMIntegralCurve.comp_mul hγ (-1)
        have hcurve : (curveAt v hcomplete x ∘ fun s : ℝ => s * (-1)) =
            fun s : ℝ => curveAt v hcomplete x (-s) := by
          funext s
          exact congrArg (curveAt v hcomplete x) (mul_neg_one s)
        have hfield : (-1 : ℝ) • v = -v := by
          funext y
          exact neg_one_smul ℝ (v y)
        rw [hcurve, hfield] at hc
        exact hc
      have h0 : curveAt v hcomplete x (-0) = curveAt (-v) hcompleteNeg x 0 := by
        simp [curveAt_zero v hcomplete x, curveAt_zero (-v) hcompleteNeg x]
      have hEq := integralCurve_eq_of_agree (t₀ := 0) (-v) hvneg1 hrev
        (curveAt_integralCurve (-v) hcompleteNeg x) h0
      have hh := congrFun hEq (-t)
      simpa [neg_neg] using hh
    have hcongr : (fun x : M => curveAt v hcomplete x t₀) =ᶠ[𝓝 x₀]
        (fun x : M => curveAt (-v) hcompleteNeg x (-t₀)) := by
      exact Filter.Eventually.of_forall (fun x => hrefl x t₀)
    exact hnonneg.congr_of_eventuallyEq hcongr

theorem globalFlow_diffeomorph_of_complete [FiniteDimensional ℝ E]
    [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (s : ℝ) :
    ∃ d : Diffeomorph I I M M ∞,
      (∀ x, d x = curveAt v hcomplete x s) ∧
      (∀ x, d.symm x = curveAt v hcomplete x (-s)) := by
  have hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hleft : ∀ x : M,
      curveAt v hcomplete (curveAt v hcomplete x s) (-s) = x := by
    intro x
    rw [← curveAt_add v hv1 hcomplete x s (-s)]
    simpa using curveAt_zero v hcomplete x
  have hright : ∀ x : M,
      curveAt v hcomplete (curveAt v hcomplete x (-s)) s = x := by
    intro x
    rw [← curveAt_add v hv1 hcomplete x (-s) s]
    simpa [add_comm] using curveAt_zero v hcomplete x
  have hforward : ContMDiff I I ∞ (fun x : M => curveAt v hcomplete x s) := by
    intro x
    exact contMDiffAt_globalFlow_of_complete v hv hcomplete s x
  have hreverse : ContMDiff I I ∞ (fun x : M => curveAt v hcomplete x (-s)) := by
    intro x
    exact contMDiffAt_globalFlow_of_complete v hv hcomplete (-s) x
  let e : M ≃ M :=
    { toFun := fun x => curveAt v hcomplete x s
      invFun := fun x => curveAt v hcomplete x (-s)
      left_inv := hleft
      right_inv := hright }
  refine ⟨⟨e, hforward, hreverse⟩, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl

theorem contMDiffAt_globalFlow_joint_of_complete [FiniteDimensional ℝ E]
    [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (t₀ : ℝ) (x₀ : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) (t₀, x₀) := by
  have hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (⟨q.2, v q.2⟩ : TangentBundle I M)) := by
    have hproj : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (Prod.snd : ℝ × M → M) :=
      contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I) (n := ∞)
    have hcomp : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        ((fun x : M => (⟨x, v x⟩ : TangentBundle I M)) ∘
          (Prod.snd : ℝ × M → M)) := hv.comp hproj
    simpa [Function.comp_def] using hcomp
  let y : M := curveAt v hcomplete x₀ t₀
  obtain ⟨U, hUopen, hyU, T, hT, Ψ, hΨinit, hΨsm, hΨbare⟩ :=
    local_flow_jointSmooth_and_integralCurve (E := E) (I := I) (M := M)
      (X := fun _ : ℝ => v) hX t₀ y
  have hz : ContMDiffAt I I ∞
      (fun x : M => curveAt v hcomplete x t₀) x₀ :=
    contMDiffAt_globalFlow_of_complete v hv hcomplete t₀ x₀
  have hzU : {x : M | curveAt v hcomplete x t₀ ∈ U} ∈ 𝓝 x₀ := by
    have hy : curveAt v hcomplete x₀ t₀ ∈ U := by
      exact hyU
    exact hz.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hy)
  let V : Set (ℝ × M) :=
    Set.Ioo (t₀ - T) (t₀ + T) ×ˢ {x : M | curveAt v hcomplete x t₀ ∈ U}
  have hVmem : (t₀, x₀) ∈ V := by
    constructor
    · exact ⟨by linarith, by linarith⟩
    · exact hyU
  have hVnhds : V ∈ 𝓝 (t₀, x₀) := by
    exact prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) hzU
  have hagree : ∀ p ∈ U, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
      curveAt v hcomplete p (t - t₀) = Ψ p t := by
    intro p hp t ht
    let γp : ℝ → M := fun s => curveAt v hcomplete p (s - t₀)
    have hγp : IsMIntegralCurve γp v := by
      have hcomp := (curveAt_integralCurve v hcomplete p).comp_add (-t₀)
      simpa [γp, Function.comp_def, sub_eq_add_neg] using hcomp
    have hγOn : IsMIntegralCurveOn γp v
        (Set.Ioo (t₀ - T) (t₀ + T)) :=
      hγp.isMIntegralCurveOn _
    have hΨOn : IsMIntegralCurveOn (Ψ p) v
        (Set.Ioo (t₀ - T) (t₀ + T)) := by
      intro s hs
      simpa using (hΨbare p hp s hs).hasMFDerivWithinAt
    have ht₀ : t₀ ∈ Set.Ioo (t₀ - T) (t₀ + T) := by
      constructor <;> linarith
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := t₀) (a := t₀ - T) (b := t₀ + T) ht₀ hv1 hγOn hΨOn
      (by
        change curveAt v hcomplete p (t₀ - t₀) = Ψ p t₀
        rw [sub_self, curveAt_zero v hcomplete p]
        exact (hΨinit p hp).symm)
    have hval := heq ht
    simpa [γp, sub_eq_add_neg] using hval
  have hmain : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ (curveAt v hcomplete p.2 t₀) p.1) (t₀, x₀) := by
    have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × M => (p.1, curveAt v hcomplete p.2 t₀)) (t₀, x₀) := by
      exact (contMDiffAt_fst (p := (t₀, x₀))).prodMk
        (hz.comp (t₀, x₀) (contMDiffAt_snd (p := (t₀, x₀))))
    have hΨat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => Ψ q.2 q.1) (t₀, y) := by
      exact (hΨsm (t₀, y) (by constructor <;> [exact ⟨by linarith, by linarith⟩; exact hyU])).contMDiffAt
        (prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
          (hUopen.mem_nhds hyU))
    have hcomp := hΨat.comp (t₀, x₀) hpair
    simpa [Function.comp_def, y] using hcomp
  have heq : (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) =ᶠ[𝓝 (t₀, x₀)]
      (fun p : ℝ × M => Ψ (curveAt v hcomplete p.2 t₀) p.1) := by
    exact Filter.Eventually.mono hVnhds (fun p hp => by
      have hstep := curveAt_add v hv1 hcomplete p.2 t₀ (p.1 - t₀)
      have hstep' : curveAt v hcomplete p.2 p.1 =
          curveAt v hcomplete (curveAt v hcomplete p.2 t₀) (p.1 - t₀) := by
        rw [← hstep]
        congr 1
        ring
      change curveAt v hcomplete p.2 p.1 = Ψ
        (curveAt v hcomplete p.2 t₀) p.1
      rw [hstep']
      exact hagree (curveAt v hcomplete p.2 t₀) hp.2 p.1 hp.1)
  exact hmain.congr_of_eventuallyEq heq

theorem contMDiff_globalFlow_joint_of_complete [FiniteDimensional ℝ E]
    [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) := by
  intro p
  rcases p with ⟨t₀, x₀⟩
  exact contMDiffAt_globalFlow_joint_of_complete v hv hcomplete t₀ x₀

theorem portPrivate_c55af3af_continuousAt_globalFlow_of_compactSupport_nonneg [FiniteDimensional ℝ E]
    [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x₀ : M) :
    ContinuousAt (fun p : ℝ × M =>
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.2 p.1) (t₀, x₀) := by
  let hcomplete := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let γ : ℝ → M := curveAt v hcomplete x₀
  let K : Set M := γ '' Set.Icc (0 : ℝ) t₀
  have hK : IsCompact K := by
    exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) t₀)).image
      (curveAt_integralCurve v hcomplete x₀).continuous
  rcases exists_uniform_localFlow_on_compact v hv hK with ⟨ε, hε, hflow⟩
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  rcases exists_nat_gt (t₀ / δ) with ⟨n, hn⟩
  have hnpos : 0 < n := by
    by_contra hn0
    have hnle : n = 0 := Nat.eq_zero_of_not_pos hn0
    have hncast : (n : ℝ) = 0 := by exact_mod_cast hnle
    have hdiv : 0 ≤ t₀ / δ := div_nonneg ht₀ (le_of_lt hδ)
    have hlt : t₀ / δ < 0 := by
      rw [hncast] at hn
      exact hn
    linarith
  let s : ℝ := min (((n - 1 : ℕ) : ℝ) * δ) t₀
  have hs_mem : s ∈ Set.Icc (0 : ℝ) t₀ := by
    dsimp [s]
    constructor
    · exact le_min (mul_nonneg (by positivity : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ)) (le_of_lt hδ)) ht₀
    · exact min_le_right _ _
  have hts : |t₀ - s| < ε := by
    dsimp [s]
    by_cases h : t₀ ≤ ((n - 1 : ℕ) : ℝ) * δ
    · rw [min_eq_right h]
      simpa using hε
    · have hlt : ((n - 1 : ℕ) : ℝ) * δ < t₀ := lt_of_not_ge h
      rw [min_eq_left (le_of_lt hlt)]
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        cases n with
        | zero => exact (False.elim (Nat.lt_irrefl 0 hnpos))
        | succ n' =>
            simp [Nat.cast_succ]
      have hδε : δ < ε := by dsimp [δ]; linarith
      have hnδ : t₀ < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hlt))]
      nlinarith [hcast, hnδ, hδε]
  have hγs : curveAt v hcomplete x₀ s ∈ K := by
    dsimp [K, γ]
    exact ⟨s, hs_mem, rfl⟩
  rcases hflow (curveAt v hcomplete x₀ s) hγs with ⟨U, hyU, hUopen, Ψ, hΨinitial, hΨsm, hΨbare⟩
  have hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hσmem0 : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> linarith
  have hagree : ∀ p ∈ U, ∀ τ ∈ Ioo (-ε) ε, curveAt v hcomplete p τ = Ψ p τ := by
    intro p hp τ hτ
    have hγOn : IsMIntegralCurveOn (curveAt v hcomplete p) v (Ioo (-ε) ε) :=
      (curveAt_integralCurve v hcomplete p).isMIntegralCurveOn _
    have hΨOn : IsMIntegralCurveOn (Ψ p) v (Ioo (-ε) ε) := fun t ht =>
      (hΨbare p hp t ht).hasMFDerivWithinAt
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0)
      (a := -ε) (b := ε) hσmem0 hv1 (hγOn) (hΨOn) (by
        rw [curveAt_zero v hcomplete p]
        exact (hΨinitial p hp).symm)
    exact heq hτ
  have hcont_s : ContinuousAt (fun x : M => curveAt v hcomplete x s) x₀ :=
    (portPrivate_c55af3af_contMDiffAt_curveAt_slice v hv hcomplete s x₀).continuousAt
  have hmemU : {x : M | curveAt v hcomplete x s ∈ U} ∈ 𝓝 x₀ :=
    hcont_s.preimage_mem_nhds (hUopen.mem_nhds hyU)
  let η : ℝ := (ε - |t₀ - s|) / 2
  have hη : 0 < η := by
    dsimp [η]
    nlinarith [hts]
  let V : Set (ℝ × M) := (Set.Ioo (t₀ - η) (t₀ + η)) ×ˢ {x : M | curveAt v hcomplete x s ∈ U}
  have hVmem : (t₀, x₀) ∈ V := by
    dsimp [V]
    constructor
    · constructor <;> linarith [hts, hη]
    · exact hyU
  have hVnhds : V ∈ 𝓝 (t₀, x₀) := by
    dsimp [V]
    exact prod_mem_nhds (isOpen_Ioo.mem_nhds (by constructor <;> linarith [hts, hη])) hmemU
  have hVmain : ∀ (t : ℝ) (x : M), (t, x) ∈ V →
      curveAt v hcomplete x t = Ψ (curveAt v hcomplete x s) (t - s) := by
    intro t x htx
    have htε : |t - s| < ε := by
      have hsub : |t - t₀| < η := by
        rw [abs_lt]
        constructor <;> linarith [htx.1.1, htx.1.2]
      have htri : |t - s| ≤ |t - t₀| + |t₀ - s| := by
        calc
          |t - s| = |(t - t₀) + (t₀ - s)| := by ring_nf
          _ ≤ |t - t₀| + |t₀ - s| := abs_add_le _ _
      dsimp [η] at hsub
      nlinarith [hts, htri]
    have hxU : curveAt v hcomplete x s ∈ U := htx.2
    have hstep : curveAt v hcomplete x t = curveAt v hcomplete (curveAt v hcomplete x s) (t - s) := by
      have hh := curveAt_add v hv1 hcomplete x s (t - s)
      rw [show s + (t - s) = t by ring] at hh
      exact hh
    rw [hstep]
    exact hagree (curveAt v hcomplete x s) hxU (t - s)
      ⟨(abs_lt.mp htε).1, (abs_lt.mp htε).2⟩
  have hmain : ContinuousAt (fun p : ℝ × M => Ψ (curveAt v hcomplete p.2 s) (p.1 - s)) (t₀, x₀) := by
    have hfst : ContinuousAt (fun p : ℝ × M => p.1 - s) (t₀, x₀) :=
      (continuousAt_fst : ContinuousAt (fun p : ℝ × M => p.1) (t₀, x₀)).sub continuousAt_const
    have hsnd : ContinuousAt (fun p : ℝ × M => curveAt v hcomplete p.2 s) (t₀, x₀) := by
      have hcsnd : ContinuousAt (fun p : ℝ × M => p.2) (t₀, x₀) :=
        (continuousAt_snd : ContinuousAt (fun p : ℝ × M => p.2) (t₀, x₀))
      exact ContinuousAt.comp (x := (t₀, x₀)) (f := fun p : ℝ × M => p.2)
        (g := fun x : M => curveAt v hcomplete x s) hcont_s hcsnd
    have hpair : ContinuousAt (fun p : ℝ × M => (p.1 - s, curveAt v hcomplete p.2 s)) (t₀, x₀) :=
      hfst.prodMk hsnd
    have hpt : (t₀ - s, curveAt v hcomplete x₀ s) ∈ Ioo (-ε) ε ×ˢ U := by
      constructor
      · change t₀ - s ∈ Ioo (-ε) ε
        exact ⟨(abs_lt.mp hts).1, (abs_lt.mp hts).2⟩
      · exact hyU
    have hΨat : ContinuousAt (fun q : ℝ × M => Ψ q.2 q.1) (t₀ - s, curveAt v hcomplete x₀ s) := by
      have hc : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.2 q.1)
          (t₀ - s, curveAt v hcomplete x₀ s) :=
        (hΨsm (t₀ - s, curveAt v hcomplete x₀ s) hpt).contMDiffAt (by
          exact prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨(abs_lt.mp hts).1, (abs_lt.mp hts).2⟩)
            (hUopen.mem_nhds hyU))
      exact hc.continuousAt
    have hcomp := ContinuousAt.comp (x := (t₀, x₀)) (f := fun p : ℝ × M =>
      (p.1 - s, curveAt v hcomplete p.2 s)) (g := fun q : ℝ × M => Ψ q.2 q.1) hΨat hpair
    simpa [Function.comp_def] using hcomp
  have heq : (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) =ᶠ[𝓝 (t₀, x₀)]
      (fun p : ℝ × M => Ψ (curveAt v hcomplete p.2 s) (p.1 - s)) := by
    exact Filter.eventuallyEq_of_mem hVnhds (by intro p hp; exact (hVmain p.1 p.2 hp))
  exact hmain.congr_of_eventuallyEq heq

theorem portPrivate_c55af3af_contMDiffAt_curveAt_of_slice [FiniteDimensional ℝ E] [CompleteSpace E]
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff ∞ (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (t₀ : ℝ) (x₀ : M)
    (hslice : ContMDiffAt I I ∞ (fun x => curveAt v hcomplete x t₀) x₀) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) (t₀, x₀) := by
  let s : ℝ := t₀
  rcases exists_uniform_localFlow_on_compact v hv
    (isCompact_singleton : IsCompact ({curveAt v hcomplete x₀ s} : Set M)) with
    ⟨ε, hε, hflow⟩
  have hγs : curveAt v hcomplete x₀ s ∈ ({curveAt v hcomplete x₀ s} : Set M) := rfl
  have hts : |t₀ - s| < ε := by simpa only [s, sub_self, abs_zero] using hε
  rcases hflow (curveAt v hcomplete x₀ s) hγs with
    ⟨U, hyU, hUopen, Ψ, hΨinitial, hΨsm, hΨbare⟩
  have hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hσmem0 : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> linarith
  have hagree : ∀ p ∈ U, ∀ τ ∈ Ioo (-ε) ε, curveAt v hcomplete p τ = Ψ p τ := by
    intro p hp τ hτ
    have hγOn : IsMIntegralCurveOn (curveAt v hcomplete p) v (Ioo (-ε) ε) :=
      (curveAt_integralCurve v hcomplete p).isMIntegralCurveOn _
    have hΨOn : IsMIntegralCurveOn (Ψ p) v (Ioo (-ε) ε) := fun t ht =>
      (hΨbare p hp t ht).hasMFDerivWithinAt
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0)
      (a := -ε) (b := ε) hσmem0 hv1 (hγOn) (hΨOn) (by
        rw [curveAt_zero v hcomplete p]
        exact (hΨinitial p hp).symm)
    exact heq hτ
  have hcont_s : ContinuousAt (fun x : M => curveAt v hcomplete x s) x₀ :=
    hslice.continuousAt
  have hmemU : {x : M | curveAt v hcomplete x s ∈ U} ∈ 𝓝 x₀ :=
    hcont_s.preimage_mem_nhds (hUopen.mem_nhds hyU)
  let η : ℝ := (ε - |t₀ - s|) / 2
  have hη : 0 < η := by
    dsimp [η]
    nlinarith [hts]
  let V : Set (ℝ × M) := (Set.Ioo (t₀ - η) (t₀ + η)) ×ˢ {x : M | curveAt v hcomplete x s ∈ U}
  have hVmem : (t₀, x₀) ∈ V := by
    dsimp [V]
    constructor
    · constructor <;> linarith [hts, hη]
    · exact hyU
  have hVnhds : V ∈ 𝓝 (t₀, x₀) := by
    dsimp [V]
    exact prod_mem_nhds (isOpen_Ioo.mem_nhds (by constructor <;> linarith [hts, hη])) hmemU
  have hVmain : ∀ (t : ℝ) (x : M), (t, x) ∈ V →
      curveAt v hcomplete x t = Ψ (curveAt v hcomplete x s) (t - s) := by
    intro t x htx
    have htε : |t - s| < ε := by
      have hsub : |t - t₀| < η := by
        rw [abs_lt]
        constructor <;> linarith [htx.1.1, htx.1.2]
      have htri : |t - s| ≤ |t - t₀| + |t₀ - s| := by
        calc
          |t - s| = |(t - t₀) + (t₀ - s)| := by ring_nf
          _ ≤ |t - t₀| + |t₀ - s| := abs_add_le _ _
      dsimp [η] at hsub
      nlinarith [hts, htri]
    have hxU : curveAt v hcomplete x s ∈ U := htx.2
    have hstep : curveAt v hcomplete x t = curveAt v hcomplete (curveAt v hcomplete x s) (t - s) := by
      have hh := curveAt_add v hv1 hcomplete x s (t - s)
      rw [show s + (t - s) = t by ring] at hh
      exact hh
    rw [hstep]
    exact hagree (curveAt v hcomplete x s) hxU (t - s)
      ⟨(abs_lt.mp htε).1, (abs_lt.mp htε).2⟩
  have hmain : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ (curveAt v hcomplete p.2 s) (p.1 - s)) (t₀, x₀) := by
    have hfst : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => p.1 - s) (t₀, x₀) := by
      have hsub' : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun z : ℝ => z - s) t₀ := by
        exact (contDiff_id.sub contDiff_const).contDiffAt.contMDiffAt
      have hcomp := ContMDiffAt.comp (x := (t₀, x₀)) (M := ℝ × M) (M' := ℝ) (M'' := ℝ)
        (I := 𝓘(ℝ, ℝ).prod I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
        (f := Prod.fst) (g := fun z : ℝ => z - s) hsub' (contMDiffAt_fst (p := (t₀, x₀)))
      simpa [Function.comp_def] using hcomp
    have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M => curveAt v hcomplete p.2 s) (t₀, x₀) :=
      hslice.comp (t₀, x₀)
        (contMDiffAt_snd (p := (t₀, x₀)))
    have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I)) ∞
        (fun p : ℝ × M => (p.1 - s, curveAt v hcomplete p.2 s)) (t₀, x₀) :=
      hfst.prodMk hsnd
    have hΨat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.2 q.1)
        (t₀ - s, curveAt v hcomplete x₀ s) := by
      have hpt : (t₀ - s, curveAt v hcomplete x₀ s) ∈ Ioo (-ε) ε ×ˢ U := by
        constructor
        · change t₀ - s ∈ Ioo (-ε) ε
          exact ⟨(abs_lt.mp hts).1, (abs_lt.mp hts).2⟩
        · exact hyU
      exact (hΨsm (t₀ - s, curveAt v hcomplete x₀ s) hpt).contMDiffAt (by
        exact prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨(abs_lt.mp hts).1, (abs_lt.mp hts).2⟩)
          (hUopen.mem_nhds hyU))
    have hcomp := hΨat.comp (t₀, x₀) hpair
    simpa [Function.comp_def] using hcomp
  have heq : (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) =ᶠ[𝓝 (t₀, x₀)]
      (fun p : ℝ × M => Ψ (curveAt v hcomplete p.2 s) (p.1 - s)) := by
    exact Filter.eventuallyEq_of_mem hVnhds (by intro p hp; exact (hVmain p.1 p.2 hp))
  exact hmain.congr_of_eventuallyEq heq

theorem contMDiff_curveAt [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff ∞ (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  rintro ⟨t₀, x₀⟩
  exact portPrivate_c55af3af_contMDiffAt_curveAt_of_slice v hv hcomplete t₀ x₀
    (portPrivate_c55af3af_contMDiffAt_curveAt_slice v hv hcomplete t₀ x₀)

theorem contMDiffAt_globalFlow_of_compactSupport_nonneg [FiniteDimensional ℝ E]
    [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x₀ : M) :
    ContMDiffAt I I ∞
      (fun x : M => curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x t₀) x₀ := by
  exact portPrivate_c55af3af_contMDiffAt_curveAt_slice_nonneg v hv
    (exists_globalIntegralCurve_of_compactSupport v hv hsupp) ht₀ x₀

theorem contMDiffAt_globalFlow_of_compactSupport [FiniteDimensional ℝ E] [CompleteSpace E]
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) (t₀ : ℝ) (x₀ : M) :
    ContMDiffAt I I ∞
      (fun x : M => curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x t₀) x₀ := by
  exact portPrivate_c55af3af_contMDiffAt_curveAt_slice v hv
    (exists_globalIntegralCurve_of_compactSupport v hv hsupp) t₀ x₀

theorem continuous_globalFlow_of_compactSupport [FiniteDimensional ℝ E] [CompleteSpace E]
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) :
    Continuous (fun p : ℝ × M =>
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.2 p.1) := by
  exact (contMDiff_curveAt v hv
    (exists_globalIntegralCurve_of_compactSupport v hv hsupp)).continuous

theorem contMDiffAt_globalFlow_joint_of_compactSupport_nonneg [FiniteDimensional ℝ E]
    [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x₀ : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M =>
        curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.2 p.1) (t₀, x₀) := by
  exact portPrivate_c55af3af_contMDiffAt_curveAt_of_slice v hv
    (exists_globalIntegralCurve_of_compactSupport v hv hsupp) t₀ x₀
    (contMDiffAt_globalFlow_of_compactSupport_nonneg v hv hsupp ht₀ x₀)

theorem contMDiffAt_globalFlow_joint_of_compactSupport [FiniteDimensional ℝ E] [CompleteSpace E]
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) (t₀ : ℝ) (x₀ : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M =>
        curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.2 p.1) (t₀, x₀) := by
  exact contMDiff_curveAt v hv (exists_globalIntegralCurve_of_compactSupport v hv hsupp) (t₀, x₀)

theorem contMDiff_globalFlow_joint_of_compactSupport [FiniteDimensional ℝ E] [CompleteSpace E]
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M =>
        curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.2 p.1) := by
  exact contMDiff_curveAt v hv (exists_globalIntegralCurve_of_compactSupport v hv hsupp)

theorem curveAt_eq_self_of_eq_zero [IsManifold I 1 M] [BoundarylessManifold I M]
    [T2Space M] (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    {x : M} (hvx : v x = 0) (t : ℝ) : curveAt v hcomplete x t = x := by
  exact congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv
    (curveAt_integralCurve v hcomplete x) (isMIntegralCurve_const hvx)
    (curveAt_zero v hcomplete x)) t

theorem exists_globalIntegralCurve_of_hasCompactSupport_sub_const
    [CompleteSpace E] (v : E → E) (hv : ContDiff ℝ 1 v) (c : E)
    (hsupp : HasCompactSupport (fun x => v x - c)) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ IsMIntegralCurve (I := 𝓘(ℝ, E)) γ v := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp
    (hv.sub contDiff_const) one_ne_zero
  have hlip : LipschitzWith K v := by
    refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
    simpa only [dist_sub_right] using hK.dist_le_mul a b
  obtain ⟨B, hB⟩ := hsupp.exists_bound_of_continuous (hv.continuous.sub continuous_const)
  have hB₀ : 0 ≤ B := (norm_nonneg (v 0 - c)).trans (hB 0)
  let L : NNReal := ⟨B + ‖c‖, add_nonneg hB₀ (norm_nonneg c)⟩
  have hb : ∀ y : E, ‖v y‖ ≤ L := by
    intro y
    calc
      ‖v y‖ = ‖(v y - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖v y - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ (L : ℝ) := add_le_add (hB y) le_rfl
  have hlocal : ∀ y : E, ∃ γ : ℝ → E, γ 0 = y ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ, E)) γ v (Set.Ioo (-1) 1) := by
    intro y
    let t₀ : Set.Icc (-1 : ℝ) 1 := ⟨0, by norm_num⟩
    have hp : IsPicardLindelof (fun _ : ℝ => v) t₀ y (L + 1) 0 L K :=
      IsPicardLindelof.of_time_independent (fun z _ => hb z)
        hlip.lipschitzOnWith (by simp [t₀])
    obtain ⟨γ, hγ₀, hγ⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨γ, hγ₀, ?_⟩
    intro t ht
    have hd : HasDerivAt γ (v (γ t)) t :=
      (hγ t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact hd.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn (I := 𝓘(ℝ, E))
    (contMDiff_vectorSpace_iff_contDiff.mpr hv) zero_lt_one hlocal x

end DifferentialGeometry.Analysis.ODE

end
