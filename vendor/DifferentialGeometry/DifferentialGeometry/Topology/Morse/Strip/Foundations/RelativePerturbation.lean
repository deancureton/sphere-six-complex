module

public import DifferentialGeometry.Topology.Morse.NormalForm.Manifold
public import DifferentialGeometry.Topology.Morse.Strip.Defs
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter


noncomputable section

namespace MorseExistence

section Euclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem assoc_chartHessianAt_apply {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) (u v : E) :
    QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt g x) u v =
      fderiv ℝ (fderiv ℝ g) x u v := by
  have hQ : ∀ y : E, DifferentialGeometry.Topology.Morse.chartHessianAt g x y = (fderiv ℝ (fderiv ℝ g) x y) y := fun _ => rfl
  have hs : IsSymmSndFDerivAt ℝ g x := hg.isSymmSndFDerivAt (by simp)
  have hsymm : (fderiv ℝ (fderiv ℝ g) x u) v = (fderiv ℝ (fderiv ℝ g) x v) u := hs u v
  have htwoL : 2 * (fderiv ℝ (fderiv ℝ g) x u) v =
      (fderiv ℝ (fderiv ℝ g) x (u + v)) (u + v) - (fderiv ℝ (fderiv ℝ g) x u) u -
        (fderiv ℝ (fderiv ℝ g) x v) v := by
    simp only [map_add, add_apply]
    rw [hsymm]; ring
  have htwoR : 2 * QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt g x) u v =
      DifferentialGeometry.Topology.Morse.chartHessianAt g x (u + v) - DifferentialGeometry.Topology.Morse.chartHessianAt g x u - DifferentialGeometry.Topology.Morse.chartHessianAt g x v := by
    have htwo := QuadraticMap.two_nsmul_associated (R := ℝ) (S := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt g x)
    have hxy : ((2 • QuadraticMap.associatedHom (R := ℝ) (S := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt g x)) u v) =
        ((DifferentialGeometry.Topology.Morse.chartHessianAt g x).polarBilin u v) :=
      congrArg (fun F : LinearMap.BilinMap ℝ E ℝ => F u v) htwo
    change 2 • QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt g x) u v =
      (DifferentialGeometry.Topology.Morse.chartHessianAt g x).polarBilin u v at hxy
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar] at hxy
    simpa [nsmul_eq_mul] using hxy
  have hmain : 2 * (fderiv ℝ (fderiv ℝ g) x u) v =
      2 * QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt g x) u v := by
    rw [htwoR, hQ, hQ, hQ]
    exact htwoL
  exact (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hmain).symm

theorem separatingLeft_assoc_iff {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt g x)).SeparatingLeft ↔
      ∀ v, (∀ w, fderiv ℝ (fderiv ℝ g) x v w = 0) → v = 0 := by
  unfold LinearMap.SeparatingLeft
  simp only [assoc_chartHessianAt_apply hg]

theorem chartHessianAt_congr {g₁ g₂ : E → ℝ} {x : E} (h : g₁ =ᶠ[𝓝 x] g₂) :
    DifferentialGeometry.Topology.Morse.chartHessianAt g₁ x = DifferentialGeometry.Topology.Morse.chartHessianAt g₂ x := by
  unfold DifferentialGeometry.Topology.Morse.chartHessianAt DifferentialGeometry.Topology.Morse.chartHessianBilinAt
  have : fderiv ℝ (fderiv ℝ g₁) x = fderiv ℝ (fderiv ℝ g₂) x := h.fderiv.fderiv_eq
  simp only [this]

theorem two_ne_infty : (2 : WithTop ℕ∞) ≠ ∞ := by
  decide

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  decide

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_fderiv_comp_of_fderiv_eq_zero {h : E → ℝ} {σ : F → E} {x : F}
    (hh : ContDiffAt ℝ 2 h (σ x)) (hσ : ContDiffAt ℝ 2 σ x) (hcrit : fderiv ℝ h (σ x) = 0)
    (u v : F) :
    fderiv ℝ (fderiv ℝ (h ∘ σ)) x u v =
      fderiv ℝ (fderiv ℝ h) (σ x) (fderiv ℝ σ x u) (fderiv ℝ σ x v) := by
  have hσev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 σ y := hσ.eventually two_ne_infty
  have hhev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 h (σ y) :=
    hσ.continuousAt.tendsto.eventually (hh.eventually two_ne_infty)
  have hfd : fderiv ℝ (h ∘ σ) =ᶠ[𝓝 x] fun y => (fderiv ℝ h (σ y)).comp (fderiv ℝ σ y) := by
    filter_upwards [hσev, hhev] with y hσy hhy
    exact fderiv_comp y (hhy.differentiableAt (by norm_num)) (hσy.differentiableAt (by norm_num))
  rw [hfd.fderiv_eq]
  have hc : HasFDerivAt (fun y => fderiv ℝ h (σ y))
      ((fderiv ℝ (fderiv ℝ h) (σ x)).comp (fderiv ℝ σ x)) x := by
    have h1 : HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) (σ x)) (σ x) :=
      ((hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    have h2 : HasFDerivAt σ (fderiv ℝ σ x) x :=
      (hσ.differentiableAt (by norm_num)).hasFDerivAt
    exact h1.comp x h2
  have hd : HasFDerivAt (fderiv ℝ σ) (fderiv ℝ (fderiv ℝ σ) x) x :=
    ((hσ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hcomp := hc.clm_comp hd
  rw [hcomp.fderiv]
  simp [hcrit]

theorem separatingLeft_chartHessianAt_comp_iff {h : E → ℝ} {σ : F → E} {τ : E → F} {x : F}
    (hh : ContDiffAt ℝ 2 h (σ x)) (hσ : ContDiffAt ℝ 2 σ x) (hτ : ContDiffAt ℝ 2 τ (σ x))
    (hτσ : τ ∘ σ =ᶠ[𝓝 x] id) (hστ : σ ∘ τ =ᶠ[𝓝 (σ x)] id)
    (hcrit : fderiv ℝ h (σ x) = 0) :
    (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt (h ∘ σ) x)).SeparatingLeft ↔
      (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt h (σ x))).SeparatingLeft := by
  have hhσ : ContDiffAt ℝ 2 (h ∘ σ) x := hh.comp x hσ
  rw [separatingLeft_assoc_iff hhσ, separatingLeft_assoc_iff hh]
  simp only [fderiv_fderiv_comp_of_fderiv_eq_zero hh hσ hcrit]
  set S := fderiv ℝ σ x with hS
  set T := fderiv ℝ τ (σ x) with hT
  have hτσx : τ (σ x) = x := hτσ.eq_of_nhds
  have hTS : ∀ u, T (S u) = u := by
    intro u
    have h1 : fderiv ℝ (τ ∘ σ) x = T.comp S :=
      fderiv_comp x (hτ.differentiableAt (by norm_num)) (hσ.differentiableAt (by norm_num))
    have h2 : fderiv ℝ (τ ∘ σ) x = ContinuousLinearMap.id ℝ F := by
      rw [hτσ.fderiv_eq]; exact fderiv_id
    have := congrArg (fun A : F →L[ℝ] F => A u) (h1.symm.trans h2)
    simpa using this
  have hST : ∀ w, S (T w) = w := by
    intro w
    have hσ' : DifferentiableAt ℝ σ (τ (σ x)) := by
      rw [hτσx]; exact hσ.differentiableAt (by norm_num)
    have h1 : fderiv ℝ (σ ∘ τ) (σ x) = (fderiv ℝ σ (τ (σ x))).comp T :=
      fderiv_comp (σ x) hσ' (hτ.differentiableAt (by norm_num))
    rw [hτσx] at h1
    have h2 : fderiv ℝ (σ ∘ τ) (σ x) = ContinuousLinearMap.id ℝ E := by
      rw [hστ.fderiv_eq]; exact fderiv_id
    have := congrArg (fun A : E →L[ℝ] E => A w) (h1.symm.trans h2)
    simpa using this
  constructor
  · intro H u' hu'
    have := H (T u') (fun v => by rw [hST]; exact hu' _)
    rw [← hST u', this, map_zero]
  · intro H u hu
    have : S u = 0 := H (S u) (fun w => by rw [← hST w]; exact hu (T w))
    rw [← hTS u, this, map_zero]

theorem fderiv_comp_eq_zero_iff {h : E → ℝ} {σ : F → E} {τ : E → F} {x : F}
    (hh : ContDiffAt ℝ 2 h (σ x)) (hσ : ContDiffAt ℝ 2 σ x) (hτ : ContDiffAt ℝ 2 τ (σ x))
    (hτσ : τ ∘ σ =ᶠ[𝓝 x] id) (hστ : σ ∘ τ =ᶠ[𝓝 (σ x)] id) :
    fderiv ℝ (h ∘ σ) x = 0 ↔ fderiv ℝ h (σ x) = 0 := by
  set S := fderiv ℝ σ x with hS
  set T := fderiv ℝ τ (σ x) with hT
  have hτσx : τ (σ x) = x := hτσ.eq_of_nhds
  have hST : ∀ w, S (T w) = w := by
    intro w
    have hσ' : DifferentiableAt ℝ σ (τ (σ x)) := by
      rw [hτσx]; exact hσ.differentiableAt (by norm_num)
    have h1 : fderiv ℝ (σ ∘ τ) (σ x) = (fderiv ℝ σ (τ (σ x))).comp T :=
      fderiv_comp (σ x) hσ' (hτ.differentiableAt (by norm_num))
    rw [hτσx] at h1
    have h2 : fderiv ℝ (σ ∘ τ) (σ x) = ContinuousLinearMap.id ℝ E := by
      rw [hστ.fderiv_eq]; exact fderiv_id
    have := congrArg (fun A : E →L[ℝ] E => A w) (h1.symm.trans h2)
    simpa using this
  have h1 : fderiv ℝ (h ∘ σ) x = (fderiv ℝ h (σ x)).comp S :=
    fderiv_comp x (hh.differentiableAt (by norm_num)) (hσ.differentiableAt (by norm_num))
  rw [h1]
  constructor
  · intro H
    ext w
    have := congrArg (fun A : F →L[ℝ] ℝ => A (T w)) H
    simpa [hST] using this
  · intro H
    rw [H]; simp

theorem chartHessianAt_sub_clm {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) (ℓ : E →L[ℝ] ℝ) :
    DifferentialGeometry.Topology.Morse.chartHessianAt (fun y => g y - ℓ y) x = DifferentialGeometry.Topology.Morse.chartHessianAt g x := by
  have hev : fderiv ℝ (fun y => g y - ℓ y) =ᶠ[𝓝 x] fun y => fderiv ℝ g y - ℓ := by
    filter_upwards [hg.eventually two_ne_infty] with y hy
    change fderiv ℝ (g - ⇑ℓ) y = _
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.sub ℓ.hasFDerivAt).fderiv]
  unfold DifferentialGeometry.Topology.Morse.chartHessianAt DifferentialGeometry.Topology.Morse.chartHessianBilinAt
  have : fderiv ℝ (fderiv ℝ (fun y => g y - ℓ y)) x = fderiv ℝ (fderiv ℝ g) x := by
    rw [hev.fderiv_eq]
    exact fderiv_sub_const ℓ
  simp only [this]

end Euclid

section FinModel

variable {n : ℕ}

theorem clm_apply_eq_sum (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

theorem clm_eq_zero_of_forall_single (L : (Fin n → ℝ) →L[ℝ] ℝ)
    (h : ∀ i, L (Pi.single i 1) = 0) : L = 0 := by
  ext v
  rw [clm_apply_eq_sum]
  simp [h]

def innerCLM : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => ∑ i, L i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
      map_add' := by
        intro L₁ L₂
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c L
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }

@[simp]
theorem innerCLM_apply (L y : Fin n → ℝ) : innerCLM L y = ∑ i, L i * y i := by
  simp [innerCLM]

def bilinToEnd (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).comp B

@[simp]
theorem bilinToEnd_apply (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) (i : Fin n) :
    bilinToEnd B v i = B v (Pi.single i 1) := rfl

def bilinToEndₗ :
    ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) →ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) where
  toFun := bilinToEnd
  map_add' := by
    intro B₁ B₂
    ext v i
    simp
  map_smul' := by
    intro c B
    ext v i
    simp

theorem continuous_bilinToEnd : Continuous (bilinToEnd (n := n)) := by
  have h := LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ)
    (E := ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)) (F' := ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    (bilinToEndₗ (n := n))
  exact h

theorem bilinToEnd_eq_zero_iff (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    bilinToEnd B v = 0 ↔ ∀ w, B v w = 0 := by
  constructor
  · intro h w
    have h' : B v = 0 := clm_eq_zero_of_forall_single _ fun i => by
      have := congrFun h i
      simpa using this
    simp [h']
  · intro h
    ext i
    simp [h]

theorem det_bilinToEnd_ne_zero_iff (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
    (bilinToEnd B).det ≠ 0 ↔ ∀ v, (∀ w, B v w = 0) → v = 0 := by
  have h1 : (bilinToEnd B).det = LinearMap.det ((bilinToEnd B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := rfl
  rw [h1, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  constructor
  · intro hinj v hv
    have : bilinToEnd B v = 0 := (bilinToEnd_eq_zero_iff B v).2 hv
    exact hinj (by simpa using this)
  · intro h v w hvw
    have : bilinToEnd B (v - w) = 0 := by
      have hvw' : bilinToEnd B v = bilinToEnd B w := hvw
      rw [map_sub, hvw', sub_self]
    have := h (v - w) ((bilinToEnd_eq_zero_iff B (v - w)).1 this)
    exact sub_eq_zero.1 this

def gradVec (G : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fderiv ℝ G x (Pi.single i 1)

theorem hasFDerivAt_gradVec {G : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hG : ContDiffAt ℝ 2 G x) :
    HasFDerivAt (gradVec G) (bilinToEnd (fderiv ℝ (fderiv ℝ G) x)) x := by
  have hH : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  rw [hasFDerivAt_pi']
  intro i
  have := (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ) : Fin n → ℝ)).hasFDerivAt.comp x hH
  exact this

theorem gradVec_eq_of_fderiv_sub_eq_zero {G : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hG : DifferentiableAt ℝ G x) {L : Fin n → ℝ}
    (h : fderiv ℝ (fun y => G y - innerCLM L y) x = 0) : gradVec G x = L := by
  change fderiv ℝ (G - ⇑(innerCLM L)) x = 0 at h
  rw [(hG.hasFDerivAt.sub (innerCLM L).hasFDerivAt).fderiv] at h
  ext i
  have := congrArg (fun A : (Fin n → ℝ) →L[ℝ] ℝ => A (Pi.single i 1)) h
  simp only [sub_apply, zero_apply, innerCLM_apply,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    at this
  unfold gradVec
  linarith

theorem exists_null_bad_set {G : (Fin n → ℝ) → ℝ} {C : Set (Fin n → ℝ)}
    (hG : ∀ x ∈ C, ContDiffAt ℝ 2 G x) :
    ∃ N : Set (Fin n → ℝ), MeasureTheory.volume N = 0 ∧
      ∀ L ∉ N, ∀ x ∈ C, fderiv ℝ (fun y => G y - innerCLM L y) x = 0 →
        (QuadraticMap.associated (R := ℝ)
          (DifferentialGeometry.Topology.Morse.chartHessianAt (fun y => G y - innerCLM L y) x)).SeparatingLeft := by
  refine ⟨gradVec G '' {x | x ∈ C ∧ (bilinToEnd (fderiv ℝ (fderiv ℝ G) x)).det = 0}, ?_, ?_⟩
  · exact MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero MeasureTheory.volume
      (f' := fun x => bilinToEnd (fderiv ℝ (fderiv ℝ G) x))
      (fun x hx => (hasFDerivAt_gradVec (hG x hx.1)).hasFDerivWithinAt) (fun x hx => hx.2)
  · intro L hL x hx hcrit
    have hx2 : ContDiffAt ℝ 2 G x := hG x hx
    have hgrad : gradVec G x = L :=
      gradVec_eq_of_fderiv_sub_eq_zero (hx2.differentiableAt (by norm_num)) hcrit
    have hdet : (bilinToEnd (fderiv ℝ (fderiv ℝ G) x)).det ≠ 0 := fun h => hL ⟨x, ⟨hx, h⟩, hgrad⟩
    rw [chartHessianAt_sub_clm hx2, separatingLeft_assoc_iff hx2]
    exact (det_bilinToEnd_ne_zero_iff _).1 hdet

theorem exists_mem_notMem_of_null {N : Set (Fin n → ℝ)} (hN : MeasureTheory.volume N = 0)
    {P : (Fin n → ℝ) → Prop} (hU : ∀ᶠ L in 𝓝 (0 : Fin n → ℝ), P L) : ∃ L, P L ∧ L ∉ N := by
  by_contra h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hU
  have hsub : Metric.ball (0 : Fin n → ℝ) ε ⊆ N := fun y hy =>
    by_contra fun hyN => h ⟨y, hball (Metric.mem_ball.1 hy), hyN⟩
  have h1 : MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) ε) = 0 :=
    MeasureTheory.measure_mono_null hsub hN
  exact (Metric.measure_ball_pos MeasureTheory.volume (0 : Fin n → ℝ) hε).ne' h1

theorem uniform_close_of_compact {W : Type*} [NormedAddCommGroup W]
    [ProperSpace W] {Δ : W → ℝ} (hΔ : Continuous Δ) {K : Set W} (hK : IsCompact K) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∀ B ∈ K, ∀ B', ‖B' - B‖ < δ → |Δ B' - Δ B| < η := by
  have hK₁ : IsCompact (Metric.cthickening 1 K) := hK.cthickening
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (hK₁.uniformContinuousOn_of_continuous hΔ.continuousOn) η hη
  refine ⟨min δ 1, by positivity, fun B hB B' hB' => ?_⟩
  have h1 : B' ∈ Metric.cthickening 1 K :=
    Metric.mem_cthickening_of_dist_le _ _ _ _ hB
      (by rw [dist_eq_norm]; exact hB'.le.trans (min_le_right _ _))
  have h2 : B ∈ Metric.cthickening 1 K := Metric.self_subset_cthickening _ hB
  have := hδ' _ h1 _ h2 (by rw [dist_eq_norm]; exact hB'.trans_le (min_le_left _ _))
  rwa [Real.dist_eq] at this

def matOf (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) : Fin n → Fin n → ℝ :=
  fun i j => B (Pi.single i 1) (Pi.single j 1)

theorem continuous_matOf : Continuous (matOf (n := n)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1 : ℝ) : Fin n → ℝ)).continuous.comp
    (ContinuousLinearMap.apply ℝ ((Fin n → ℝ) →L[ℝ] ℝ)
      (Pi.single i (1 : ℝ) : Fin n → ℝ)).continuous)

theorem matOf_sub (B₁ B₂ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
    matOf (B₁ - B₂) = matOf B₁ - matOf B₂ := by
  ext i j
  simp [matOf]

theorem norm_single_one_le (i : Fin n) : ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem norm_matOf_le (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) : ‖matOf B‖ ≤ ‖B‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg B)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg B)).2 fun j => ?_
  calc ‖matOf B i j‖ = ‖B (Pi.single i 1) (Pi.single j 1)‖ := rfl
    _ ≤ ‖B (Pi.single i 1)‖ * ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖B (Pi.single i 1)‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_single_one_le j) (ContinuousLinearMap.opNorm_nonneg _)
    _ = ‖B (Pi.single i 1)‖ := mul_one _
    _ ≤ ‖B‖ * ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖B‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_single_one_le i) (ContinuousLinearMap.opNorm_nonneg _)
    _ = ‖B‖ := mul_one _

theorem clm_apply_eq_sum_smul {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    (B : (Fin n → ℝ) →L[ℝ] W) (v : Fin n → ℝ) :
    B v = ∑ i, v i • B (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

theorem vecMul_matOf (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) (j : Fin n) :
    Matrix.vecMul v (Matrix.of (matOf B)) j = B v (Pi.single j 1) := by
  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, matOf]
  rw [clm_apply_eq_sum_smul B v]
  simp [smul_eq_mul]

theorem det_matOf_ne_zero_iff (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
    (Matrix.of (matOf B)).det ≠ 0 ↔ ∀ v, (∀ w, B v w = 0) → v = 0 := by
  rw [Ne, ← Matrix.exists_vecMul_eq_zero_iff]
  constructor
  · intro h v hv
    by_contra hv0
    refine h ⟨v, hv0, ?_⟩
    ext j
    rw [vecMul_matOf]
    exact hv _
  · rintro h ⟨v, hv0, hv⟩
    refine hv0 (h v fun w => ?_)
    have hB : B v = 0 := clm_eq_zero_of_forall_single _ fun j => by
      rw [← vecMul_matOf, hv]; rfl
    simp [hB]

theorem stability {G : (Fin n → ℝ) → ℝ} {C : Set (Fin n → ℝ)} (hC : IsCompact C)
    (hG : ∀ x ∈ C, ContDiffAt ℝ 2 G x)
    (hnd : ∀ x ∈ C, fderiv ℝ G x = 0 →
      (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt G x)).SeparatingLeft) :
    ∃ ε > 0, ∀ h : (Fin n → ℝ) → ℝ, (∀ x ∈ C, ContDiffAt ℝ 2 h x) →
      (∀ x ∈ C, ‖fderiv ℝ h x - fderiv ℝ G x‖ ≤ ε) →
      (∀ x ∈ C, ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ G) x‖ ≤ ε) →
      ∀ x ∈ C, fderiv ℝ h x = 0 →
        (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt h x)).SeparatingLeft := by
  classical
  set Δ : (Fin n → Fin n → ℝ) → ℝ := fun A => (Matrix.of A).det with hΔ
  have hΔc : Continuous Δ := Continuous.matrix_det continuous_id
  set Hg := fderiv ℝ (fderiv ℝ G) with hHg
  have hHgc : ContinuousOn Hg C := fun x hx =>
    (((hG x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt.continuousWithinAt
  have hDgc : ContinuousOn (fderiv ℝ G) C := fun x hx =>
    ((hG x hx).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hMc : ContinuousOn (fun x => matOf (Hg x)) C := continuous_matOf.comp_continuousOn hHgc
  set ψ : (Fin n → ℝ) → ℝ := fun x => ‖fderiv ℝ G x‖ + |Δ (matOf (Hg x))| with hψ
  have hψc : ContinuousOn ψ C :=
    hDgc.norm.add ((hΔc.comp_continuousOn hMc).abs)
  have hψpos : ∀ x ∈ C, 0 < ψ x := by
    intro x hx
    by_cases h0 : fderiv ℝ G x = 0
    · have hsep := hnd x hx h0
      rw [separatingLeft_assoc_iff (hG x hx)] at hsep
      have hdet : Δ (matOf (Hg x)) ≠ 0 := (det_matOf_ne_zero_iff _).2 hsep
      have : 0 < |Δ (matOf (Hg x))| := abs_pos.2 hdet
      simp only [hψ]
      linarith [norm_nonneg (fderiv ℝ G x)]
    · have : 0 < ‖fderiv ℝ G x‖ := norm_pos_iff.2 h0
      simp only [hψ]
      linarith [abs_nonneg (Δ (matOf (Hg x)))]
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, one_pos, fun h _ _ _ x hx => ?_⟩
    rw [hCe] at hx
    exact absurd hx (notMem_empty x)
  obtain ⟨x₀, hx₀, hmin⟩ := hC.exists_isMinOn hCne hψc
  set m := ψ x₀ with hm
  have hmpos : 0 < m := hψpos x₀ hx₀
  have hmle : ∀ x ∈ C, m ≤ ψ x := fun x hx => hmin hx
  have hK : IsCompact ((fun x => matOf (Hg x)) '' C) := hC.image_of_continuousOn hMc
  obtain ⟨δ, hδ, hδ'⟩ := uniform_close_of_compact hΔc hK (half_pos hmpos)
  refine ⟨min (m / 2) (δ / 2), by positivity, ?_⟩
  intro h hh h1 h2 x hx hcrit
  set ε := min (m / 2) (δ / 2) with hε
  have hε1 : ε ≤ m / 2 := min_le_left _ _
  have hε2 : ε ≤ δ / 2 := min_le_right _ _
  have hDg : ‖fderiv ℝ G x‖ ≤ ε := by
    have := h1 x hx
    rwa [hcrit, zero_sub, norm_neg] at this
  have hΔg : m / 2 ≤ |Δ (matOf (Hg x))| := by
    have := hmle x hx
    simp only [hψ] at this
    linarith
  have hdist : ‖matOf (fderiv ℝ (fderiv ℝ h) x) - matOf (Hg x)‖ < δ := by
    rw [← matOf_sub]
    calc ‖matOf (fderiv ℝ (fderiv ℝ h) x - Hg x)‖ ≤ ‖fderiv ℝ (fderiv ℝ h) x - Hg x‖ :=
          norm_matOf_le _
      _ ≤ ε := h2 x hx
      _ < δ := by linarith
  have hclose := hδ' _ (mem_image_of_mem _ hx) _ hdist
  have hdet : Δ (matOf (fderiv ℝ (fderiv ℝ h) x)) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hclose
    linarith
  rw [separatingLeft_assoc_iff (hh x hx)]
  exact (det_matOf_ne_zero_iff _).1 hdet

theorem norm_compL_le (A : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg A) fun B => ?_
  rw [ContinuousLinearMap.compL_apply]
  exact ContinuousLinearMap.opNorm_comp_le A B

theorem fderiv_pert_eq {G : (Fin n → ℝ) → ℝ} {Ψ : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hG : DifferentiableAt ℝ G x) (hΨ : DifferentiableAt ℝ Ψ x) (L : Fin n → ℝ) :
    fderiv ℝ (fun y => G y - innerCLM L (Ψ y)) x =
      fderiv ℝ G x - (innerCLM L).comp (fderiv ℝ Ψ x) := by
  have h : HasFDerivAt (fun y => innerCLM L (Ψ y)) ((innerCLM L).comp (fderiv ℝ Ψ x)) x :=
    (innerCLM L).hasFDerivAt.comp x hΨ.hasFDerivAt
  exact (hG.hasFDerivAt.sub h).fderiv

theorem eventually_nondegenerate_pert {G : (Fin n → ℝ) → ℝ} {Ψ : (Fin n → ℝ) → (Fin n → ℝ)}
    {C U : Set (Fin n → ℝ)} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hG : ContDiffOn ℝ ∞ G U) (hΨ : ContDiffOn ℝ ∞ Ψ U)
    (hnd : ∀ x ∈ C, fderiv ℝ G x = 0 →
      (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt G x)).SeparatingLeft) :
    ∀ᶠ L in 𝓝 (0 : Fin n → ℝ), ∀ x ∈ C, fderiv ℝ (fun y => G y - innerCLM L (Ψ y)) x = 0 →
      (QuadraticMap.associated (R := ℝ)
        (DifferentialGeometry.Topology.Morse.chartHessianAt (fun y => G y - innerCLM L (Ψ y)) x)).SeparatingLeft := by
  have hG2 : ∀ x ∈ C, ContDiffAt ℝ 2 G x := fun x hx =>
    (hG.contDiffAt (hU.mem_nhds (hCU hx))).of_le two_le_infty
  obtain ⟨ε, hε, hstab⟩ := stability hC hG2 hnd
  have hG1 : ContDiffOn ℝ ∞ (fderiv ℝ G) U := hG.fderiv_of_isOpen hU (by simp)
  have hΨ1 : ContDiffOn ℝ ∞ (fderiv ℝ Ψ) U := hΨ.fderiv_of_isOpen hU (by simp)
  have hΨ1c : ContinuousOn (fderiv ℝ Ψ) U := hΨ.continuousOn_fderiv_of_isOpen hU (by simp)
  have hΨ2c : ContinuousOn (fderiv ℝ (fderiv ℝ Ψ)) U :=
    hΨ1.continuousOn_fderiv_of_isOpen hU (by simp)
  obtain ⟨M₁, hM₁⟩ := IsCompact.exists_bound_of_continuousOn
    (E := (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) hC (hΨ1c.mono hCU)
  obtain ⟨M₂, hM₂⟩ := IsCompact.exists_bound_of_continuousOn
    (E := (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) hC (hΨ2c.mono hCU)
  set Mb := max (max M₁ M₂) 0 with hMb
  have hMb0 : 0 ≤ Mb := le_max_right _ _
  have hM₁' : ∀ x ∈ C, ‖fderiv ℝ Ψ x‖ ≤ Mb := fun x hx =>
    (hM₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hM₂' : ∀ x ∈ C, ‖fderiv ℝ (fderiv ℝ Ψ) x‖ ≤ Mb := fun x hx =>
    (hM₂ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
  set K₀ := ‖(innerCLM : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)‖ with hK₀
  have hK₀0 : 0 ≤ K₀ := ContinuousLinearMap.opNorm_nonneg _
  refine Metric.eventually_nhds_iff.2 ⟨ε / (K₀ * Mb + 1), by positivity, fun L hL => ?_⟩
  rw [dist_zero_right] at hL
  have hLM : ‖innerCLM L‖ * Mb ≤ ε := by
    have h1 : ‖innerCLM L‖ ≤ K₀ * ‖L‖ := ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖L‖ * (K₀ * Mb + 1) < ε := by
      rwa [lt_div_iff₀ (by positivity)] at hL
    nlinarith [norm_nonneg L, ContinuousLinearMap.opNorm_nonneg (innerCLM L)]
  set h : (Fin n → ℝ) → ℝ := fun y => G y - innerCLM L (Ψ y) with hh
  have hGd : ∀ y ∈ U, DifferentiableAt ℝ G y := fun y hy =>
    (hG.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hΨd : ∀ y ∈ U, DifferentiableAt ℝ Ψ y := fun y hy =>
    (hΨ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hfd : ∀ y ∈ U, fderiv ℝ h y = fderiv ℝ G y - (innerCLM L).comp (fderiv ℝ Ψ y) :=
    fun y hy => fderiv_pert_eq (hGd y hy) (hΨd y hy) L
  have hh2 : ∀ x ∈ C, ContDiffAt ℝ 2 h x := by
    intro x hx
    have h1 : ContDiffAt ℝ ∞ G x := hG.contDiffAt (hU.mem_nhds (hCU hx))
    have h2 : ContDiffAt ℝ ∞ (fun y => innerCLM L (Ψ y)) x :=
      (innerCLM L).contDiff.contDiffAt.comp x (hΨ.contDiffAt (hU.mem_nhds (hCU hx)))
    exact (h1.sub h2).of_le two_le_infty
  refine hstab h hh2 (fun x hx => ?_) (fun x hx => ?_)
  · rw [hfd x (hCU hx), sub_sub_cancel_left, norm_neg]
    calc ‖(innerCLM L).comp (fderiv ℝ Ψ x)‖ ≤ ‖innerCLM L‖ * ‖fderiv ℝ Ψ x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖innerCLM L‖ * Mb :=
          mul_le_mul_of_nonneg_left (hM₁' x hx) (ContinuousLinearMap.opNorm_nonneg _)
      _ ≤ ε := hLM
  · have hev : fderiv ℝ h =ᶠ[𝓝 x] fun y => fderiv ℝ G y -
        ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ (innerCLM L) (fderiv ℝ Ψ y) := by
      filter_upwards [hU.mem_nhds (hCU hx)] with y hy
      rw [hfd y hy, ContinuousLinearMap.compL_apply]
    have hG2d : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
      ((hG1.contDiffAt (hU.mem_nhds (hCU hx))).differentiableAt (by simp)).hasFDerivAt
    have hΨ2d : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) x) x :=
      ((hΨ1.contDiffAt (hU.mem_nhds (hCU hx))).differentiableAt (by simp)).hasFDerivAt
    have hcomp := (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ
      (innerCLM L)).hasFDerivAt.comp x hΨ2d
    have hfd2 : fderiv ℝ (fun y => fderiv ℝ G y -
        ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ (innerCLM L) (fderiv ℝ Ψ y)) x =
        fderiv ℝ (fderiv ℝ G) x - (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ
          (innerCLM L)).comp (fderiv ℝ (fderiv ℝ Ψ) x) := (hG2d.sub hcomp).fderiv
    have hcancel : fderiv ℝ (fderiv ℝ G) x - (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ
          (innerCLM L)).comp (fderiv ℝ (fderiv ℝ Ψ) x) - fderiv ℝ (fderiv ℝ G) x =
        -((ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ
          (innerCLM L)).comp (fderiv ℝ (fderiv ℝ Ψ) x)) := by abel
    have hnn : ‖-((ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ
          (innerCLM L)).comp (fderiv ℝ (fderiv ℝ Ψ) x))‖ =
        ‖(ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ
          (innerCLM L)).comp (fderiv ℝ (fderiv ℝ Ψ) x)‖ := ContinuousLinearMap.opNorm_neg _
    rw [hev.fderiv_eq, hfd2, hcancel, hnn]
    calc ‖(ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ (innerCLM L)).comp
          (fderiv ℝ (fderiv ℝ Ψ) x)‖
        ≤ ‖ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ (innerCLM L)‖ *
            ‖fderiv ℝ (fderiv ℝ Ψ) x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖innerCLM L‖ * Mb :=
          mul_le_mul (norm_compL_le _) (hM₂' x hx) (ContinuousLinearMap.opNorm_nonneg _)
            (ContinuousLinearMap.opNorm_nonneg _)
      _ ≤ ε := hLM

end FinModel

section Manifold

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M]

def chartRep (I : ModelWithCorners ℝ (Fin n → ℝ) H) (g : M → ℝ) (q : M) : (Fin n → ℝ) → ℝ :=
  fun y => g ((extChartAt I q).symm y)

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem hessianAt_eq (g : M → ℝ) (p : M) :
    hessianAt I g p = DifferentialGeometry.Topology.Morse.chartHessianAt (chartRep I g p) (extChartAt I p p) := rfl

omit [I.Boundaryless] in
theorem contDiffOn_chartRep {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (q : M) :
    ContDiffOn ℝ ∞ (chartRep I g q) (extChartAt I q).target := by
  have := hg.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := I) (n := ∞) q)
  exact contMDiffOn_iff_contDiffOn.1 this

theorem contDiffAt_chartRep {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {q : M}
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt I q).target) :
    ContDiffAt ℝ ∞ (chartRep I g q) y :=
  (contDiffOn_chartRep hg q).contDiffAt ((isOpen_extChartAt_target q).mem_nhds hy)

theorem isCriticalPointAt_iff_fderiv_of_localInverse (I : ModelWithCorners ℝ (Fin n → ℝ) H)
    {x : M} {σ : M → Fin n → ℝ} {τ : (Fin n → ℝ) → M} {h : (Fin n → ℝ) → ℝ}
    (hleft : (τ ∘ σ) =ᶠ[nhds x] id)
    (hright : (σ ∘ τ) =ᶠ[nhds (σ x)] id)
    (hσmd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) σ x)
    (hτmd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I τ (σ x))
    (hh : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ h (σ x)) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (h ∘ σ) x ↔ fderiv ℝ h (σ x) = 0 := by
  exact DifferentialGeometry.Topology.Morse.isCriticalPointAt_iff_fderiv_of_localInverse
    I hleft hright hσmd hτmd hh

theorem isCriticalPointAt_iff_chart {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) {p q : M}
    (hp : p ∈ (extChartAt I q).source) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p ↔ fderiv ℝ (chartRep I g q) (extChartAt I q p) = 0 := by
  set e := extChartAt I q with he
  have hp' : p ∈ (chartAt H q).source := by rwa [extChartAt_source] at hp
  have htgt : e.target ∈ 𝓝 (e p) :=
    (isOpen_extChartAt_target q).mem_nhds (e.map_source hp)
  have hleft : ((e.symm : (Fin n → ℝ) → M) ∘ (e : M → Fin n → ℝ)) =ᶠ[𝓝 p] id := by
    filter_upwards [extChartAt_source_mem_nhds' hp] with x hx
    exact e.left_inv hx
  have hright : ((e : M → Fin n → ℝ) ∘ (e.symm : (Fin n → ℝ) → M)) =ᶠ[𝓝 (e p)] id := by
    filter_upwards [htgt] with y hy
    exact e.right_inv hy
  have hσmd : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) e p :=
    (contMDiffAt_extChartAt' (n := ∞) hp').mdifferentiableAt (by simp)
  have hτmd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) I e.symm (e p) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt htgt).mdifferentiableAt (by simp)
  have hh : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (chartRep I g q) (e p) :=
    (hg _).comp _ ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt htgt)
  have key := isCriticalPointAt_iff_fderiv_of_localInverse I
    hleft hright hσmd hτmd hh
  have heq : g =ᶠ[𝓝 p] (chartRep I g q ∘ e) := by
    filter_upwards [extChartAt_source_mem_nhds' hp] with x hx
    change g x = g (e.symm (e x))
    rw [e.left_inv hx]
  unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt
  rw [heq.mfderiv_eq]
  exact key

theorem contDiffAt_transition {p q x : M} (hxp : x ∈ (extChartAt I p).source)
    (hxq : x ∈ (extChartAt I q).source) :
    ContDiffAt ℝ ∞ (extChartAt I q ∘ (extChartAt I p).symm) (extChartAt I p x) := by
  rw [← contMDiffAt_iff_contDiffAt]
  have hxq' : x ∈ (chartAt H q).source := by rwa [extChartAt_source] at hxq
  have h1 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) I ∞ (extChartAt I p).symm (extChartAt I p x) :=
    (contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds ((extChartAt I p).map_source hxp))
  have h2 : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (extChartAt I q)
      ((extChartAt I p).symm (extChartAt I p x)) := by
    rw [(extChartAt I p).left_inv hxp]
    exact contMDiffAt_extChartAt' hxq'
  exact h2.comp _ h1

omit [IsManifold I ∞ M] in
theorem isOpen_transition_domain (p q : M) :
    IsOpen ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' (extChartAt I q).source) :=
  (continuousOn_extChartAt_symm p).isOpen_inter_preimage (isOpen_extChartAt_target p)
    (isOpen_extChartAt_source q)

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem mem_transition_domain {p q x : M} (hxp : x ∈ (extChartAt I p).source)
    (hxq : x ∈ (extChartAt I q).source) :
    extChartAt I p x ∈
      (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' (extChartAt I q).source := by
  refine ⟨(extChartAt I p).map_source hxp, ?_⟩
  simp only [mem_preimage, (extChartAt I p).left_inv hxp]
  exact hxq

omit [IsManifold I ∞ M] in
theorem transition_eventuallyEq_id {p q x : M} (hxp : x ∈ (extChartAt I p).source)
    (hxq : x ∈ (extChartAt I q).source) :
    ((extChartAt I p ∘ (extChartAt I q).symm) ∘ (extChartAt I q ∘ (extChartAt I p).symm))
      =ᶠ[𝓝 (extChartAt I p x)] id := by
  filter_upwards [(isOpen_transition_domain p q).mem_nhds (mem_transition_domain hxp hxq)]
    with y hy
  simp only [Function.comp_apply, id]
  rw [(extChartAt I q).left_inv hy.2, (extChartAt I p).right_inv hy.1]

omit [IsManifold I ∞ M] in
theorem chartRep_eventuallyEq (g : M → ℝ) {p q x : M} (hxp : x ∈ (extChartAt I p).source)
    (hxq : x ∈ (extChartAt I q).source) :
    chartRep I g p =ᶠ[𝓝 (extChartAt I p x)]
      (chartRep I g q ∘ (extChartAt I q ∘ (extChartAt I p).symm)) := by
  filter_upwards [(isOpen_transition_domain p q).mem_nhds (mem_transition_domain hxp hxq)]
    with y hy
  simp only [chartRep, Function.comp_apply, (extChartAt I q).left_inv hy.2]

theorem isNondegenerateCriticalPointAt_iff_chart {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    {p q : M} (hp : p ∈ (extChartAt I q).source) :
    DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g p ↔
      (fderiv ℝ (chartRep I g q) (extChartAt I q p) = 0 ∧
        (QuadraticMap.associated (R := ℝ)
          (DifferentialGeometry.Topology.Morse.chartHessianAt (chartRep I g q) (extChartAt I q p))).SeparatingLeft) := by
  have hcrit := isCriticalPointAt_iff_chart hg hp
  unfold DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt
  rw [hcrit]
  refine and_congr_right fun hc => ?_
  change (QuadraticMap.associated (R := ℝ) (hessianAt I g p)).SeparatingLeft ↔ _
  rw [hessianAt_eq]
  have hpp : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  rw [chartHessianAt_congr (chartRep_eventuallyEq g hpp hp)]
  set σ := extChartAt I q ∘ (extChartAt I p).symm with hσdef
  set τ := extChartAt I p ∘ (extChartAt I q).symm with hτdef
  have hσx : σ (extChartAt I p p) = extChartAt I q p := by
    simp [hσdef]
  have hσ : ContDiffAt ℝ 2 σ (extChartAt I p p) :=
    (contDiffAt_transition hpp hp).of_le two_le_infty
  have hτ : ContDiffAt ℝ 2 τ (σ (extChartAt I p p)) := by
    rw [hσx]; exact (contDiffAt_transition hp hpp).of_le two_le_infty
  have hτσ : τ ∘ σ =ᶠ[𝓝 (extChartAt I p p)] id := transition_eventuallyEq_id hpp hp
  have hστ : σ ∘ τ =ᶠ[𝓝 (σ (extChartAt I p p))] id := by
    rw [hσx]; exact transition_eventuallyEq_id hp hpp
  have hh : ContDiffAt ℝ 2 (chartRep I g q) (σ (extChartAt I p p)) := by
    rw [hσx]
    exact (contDiffAt_chartRep hg ((extChartAt I q).map_source hp)).of_le two_le_infty
  have hc' : fderiv ℝ (chartRep I g q) (σ (extChartAt I p p)) = 0 := by rw [hσx]; exact hc
  have := separatingLeft_chartHessianAt_comp_iff hh hσ hτ hτσ hστ hc'
  rw [hσx] at this
  exact this

theorem isOpen_regular {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) :
    IsOpen {x | ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hxs : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  rw [mem_ofPred_eq, isCriticalPointAt_iff_chart hg hxs] at hx
  have hcont : ContinuousOn (fderiv ℝ (chartRep I g x)) (extChartAt I x).target :=
    (contDiffOn_chartRep hg x).continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target x)
      (by simp)
  have hne : ∀ᶠ y in 𝓝 (extChartAt I x x), fderiv ℝ (chartRep I g x) y ≠ 0 :=
    (hcont.continuousAt ((isOpen_extChartAt_target x).mem_nhds
      (mem_extChartAt_target x))).eventually_ne hx
  have hcx : ContinuousAt (extChartAt I x) x := continuousAt_extChartAt x
  filter_upwards [hcx.tendsto.eventually hne, extChartAt_source_mem_nhds (I := I) x] with y hy hys
  rw [isCriticalPointAt_iff_chart hg hys]
  exact hy

section Step

variable [T2Space M]

def bumpPert {c : M} (b : SmoothBumpFunction I c) (L : Fin n → ℝ) : M → ℝ :=
  fun x => b x * innerCLM L (extChartAt I c x)

omit [I.Boundaryless] in
theorem contMDiff_bumpPert {c : M} (b : SmoothBumpFunction I c) (L : Fin n → ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (bumpPert b L) := by
  have hφ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => innerCLM L (extChartAt I c x))
      (chartAt H c).source :=
    (innerCLM L).contMDiff.comp_contMDiffOn contMDiffOn_extChartAt
  exact b.contMDiff_smul hφ

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
theorem abs_bumpPert_le {c : M} (b : SmoothBumpFunction I c) (L : Fin n → ℝ) (x : M) :
    |bumpPert b L x| ≤ ‖innerCLM L‖ * (‖extChartAt I c c‖ + b.rOut) := by
  have hR : 0 ≤ ‖extChartAt I c c‖ + b.rOut := add_nonneg (norm_nonneg _) b.rOut_pos.le
  have hL0 : 0 ≤ ‖innerCLM L‖ := ContinuousLinearMap.opNorm_nonneg _
  by_cases hx : x ∈ Function.support b
  · rw [b.support_eq_inter_preimage] at hx
    obtain ⟨-, hx2⟩ := hx
    rw [mem_preimage, Metric.mem_ball, dist_eq_norm] at hx2
    have hnorm : ‖extChartAt I c x‖ ≤ ‖extChartAt I c c‖ + b.rOut := by
      have := norm_sub_norm_le (extChartAt I c x) (extChartAt I c c)
      linarith
    have hb1 : |b x| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [b.nonneg (x := x)], b.le_one⟩
    have hℓ : |innerCLM L (extChartAt I c x)| ≤ ‖innerCLM L‖ * ‖extChartAt I c x‖ :=
      (innerCLM L).le_opNorm _
    calc |bumpPert b L x| = |b x| * |innerCLM L (extChartAt I c x)| := abs_mul _ _
      _ ≤ 1 * (‖innerCLM L‖ * ‖extChartAt I c x‖) :=
          mul_le_mul hb1 hℓ (abs_nonneg _) zero_le_one
      _ ≤ ‖innerCLM L‖ * (‖extChartAt I c c‖ + b.rOut) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hnorm hL0
  · have : b x = 0 := Function.notMem_support.1 hx
    simp only [bumpPert, this, zero_mul, abs_zero]
    positivity

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
theorem chartRep_sub_bumpPert {c : M} (b : SmoothBumpFunction I c) (L : Fin n → ℝ) (g : M → ℝ)
    (q : M) :
    chartRep I (fun x => g x - bumpPert b L x) q = fun y => chartRep I g q y -
      innerCLM L (b ((extChartAt I q).symm y) • extChartAt I c ((extChartAt I q).symm y)) := by
  funext y
  simp only [chartRep, bumpPert, map_smul, smul_eq_mul]

omit [I.Boundaryless] in
theorem contDiffOn_bumpVec {c : M} (b : SmoothBumpFunction I c) (q : M) :
    ContDiffOn ℝ ∞ (fun y => b ((extChartAt I q).symm y) •
      extChartAt I c ((extChartAt I q).symm y)) (extChartAt I q).target := by
  have h1 : ContMDiff I 𝓘(ℝ, Fin n → ℝ) ∞ (fun x => b x • extChartAt I c x) :=
    b.contMDiff_smul contMDiffOn_extChartAt
  have := h1.comp_contMDiffOn (contMDiffOn_extChartAt_symm (n := ∞) q)
  exact contMDiffOn_iff_contDiffOn.1 this

theorem step {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    {ι : Type*} [Finite ι] {Cs : ι → Set M} {cs : ι → M} (hCs : ∀ j, IsCompact (Cs j))
    (hCsub : ∀ j, Cs j ⊆ (extChartAt I (cs j)).source)
    (hnd : ∀ j, ∀ p ∈ Cs j, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p → DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g p)
    {c : M} (b : SmoothBumpFunction I c) {ρ : ℝ} (hρ : ρ < b.rIn) {τ : ℝ} (hτ : 0 < τ) :
    ∃ g' : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g' ∧ (∀ x, x ∉ Function.support b → g' x = g x) ∧
      (∀ x, |g' x - g x| ≤ τ) ∧
      (∀ j, ∀ p ∈ Cs j, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g' p → DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g' p) ∧
      (∀ p ∈ (extChartAt I c).symm '' Metric.closedBall (extChartAt I c c) ρ,
        DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g' p → DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g' p) := by
  classical
  have hC₀T : Metric.closedBall (extChartAt I c c) ρ ⊆ (extChartAt I c).target := by
    intro y hy
    apply b.closedBall_subset
    refine ⟨Metric.closedBall_subset_closedBall (hρ.le.trans b.rIn_lt_rOut.le) hy, ?_⟩
    rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact mem_univ _
  have hG2 : ∀ y ∈ Metric.closedBall (extChartAt I c c) ρ, ContDiffAt ℝ 2 (chartRep I g c) y :=
    fun y hy => (contDiffAt_chartRep hg (hC₀T hy)).of_le two_le_infty
  obtain ⟨N, hN, hgood⟩ := exists_null_bad_set hG2
  have hold : ∀ j, ∀ᶠ L in 𝓝 (0 : Fin n → ℝ), ∀ y ∈ extChartAt I (cs j) '' Cs j,
      fderiv ℝ (fun y' => chartRep I g (cs j) y' - innerCLM L (b ((extChartAt I (cs j)).symm y') •
        extChartAt I c ((extChartAt I (cs j)).symm y'))) y = 0 →
      (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt (fun y' => chartRep I g (cs j) y' -
        innerCLM L (b ((extChartAt I (cs j)).symm y') •
          extChartAt I c ((extChartAt I (cs j)).symm y'))) y)).SeparatingLeft := by
    intro j
    have hCj : IsCompact (extChartAt I (cs j) '' Cs j) :=
      (hCs j).image_of_continuousOn ((continuousOn_extChartAt (I := I) (cs j)).mono (hCsub j))
    have hCjT : extChartAt I (cs j) '' Cs j ⊆ (extChartAt I (cs j)).target := by
      rintro y ⟨p, hp, rfl⟩; exact (extChartAt I (cs j)).map_source (hCsub j hp)
    have hndj : ∀ y ∈ extChartAt I (cs j) '' Cs j, fderiv ℝ (chartRep I g (cs j)) y = 0 →
        (QuadraticMap.associated (R := ℝ)
          (DifferentialGeometry.Topology.Morse.chartHessianAt (chartRep I g (cs j)) y)).SeparatingLeft := by
      rintro y ⟨p, hp, rfl⟩ hy
      have hcrit : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p := (isCriticalPointAt_iff_chart hg (hCsub j hp)).2 hy
      exact ((isNondegenerateCriticalPointAt_iff_chart hg (hCsub j hp)).1 (hnd j p hp hcrit)).2
    exact eventually_nondegenerate_pert hCj (isOpen_extChartAt_target (cs j)) hCjT
      (contDiffOn_chartRep hg (cs j)) (contDiffOn_bumpVec b (cs j)) hndj
  have hold' := Filter.eventually_all.2 hold
  have hsup : ∀ᶠ L in 𝓝 (0 : Fin n → ℝ),
      ‖innerCLM L‖ * (‖extChartAt I c c‖ + b.rOut) ≤ τ := by
    have hR0 : 0 ≤ ‖extChartAt I c c‖ + b.rOut := add_nonneg (norm_nonneg _) b.rOut_pos.le
    set K₀ := ‖(innerCLM : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)‖ with hK₀
    have hK₀0 : 0 ≤ K₀ := ContinuousLinearMap.opNorm_nonneg _
    refine Metric.eventually_nhds_iff.2
      ⟨τ / (K₀ * (‖extChartAt I c c‖ + b.rOut) + 1), by positivity, fun L hL => ?_⟩
    rw [dist_zero_right] at hL
    have h1 : ‖innerCLM L‖ ≤ K₀ * ‖L‖ := ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖L‖ * (K₀ * (‖extChartAt I c c‖ + b.rOut) + 1) < τ := by
      rwa [lt_div_iff₀ (by positivity)] at hL
    nlinarith [norm_nonneg L, ContinuousLinearMap.opNorm_nonneg (innerCLM L)]
  obtain ⟨L, ⟨hLold, hLsup⟩, hLN⟩ := exists_mem_notMem_of_null hN (hold'.and hsup)
  have hg' : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => g x - bumpPert b L x) :=
    hg.sub (contMDiff_bumpPert b L)
  refine ⟨fun x => g x - bumpPert b L x, hg', ?_, ?_, ?_, ?_⟩
  · intro x hx
    have : b x = 0 := Function.notMem_support.1 hx
    simp [bumpPert, this]
  · intro x
    rw [sub_sub_cancel_left, abs_neg]
    exact (abs_bumpPert_le b L x).trans hLsup
  · intro j p hp hcrit
    rw [isNondegenerateCriticalPointAt_iff_chart hg' (hCsub j hp)]
    rw [isCriticalPointAt_iff_chart hg' (hCsub j hp)] at hcrit
    rw [chartRep_sub_bumpPert] at hcrit ⊢
    exact ⟨hcrit, hLold j _ ⟨p, hp, rfl⟩ hcrit⟩
  · rintro p ⟨y, hy, rfl⟩ hcrit
    have hyT : y ∈ (extChartAt I c).target := hC₀T hy
    have hp : (extChartAt I c).symm y ∈ (extChartAt I c).source := (extChartAt I c).map_target hyT
    have hey : extChartAt I c ((extChartAt I c).symm y) = y := (extChartAt I c).right_inv hyT
    rw [isNondegenerateCriticalPointAt_iff_chart hg' hp, hey]
    rw [isCriticalPointAt_iff_chart hg' hp, hey] at hcrit
    have hb1 : b =ᶠ[𝓝 ((extChartAt I c).symm y)] 1 := by
      refine b.eventuallyEq_one_of_dist_lt ?_ ?_
      · rw [← extChartAt_source I]; exact hp
      · rw [hey]
        exact lt_of_le_of_lt (Metric.mem_closedBall.1 hy) hρ
    have hcont : ContinuousAt (extChartAt I c).symm y :=
      (continuousOn_extChartAt_symm c).continuousAt ((isOpen_extChartAt_target c).mem_nhds hyT)
    have hloc : chartRep I (fun x => g x - bumpPert b L x) c =ᶠ[𝓝 y]
        fun y' => chartRep I g c y' - innerCLM L y' := by
      filter_upwards [hcont.tendsto.eventually hb1, (isOpen_extChartAt_target c).mem_nhds hyT]
        with y' h1 hT
      simp only [Pi.one_apply] at h1
      simp only [chartRep, bumpPert]
      rw [h1, (extChartAt I c).right_inv hT, one_mul]
    rw [hloc.fderiv_eq] at hcrit
    rw [hloc.fderiv_eq, chartHessianAt_congr hloc]
    exact ⟨hcrit, hgood L hLN y hy hcrit⟩

end Step

end Manifold

end MorseExistence

open MorseExistence

theorem exists_morseStrip_proof {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b := by
  classical
  have hfc : Continuous f := hf.continuous
  obtain ⟨δ, hδ, hδab, hcollar⟩ : ∃ δ > 0, δ ≤ b - a ∧ ∀ x, f x ∈ Icc a b →
      (f x ≤ a + δ ∨ b - δ ≤ f x) → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    have hclosed : IsClosed {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} := by
      have := (isOpen_regular hf).isClosed_compl
      convert this using 1
      ext x; simp
    have hCrit : IsCompact (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) :=
      hcompact.inter_right hclosed
    have hS : IsCompact (f '' (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})) := hCrit.image hfc
    have ha : a ∉ f '' (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) := by
      rintro ⟨x, ⟨-, hx2⟩, hx3⟩; exact hreg x (Or.inl hx3) hx2
    have hb : b ∉ f '' (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) := by
      rintro ⟨x, ⟨-, hx2⟩, hx3⟩; exact hreg x (Or.inr hx3) hx2
    obtain ⟨δ₁, hδ₁, h1⟩ := Metric.mem_nhds_iff.1 (hS.isClosed.isOpen_compl.mem_nhds ha)
    obtain ⟨δ₂, hδ₂, h2⟩ := Metric.mem_nhds_iff.1 (hS.isClosed.isOpen_compl.mem_nhds hb)
    refine ⟨min (min δ₁ δ₂ / 2) (b - a), by positivity, min_le_right _ _,
      fun x hx hx' hcrit => ?_⟩
    have hmem : f x ∈ f '' (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) := ⟨x, ⟨hx, hcrit⟩, rfl⟩
    have hm1 : min (min δ₁ δ₂ / 2) (b - a) ≤ δ₁ / 2 := by
      refine (min_le_left _ _).trans ?_
      exact div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two
    have hm2 : min (min δ₁ δ₂ / 2) (b - a) ≤ δ₂ / 2 := by
      refine (min_le_left _ _).trans ?_
      exact div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two
    rcases hx' with h | h
    · refine h1 ?_ hmem
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1]
    · refine h2 ?_ hmem
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.2]
  set K' := f ⁻¹' Icc (a + δ / 2) (b - δ / 2) with hK'def
  set V' := f ⁻¹' Ioo (a + δ / 4) (b - δ / 4) with hV'def
  set R := f ⁻¹' Icc (a + δ / 4) (a + δ / 2) ∪ f ⁻¹' Icc (b - δ / 2) (b - δ / 4) with hRdef
  have hK' : IsCompact K' :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hV' : IsOpen V' := isOpen_Ioo.preimage hfc
  have hR : IsCompact R := by
    refine hcompact.of_isClosed_subset
      ((isClosed_Icc.preimage hfc).union (isClosed_Icc.preimage hfc)) ?_
    rintro x (hx | hx)
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hK'V' : K' ⊆ V' := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hV'strip : V' ⊆ f ⁻¹' Ioo a b := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hRreg : ∀ x ∈ R, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    rintro x (hx | hx)
    · exact hcollar x ⟨by linarith [hx.1], by linarith [hx.2]⟩ (Or.inl (by linarith [hx.2]))
    · exact hcollar x ⟨by linarith [hx.1], by linarith [hx.2]⟩ (Or.inr (by linarith [hx.1]))
  have hr : ∀ q : M, ∃ r > 0,
      Metric.closedBall (extChartAt I q q) r ⊆ (extChartAt I q).target := by
    intro q
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (extChartAt_target_mem_nhds (I := I) q)
    exact ⟨ε / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
  choose r hr0 hrT using hr
  obtain ⟨tR, -, htR⟩ := hR.elim_nhds_subcover
    (fun q => (chartAt H q).source ∩ extChartAt I q ⁻¹' Metric.ball (extChartAt I q q) (r q))
    (fun q _ => (isOpen_extChartAt_preimage q Metric.isOpen_ball).mem_nhds
      ⟨mem_chart_source H q, Metric.mem_ball_self (hr0 q)⟩)
  have hDcomp : ∀ q : M,
      IsCompact (R ∩ (extChartAt I q).symm '' Metric.closedBall (extChartAt I q q) (r q)) :=
    fun q => hR.inter_right ((isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm q).mono (hrT q))).isClosed
  have hDsub : ∀ q : M, R ∩ (extChartAt I q).symm '' Metric.closedBall (extChartAt I q q) (r q) ⊆
      (extChartAt I q).source := by
    rintro q x ⟨-, y, hy, rfl⟩; exact (extChartAt I q).map_target (hrT q hy)
  have hDnd : ∀ q : M,
      ∀ p ∈ R ∩ (extChartAt I q).symm '' Metric.closedBall (extChartAt I q q) (r q),
      DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p → DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f p :=
    fun q p hp hcrit => absurd hcrit (hRreg p hp.1)
  have hb : ∀ c : M, ∃ b : SmoothBumpFunction I c, c ∈ K' → tsupport b ⊆ V' := by
    intro c
    by_cases hc : c ∈ K'
    · obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) c).mem_iff.1
        (hV'.mem_nhds (hK'V' hc))
      exact ⟨b, fun _ => hb⟩
    · exact ⟨Classical.arbitrary _, fun h => absurd h hc⟩
  choose bump hbump using hb
  obtain ⟨tB, htBK', htB⟩ := hK'.elim_nhds_subcover
    (fun c => (chartAt H c).source ∩
      extChartAt I c ⁻¹' Metric.ball (extChartAt I c c) ((bump c).rIn / 2))
    (fun c _ => (isOpen_extChartAt_preimage c Metric.isOpen_ball).mem_nhds
      ⟨mem_chart_source H c, Metric.mem_ball_self (by linarith [(bump c).rIn_pos])⟩)
  have hCBT : ∀ c : M, Metric.closedBall (extChartAt I c c) ((bump c).rIn / 2) ⊆
      (extChartAt I c).target := fun c y hy => (bump c).closedBall_subset
    ⟨Metric.closedBall_subset_closedBall
      (by linarith [(bump c).rIn_pos, (bump c).rIn_lt_rOut]) hy,
      by rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact mem_univ _⟩
  have hCBcomp : ∀ c : M, IsCompact ((extChartAt I c).symm ''
      Metric.closedBall (extChartAt I c c) ((bump c).rIn / 2)) := fun c =>
    (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm c).mono (hCBT c))
  have hCBsub : ∀ c : M, (extChartAt I c).symm ''
      Metric.closedBall (extChartAt I c c) ((bump c).rIn / 2) ⊆ (extChartAt I c).source := by
    rintro c x ⟨y, hy, rfl⟩; exact (extChartAt I c).map_target (hCBT c hy)
  set τ := δ / (4 * (tB.card + 1)) with hτdef
  have hτ : 0 < τ := by positivity
  have hind : ∀ s : Finset M, ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ x, x ∉ (⋃ c ∈ s, Function.support (bump c)) → g x = f x) ∧
      (∀ x, |g x - f x| ≤ s.card * τ) ∧
      (∀ q ∈ tR, ∀ p ∈ R ∩ (extChartAt I q).symm '' Metric.closedBall (extChartAt I q q) (r q),
        DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p → DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g p) ∧
      (∀ c ∈ s, ∀ p ∈ (extChartAt I c).symm ''
          Metric.closedBall (extChartAt I c c) ((bump c).rIn / 2),
        DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p → DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g p) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨f, hf, fun x _ => rfl, fun x => by simp, fun q _ p hp => hDnd q p hp,
        fun c hc => absurd hc (Finset.notMem_empty c)⟩
    | insert c s hcs ih =>
      obtain ⟨g, hg, hgf, hgb, hgR, hgB⟩ := ih
      obtain ⟨g', hg', hg'g, hg'b, hg'old, hg'new⟩ := step hg
        (ι := {q // q ∈ tR} ⊕ {c' // c' ∈ s})
        (Cs := Sum.elim
          (fun q => R ∩ (extChartAt I q.1).symm '' Metric.closedBall (extChartAt I q.1 q.1) (r q.1))
          (fun c' => (extChartAt I c'.1).symm ''
            Metric.closedBall (extChartAt I c'.1 c'.1) ((bump c'.1).rIn / 2)))
        (cs := Sum.elim (fun q => q.1) (fun c' => c'.1))
        (by rintro (q | c'); exacts [hDcomp q.1, hCBcomp c'.1])
        (by rintro (q | c'); exacts [hDsub q.1, hCBsub c'.1])
        (by
          rintro (q | c') p hp hcrit
          · exact hgR q.1 q.2 p hp hcrit
          · exact hgB c'.1 c'.2 p hp hcrit)
        (bump c) (by linarith [(bump c).rIn_pos] : (bump c).rIn / 2 < (bump c).rIn) hτ
      refine ⟨g', hg', ?_, ?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.set_biUnion_insert] at hx
        rw [hg'g x (fun h => hx (Or.inl h)), hgf x (fun h => hx (Or.inr h))]
      · intro x
        rw [Finset.card_insert_of_notMem hcs]
        calc |g' x - f x| = |(g' x - g x) + (g x - f x)| := by ring_nf
          _ ≤ |g' x - g x| + |g x - f x| := abs_add_le _ _
          _ ≤ τ + s.card * τ := add_le_add (hg'b x) (hgb x)
          _ = ((s.card + 1 : ℕ) : ℝ) * τ := by push_cast; ring
      · intro q hq p hp hcrit; exact hg'old (Sum.inl ⟨q, hq⟩) p hp hcrit
      · intro c' hc' p hp hcrit
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hg'new p hp hcrit
        · exact hg'old (Sum.inr ⟨c', hc'⟩) p hp hcrit
  obtain ⟨g, hg, hgf, hgb, hgR, hgB⟩ := hind tB
  have hDclosed : IsClosed (⋃ c ∈ tB, tsupport (bump c)) :=
    isClosed_biUnion_finset fun c _ => isClosed_tsupport _
  have hDV' : (⋃ c ∈ tB, tsupport (bump c)) ⊆ V' := by
    intro x hx
    rw [mem_iUnion₂] at hx
    obtain ⟨c, hc, hx⟩ := hx
    exact hbump c (htBK' c hc) hx
  have hsuppD : (⋃ c ∈ tB, Function.support (bump c)) ⊆ ⋃ c ∈ tB, tsupport (bump c) :=
    iUnion₂_mono fun c _ => subset_tsupport _
  have hgfD : ∀ x, x ∉ (⋃ c ∈ tB, tsupport (bump c)) → g x = f x :=
    fun x hx => hgf x (fun h => hx (hsuppD h))
  have hgfnhds : ∀ x, x ∉ (⋃ c ∈ tB, tsupport (bump c)) → g =ᶠ[𝓝 x] f := fun x hx => by
    filter_upwards [hDclosed.isOpen_compl.mem_nhds hx] with y hy
    exact hgfD y hy
  have hbound : ∀ x, |g x - f x| < δ / 4 := by
    intro x
    refine (hgb x).trans_lt ?_
    have hc : (0 : ℝ) ≤ tB.card := Nat.cast_nonneg _
    rw [hτdef, ← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hmod : ModifiedWithin f a b g := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact hgfD x (fun h => hx (hV'strip (hDV' h)))
    · by_cases hxD : x ∈ ⋃ c ∈ tB, tsupport (bump c)
      · have hxV := hDV' hxD
        have := hbound x
        rw [abs_lt] at this
        exact ⟨by linarith [hxV.1], by linarith [hxV.2]⟩
      · rw [hgfD x hxD]; exact hx
  refine ⟨g, hmod, ⟨hg, hab, ?_, ?_, ?_⟩⟩
  · rw [hmod.preimage_Icc]; exact hcompact
  · intro x hx
    have hxs : x ∉ f ⁻¹' Ioo a b := fun h => by
      have := hmod.mapsTo h
      rcases hx with hx | hx
      · rw [hx] at this; exact lt_irrefl a this.1
      · rw [hx] at this; exact lt_irrefl b this.2
    have hxD : x ∉ ⋃ c ∈ tB, tsupport (bump c) := fun h => hxs (hV'strip (hDV' h))
    have hfx : f x = g x := (hgfD x hxD).symm
    unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt
    rw [(hgfnhds x hxD).mfderiv_eq]
    exact hreg x (by rwa [hfx])
  · intro x hx hcrit
    have hfx : f x ∈ Ioo a b := by
      by_contra h
      rw [hgfD x (fun hD => h (hV'strip (hDV' hD)))] at hx
      exact h hx
    by_cases hxK : x ∈ K'
    · have := htB hxK
      rw [mem_iUnion₂] at this
      obtain ⟨c, hc, hxc⟩ := this
      refine hgB c hc x ⟨extChartAt I c x, Metric.ball_subset_closedBall hxc.2,
        (extChartAt I c).left_inv (by rw [extChartAt_source]; exact hxc.1)⟩ hcrit
    · by_cases hxD : x ∈ ⋃ c ∈ tB, tsupport (bump c)
      · have hxV := hDV' hxD
        have hxR : x ∈ R := by
          simp only [hK'def, mem_preimage, mem_Icc, not_and_or, not_le] at hxK
          rcases hxK with h | h
          · exact Or.inl ⟨hxV.1.le, h.le⟩
          · exact Or.inr ⟨h.le, hxV.2.le⟩
        have := htR hxR
        rw [mem_iUnion₂] at this
        obtain ⟨q, hq, hxq⟩ := this
        exact hgR q hq x ⟨hxR, extChartAt I q x, Metric.ball_subset_closedBall hxq.2,
          (extChartAt I q).left_inv (by rw [extChartAt_source]; exact hxq.1)⟩ hcrit
      · exfalso
        have hcritf : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
          unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt at hcrit ⊢
          rwa [(hgfnhds x hxD).mfderiv_eq] at hcrit
        simp only [hK'def, mem_preimage, mem_Icc, not_and_or, not_le] at hxK
        refine hcollar x ⟨hfx.1.le, hfx.2.le⟩ ?_ hcritf
        rcases hxK with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)

end

end DifferentialGeometry.Topology
