module

public import DifferentialGeometry.Topology.Morse.Cancellation.Setup.CancelSetup

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split recombine_decompose
  morseNorm_recombine_sq)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

def unitTangent (t : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t := (1 : ℝ)

theorem smul_unitTangent (t r : ℝ) : r • unitTangent t = (r : TangentSpace 𝓘(ℝ, ℝ) t) := by
  change r * 1 = r
  ring

theorem hasDerivAt_comp_curve {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) {φ : M → F}
    (hφ : MDifferentiableAt I 𝓘(ℝ, F) φ (γ t)) :
    HasDerivAt (fun r => φ (γ r))
      ((NormedSpace.fromTangentSpace (φ (γ t)))
        (mfderiv I 𝓘(ℝ, F) φ (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (unitTangent t)))) t := by
  have hcomp := HasMFDerivAt.comp t hφ.hasMFDerivAt hγ.hasMFDerivAt
  have hfd := hasMFDerivAt_iff_hasFDerivAt.1 hcomp
  refine hasDerivAt_iff_hasFDerivAt.2 (hfd.congr_fderiv ?_)
  apply ContinuousLinearMap.ext
  intro r
  change (NormedSpace.fromTangentSpace (φ (γ t)))
      ((mfderiv I 𝓘(ℝ, F) φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) r)) =
    (id r : ℝ) • (NormedSpace.fromTangentSpace (φ (γ t)))
      ((mfderiv I 𝓘(ℝ, F) φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) (unitTangent t)))
  rw [← map_smul, ← map_smul, ← map_smul, smul_unitTangent]
  rfl

theorem mfderiv_integralCurve_unitTangent {V : (x : M) → TangentSpace I x} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V) (t : ℝ) : mfderiv 𝓘(ℝ, ℝ) I γ t (unitTangent t) = V (γ t) := by
  rw [(hγ t).mfderiv]
  change (1 : ℝ) • V (γ t) = V (γ t)
  rw [one_smul]

theorem hasDerivAt_comp_integralCurve {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : (x : M) → TangentSpace I x} {γ : ℝ → M} (hγ : IsMIntegralCurve γ V) {t : ℝ}
    {φ : M → F} (hφ : MDifferentiableAt I 𝓘(ℝ, F) φ (γ t)) :
    HasDerivAt (fun r => φ (γ r))
      ((NormedSpace.fromTangentSpace (φ (γ t))) (mfderiv I 𝓘(ℝ, F) φ (γ t) (V (γ t)))) t := by
  have := hasDerivAt_comp_curve (hγ t).mdifferentiableAt hφ
  rwa [mfderiv_integralCurve_unitTangent hγ] at this

section Velocity

variable [IsManifold I ∞ M] [I.Boundaryless]

theorem contMDiffAt_velocity {G : ℝ × M → M} {U : Set (ℝ × M)} (hU : IsOpen U)
    (hG : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ G U) {S : Set M} (hS : IsOpen S)
    (hSU : ∀ x ∈ S, (0, x) ∈ U) (hG0 : ∀ x ∈ S, G (0, x) = x) {Z : (x : M) → TangentSpace I x}
    (hZ : ∀ x ∈ S, Z x = mfderiv 𝓘(ℝ, ℝ) I (fun r => G (r, x)) 0 (unitTangent 0))
    {x₀ : M} (hx₀ : x₀ ∈ S) :
    ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun x => (⟨x, Z x⟩ : TangentBundle I M)) x₀ := by
  rw [Bundle.contMDiffAt_section]
  set e := extChartAt I x₀ with he
  set Ĝ : ℝ × (Fin n → ℝ) → Fin n → ℝ := fun q => e (G (q.1, e.symm q.2)) with hĜdef
  set Û : Set (ℝ × (Fin n → ℝ)) :=
    {q | q.2 ∈ e.target ∧ (q.1, e.symm q.2) ∈ U ∧ G (q.1, e.symm q.2) ∈ e.source} with hÛdef
  set σ : ℝ × (Fin n → ℝ) → ℝ × M := fun q => (q.1, e.symm q.2) with hσdef
  have hT : IsOpen e.target := isOpen_extChartAt_target x₀
  have hσc : ContinuousOn σ {q | q.2 ∈ e.target} := by
    refine continuousOn_fst.prodMk ?_
    exact (continuousOn_extChartAt_symm x₀).comp continuousOn_snd fun q hq => hq
  have hU1 : IsOpen {q : ℝ × (Fin n → ℝ) | q.2 ∈ e.target ∧ σ q ∈ U} :=
    hσc.isOpen_inter_preimage (hT.preimage continuous_snd) hU
  have hÛo : IsOpen Û := by
    have hGc : ContinuousOn (fun q => G (σ q)) {q | q.2 ∈ e.target ∧ σ q ∈ U} :=
      hG.continuousOn.comp (hσc.mono fun q hq => hq.1) fun q hq => hq.2
    have := hGc.isOpen_inter_preimage hU1 (isOpen_extChartAt_source (I := I) x₀)
    convert this using 1
    ext q
    simp only [hÛdef, mem_ofPred_eq, mem_inter_iff, mem_preimage, hσdef]
    tauto
  have hσs : ContMDiffOn 𝓘(ℝ, ℝ × (Fin n → ℝ)) (𝓘(ℝ, ℝ).prod I) ∞ σ {q | q.2 ∈ e.target} := by
    refine ContMDiffOn.prodMk ?_ ?_
    · exact (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).contMDiffOn
    · exact (contMDiffOn_extChartAt_symm x₀).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)).contMDiffOn fun q hq => hq
  have hĜ : ContDiffOn ℝ ∞ Ĝ Û := by
    refine ContMDiffOn.contDiffOn ?_
    have h1 : ContMDiffOn 𝓘(ℝ, ℝ × (Fin n → ℝ)) I ∞ (fun q => G (σ q)) Û :=
      hG.comp (hσs.mono fun q hq => hq.1) fun q hq => hq.2.1
    have h2 : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ e e.source := by
      rw [he, extChartAt_source]
      exact contMDiffOn_extChartAt
    exact h2.comp h1 fun q hq => hq.2.2
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ Ĝ) Û :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hÛo).1 hĜ).2
  have hx₀Û : (0, e x₀) ∈ Û := by
    refine ⟨mem_extChartAt_target x₀, ?_, ?_⟩
    · change (0, e.symm (e x₀)) ∈ U
      rw [he, extChartAt_to_inv]
      exact hSU x₀ hx₀
    · change G (0, e.symm (e x₀)) ∈ e.source
      rw [he, extChartAt_to_inv, hG0 x₀ hx₀]
      exact mem_extChartAt_source x₀
  have hcand : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (fun x => fderiv ℝ Ĝ (0, e x) (1, 0)) x₀ := by
    have h1 : ContDiffAt ℝ ∞ (fun q => fderiv ℝ Ĝ q (1, 0)) (0, e x₀) :=
      (hfd.clm_apply contDiffOn_const).contDiffAt (hÛo.mem_nhds hx₀Û)
    have h2 : ContMDiffAt I 𝓘(ℝ, ℝ × (Fin n → ℝ)) ∞ (fun x => ((0 : ℝ), e x)) x₀ := by
      have : (fun x => ((0 : ℝ), e x)) = (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) ∘ e := by
        funext x; rfl
      rw [this]
      exact (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)).contMDiffAt.comp x₀ contMDiffAt_extChartAt
    exact h1.contMDiffAt.comp x₀ h2
  refine hcand.congr_of_eventuallyEq ?_
  have hnhds : e.source ∩ S ∈ 𝓝 x₀ :=
    inter_mem (extChartAt_source_mem_nhds x₀) (hS.mem_nhds hx₀)
  filter_upwards [hnhds] with x hx
  have hxs : x ∈ (chartAt H x₀).source := by rw [← extChartAt_source I]; exact hx.1
  rw [DifferentialGeometry.Topology.Morse.tangentTrivializationAt_apply I x₀ x hx.1 _,
    tangentSpaceModelContinuousLinearEquiv_apply]
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r => G (r, x)) 0 := by
    have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ G (0, x) :=
      hG.contMDiffAt (hU.mem_nhds (hSU x hx.2))
    have h2 : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun r : ℝ => (r, x)) 0 :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact (h1.comp 0 h2).mdifferentiableAt (by simp)
  have hext : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) e (G (0, x)) := by
    rw [hG0 x hx.2]; exact mdifferentiableAt_extChartAt hxs
  have hcomp := mfderiv_comp_of_eq hext hγ rfl
  have hfder : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (e ∘ fun r => G (r, x)) 0 =
      fderiv ℝ (fun r => e (G (r, x))) 0 := mfderiv_eq_fderiv
  have hkey : (mfderiv I 𝓘(ℝ, Fin n → ℝ) e (G (0, x)))
      (mfderiv 𝓘(ℝ, ℝ) I (fun r => G (r, x)) 0 (unitTangent 0)) =
        fderiv ℝ (fun r => e (G (r, x))) 0 1 :=
    DFunLike.congr_fun (hcomp.symm.trans hfder) (unitTangent 0)
  have hcurve : (fun r => e (G (r, x))) = fun r => Ĝ (r, e x) := by
    funext r
    simp only [hĜdef]
    rw [e.left_inv hx.1]
  have hxÛ : (0, e x) ∈ Û := by
    refine ⟨(extChartAt I x₀).map_source hx.1, ?_, ?_⟩
    · change (0, e.symm (e x)) ∈ U
      rw [e.left_inv hx.1]
      exact hSU x hx.2
    · change G (0, e.symm (e x)) ∈ e.source
      rw [e.left_inv hx.1, hG0 x hx.2]
      exact hx.1
  have hĜd : DifferentiableAt ℝ Ĝ (0, e x) :=
    (hĜ.differentiableOn (by simp)).differentiableAt (hÛo.mem_nhds hxÛ)
  have hchain : HasFDerivAt (Ĝ ∘ fun r : ℝ => (r, e x))
      ((fderiv ℝ Ĝ (0, e x)).comp (ContinuousLinearMap.inl ℝ ℝ (Fin n → ℝ))) 0 :=
    hĜd.hasFDerivAt.comp (0 : ℝ) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) (e x))
  have hfin : fderiv ℝ (fun r => e (G (r, x))) 0 1 = fderiv ℝ Ĝ (0, e x) (1, 0) := by
    rw [hcurve]
    change fderiv ℝ (Ĝ ∘ fun r : ℝ => (r, e x)) 0 1 = _
    rw [hchain.fderiv]
    rfl
  have hcong : ∀ z, z = G (0, x) → (mfderiv I 𝓘(ℝ, Fin n → ℝ) e z)
      (mfderiv 𝓘(ℝ, ℝ) I (fun r => G (r, x)) 0 (unitTangent 0)) = fderiv ℝ Ĝ (0, e x) (1, 0) := by
    rintro z rfl
    exact hkey.trans hfin
  exact (congrArg (mfderiv I 𝓘(ℝ, Fin n → ℝ) e x) (hZ x hx.2)).trans (hcong x (hG0 x hx.2).symm)

end Velocity

namespace ModelField

variable {k : ℕ} (hk : k ≤ n) {r₀ : ℝ} {γ : ℝ → Fin n → ℝ} {t₀ t₁ : ℝ}

theorem hasDerivAt_negPart_coord
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (i : Fin k) :
    HasDerivAt (fun s => negPart hk (γ s) i) (theta r₀ (γ t) * negPart hk (γ t) i) t := by
  have := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_negPart_curve hk hγ ht)
  refine this.congr_deriv ?_
  simp

theorem hasDerivAt_posPart_coord
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (j : Fin (n - k)) :
    HasDerivAt (fun s => posPart hk (γ s) j) (-(theta r₀ (γ t) * posPart hk (γ t) j)) t := by
  have := (EuclideanSpace.proj j).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_posPart_curve hk hγ ht)
  refine this.congr_deriv ?_
  simp

theorem negPart_mul_posPart_const
    (hγ : ∀ t ∈ Icc t₀ t₁, HasDerivAt γ (modelField k r₀ (γ t)) t) (i : Fin k) (j : Fin (n - k)) :
    ∀ t ∈ Icc t₀ t₁, negPart hk (γ t) i * posPart hk (γ t) j =
      negPart hk (γ t₀) i * posPart hk (γ t₀) j := by
  have hd : ∀ t ∈ Icc t₀ t₁,
      HasDerivAt (fun s => negPart hk (γ s) i * posPart hk (γ s) j) 0 t := by
    intro t ht
    have := (hasDerivAt_negPart_coord hk hγ ht i).mul (hasDerivAt_posPart_coord hk hγ ht j)
    convert this using 1; ring
  refine constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hd) fun t ht => ?_
  exact (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt

theorem morseNorm_sq_eq_sum (y : Fin n → ℝ) : morseNorm n y ^ 2 = ∑ i, y i ^ 2 := by
  change ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ^ 2 = _
  simpa using EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))

theorem hasDerivAt_morseNorm_sq_half {ρ : ℝ → Fin n → ℝ} {ρ' : Fin n → ℝ} {t : ℝ}
    (hρ : HasDerivAt ρ ρ' t) :
    HasDerivAt (fun r => morseNorm n (ρ r) ^ 2 / 2) (∑ i, ρ t i * ρ' i) t := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasDerivAt (fun r => ρ r i * ρ r i) (ρ' i * ρ t i + ρ t i * ρ' i) t := fun i _ =>
    (hasDerivAt_pi.1 hρ i).mul (hasDerivAt_pi.1 hρ i)
  have h2 := (HasDerivAt.sum h).div_const 2
  have hfun : (fun r => morseNorm n (ρ r) ^ 2 / 2) = fun r => (∑ i, ρ r i * ρ r i) / 2 := by
    funext r
    rw [morseNorm_sq_eq_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun]
  refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)).congr_deriv ?_
  · simp [Finset.sum_apply]
  · rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem solve_transport {k m : ℕ} {u u' : EuclideanSpace ℝ (Fin k)}
    {v v' : EuclideanSpace ℝ (Fin m)} {κ : ℝ} (hu : u ≠ 0)
    (hprod : ∀ i j, u' i * v j + u i * v' j = -κ * (u i * v j))
    (hlev : inner ℝ v v' = inner ℝ u u') (hv0 : v = 0 → u' = 0 ∧ v' = 0) :
    u' = (-κ * (‖v‖ ^ 2 / (‖u‖ ^ 2 + ‖v‖ ^ 2))) • u ∧
      v' = (-κ * (‖u‖ ^ 2 / (‖u‖ ^ 2 + ‖v‖ ^ 2))) • v := by
  by_cases hv : v = 0
  · obtain ⟨h1, h2⟩ := hv0 hv
    subst hv
    simp [h1, h2]
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (by ext i; simp [h i])
  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (by ext j; simp [h j])
  set α : ℝ := -κ - v' j₀ / v j₀ with hα
  set β : ℝ := -κ - u' i₀ / u i₀ with hβ
  have hu' : u' = α • u := by
    ext i
    have h := hprod i j₀
    simp only [PiLp.smul_apply, smul_eq_mul, hα]
    field_simp
    linarith
  have hv' : v' = β • v := by
    ext j
    have h := hprod i₀ j
    simp only [PiLp.smul_apply, smul_eq_mul, hβ]
    field_simp
    linarith
  have hsum : α + β = -κ := by
    have h := hprod i₀ j₀
    rw [hu', hv'] at h
    simp only [PiLp.smul_apply, smul_eq_mul] at h
    have h' : (α + β + κ) * (u i₀ * v j₀) = 0 := by linarith
    rcases mul_eq_zero.1 h' with h'' | h''
    · linarith
    · exact absurd h'' (mul_ne_zero hi₀ hj₀)
  have hlev' : β * ‖v‖ ^ 2 = α * ‖u‖ ^ 2 := by
    rw [hu', hv', inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at hlev
    exact hlev
  have hpos : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.2 hu
    positivity
  have hαv : α = -κ * (‖v‖ ^ 2 / (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
    field_simp
    nlinarith [hsum, hlev']
  have hβv : β = -κ * (‖u‖ ^ 2 / (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
    field_simp
    nlinarith [hsum, hlev']
  exact ⟨by rw [hu', hαv], by rw [hv', hβv]⟩

end ModelField

variable {f : M → ℝ} {a b : ℝ} {crit : Finset M}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} (c : IndexZeroCancellingPair I f a' b' p q)

def qBall : Set M := c.d.χ '' {y | morseNorm n y < c.D.rm q c.hq}

theorem isOpen_qBall : IsOpen c.qBall := c.D.isOpen_modelBall q c.hq

theorem qBall_subset_image_ball : c.qBall ⊆ c.d.χ '' Metric.ball 0 c.d.R' :=
  c.D.modelBall_subset_image_ball q c.hq

def openChartTube : Set M :=
  {x | f x ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)} ∩ c.D.π c.c₂ ⁻¹' c.qBall

theorem isOpen_openChartTube : IsOpen c.openChartTube :=
  (isOpen_Ioo.preimage c.hfs.continuous).inter
    (c.isOpen_qBall.preimage (c.D.continuous_π c.hfs c.c₂))

theorem f_mem_of_mem_openChartTube {x : M} (hx : x ∈ c.openChartTube) :
    f x ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η) := hx.1

theorem π_mem_qBall {x : M} (hx : x ∈ c.openChartTube) : c.D.π c.c₂ x ∈ c.qBall := hx.2

theorem mem_openChartTube_iff {x : M} :
    x ∈ c.openChartTube ↔ f x ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η) ∧ c.D.π c.c₂ x ∈ c.qBall := Iff.rfl

theorem c₂_mem_Icc : c.c₂ ∈ Icc a' b' :=
  ⟨(c.a'_lt_c₁_sub_η.trans (by linarith [c.c₁_lt_c₂, c.η_pos])).le,
    (by linarith [c.c₂_add_η_lt_b', c.η_pos] : c.c₂ < b').le⟩

theorem c₂_mem_tube : c.c₂ ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η) :=
  ⟨by linarith [c.c₁_lt_c₂, c.η_pos], by linarith [c.η_pos]⟩

theorem mem_regularFlowDomain_of_f_mem {x : M} (hx : f x ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)) :
    x ∈ c.D.regularFlowDomain c.c₂ :=
  c.tube_subset_regularFlowDomain (Ioo_subset_Icc_self hx)

theorem openChartTube_subset_regularFlowDomain : c.openChartTube ⊆ c.D.regularFlowDomain c.c₂ := fun _ hx => c.mem_regularFlowDomain_of_f_mem hx.1

theorem f_π_eq {x : M} (hx : x ∈ c.openChartTube) : f (c.D.π c.c₂ x) = c.c₂ :=
  f_π c.hfs c.c₂_mem_Icc (c.openChartTube_subset_regularFlowDomain hx)

theorem smallBall_f_ne_c₂ : ∀ p' hp', ∀ y ∈ c.D.smallBall p' hp', f y ≠ c.c₂ :=
  fun p' hp' y hy h =>
    c.levels_avoid_smallBall (by rw [h]; exact Ioo_subset_Icc_self c.c₂_mem_tube) p' hp' hy

theorem π_flow_eq {x : M} {s : ℝ} (hx : x ∈ c.D.regularFlowDomain c.c₂) (hs : c.D.flow s x ∈ c.D.regularFlowDomain c.c₂) :
    c.D.π c.c₂ (c.D.flow s x) = c.D.π c.c₂ x :=
  π_flow c.hfs c.c₂_mem_Icc c.smallBall_f_ne_c₂ hx hs

theorem f_flow_eq_sub_tube {x : M} (hx : f x ∈ Icc (c.c₁ - c.η) (c.c₂ + c.η)) {T : ℝ}
    (hT : f x - T ∈ Icc (c.c₁ - c.η) (c.c₂ + c.η)) :
    ∀ s ∈ uIcc 0 T, f (c.D.flow s x) = f x - s := by
  have h1 := c.a'_lt_c₁_sub_η
  have h2 := c.c₂_add_η_lt_b'
  refine f_flow_eq_sub_of_levels c.hfs (D := c.D) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hT.1], by linarith [hT.2]⟩ fun y hy => c.levels_avoid_smallBall ?_
  rw [mem_uIcc] at hy
  rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> constructor <;> linarith [hx.1, hx.2, hT.1, hT.2]

def w (x : M) : Fin n → ℝ := c.d.χ.symm (c.D.π c.c₂ x)

theorem morseNorm_w_lt {x : M} (hx : x ∈ c.openChartTube) : morseNorm n (c.w x) < c.D.rm q c.hq := by
  obtain ⟨y, hy, hyx⟩ := c.π_mem_qBall hx
  have : c.w x = y := by
    unfold w
    rw [← hyx, c.d.χ.left_inv (c.d.hsrc y (hy.le.trans (c.D.hrm q c.hq).2))]
  rw [this]; exact hy

theorem morseNorm_w_le_R {x : M} (hx : x ∈ c.openChartTube) : morseNorm n (c.w x) ≤ c.d.R :=
  (c.morseNorm_w_lt hx).le.trans (c.D.hrm q c.hq).2

theorem w_mem_ball {x : M} (hx : x ∈ c.openChartTube) : c.w x ∈ Metric.ball (0 : Fin n → ℝ) c.d.R' :=
  mem_ball_of_morseNorm_lt ((c.morseNorm_w_lt hx).trans (c.D.rm_lt_R' q c.hq))

theorem chart_w {x : M} (hx : x ∈ c.openChartTube) : c.d.χ (c.w x) = c.D.π c.c₂ x :=
  c.d.symm_image_eq (c.qBall_subset_image_ball (c.π_mem_qBall hx))

theorem nf_w {x : M} (hx : x ∈ c.openChartTube) : morseNormalForm c.d.hk (f q) (c.w x) = c.c₂ := by
  rw [← c.d.hnorm _ (c.morseNorm_w_le_R hx), c.chart_w hx, c.f_π_eq hx]

theorem normSq_negPart_w {x : M} (hx : x ∈ c.openChartTube) :
    ‖negPart c.d.hk (c.w x)‖ ^ 2 = ‖posPart c.d.hk (c.w x)‖ ^ 2 + 2 * c.ε₂ := by
  have h := c.nf_w hx
  rw [morseNormalForm_split] at h
  unfold c₂ at h
  linarith

def ζ (x : M) : EuclideanSpace ℝ (Fin (n - c.d.k)) := posPart c.d.hk (c.w x)

theorem ζ_def (x : M) : c.ζ x = posPart c.d.hk (c.w x) := rfl

theorem contMDiffOn_w : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ c.w c.openChartTube :=
  c.d.hχsymm.comp (c.D.contMDiff_π c.hfs c.c₂).contMDiffOn fun _ hx =>
    c.qBall_subset_image_ball (c.π_mem_qBall hx)

theorem contMDiffOn_ζ :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) ∞ c.ζ c.openChartTube :=
  (ModelField.posPartL c.d.hk).contMDiff.comp_contMDiffOn c.contMDiffOn_w

theorem mdifferentiableAt_ζ {x : M} (hx : x ∈ c.openChartTube) :
    MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) c.ζ x :=
  (c.contMDiffOn_ζ.contMDiffAt (c.isOpen_openChartTube.mem_nhds hx)).mdifferentiableAt (by simp)

theorem continuousOn_ζ : ContinuousOn c.ζ c.openChartTube := c.contMDiffOn_ζ.continuousOn

theorem ζ_flow {x : M} {t : ℝ} (hx : x ∈ c.openChartTube) (hxt : c.D.flow t x ∈ c.openChartTube) :
    c.ζ (c.D.flow t x) = c.ζ x := by
  unfold ζ w
  rw [c.π_flow_eq (c.openChartTube_subset_regularFlowDomain hx) (c.openChartTube_subset_regularFlowDomain hxt)]

theorem morseNorm_armPt_lt (i : Fin 2) : morseNorm n (c.d.armPt c.hkq c.ε i) < c.D.rm q c.hq := by
  have h := c.d.morseNorm_sq_of_mem_leftModelSphere
    (c.d.armPt_mem_leftModelSphere c.hkq c.hε.le i)
  have h2 := c.sqrt_two_ε_lt_rmq
  have h3 := c.rmq_pos
  refine (MorseNormalChart.morseNorm_le_sqrt_of_sq_le h.le).trans_lt ?_
  linarith

theorem π_flow_z₀ {s : ℝ} (hs : s ∈ Icc 0 c.transitTime) :
    c.D.π c.c₂ (c.D.flow s c.z₀) = c.D.flow (c.ε₂ - c.ε) c.z₀ := by
  unfold GradientLikeStrip.π
  rw [c.f_flow_z₀ hs, flow_flow]
  congr 1
  unfold c₂; ring

theorem flow_z₀_mem_openChartTube {s : ℝ} (hs : s ∈ Icc 0 c.transitTime) : c.D.flow s c.z₀ ∈ c.openChartTube := by
  have hT : c.transitTime = f q - f p - 2 * c.ε := rfl
  refine ⟨?_, ?_⟩
  · change f (c.D.flow s c.z₀) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)
    rw [c.f_flow_z₀ hs]
    unfold c₁ c₂
    constructor <;> linarith [hs.1, hs.2, c.η_pos, c.ε₁_lt_ε, c.ε₂_lt_ε]
  · change c.D.π c.c₂ (c.D.flow s c.z₀) ∈ c.qBall
    rw [c.π_flow_z₀ hs]
    have hmem := flow_mem_of_posPart_eq_zero (D := c.D) c.hq (c.morseNorm_armPt_lt c.i)
      (c.d.armPt_mem_leftModelSphere c.hkq c.hε.le c.i).1 (t := c.ε₂ - c.ε)
      (by linarith [c.ε₂_lt_ε])
    exact image_mono (fun z hz => hz.1.trans_lt (c.morseNorm_armPt_lt c.i)) hmem

theorem ζ_flow_z₀ {s : ℝ} (hs : s ∈ Icc 0 c.transitTime) : c.ζ (c.D.flow s c.z₀) = 0 := by
  unfold ζ w
  rw [c.π_flow_z₀ hs]
  have hmem := flow_mem_of_posPart_eq_zero (D := c.D) c.hq (c.morseNorm_armPt_lt c.i)
    (c.d.armPt_mem_leftModelSphere c.hkq c.hε.le c.i).1 (t := c.ε₂ - c.ε)
    (by linarith [c.ε₂_lt_ε])
  obtain ⟨z, hz, hzx⟩ := hmem
  have hz₀ : c.D.flow (c.ε₂ - c.ε) c.z₀ = c.d.χ z := hzx.symm
  rw [hz₀, c.d.χ.left_inv (c.d.hsrc z (hz.1.trans
    ((c.morseNorm_armPt_lt c.i).le.trans (c.D.hrm q c.hq).2)))]
  exact hz.2

def lev (r : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  recombine c.d.hk
    ((Real.sqrt (Real.exp (-2 * r) * ‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂) /
      Real.sqrt (‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂)) • negPart c.d.hk y)
    (Real.exp (-r) • posPart c.d.hk y)

theorem negPart_lev (r : ℝ) (y : Fin n → ℝ) :
    negPart c.d.hk (c.lev r y) =
      (Real.sqrt (Real.exp (-2 * r) * ‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂) /
        Real.sqrt (‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂)) • negPart c.d.hk y :=
  ModelField.negPart_recombine _ _ _

theorem posPart_lev (r : ℝ) (y : Fin n → ℝ) :
    posPart c.d.hk (c.lev r y) = Real.exp (-r) • posPart c.d.hk y :=
  ModelField.posPart_recombine _ _ _

theorem lev_zero (y : Fin n → ℝ) : c.lev 0 y = y := by
  unfold lev
  have hpos : 0 < ‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂ := by
    have := c.ε₂_pos; positivity
  rw [mul_zero, Real.exp_zero, one_mul, neg_zero, Real.exp_zero, one_smul,
    div_self (Real.sqrt_ne_zero'.2 hpos), one_smul, recombine_decompose]

theorem lev_of_posPart_eq_zero {y : Fin n → ℝ} (hv : posPart c.d.hk y = 0) (r : ℝ) :
    c.lev r y = y := by
  unfold lev
  have hε := c.ε₂_pos
  have h0 : ‖posPart c.d.hk y‖ ^ 2 = 0 := by rw [hv, norm_zero]; ring
  have hne : Real.sqrt (‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (by positivity)
  have hnum : Real.sqrt (Real.exp (-2 * r) * ‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂) =
      Real.sqrt (‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂) := by
    rw [h0, mul_zero]
  rw [hnum, div_self hne, one_smul, hv, smul_zero]
  conv_rhs => rw [← recombine_decompose c.d.hk y, hv]

theorem normSq_negPart_lev {y : Fin n → ℝ}
    (hy : ‖negPart c.d.hk y‖ ^ 2 = ‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂) (r : ℝ) :
    ‖negPart c.d.hk (c.lev r y)‖ ^ 2 = ‖posPart c.d.hk (c.lev r y)‖ ^ 2 + 2 * c.ε₂ := by
  rw [negPart_lev, posPart_lev, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, div_pow, hy]
  have hε := c.ε₂_pos
  have h1 : 0 ≤ Real.exp (-2 * r) * ‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂ := by positivity
  have h2 : 0 < ‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂ := by positivity
  rw [Real.sq_sqrt h1, Real.sq_sqrt h2.le, div_mul_cancel₀ _ h2.ne', ← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem nf_lev {y : Fin n → ℝ}
    (hy : ‖negPart c.d.hk y‖ ^ 2 = ‖posPart c.d.hk y‖ ^ 2 + 2 * c.ε₂) (r : ℝ) :
    morseNormalForm c.d.hk (f q) (c.lev r y) = c.c₂ := by
  rw [morseNormalForm_split, c.normSq_negPart_lev hy r]
  unfold c₂; ring

theorem contDiff_lev : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => c.lev z.1 z.2) := by
  have hε := c.ε₂_pos
  have hv : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => posPart c.d.hk z.2) :=
    (ModelField.posPartL c.d.hk).contDiff.comp contDiff_snd
  have hu : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => negPart c.d.hk z.2) :=
    (ModelField.negPartL c.d.hk).contDiff.comp contDiff_snd
  have hnsq : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => ‖posPart c.d.hk z.2‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp hv
  have hexp : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => Real.exp (-2 * z.1)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
  have hexp' : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) => Real.exp (-z.1)) :=
    Real.contDiff_exp.comp contDiff_fst.neg
  have hnum : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      Real.sqrt (Real.exp (-2 * z.1) * ‖posPart c.d.hk z.2‖ ^ 2 + 2 * c.ε₂)) :=
    ((hexp.mul hnsq).add contDiff_const).sqrt fun z => by positivity
  have hden : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      Real.sqrt (‖posPart c.d.hk z.2‖ ^ 2 + 2 * c.ε₂)) :=
    (hnsq.add contDiff_const).sqrt fun z => by positivity
  have hq : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      Real.sqrt (Real.exp (-2 * z.1) * ‖posPart c.d.hk z.2‖ ^ 2 + 2 * c.ε₂) /
        Real.sqrt (‖posPart c.d.hk z.2‖ ^ 2 + 2 * c.ε₂)) :=
    hnum.div hden fun z => Real.sqrt_ne_zero'.2 (by positivity)
  have : (fun z : ℝ × (Fin n → ℝ) => c.lev z.1 z.2) = fun z =>
      ModelField.recombineL c.d.hk
        ((Real.sqrt (Real.exp (-2 * z.1) * ‖posPart c.d.hk z.2‖ ^ 2 + 2 * c.ε₂) /
          Real.sqrt (‖posPart c.d.hk z.2‖ ^ 2 + 2 * c.ε₂)) • negPart c.d.hk z.2,
          Real.exp (-z.1) • posPart c.d.hk z.2) := by
    funext z
    rw [ModelField.recombineL_apply]
    rfl
  rw [this]
  exact (ModelField.recombineL c.d.hk).contDiff.comp ((hq.smul hu).prodMk (hexp'.smul hv))

theorem continuous_lev : Continuous (fun z : ℝ × (Fin n → ℝ) => c.lev z.1 z.2) :=
  c.contDiff_lev.continuous

def levelDeformation (r : ℝ) (x : M) : M := c.D.flow (c.c₂ - f x) (c.d.χ (c.lev r (c.w x)))

theorem levelDeformation_zero {x : M} (hx : x ∈ c.openChartTube) : c.levelDeformation 0 x = x := by
  unfold levelDeformation
  rw [c.lev_zero, c.chart_w hx]
  unfold GradientLikeStrip.π
  rw [flow_flow]
  rw [show f x - c.c₂ + (c.c₂ - f x) = 0 by ring, flow_zero]

def levelDeformationDomain : Set (ℝ × M) :=
  {z | z.2 ∈ c.openChartTube ∧ morseNorm n (c.lev z.1 (c.w z.2)) < c.D.rm q c.hq}

theorem continuousOn_lev_w :
    ContinuousOn (fun z : ℝ × M => c.lev z.1 (c.w z.2)) {z | z.2 ∈ c.openChartTube} := by
  have h1 : ContinuousOn (fun z : ℝ × M => (z.1, c.w z.2)) {z | z.2 ∈ c.openChartTube} :=
    continuousOn_fst.prodMk (c.contMDiffOn_w.continuousOn.comp continuousOn_snd fun z hz => hz)
  have h2 := c.continuous_lev.comp_continuousOn h1
  exact h2

theorem isOpen_levelDeformationDomain : IsOpen c.levelDeformationDomain := by
  have h1 : IsOpen {z : ℝ × M | z.2 ∈ c.openChartTube} := c.isOpen_openChartTube.preimage continuous_snd
  exact c.continuousOn_lev_w.isOpen_inter_preimage h1 (isOpen_morseNorm_lt _)

theorem mem_levelDeformationDomain {x : M} (hx : x ∈ c.openChartTube) : ((0 : ℝ), x) ∈ c.levelDeformationDomain := by
  refine ⟨hx, ?_⟩
  change morseNorm n (c.lev 0 (c.w x)) < c.D.rm q c.hq
  rw [c.lev_zero]
  exact c.morseNorm_w_lt hx

theorem eventually_lev_mem {x : M} (hx : x ∈ c.openChartTube) :
    ∀ᶠ r in 𝓝 (0 : ℝ), morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq := by
  have hc : Continuous (fun r : ℝ => c.lev r (c.w x)) :=
    c.continuous_lev.comp (continuous_id.prodMk continuous_const)
  have := (hc.continuousAt (x := 0)).preimage_mem_nhds
    ((isOpen_morseNorm_lt (c.D.rm q c.hq)).mem_nhds (by
      change morseNorm n (c.lev 0 (c.w x)) < c.D.rm q c.hq
      rw [c.lev_zero]; exact c.morseNorm_w_lt hx))
  exact this

theorem eventually_mem_levelDeformationDomain {x : M} (hx : x ∈ c.openChartTube) : ∀ᶠ r in 𝓝 (0 : ℝ), (r, x) ∈ c.levelDeformationDomain := by
  filter_upwards [c.eventually_lev_mem hx] with r hr
  exact ⟨hx, hr⟩

theorem contMDiffOn_levelDeformation : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => c.levelDeformation z.1 z.2) c.levelDeformationDomain := by
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × (Fin n → ℝ)) ∞
      (fun z : ℝ × M => (z.1, c.w z.2)) c.levelDeformationDomain :=
    contMDiffOn_fst.prodMk_space (c.contMDiffOn_w.comp contMDiffOn_snd fun z hz => hz.1)
  have hlev : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun z : ℝ × M => c.lev z.1 (c.w z.2)) c.levelDeformationDomain :=
    c.contDiff_lev.contMDiff.comp_contMDiffOn hw
  have hχ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => c.d.χ (c.lev z.1 (c.w z.2))) c.levelDeformationDomain :=
    c.d.hχ.comp hlev fun z hz => mem_ball_of_morseNorm_lt (hz.2.trans (c.D.rm_lt_R' q c.hq))
  have hpair : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun z : ℝ × M => (c.c₂ - f z.2, c.d.χ (c.lev z.1 (c.w z.2)))) c.levelDeformationDomain :=
    ((contMDiff_const.sub (c.hfs.comp contMDiff_snd)).contMDiffOn).prodMk hχ
  exact c.D.contMDiff_flow_joint.comp_contMDiffOn hpair

def transverseField (x : M) : TangentSpace I x := mfderiv 𝓘(ℝ, ℝ) I (fun r => c.levelDeformation r x) 0 (unitTangent 0)

theorem transverseField_def (x : M) : c.transverseField x = mfderiv 𝓘(ℝ, ℝ) I (fun r => c.levelDeformation r x) 0 (unitTangent 0) := rfl

theorem contMDiffOn_transverseField :
    ContMDiffOn I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => (⟨x, c.transverseField x⟩ : TangentBundle I M)) c.openChartTube := fun _ hx =>
  (contMDiffAt_velocity c.isOpen_levelDeformationDomain c.contMDiffOn_levelDeformation c.isOpen_openChartTube (fun _ hx => c.mem_levelDeformationDomain hx)
    (fun _ hx => c.levelDeformation_zero hx) (fun _ _ => rfl) hx).contMDiffWithinAt

theorem mdifferentiableAt_levelDeformation_curve {x : M} (hx : x ∈ c.openChartTube) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r => c.levelDeformation r x) 0 := by
  have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => c.levelDeformation z.1 z.2) (0, x) :=
    c.contMDiffOn_levelDeformation.contMDiffAt (c.isOpen_levelDeformationDomain.mem_nhds (c.mem_levelDeformationDomain hx))
  have h2 : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞ (fun r : ℝ => (r, x)) 0 :=
    contMDiffAt_id.prodMk contMDiffAt_const
  exact (h1.comp 0 h2).mdifferentiableAt (by simp)

theorem continuousAt_levelDeformation_curve {x : M} (hx : x ∈ c.openChartTube) :
    ContinuousAt (fun r => c.levelDeformation r x) 0 :=
  (c.mdifferentiableAt_levelDeformation_curve hx).continuousAt

theorem hasDerivAt_levelDeformation {x : M} (hx : x ∈ c.openChartTube) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {φ : M → F} (hφ : MDifferentiableAt I 𝓘(ℝ, F) φ x) :
    HasDerivAt (fun r => φ (c.levelDeformation r x))
      ((NormedSpace.fromTangentSpace (φ x)) (mfderiv I 𝓘(ℝ, F) φ x (c.transverseField x))) 0 := by
  have key : ∀ y, c.levelDeformation 0 x = y → MDifferentiableAt I 𝓘(ℝ, F) φ y → HasDerivAt (fun r => φ (c.levelDeformation r x))
      ((NormedSpace.fromTangentSpace (φ y))
        (mfderiv I 𝓘(ℝ, F) φ y (mfderiv 𝓘(ℝ, ℝ) I (fun r => c.levelDeformation r x) 0 (unitTangent 0)))) 0 := by
    rintro y rfl hφ'
    exact hasDerivAt_comp_curve (c.mdifferentiableAt_levelDeformation_curve hx) hφ'
  exact key x (c.levelDeformation_zero hx) hφ

theorem f_chart_lev {x : M} (hx : x ∈ c.openChartTube) {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq) :
    f (c.d.χ (c.lev r (c.w x))) = c.c₂ := by
  rw [c.d.hnorm _ (hr.le.trans (c.D.hrm q c.hq).2), c.nf_lev (c.normSq_negPart_w hx) r]

theorem f_levelDeformation {x : M} (hx : x ∈ c.openChartTube) {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq) : f (c.levelDeformation r x) = f x := by
  unfold levelDeformation
  have hfy := c.f_chart_lev hx hr
  have h := c.f_flow_eq_sub_tube (x := c.d.χ (c.lev r (c.w x))) (T := c.c₂ - f x)
    (by rw [hfy]; exact Ioo_subset_Icc_self c.c₂_mem_tube)
    (by rw [hfy, sub_sub_cancel]; exact Ioo_subset_Icc_self hx.1) _ right_mem_uIcc
  rw [h, hfy]; ring

theorem chart_lev_mem_regularFlowDomain {x : M} (hx : x ∈ c.openChartTube) {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq) :
    c.d.χ (c.lev r (c.w x)) ∈ c.D.regularFlowDomain c.c₂ :=
  c.mem_regularFlowDomain_of_f_mem (by rw [c.f_chart_lev hx hr]; exact c.c₂_mem_tube)

theorem levelDeformation_mem_regularFlowDomain {x : M} (hx : x ∈ c.openChartTube) {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq) : c.levelDeformation r x ∈ c.D.regularFlowDomain c.c₂ :=
  c.mem_regularFlowDomain_of_f_mem (by rw [c.f_levelDeformation hx hr]; exact hx.1)

theorem π_levelDeformation {x : M} (hx : x ∈ c.openChartTube) {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq) :
    c.D.π c.c₂ (c.levelDeformation r x) = c.d.χ (c.lev r (c.w x)) := by
  have h := c.π_flow_eq (c.chart_lev_mem_regularFlowDomain hx hr) (s := c.c₂ - f x) (c.levelDeformation_mem_regularFlowDomain hx hr)
  unfold levelDeformation
  rw [h]
  exact π_eq_self_of_level (c.f_chart_lev hx hr)

theorem levelDeformation_mem_openChartTube {x : M} (hx : x ∈ c.openChartTube) {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq) : c.levelDeformation r x ∈ c.openChartTube := by
  refine ⟨?_, ?_⟩
  · change f (c.levelDeformation r x) ∈ Ioo (c.c₁ - c.η) (c.c₂ + c.η)
    rw [c.f_levelDeformation hx hr]; exact hx.1
  · change c.D.π c.c₂ (c.levelDeformation r x) ∈ c.qBall
    rw [c.π_levelDeformation hx hr]
    exact ⟨_, hr, rfl⟩

theorem w_levelDeformation {x : M} (hx : x ∈ c.openChartTube) {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq) : c.w (c.levelDeformation r x) = c.lev r (c.w x) := by
  change c.d.χ.symm (c.D.π c.c₂ (c.levelDeformation r x)) = c.lev r (c.w x)
  rw [c.π_levelDeformation hx hr, c.d.χ.left_inv (c.d.hsrc _ (hr.le.trans (c.D.hrm q c.hq).2))]

theorem ζ_levelDeformation {x : M} (hx : x ∈ c.openChartTube) {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq) :
    c.ζ (c.levelDeformation r x) = Real.exp (-r) • c.ζ x := by
  unfold ζ
  rw [c.w_levelDeformation hx hr, c.posPart_lev]

theorem eventually_f_levelDeformation {x : M} (hx : x ∈ c.openChartTube) :
    ∀ᶠ r in 𝓝 (0 : ℝ), f (c.levelDeformation r x) = f x := by
  filter_upwards [c.eventually_lev_mem hx] with r hr using c.f_levelDeformation hx hr

theorem eventually_ζ_levelDeformation {x : M} (hx : x ∈ c.openChartTube) :
    ∀ᶠ r in 𝓝 (0 : ℝ), c.ζ (c.levelDeformation r x) = Real.exp (-r) • c.ζ x := by
  filter_upwards [c.eventually_lev_mem hx] with r hr using c.ζ_levelDeformation hx hr

theorem eventually_levelDeformation_mem_openChartTube {x : M} (hx : x ∈ c.openChartTube) :
    ∀ᶠ r in 𝓝 (0 : ℝ), c.levelDeformation r x ∈ c.openChartTube := by
  filter_upwards [c.eventually_lev_mem hx] with r hr using c.levelDeformation_mem_openChartTube hx hr

theorem df_transverseField {x : M} (hx : x ∈ c.openChartTube) : dfV I f c.transverseField x = 0 := by
  have h1 := c.hasDerivAt_levelDeformation hx ((c.hfs x).mdifferentiableAt (by simp))
  have h2 : HasDerivAt (fun r => f (c.levelDeformation r x)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (f x)).congr_of_eventuallyEq (c.eventually_f_levelDeformation hx)
  exact h1.unique h2

theorem dζ_transverseField {x : M} (hx : x ∈ c.openChartTube) :
    (NormedSpace.fromTangentSpace (c.ζ x))
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) c.ζ x (c.transverseField x)) = -c.ζ x := by
  have h1 := c.hasDerivAt_levelDeformation hx (c.mdifferentiableAt_ζ hx)
  have h2 : HasDerivAt (fun r : ℝ => Real.exp (-r) • c.ζ x) ((Real.exp (-0) * -1) • c.ζ x) 0 :=
    ((Real.hasDerivAt_exp (-0)).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).smul_const (c.ζ x)
  rw [neg_zero, Real.exp_zero, one_mul, neg_one_smul] at h2
  have h3 : HasDerivAt (fun r => c.ζ (c.levelDeformation r x)) (-c.ζ x) 0 :=
    h2.congr_of_eventuallyEq (c.eventually_ζ_levelDeformation hx)
  exact h1.unique h3

theorem dζ_V {x : M} (hx : x ∈ c.openChartTube) :
    (NormedSpace.fromTangentSpace (c.ζ x))
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) c.ζ x (c.D.V x)) = 0 := by
  have key : ∀ y, c.D.flow 0 x = y →
      MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) c.ζ y →
      HasDerivAt (fun t => c.ζ (c.D.flow t x)) ((NormedSpace.fromTangentSpace (c.ζ y))
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - c.d.k))) c.ζ y (c.D.V y))) 0 := by
    rintro y rfl hy
    exact hasDerivAt_comp_integralCurve (c.D.isMIntegralCurve_flow x) hy
  have h1 := key x (c.D.flow_zero x) (c.mdifferentiableAt_ζ hx)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), c.ζ (c.D.flow t x) = c.ζ x := by
    have hmem : {t : ℝ | c.D.flow t x ∈ c.openChartTube} ∈ 𝓝 (0 : ℝ) :=
      (c.D.continuous_flow_curve x).continuousAt.preimage_mem_nhds
        (c.isOpen_openChartTube.mem_nhds (by rw [c.D.flow_zero]; exact hx))
    filter_upwards [hmem] with t ht using c.ζ_flow hx ht
  have h2 : HasDerivAt (fun t => c.ζ (c.D.flow t x)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (c.ζ x)).congr_of_eventuallyEq hev
  exact h1.unique h2

theorem transverseField_eq_zero_iff {x : M} (hx : x ∈ c.openChartTube) : c.transverseField x = 0 ↔ c.ζ x = 0 := by
  constructor
  · intro h
    have := c.dζ_transverseField hx
    rw [h, map_zero, map_zero] at this
    exact neg_eq_zero.1 this.symm
  · intro h
    have hconst : (fun r => c.levelDeformation r x) = fun _ => x := by
      funext r
      unfold levelDeformation
      rw [c.lev_of_posPart_eq_zero h r, c.chart_w hx]
      unfold GradientLikeStrip.π
      rw [flow_flow, show f x - c.c₂ + (c.c₂ - f x) = 0 by ring, c.D.flow_zero]
    change mfderiv 𝓘(ℝ, ℝ) I (fun r => c.levelDeformation r x) 0 (unitTangent 0) = 0
    rw [hconst, mfderiv_const]
    rfl

theorem transverseField_flow_z₀ {s : ℝ} (hs : s ∈ Icc 0 c.transitTime) : c.transverseField (c.D.flow s c.z₀) = 0 :=
  (c.transverseField_eq_zero_iff (c.flow_z₀_mem_openChartTube hs)).2 (c.ζ_flow_z₀ hs)

def κ (x : M) : ℝ := (2 * ‖c.ζ x‖ ^ 2 + 2 * c.ε₂) / (‖c.ζ x‖ ^ 2 + 2 * c.ε₂)

theorem one_le_κ (x : M) : 1 ≤ c.κ x := by
  unfold κ
  have hε := c.ε₂_pos
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖c.ζ x‖]

theorem κ_lt_two (x : M) : c.κ x < 2 := by
  unfold κ
  have hε := c.ε₂_pos
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖c.ζ x‖]

theorem κ_pos (x : M) : 0 < c.κ x := lt_of_lt_of_le one_pos (c.one_le_κ x)

def transverseScale (x : M) (r : ℝ) : ℝ :=
  Real.sqrt (Real.exp (-2 * r) * ‖c.ζ x‖ ^ 2 + 2 * c.ε₂) /
    Real.sqrt (‖c.ζ x‖ ^ 2 + 2 * c.ε₂) * Real.exp (-r)

theorem transverseScale_zero (x : M) : c.transverseScale x 0 = 1 := by
  unfold transverseScale
  have hε := c.ε₂_pos
  rw [mul_zero, Real.exp_zero, one_mul, neg_zero, Real.exp_zero, mul_one,
    div_self (Real.sqrt_ne_zero'.2 (by positivity))]

theorem hasDerivAt_transverseScale (x : M) : HasDerivAt (c.transverseScale x) (-c.κ x) 0 := by
  set A := ‖c.ζ x‖ ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hε := c.ε₂_pos
  have hB : 0 < A + 2 * c.ε₂ := by positivity
  have h1 : HasDerivAt (fun r : ℝ => Real.exp (-2 * r)) (-2) 0 := by
    have := (Real.hasDerivAt_exp (-2 * 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_mul (-2))
    refine this.congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun r : ℝ => Real.exp (-2 * r) * A + 2 * c.ε₂) (-2 * A) 0 :=
    (h1.mul_const A).add_const _
  have h3 := h2.sqrt (by simp only [mul_zero, Real.exp_zero, one_mul, ne_eq]; positivity)
  have h4 : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-1) 0 := by
    have := (Real.hasDerivAt_exp (-0)).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    refine this.congr_deriv ?_
    simp
  have h5 := (h3.div_const (Real.sqrt (A + 2 * c.ε₂))).mul h4
  refine h5.congr_deriv ?_
  have hs : Real.sqrt (Real.exp (-2 * 0) * A + 2 * c.ε₂) = Real.sqrt (A + 2 * c.ε₂) := by simp
  rw [hs, neg_zero, Real.exp_zero]
  unfold κ
  have hsq : Real.sqrt (A + 2 * c.ε₂) ^ 2 = A + 2 * c.ε₂ := Real.sq_sqrt hB.le
  have hsp : 0 < Real.sqrt (A + 2 * c.ε₂) := Real.sqrt_pos.2 hB
  field_simp
  nlinarith [hsq]

theorem negPart_mul_posPart_lev (x : M) (r : ℝ) (i : Fin c.d.k) (j : Fin (n - c.d.k)) :
    negPart c.d.hk (c.lev r (c.w x)) i * posPart c.d.hk (c.lev r (c.w x)) j =
      c.transverseScale x r * (negPart c.d.hk (c.w x) i * posPart c.d.hk (c.w x) j) := by
  rw [negPart_lev, posPart_lev]
  simp only [PiLp.smul_apply, smul_eq_mul]
  unfold transverseScale ζ
  ring

theorem hstay_π_of_hstay {x : M}
    (hstay : ∀ s ∈ uIcc 0 (f x - c.c₂), c.D.flow s x ∈ c.qBall) :
    ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.D.π c.c₂ x) ∈ c.qBall := by
  intro s hs
  unfold GradientLikeStrip.π
  rw [flow_flow]
  apply hstay
  rw [mem_uIcc] at hs ⊢
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; constructor <;> linarith
  · left; constructor <;> linarith

theorem eventually_segment_mem {x : M} (hx : x ∈ c.openChartTube)
    (hstay : ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.D.π c.c₂ x) ∈ c.qBall) :
    ∀ᶠ r in 𝓝 (0 : ℝ), morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq ∧
      ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.d.χ (c.lev r (c.w x))) ∈ c.qBall := by
  have hlevc : Continuous (fun r : ℝ => c.lev r (c.w x)) :=
    c.continuous_lev.comp (continuous_id.prodMk continuous_const)
  have hOo : IsOpen {z : ℝ × ℝ | c.lev z.2 (c.w x) ∈ Metric.ball (0 : Fin n → ℝ) c.d.R'} :=
    (Metric.isOpen_ball.preimage hlevc).preimage continuous_snd
  have h1 : ContinuousOn (fun z : ℝ × ℝ => c.d.χ (c.lev z.2 (c.w x)))
      {z : ℝ × ℝ | c.lev z.2 (c.w x) ∈ Metric.ball (0 : Fin n → ℝ) c.d.R'} :=
    c.d.χ.continuousOn.comp (hlevc.comp continuous_snd).continuousOn fun z hz => c.d.hball hz
  have hpair : ContinuousOn (fun z : ℝ × ℝ => (z.1, c.d.χ (c.lev z.2 (c.w x))))
      {z : ℝ × ℝ | c.lev z.2 (c.w x) ∈ Metric.ball (0 : Fin n → ℝ) c.d.R'} :=
    continuousOn_fst.prodMk h1
  have hΦc : ContinuousOn (fun z : ℝ × ℝ => c.D.flow z.1 (c.d.χ (c.lev z.2 (c.w x))))
      {z : ℝ × ℝ | c.lev z.2 (c.w x) ∈ Metric.ball (0 : Fin n → ℝ) c.d.R'} :=
    c.D.continuous_flow_joint.comp_continuousOn hpair
  have hA : IsOpen ({z : ℝ × ℝ | c.lev z.2 (c.w x) ∈ Metric.ball (0 : Fin n → ℝ) c.d.R'} ∩
      (fun z : ℝ × ℝ => c.D.flow z.1 (c.d.χ (c.lev z.2 (c.w x)))) ⁻¹' c.qBall) :=
    hΦc.isOpen_inter_preimage hOo c.isOpen_qBall
  have hsub : uIcc 0 (c.c₂ - f x) ×ˢ ({0} : Set ℝ) ⊆
      {z : ℝ × ℝ | c.lev z.2 (c.w x) ∈ Metric.ball (0 : Fin n → ℝ) c.d.R'} ∩
        (fun z : ℝ × ℝ => c.D.flow z.1 (c.d.χ (c.lev z.2 (c.w x)))) ⁻¹' c.qBall := by
    rintro ⟨s, r⟩ ⟨hs, hr⟩
    rw [mem_singleton_iff] at hr
    subst hr
    refine ⟨?_, ?_⟩
    · change c.lev 0 (c.w x) ∈ Metric.ball 0 c.d.R'
      rw [c.lev_zero]; exact c.w_mem_ball hx
    · change c.D.flow s (c.d.χ (c.lev 0 (c.w x))) ∈ c.qBall
      rw [c.lev_zero, c.chart_w hx]; exact hstay s hs
  obtain ⟨u, v, -, hv, hsu, h0v, huv⟩ :=
    generalized_tube_lemma isCompact_uIcc isCompact_singleton hA hsub
  have hvn : v ∈ 𝓝 (0 : ℝ) := hv.mem_nhds (h0v rfl)
  filter_upwards [hvn] with r hr
  have hall : ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.d.χ (c.lev r (c.w x))) ∈ c.qBall := by
    intro s hs
    have h := huv (show (s, r) ∈ u ×ˢ v from ⟨hsu hs, hr⟩)
    exact h.2
  refine ⟨?_, hall⟩
  have h0 := hall 0 left_mem_uIcc
  rw [c.D.flow_zero] at h0
  obtain ⟨z, hz, hzr⟩ := h0
  have hO0 : c.lev r (c.w x) ∈ Metric.ball (0 : Fin n → ℝ) c.d.R' :=
    (huv (show ((0 : ℝ), r) ∈ u ×ˢ v from ⟨hsu left_mem_uIcc, hr⟩)).1
  have hzz : c.lev r (c.w x) = z :=
    c.d.χ.injOn (c.d.hball hO0) (c.d.hsrc z (hz.le.trans (c.D.hrm q c.hq).2)) hzr.symm
  rw [hzz]; exact hz

theorem prod_invariant_levelDeformation {x : M} {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq)
    (hseg : ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.d.χ (c.lev r (c.w x))) ∈ c.qBall)
    (i : Fin c.d.k) (j : Fin (n - c.d.k)) :
    negPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)) i * posPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)) j =
      negPart c.d.hk (c.lev r (c.w x)) i * posPart c.d.hk (c.lev r (c.w x)) j := by
  have hγ := hasDerivAt_symm_flow_Icc (D := c.D) c.hq (x := c.d.χ (c.lev r (c.w x)))
    (t₀ := min 0 (c.c₂ - f x)) (t₁ := max 0 (c.c₂ - f x)) hseg
  have hconst := ModelField.negPart_mul_posPart_const c.d.hk hγ i j
  have h0 := hconst 0 left_mem_uIcc
  have hT := hconst (c.c₂ - f x) right_mem_uIcc
  rw [c.D.flow_zero, c.d.χ.left_inv (c.d.hsrc _ (hr.le.trans (c.D.hrm q c.hq).2))] at h0
  exact hT.trans h0.symm

theorem levelDeformation_mem_qBall_of_seg {x : M} {r : ℝ}
    (hseg : ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.d.χ (c.lev r (c.w x))) ∈ c.qBall) :
    c.levelDeformation r x ∈ c.qBall :=
  hseg _ right_mem_uIcc

theorem prod_w_eq {x : M} (hx : x ∈ c.openChartTube)
    (hstay : ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.D.π c.c₂ x) ∈ c.qBall)
    (i : Fin c.d.k) (j : Fin (n - c.d.k)) :
    negPart c.d.hk (c.d.χ.symm x) i * posPart c.d.hk (c.d.χ.symm x) j =
      negPart c.d.hk (c.w x) i * posPart c.d.hk (c.w x) j := by
  have hseg : ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.d.χ (c.lev 0 (c.w x))) ∈ c.qBall := by
    rw [c.lev_zero, c.chart_w hx]; exact hstay
  have h := c.prod_invariant_levelDeformation (r := 0) (by rw [c.lev_zero]; exact c.morseNorm_w_lt hx) hseg i j
  rw [c.levelDeformation_zero hx, c.lev_zero] at h
  exact h

theorem prod_levelDeformation_eq {x : M} (hx : x ∈ c.openChartTube) {r : ℝ}
    (hr : morseNorm n (c.lev r (c.w x)) < c.D.rm q c.hq)
    (hseg : ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.d.χ (c.lev r (c.w x))) ∈ c.qBall)
    (hstay : ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.D.π c.c₂ x) ∈ c.qBall)
    (i : Fin c.d.k) (j : Fin (n - c.d.k)) :
    negPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)) i * posPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)) j =
      c.transverseScale x r * (negPart c.d.hk (c.d.χ.symm x) i * posPart c.d.hk (c.d.χ.symm x) j) := by
  rw [c.prod_invariant_levelDeformation hr hseg i j, c.negPart_mul_posPart_lev, c.prod_w_eq hx hstay i j]

theorem negPart_w_ne_zero {x : M} (hx : x ∈ c.openChartTube) : negPart c.d.hk (c.w x) ≠ 0 := by
  intro h
  have := c.normSq_negPart_w hx
  rw [h, norm_zero] at this
  nlinarith [c.ε₂_pos, sq_nonneg ‖posPart c.d.hk (c.w x)‖]

theorem ζ_eq_zero_of_posPart_eq_zero {x : M} (hx : x ∈ c.openChartTube)
    (hstay : ∀ s ∈ uIcc 0 (c.c₂ - f x), c.D.flow s (c.D.π c.c₂ x) ∈ c.qBall)
    (hv : posPart c.d.hk (c.d.χ.symm x) = 0) : c.ζ x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, negPart c.d.hk (c.w x) i ≠ 0 := by
    by_contra h
    push Not at h
    exact c.negPart_w_ne_zero hx (by ext i; simp [h i])
  rw [c.ζ_def]
  ext j
  have h := c.prod_w_eq hx hstay i j
  rw [hv] at h
  simp only [PiLp.zero_apply, mul_zero] at h
  have := (mul_eq_zero.1 h.symm).resolve_left hi
  simpa using this

theorem normSq_negPart_of_mem {y : Fin n → ℝ} (hyR : morseNorm n y ≤ c.d.R)
    (hx : c.d.χ y ∈ c.openChartTube) :
    2 * (c.ε₂ - c.η) ≤ ‖negPart c.d.hk y‖ ^ 2 ∧ 0 < ‖negPart c.d.hk y‖ ^ 2 := by
  have h := c.d.hnorm y hyR
  rw [morseNormalForm_split] at h
  have hf := hx.1.2
  unfold c₂ at hf
  have := c.η_lt_right
  constructor <;> nlinarith [sq_nonneg ‖posPart c.d.hk y‖, sq_nonneg c.d.r₀]

theorem negPart_ne_zero_of_mem {y : Fin n → ℝ} (hyR : morseNorm n y ≤ c.d.R)
    (hx : c.d.χ y ∈ c.openChartTube) : negPart c.d.hk y ≠ 0 := by
  intro h
  have := (c.normSq_negPart_of_mem hyR hx).2
  rw [h, norm_zero] at this
  simp at this

theorem exists_ζ_eq_smul_posPart {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm q c.hq)
    (hx : c.d.χ y ∈ c.openChartTube)
    (hstay : ∀ s ∈ uIcc 0 (f (c.d.χ y) - c.c₂), c.D.flow s (c.d.χ y) ∈ c.qBall) :
    ∃ μ : ℝ, 0 < μ ∧ c.ζ (c.d.χ y) = μ • posPart c.d.hk y := by
  set x := c.d.χ y with hxdef
  have hyR : morseNorm n y ≤ c.d.R := hy.le.trans (c.D.hrm q c.hq).2
  have hsymm : c.d.χ.symm x = y := c.d.χ.left_inv (c.d.hsrc y hyR)
  have hstayπ := c.hstay_π_of_hstay hstay
  by_cases hv : posPart c.d.hk y = 0
  · exact ⟨1, one_pos, by
      rw [c.ζ_eq_zero_of_posPart_eq_zero hx hstayπ (by rw [hsymm]; exact hv), hv, smul_zero]⟩
  obtain ⟨j₀, hj₀⟩ : ∃ j, posPart c.d.hk y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (by ext j; simp [h j])
  obtain ⟨i₀, hi₀⟩ : ∃ i, negPart c.d.hk y i ≠ 0 := by
    by_contra h
    push Not at h
    exact c.negPart_ne_zero_of_mem hyR hx (by ext i; simp [h i])
  have hprod : ∀ j, negPart c.d.hk y i₀ * posPart c.d.hk y j =
      negPart c.d.hk (c.w x) i₀ * posPart c.d.hk (c.w x) j := fun j => by
    have := c.prod_w_eq hx hstayπ i₀ j
    rwa [hsymm] at this
  have hne : negPart c.d.hk y i₀ * posPart c.d.hk y j₀ ≠ 0 := mul_ne_zero hi₀ hj₀
  have hw0 : negPart c.d.hk (c.w x) i₀ ≠ 0 := fun h => by
    have := hprod j₀
    rw [h, zero_mul] at this
    exact hne this
  set T := c.c₂ - f x with hT
  have hγ := hasDerivAt_symm_flow_Icc (D := c.D) c.hq (x := c.D.π c.c₂ x)
    (t₀ := min 0 T) (t₁ := max 0 T) hstayπ
  set h : ℝ → ℝ := fun s => negPart c.d.hk (c.d.χ.symm (c.D.flow s (c.D.π c.c₂ x))) i₀ with hh
  have hcont : ContinuousOn h (uIcc 0 T) :=
    HasDerivAt.continuousOn fun s hs => ModelField.hasDerivAt_negPart_coord c.d.hk hγ hs i₀
  have hconst := ModelField.negPart_mul_posPart_const c.d.hk hγ i₀ j₀
  have hflowT : c.D.flow T (c.D.π c.c₂ x) = x := by
    unfold GradientLikeStrip.π
    rw [flow_flow, hT, show f x - c.c₂ + (c.c₂ - f x) = 0 by ring, c.D.flow_zero]
  have h0 : h 0 = negPart c.d.hk (c.w x) i₀ := by
    simp only [hh]
    rw [c.D.flow_zero]
    rfl
  have hTv : h T = negPart c.d.hk y i₀ := by
    simp only [hh]
    rw [hflowT, hsymm]
  have hnever : ∀ s ∈ uIcc 0 T, h s ≠ 0 := by
    intro s hs hs0
    have h1 := hconst s hs
    have h2 := hconst 0 left_mem_uIcc
    have h3 := hconst T right_mem_uIcc
    have hs0' : negPart c.d.hk (c.d.χ.symm (c.D.flow s (c.D.π c.c₂ x))) i₀ = 0 := hs0
    rw [hs0', zero_mul] at h1
    rw [hflowT, hsymm] at h3
    rw [← h1] at h3
    exact hne h3
  have hpos : 0 < h 0 * h T := by
    rcases lt_trichotomy (h 0 * h T) 0 with hlt | heq | hgt
    · exfalso
      have hmem : (0 : ℝ) ∈ uIcc (h 0) (h T) := by
        rcases mul_neg_iff.1 hlt with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨by rw [min_le_iff]; right; exact hb.le, by rw [le_max_iff]; left; exact ha.le⟩
        · exact ⟨by rw [min_le_iff]; left; exact ha.le, by rw [le_max_iff]; right; exact hb.le⟩
      obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc hcont hmem
      exact hnever s hs hs0
    · exfalso
      rcases mul_eq_zero.1 heq with h' | h'
      · exact hnever 0 left_mem_uIcc h'
      · exact hnever T right_mem_uIcc h'
    · exact hgt
  rw [h0, hTv] at hpos
  refine ⟨negPart c.d.hk y i₀ / negPart c.d.hk (c.w x) i₀, ?_, ?_⟩
  · rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact div_pos hb ha
    · exact div_pos_of_neg_of_neg hb ha
  · rw [c.ζ_def]
    ext j
    simp only [PiLp.smul_apply, smul_eq_mul]
    have := hprod j
    field_simp
    linarith

theorem transverseField_chart_q {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm q c.hq)
    (hx : c.d.χ y ∈ c.openChartTube)
    (hstay : ∀ s ∈ uIcc 0 (f (c.d.χ y) - c.c₂), c.D.flow s (c.d.χ y) ∈ c.qBall) :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm (c.d.χ y) (c.transverseField (c.d.χ y)) =
      recombine c.d.hk
        ((-c.κ (c.d.χ y) *
          (‖posPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2))) •
            negPart c.d.hk y)
        ((-c.κ (c.d.χ y) *
          (‖negPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2))) •
            posPart c.d.hk y) := by
  set x := c.d.χ y with hxdef
  have hyR : morseNorm n y ≤ c.d.R := hy.le.trans (c.D.hrm q c.hq).2
  have hysrc : y ∈ c.d.χ.source := c.d.hsrc y hyR
  have hyball : y ∈ Metric.ball (0 : Fin n → ℝ) c.d.R' :=
    mem_ball_of_morseNorm_lt (hy.trans (c.D.rm_lt_R' q c.hq))
  have hsymm : c.d.χ.symm x = y := c.d.χ.left_inv hysrc
  have hstayπ := c.hstay_π_of_hstay hstay
  set Zr := (NormedSpace.fromTangentSpace (c.d.χ.symm x))
    (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm x (c.transverseField x)) with hZr
  have hρ : HasDerivAt (fun r => c.d.χ.symm (c.levelDeformation r x)) Zr 0 :=
    c.hasDerivAt_levelDeformation hx (c.d.mdifferentiableAt_symm ⟨y, hyball, rfl⟩)
  have hev := c.eventually_segment_mem hx hstayπ
  have hneg : HasDerivAt (fun r => negPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)))
      (negPart c.d.hk Zr) 0 :=
    (ModelField.negPartL c.d.hk).hasFDerivAt.comp_hasDerivAt 0 hρ
  have hpos : HasDerivAt (fun r => posPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)))
      (posPart c.d.hk Zr) 0 :=
    (ModelField.posPartL c.d.hk).hasFDerivAt.comp_hasDerivAt 0 hρ
  have hprod : ∀ i j, negPart c.d.hk Zr i * posPart c.d.hk y j +
      negPart c.d.hk y i * posPart c.d.hk Zr j =
        -c.κ x * (negPart c.d.hk y i * posPart c.d.hk y j) := by
    intro i j
    have h1 : HasDerivAt (fun r => negPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)) i)
        (negPart c.d.hk Zr i) 0 := by
      have := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt 0 hneg
      exact this
    have h2 : HasDerivAt (fun r => posPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)) j)
        (posPart c.d.hk Zr j) 0 := by
      have := (EuclideanSpace.proj j).hasFDerivAt.comp_hasDerivAt 0 hpos
      exact this
    have h3 := h1.mul h2
    have h4 : HasDerivAt (fun r => c.transverseScale x r * (negPart c.d.hk y i * posPart c.d.hk y j))
        (-c.κ x * (negPart c.d.hk y i * posPart c.d.hk y j)) 0 :=
      (c.hasDerivAt_transverseScale x).mul_const _
    have h5 : HasDerivAt (fun r => negPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)) i *
        posPart c.d.hk (c.d.χ.symm (c.levelDeformation r x)) j)
        (-c.κ x * (negPart c.d.hk y i * posPart c.d.hk y j)) 0 := by
      refine h4.congr_of_eventuallyEq ?_
      filter_upwards [hev] with r hr
      rw [c.prod_levelDeformation_eq hx hr.1 hr.2 hstayπ i j, hsymm]
    have := h3.unique h5
    rw [c.levelDeformation_zero hx, hsymm] at this
    exact this
  have hlev : inner ℝ (posPart c.d.hk y) (posPart c.d.hk Zr) =
      inner ℝ (negPart c.d.hk y) (negPart c.d.hk Zr) := by
    have h3 := hpos.norm_sq.sub hneg.norm_sq
    have h4 : HasDerivAt (fun r => ‖posPart c.d.hk (c.d.χ.symm (c.levelDeformation r x))‖ ^ 2 -
        ‖negPart c.d.hk (c.d.χ.symm (c.levelDeformation r x))‖ ^ 2) 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) (2 * (f x - f q))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with r hr
      obtain ⟨z, hz, hzG⟩ := c.levelDeformation_mem_qBall_of_seg hr.2
      have hz' : c.d.χ.symm (c.levelDeformation r x) = z := by
        rw [← hzG, c.d.χ.left_inv (c.d.hsrc z (hz.le.trans (c.D.hrm q c.hq).2))]
      have hnf := c.d.hnorm z (hz.le.trans (c.D.hrm q c.hq).2)
      rw [morseNormalForm_split, hzG, c.f_levelDeformation hx hr.1] at hnf
      rw [hz']
      linarith
    have := h3.unique h4
    rw [c.levelDeformation_zero hx, hsymm] at this
    linarith
  have hv0 : posPart c.d.hk y = 0 → negPart c.d.hk Zr = 0 ∧ posPart c.d.hk Zr = 0 := by
    intro hv
    have hζ : c.ζ x = 0 := c.ζ_eq_zero_of_posPart_eq_zero hx hstayπ (by rw [hsymm]; exact hv)
    have hZ : c.transverseField x = 0 := (c.transverseField_eq_zero_iff hx).2 hζ
    have : Zr = 0 := by rw [hZr, hZ, map_zero, map_zero]
    rw [this]
    exact ⟨(ModelField.negPartL c.d.hk).map_zero, (ModelField.posPartL c.d.hk).map_zero⟩
  have hu : negPart c.d.hk y ≠ 0 := c.negPart_ne_zero_of_mem hyR hx
  obtain ⟨hu', hv'⟩ := ModelField.solve_transport hu hprod hlev hv0
  have hfinal : Zr = recombine c.d.hk
      ((-c.κ x * (‖posPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2))) •
        negPart c.d.hk y)
      ((-c.κ x * (‖negPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2))) •
        posPart c.d.hk y) := by
    rw [← recombine_decompose c.d.hk Zr, hu', hv']
  exact hfinal

theorem posPart_transverseField_chart_q {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm q c.hq)
    (hx : c.d.χ y ∈ c.openChartTube)
    (hstay : ∀ s ∈ uIcc 0 (f (c.d.χ y) - c.c₂), c.D.flow s (c.d.χ y) ∈ c.qBall) :
    posPart c.d.hk (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm (c.d.χ y) (c.transverseField (c.d.χ y))) =
      (-c.κ (c.d.χ y) *
        (‖negPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2))) •
          posPart c.d.hk y := by
  rw [c.transverseField_chart_q hy hx hstay, ModelField.posPart_recombine]

theorem negPart_transverseField_chart_q {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm q c.hq)
    (hx : c.d.χ y ∈ c.openChartTube)
    (hstay : ∀ s ∈ uIcc 0 (f (c.d.χ y) - c.c₂), c.D.flow s (c.d.χ y) ∈ c.qBall) :
    negPart c.d.hk (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.d.χ.symm (c.d.χ y) (c.transverseField (c.d.χ y))) =
      (-c.κ (c.d.χ y) *
        (‖posPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2))) •
          negPart c.d.hk y := by
  rw [c.transverseField_chart_q hy hx hstay, ModelField.negPart_recombine]

theorem posPart_transverseField_chart_q_coeff_neg {y : Fin n → ℝ} (hyR : morseNorm n y ≤ c.d.R)
    (hx : c.d.χ y ∈ c.openChartTube) :
    -c.κ (c.d.χ y) *
      (‖negPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2)) < 0 := by
  have h := (c.normSq_negPart_of_mem hyR hx).2
  have hκ := c.κ_pos (c.d.χ y)
  have hpos : 0 < ‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2 := by positivity
  have : 0 < ‖negPart c.d.hk y‖ ^ 2 / (‖negPart c.d.hk y‖ ^ 2 + ‖posPart c.d.hk y‖ ^ 2) :=
    div_pos h hpos
  nlinarith

def pBall : Set M := c.e.χ '' {y | morseNorm n y < c.D.rm p c.hp}

theorem isOpen_pBall : IsOpen c.pBall := c.D.isOpen_modelBall p c.hp

theorem pBall_subset_image_ball : c.pBall ⊆ c.e.χ '' Metric.ball 0 c.e.R' :=
  c.D.modelBall_subset_image_ball p c.hp

theorem eventually_levelDeformation_mem_pBall {x : M} (hx : x ∈ c.openChartTube) (hxp : x ∈ c.pBall) :
    ∀ᶠ r in 𝓝 (0 : ℝ), c.levelDeformation r x ∈ c.pBall :=
  (c.continuousAt_levelDeformation_curve hx).preimage_mem_nhds
    (c.isOpen_pBall.mem_nhds (by rw [c.levelDeformation_zero hx]; exact hxp))

theorem chart_p_symm_eq {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm p c.hp) :
    c.e.χ.symm (c.e.χ y) = y :=
  c.e.χ.left_inv (c.e.hsrc y (hy.le.trans (c.D.hrm p c.hp).2))

theorem chart_p_mem_image_ball {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm p c.hp) :
    c.e.χ y ∈ c.e.χ '' Metric.ball 0 c.e.R' :=
  ⟨y, mem_ball_of_morseNorm_lt (hy.trans (c.D.rm_lt_R' p c.hp)), rfl⟩

theorem hasDerivAt_symm_levelDeformation_p {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm p c.hp)
    (hx : c.e.χ y ∈ c.openChartTube) :
    HasDerivAt (fun r => c.e.χ.symm (c.levelDeformation r (c.e.χ y)))
      ((NormedSpace.fromTangentSpace (c.e.χ.symm (c.e.χ y)))
        (mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ y) (c.transverseField (c.e.χ y)))) 0 :=
  c.hasDerivAt_levelDeformation hx (c.e.mdifferentiableAt_symm (c.chart_p_mem_image_ball hy))

theorem transverseField_chart_p_orth {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm p c.hp)
    (hx : c.e.χ y ∈ c.openChartTube) :
    ∑ i, y i * mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ y) (c.transverseField (c.e.χ y)) i = 0 := by
  set x := c.e.χ y with hxdef
  have hρ := c.hasDerivAt_symm_levelDeformation_p hy hx
  have hxp : x ∈ c.pBall := ⟨y, hy, rfl⟩
  have h1 := ModelField.hasDerivAt_morseNorm_sq_half hρ
  have h1' := h1.const_add (f p)
  have h2 : HasDerivAt (fun r => f p + morseNorm n (c.e.χ.symm (c.levelDeformation r x)) ^ 2 / 2) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (f x)).congr_of_eventuallyEq ?_
    filter_upwards [c.eventually_f_levelDeformation hx, c.eventually_levelDeformation_mem_pBall hx hxp] with r hr hr'
    obtain ⟨z, hz, hzG⟩ := hr'
    have hz' : c.e.χ.symm (c.levelDeformation r x) = z := by rw [← hzG, c.chart_p_symm_eq hz]
    rw [hz', ← c.f_chart_p (hz.le.trans (c.D.hrm p c.hp).2), hzG, hr]
  have := h1'.unique h2
  rw [c.levelDeformation_zero hx, c.chart_p_symm_eq hy] at this
  exact this

theorem transverseField_chart_p_smul {y : Fin n → ℝ} (hy : morseNorm n y < c.D.rm p c.hp)
    (hx : c.e.χ y ∈ c.openChartTube) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hxt : c.e.χ (t • y) ∈ c.openChartTube) :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ (t • y)) (c.transverseField (c.e.χ (t • y))) =
      t • mfderiv I 𝓘(ℝ, Fin n → ℝ) c.e.χ.symm (c.e.χ y) (c.transverseField (c.e.χ y)) := by
  set x := c.e.χ y with hxdef
  set xt := c.e.χ (t • y) with hxtdef
  have hR : c.D.rm p c.hp ≤ c.e.R := (c.D.hrm p c.hp).2
  have hyR : morseNorm n y ≤ c.e.R := hy.le.trans hR
  have hny : 0 ≤ morseNorm n y := ModelField.morseNorm_nonneg y
  have hty : morseNorm n (t • y) = t * morseNorm n y := by
    rw [ModelField.morseNorm_smul, abs_of_pos ht0]
  have htyR : morseNorm n (t • y) < c.D.rm p c.hp := by
    rw [hty]; nlinarith
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h := hx.1.1
    rw [c.f_chart_p (by rw [morseNorm_zero]; exact c.e.R_pos.le), morseNorm_zero] at h
    have := c.f_p_add_lt_c₁_sub_η
    nlinarith [sq_nonneg c.e.r₀]
  have hnypos : 0 < morseNorm n y :=
    lt_of_le_of_ne hny fun h => hy0 ((ModelField.morseNorm_eq_zero_iff y).1 h.symm)
  have hfx : f x = f p + morseNorm n y ^ 2 / 2 := c.f_chart_p hyR
  have hfxt : f xt = f p + t ^ 2 * morseNorm n y ^ 2 / 2 := by
    rw [hxtdef, c.f_chart_p (htyR.le.trans hR), hty]; ring
  set s := f x - f xt with hs
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hs0 : 0 ≤ s := by
    rw [hs, hfx, hfxt]
    nlinarith [mul_nonneg (sq_nonneg (morseNorm n y)) (sub_nonneg.2 ht2)]
  have hxt_flow : c.D.flow s x = xt := by
    obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero (D := c.D) c.hkp hy hs0
    have hf1 : f (c.D.flow s x) = f x - s :=
      c.f_flow_eq_sub_tube (Ioo_subset_Icc_self hx.1) (T := s)
        (by rw [hs, sub_sub_cancel]; exact Ioo_subset_Icc_self hxt.1) s right_mem_uIcc
    have hf2 : f (c.e.χ (l • y)) = f p + l ^ 2 * morseNorm n y ^ 2 / 2 := by
      rw [c.f_chart_p (by rw [ModelField.morseNorm_smul, abs_of_pos hl0]; nlinarith),
        ModelField.morseNorm_smul, abs_of_pos hl0]; ring
    rw [hl, hf2, hs, hfxt] at hf1
    have hny2 : 0 < morseNorm n y ^ 2 := by positivity
    have hl2' : (l ^ 2 - t ^ 2) * morseNorm n y ^ 2 = 0 := by linarith
    have hl2 : l ^ 2 = t ^ 2 := by
      have := (mul_eq_zero.1 hl2').resolve_right hny2.ne'
      linarith
    have hlt : l = t := (sq_eq_sq₀ hl0.le ht0.le).1 hl2
    rw [hl, hlt]
  have hw : c.w xt = c.w x := by
    unfold w
    rw [← hxt_flow, c.π_flow_eq (c.openChartTube_subset_regularFlowDomain hx)
      (by rw [hxt_flow]; exact c.openChartTube_subset_regularFlowDomain hxt)]
  have hG : ∀ r, c.levelDeformation r xt = c.D.flow s (c.levelDeformation r x) := by
    intro r
    unfold levelDeformation
    rw [hw, flow_flow]
    congr 1
    rw [hs]; ring
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), c.e.χ.symm (c.levelDeformation r xt) = t • c.e.χ.symm (c.levelDeformation r x) := by
    filter_upwards [c.eventually_f_levelDeformation hx, c.eventually_levelDeformation_mem_pBall hx ⟨y, hy, rfl⟩] with r hr hr'
    obtain ⟨z, hz, hzG⟩ := hr'
    have hz' : c.e.χ.symm (c.levelDeformation r x) = z := by rw [← hzG, c.chart_p_symm_eq hz]
    have hfz : f (c.e.χ z) = f x := by rw [hzG, hr]
    have hnz : morseNorm n z = morseNorm n y := by
      rw [c.f_chart_p (hz.le.trans hR), hfx] at hfz
      have h1 := ModelField.morseNorm_nonneg z
      nlinarith
    obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero (D := c.D) c.hkp hz hs0
    have hf1 : f (c.D.flow s (c.levelDeformation r x)) = f (c.levelDeformation r x) - s :=
      c.f_flow_eq_sub_tube (by rw [hr]; exact Ioo_subset_Icc_self hx.1) (T := s)
        (by rw [hr, hs, sub_sub_cancel]; exact Ioo_subset_Icc_self hxt.1) s right_mem_uIcc
    have hf2 : f (c.e.χ (l • z)) = f p + l ^ 2 * morseNorm n y ^ 2 / 2 := by
      rw [c.f_chart_p (by rw [ModelField.morseNorm_smul, abs_of_pos hl0, hnz]; nlinarith),
        ModelField.morseNorm_smul, abs_of_pos hl0, hnz]; ring
    rw [← hzG, hl, hf2, hfz, hs, hfxt, hfx] at hf1
    have hny2 : 0 < morseNorm n y ^ 2 := by positivity
    have hl2' : (l ^ 2 - t ^ 2) * morseNorm n y ^ 2 = 0 := by linarith
    have hl2 : l ^ 2 = t ^ 2 := by
      have := (mul_eq_zero.1 hl2').resolve_right hny2.ne'
      linarith
    have hlt : l = t := (sq_eq_sq₀ hl0.le ht0.le).1 hl2
    have htz : morseNorm n (t • z) < c.D.rm p c.hp := by
      rw [ModelField.morseNorm_smul, abs_of_pos ht0, hnz]; nlinarith
    rw [hG r, ← hzG, hl, hlt, c.chart_p_symm_eq htz, c.chart_p_symm_eq hz]
  have h1 := c.hasDerivAt_symm_levelDeformation_p htyR hxt
  have h2 := (c.hasDerivAt_symm_levelDeformation_p hy hx).const_smul t
  have h3 := h2.congr_of_eventuallyEq hev
  exact h1.unique h3

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
