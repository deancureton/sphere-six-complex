module

public import DifferentialGeometry.Topology.Morse.Strip.Substrip

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {a b : ℝ} {crit : Finset M}

namespace ModelField

theorem modelField_index_zero_apply {k : ℕ} (hk : k = 0) (r₀ : ℝ) (y : Fin n → ℝ) (i : Fin n) :
    modelField k r₀ y i = -(theta r₀ y * y i) := by
  subst hk
  simp [modelField, modelDesc]

theorem morseNorm_smul (l : ℝ) (y : Fin n → ℝ) : morseNorm n (l • y) = |l| * morseNorm n y := by
  change ‖(WithLp.toLp 2 (l • y) : EuclideanSpace ℝ (Fin n))‖ = _
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

end ModelField

namespace MorseNormalChart

variable {r : M} (d : MorseNormalChart I f r)

theorem abs_f_chart_sub_le {y : Fin n → ℝ} (hy : morseNorm n y ≤ d.R) :
    |f (d.χ y) - f r| ≤ morseNorm n y ^ 2 / 2 := by
  rw [d.hnorm y hy, morseNormalForm_split d.hk, morseNorm_sq_eq_negPart_add_posPart d.hk, abs_le]
  constructor <;> nlinarith [sq_nonneg ‖negPart d.hk y‖, sq_nonneg ‖posPart d.hk y‖]

end MorseNormalChart

theorem mem_pair_iff {α : Type*} [DecidableEq α] {a b x : α} :
    x ∈ ({a, b} : Finset α) ↔ x = a ∨ x = b := by
  rw [Finset.mem_insert, Finset.mem_singleton]

namespace GradientLikeStrip

variable [IsManifold I ∞ M] {D : GradientLikeStrip I f a b crit}

theorem abs_f_sub_le_of_mem_closedSmallBall {p' : M} {hp' : p' ∈ crit} {x : M}
    (hx : x ∈ D.closedSmallBall p' hp') : |f x - f p'| ≤ (D.chart p' hp').r₀ ^ 2 / 2 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : morseNorm n y ≤ (D.chart p' hp').r₀ := hy
  have h := (D.chart p' hp').abs_f_chart_sub_le (hy'.trans (D.r₀_lt_R p' hp').le)
  have h2 : morseNorm n y ^ 2 ≤ (D.chart p' hp').r₀ ^ 2 :=
    pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy' 2
  linarith

variable [T2Space M] [I.Boundaryless]

theorem flow_ray_of_index_zero {p : M} {hp : p ∈ crit} (hk : (D.chart p hp).k = 0)
    {y : Fin n → ℝ} (hy : morseNorm n y < D.rm p hp) {t : ℝ} (ht : 0 ≤ t) :
    ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ D.flow t ((D.chart p hp).χ y) = (D.chart p hp).χ (l • y) := by
  set d := D.chart p hp with hd
  set x := d.χ y with hx
  have hr₀ := d.hr₀
  have hyR : morseNorm n y ≤ d.R := hy.le.trans (D.hrm p hp).2
  have hysrc : y ∈ d.χ.source := d.hsrc y hyR
  have hstay : ∀ s ∈ Icc 0 t, D.flow s x ∈ d.χ '' {z | morseNorm n z ≤ morseNorm n y} :=
    fun s hs => modelBall_forward_invariant_of_index_zero hk hy hs.1
  have hmodel : ∀ s ∈ Icc 0 t, D.flow s x ∈ d.χ '' {z | morseNorm n z < D.rm p hp} :=
    fun s hs =>
      image_mono (fun z (hz : morseNorm n z ≤ morseNorm n y) => hz.trans_lt hy) (hstay s hs)
  set γ : ℝ → Fin n → ℝ := fun s => d.χ.symm (D.flow s x) with hγ
  have hγ' : ∀ s ∈ Icc 0 t, HasDerivAt γ (ModelField.modelField d.k d.r₀ (γ s)) s :=
    hasDerivAt_symm_flow_Icc hp hmodel
  have hγ0 : γ 0 = y := by
    change d.χ.symm (D.flow 0 x) = y
    rw [flow_zero, hx, d.χ.left_inv hysrc]
  have hγle : ∀ s ∈ Icc 0 t, morseNorm n (γ s) ≤ morseNorm n y := by
    intro s hs
    obtain ⟨z, hz, hzs⟩ := hstay s hs
    change morseNorm n (d.χ.symm (D.flow s x)) ≤ _
    rw [← hzs, d.χ.left_inv (d.hsrc z (le_trans hz hyR))]
    exact hz
  have hχγ : ∀ s ∈ Icc 0 t, d.χ (γ s) = D.flow s x := fun s hs =>
    d.symm_image_eq (D.modelBall_subset_image_ball p hp (hmodel s hs))
  have hcoord : ∀ s ∈ Icc 0 t, ∀ i,
      HasDerivAt (fun s => γ s i) (-(ModelField.theta d.r₀ (γ s) * γ s i)) s := by
    intro s hs i
    have := hasDerivAt_pi.1 (hγ' s hs) i
    rwa [ModelField.modelField_index_zero_apply hk] at this
  obtain ⟨C, -, hC⟩ := ModelField.exists_theta_bound hr₀ hγ'
  have hminor : ∀ s ∈ Icc 0 t, ∀ i j, γ s i * y j = γ s j * y i := by
    intro s hs i j
    set g : ℝ → ℝ := fun s => γ s i * y j - γ s j * y i with hg
    have hg' : ∀ s ∈ Icc 0 t, HasDerivAt g (-(ModelField.theta d.r₀ (γ s) * g s)) s := by
      intro s hs
      have h := ((hcoord s hs i).mul_const (y j)).sub ((hcoord s hs j).mul_const (y i))
      convert h using 1
      simp only [hg]; ring
    have hcont : ContinuousOn g (Icc 0 t) := HasDerivAt.continuousOn hg'
    have hbound := norm_le_gronwallBound_of_norm_deriv_right_le (f := g)
      (f' := fun s => -(ModelField.theta d.r₀ (γ s) * g s)) (δ := 0) (K := C) (ε := 0) (a := 0)
      (b := t) hcont (fun s hs => (hg' s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by
        change ‖γ 0 i * y j - γ 0 j * y i‖ ≤ 0
        rw [hγ0, mul_comm (y i), sub_self, norm_zero])
      (fun s hs => by
        rw [norm_neg, norm_mul, Real.norm_eq_abs, abs_of_pos (ModelField.theta_pos hr₀ _),
          add_zero]
        exact mul_le_mul_of_nonneg_right (hC s (Ico_subset_Icc_self hs)) (norm_nonneg _)) s hs
    rw [gronwallBound_ε0_δ0, norm_le_zero_iff] at hbound
    simp only [hg] at hbound
    linarith
  by_cases hy0 : y = 0
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    rw [one_smul, hx, hy0, d.hχ0, D.flow_crit hp]
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hy0
  have hi₀ : y i₀ ≠ 0 := hi₀
  have hray : ∀ s ∈ Icc 0 t, γ s = (γ s i₀ / y i₀) • y := by
    intro s hs
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith [hminor s hs j i₀]
  have hne : ∀ s ∈ Icc 0 t, γ s i₀ ≠ 0 := by
    intro s hs h0
    have hγs : γ s = 0 := by rw [hray s hs, h0, zero_div, zero_smul]
    have h1 : D.flow s x = p := by rw [← hχγ s hs, hγs, d.hχ0]
    have h2 : x = p := by
      have := congrArg (D.flow (-s)) h1
      rwa [flow_neg_flow, D.flow_crit hp] at this
    apply hy0
    have h2' : d.χ y = d.χ 0 := by rw [d.hχ0]; exact h2
    exact d.χ.injOn hysrc (d.hsrc 0 (by rw [morseNorm_zero]; exact d.R_pos.le)) h2'
  have hcontγ : ContinuousOn (fun s => γ s i₀ * y i₀) (Icc 0 t) :=
    (HasDerivAt.continuousOn (fun s hs => hcoord s hs i₀)).mul continuousOn_const
  have hpos : 0 < γ t i₀ * y i₀ := by
    by_contra hle
    push Not at hle
    have h0 : 0 < γ 0 i₀ * y i₀ := by rw [hγ0]; exact mul_self_pos.2 hi₀
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht hcontγ ⟨hle, h0.le⟩
    exact hne s hs ((mul_eq_zero.1 hs0).resolve_right hi₀)
  have htI : t ∈ Icc 0 t := right_mem_Icc.2 ht
  refine ⟨γ t i₀ / y i₀, ?_, ?_, ?_⟩
  · have : γ t i₀ / y i₀ = (γ t i₀ * y i₀) / (y i₀ ^ 2) := by field_simp
    rw [this]
    exact div_pos hpos (by positivity)
  · have h1 := hγle t htI
    rw [hray t htI, ModelField.morseNorm_smul] at h1
    have hny : 0 < morseNorm n y := lt_of_le_of_ne (ModelField.morseNorm_nonneg y)
      fun h => hy0 ((ModelField.morseNorm_eq_zero_iff y).1 h.symm)
    have : |γ t i₀ / y i₀| ≤ 1 := le_of_mul_le_mul_right (by linarith) hny
    exact (abs_le.1 this).2
  · exact (hχγ t htI).symm.trans (congrArg d.χ (hray t htI))

variable (I) in
structure IndexZeroCancellingPair [DecidableEq M] (f : M → ℝ) (a' b' : ℝ) (p q : M) where
  hf : MorseStrip I f a' b'
  D : GradientLikeStrip I f a' b' {p, q}
  hcrit : ∀ x, x ∈ ({p, q} : Finset M) ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x
  hp : p ∈ ({p, q} : Finset M)
  hq : q ∈ ({p, q} : Finset M)
  ε : ℝ
  hε : 0 < ε
  hgood : D.goodPair ε p q hp hq
  hcst : ∀ p' hp', (D.chart p' hp').r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p' hp' ^ 2
  hlt : f p + 2 * ε < f q
  hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp'

namespace IndexZeroCancellingPair

variable [DecidableEq M] {a' b' : ℝ} {p q : M} (c : IndexZeroCancellingPair I f a' b' p q)

theorem hkp : (c.D.chart p c.hp).k = 0 := c.hgood.1

theorem hkq : (c.D.chart q c.hq).k = 1 := by
  obtain ⟨hk, -⟩ := c.hgood.2
  exact hk

abbrev e : MorseNormalChart I f p := c.D.chart p c.hp

abbrev d : MorseNormalChart I f q := c.D.chart q c.hq

def i : Fin 2 := c.hgood.2.choose_spec.choose

theorem i_spec : c.d.χ (c.d.armPt c.hkq c.ε c.i) ∈ c.D.basin p c.hp ∧
    c.d.χ (c.d.armPt c.hkq c.ε (c.i + 1)) ∉ c.D.basin p c.hp :=
  c.hgood.2.choose_spec.choose_spec

def z₀ : M := c.d.χ (c.d.armPt c.hkq c.ε c.i)

def z₁ : M := c.d.χ (c.d.armPt c.hkq c.ε (c.i + 1))

def transitTime : ℝ := f q - f p - 2 * c.ε

include c in
theorem hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := c.hf.smooth

theorem transitTime_pos : 0 < c.transitTime := by
  unfold transitTime; linarith [c.hlt]

include c in
theorem p_ne_q : p ≠ q := by
  intro h
  have h1 := c.hlt
  have h2 := c.hε
  subst h
  linarith

include c in
theorem f_p_mem : f p ∈ Ioo a' b' := c.D.f_mem_Ioo p c.hp

include c in
theorem f_q_mem : f q ∈ Ioo a' b' := c.D.f_mem_Ioo q c.hq

theorem hrmp : 8 * c.ε < c.D.rm p c.hp ^ 2 := (c.hcst p c.hp).2

theorem hrmq : 8 * c.ε < c.D.rm q c.hq ^ 2 := (c.hcst q c.hq).2

theorem hr₀p : c.e.r₀ ^ 2 < 2 * c.ε := (c.hcst p c.hp).1

theorem hr₀q : c.d.r₀ ^ 2 < 2 * c.ε := (c.hcst q c.hq).1

theorem rmp_pos : 0 < c.D.rm p c.hp := c.D.rm_pos p c.hp

theorem rmq_pos : 0 < c.D.rm q c.hq := c.D.rm_pos q c.hq

theorem sqrt_two_ε_lt_rmp : Real.sqrt (2 * c.ε) < c.D.rm p c.hp / 2 := by
  rw [Real.sqrt_lt' (by linarith [c.rmp_pos])]
  nlinarith [c.hrmp]

theorem sqrt_two_ε_lt_rmq : Real.sqrt (2 * c.ε) < c.D.rm q c.hq / 2 := by
  rw [Real.sqrt_lt' (by linarith [c.rmq_pos])]
  nlinarith [c.hrmq]

theorem f_z₀ : f c.z₀ = f q - c.ε :=
  f_chart_of_mem_leftModelSphere' (D := c.D) c.hq c.hrmq
    (c.d.armPt_mem_leftModelSphere c.hkq c.hε.le c.i)

theorem f_z₁ : f c.z₁ = f q - c.ε :=
  f_chart_of_mem_leftModelSphere' (D := c.D) c.hq c.hrmq
    (c.d.armPt_mem_leftModelSphere c.hkq c.hε.le (c.i + 1))

theorem z₀_mem_basin : c.z₀ ∈ c.D.basin p c.hp := c.i_spec.1

theorem z₁_notMem_basin : c.z₁ ∉ c.D.basin p c.hp := c.i_spec.2

theorem avoid_smallBall {y : M}
    (hy : f y ∈ Ioo (f p + c.e.r₀ ^ 2 / 2) (f q - c.d.r₀ ^ 2 / 2)) :
    ∀ p' hp', y ∉ c.D.smallBall p' hp' := by
  intro p' hp' hmem
  have h := abs_f_sub_lt_of_mem_smallBall hp' hmem
  rcases mem_pair_iff.1 hp' with rfl | rfl
  · rw [abs_lt] at h
    linarith [hy.1, h.2]
  · rw [abs_lt] at h
    linarith [hy.2, h.1]

theorem f_flow_z₀' {s : ℝ} (hs₀ : 0 ≤ s) (hs : s < c.transitTime + (c.ε - c.e.r₀ ^ 2 / 2)) :
    f (c.D.flow s c.z₀) = f q - c.ε - s := by
  obtain ⟨hpa, -⟩ := c.f_p_mem
  obtain ⟨-, hqb⟩ := c.f_q_mem
  have hr := c.hr₀p
  have hr' := c.hr₀q
  have hε := c.hε
  have hlt := c.hlt
  have hT : c.transitTime = f q - f p - 2 * c.ε := rfl
  rw [hT] at hs
  have hsq := sq_nonneg c.e.r₀
  have h := f_flow_eq_sub_of_levels c.hfs (D := c.D) (x := c.z₀) (T := s)
    (by rw [c.f_z₀]; constructor <;> linarith)
    (by rw [c.f_z₀]; constructor <;> linarith)
    (by
      intro y hy
      apply c.avoid_smallBall
      rw [c.f_z₀, uIcc_of_ge (by linarith)] at hy
      constructor <;> linarith [hy.1, hy.2]) s right_mem_uIcc
  rw [h, c.f_z₀]

theorem f_flow_z₀ {s : ℝ} (hs : s ∈ Icc 0 c.transitTime) : f (c.D.flow s c.z₀) = f q - c.ε - s :=
  c.f_flow_z₀' hs.1 (by linarith [hs.2, c.hr₀p])

theorem f_flow_transitTime_z₀ : f (c.D.flow c.transitTime c.z₀) = f p + c.ε := by
  rw [c.f_flow_z₀ (right_mem_Icc.2 c.transitTime_pos.le)]
  unfold transitTime; ring

theorem flow_transitTime_mem_modelBall :
    c.D.flow c.transitTime c.z₀ ∈ c.e.χ '' {y | morseNorm n y < c.D.rm p c.hp} := by
  have hz : c.D.flow c.transitTime c.z₀ ∈ c.D.basin p c.hp :=
    (flow_mem_basin_iff c.hkp c.transitTime).2 c.z₀_mem_basin
  exact mem_modelBall_of_mem_basin_index_zero c.hfs c.hkp hz
    (by rw [c.f_flow_transitTime_z₀]; linarith [c.hrmp, c.hε])

def y₀ : Fin n → ℝ := c.e.χ.symm (c.D.flow c.transitTime c.z₀)

theorem morseNorm_y₀_lt : morseNorm n c.y₀ < c.D.rm p c.hp := by
  obtain ⟨y, hy, hyx⟩ := c.flow_transitTime_mem_modelBall
  have : c.y₀ = y := by
    unfold y₀
    rw [← hyx, c.e.χ.left_inv (c.e.hsrc y (hy.le.trans (c.D.hrm p c.hp).2))]
  rw [this]; exact hy

theorem chart_y₀ : c.e.χ c.y₀ = c.D.flow c.transitTime c.z₀ :=
  c.e.symm_image_eq (c.D.modelBall_subset_image_ball p c.hp c.flow_transitTime_mem_modelBall)

theorem f_chart_p {y : Fin n → ℝ} (hy : morseNorm n y ≤ c.e.R) :
    f (c.e.χ y) = f p + morseNorm n y ^ 2 / 2 := by
  rw [c.e.hnorm y hy, morseNormalForm_index_zero _ c.hkp]

theorem morseNorm_y₀_sq : morseNorm n c.y₀ ^ 2 = 2 * c.ε := by
  have h1 := c.f_chart_p (c.morseNorm_y₀_lt.le.trans (c.D.hrm p c.hp).2)
  rw [c.chart_y₀, c.f_flow_transitTime_z₀] at h1
  linarith

theorem y₀_ne_zero : c.y₀ ≠ 0 := by
  intro h
  have := c.morseNorm_y₀_sq
  rw [h, morseNorm_zero] at this
  linarith [c.hε]

theorem z₁_mem_bottom : c.z₁ ∈ c.D.bottom := by
  obtain ⟨hpa, -⟩ := c.f_p_mem
  obtain ⟨-, hqb⟩ := c.f_q_mem
  have hε := c.hε
  have hlt := c.hlt
  rcases trichotomy (D := c.D) c.hfs c.hε c.hcst (x := c.z₁)
      (by rw [c.f_z₁]; constructor <;> linarith) with h | ⟨r, hr, hcap⟩
  · exact h
  · exfalso
    rcases mem_pair_iff.1 hr with rfl | rfl
    · rw [captured_index_zero_eq_basin c.hkp] at hcap
      exact c.z₁_notMem_basin hcap
    · have := f_le_of_mem_captured c.hfs hcap 0
      rw [flow_zero, c.f_z₁] at this
      linarith

theorem flow_z₀_ne_z₁_orbit (s t : ℝ) : c.D.flow s c.z₀ ≠ c.D.flow t c.z₁ := by
  intro h
  have h0 : c.D.flow s c.z₀ ∈ c.D.basin p c.hp := (flow_mem_basin_iff c.hkp s).2 c.z₀_mem_basin
  rw [h, flow_mem_basin_iff c.hkp] at h0
  exact c.z₁_notMem_basin h0

theorem exists_other_arm_exit : ∃ T₁ : ℝ, 0 < T₁ ∧ f (c.D.flow T₁ c.z₁) = a' ∧
    ∀ s ∈ Ico 0 T₁, a' < f (c.D.flow s c.z₁) := by
  obtain ⟨t, ht, hlt⟩ := c.z₁_mem_bottom
  have hcont : Continuous (fun s => f (c.D.flow s c.z₁)) :=
    c.hfs.continuous.comp (c.D.continuous_flow_curve c.z₁)
  have hK : IsClosed (f ⁻¹' Iic a') := isClosed_Iic.preimage c.hfs.continuous
  obtain ⟨s₀, hs₀, hs₀K, hmin⟩ := exists_first_time hK (c.D.continuous_flow_curve c.z₁) (t := t)
    ⟨t, ⟨ht, le_rfl⟩, hlt.le⟩
  have hfz₁ : a' < f c.z₁ := by
    rw [c.f_z₁]; linarith [c.f_p_mem.1, c.hlt, c.hε]
  have hpos : 0 < s₀ := by
    rcases hs₀.1.eq_or_lt with h | h
    · exfalso
      have hle : f (c.D.flow s₀ c.z₁) ≤ a' := hs₀K
      rw [← h, flow_zero] at hle
      linarith
    · exact h
  have hgt : ∀ s ∈ Ico 0 s₀, a' < f (c.D.flow s c.z₁) := fun s hs => not_le.1 (hmin s hs)
  refine ⟨s₀, hpos, le_antisymm (show f (c.D.flow s₀ c.z₁) ≤ a' from hs₀K) ?_, hgt⟩
  have hcl : IsClosed {s : ℝ | a' ≤ f (c.D.flow s c.z₁)} := isClosed_le continuous_const hcont
  have hsub : Ico 0 s₀ ⊆ {s : ℝ | a' ≤ f (c.D.flow s c.z₁)} := fun s hs => (hgt s hs).le
  have := hcl.closure_subset_iff.2 hsub
  rw [closure_Ico hpos.ne] at this
  exact this (right_mem_Icc.2 hpos.le)

theorem flow_z₀_mem_modelBall {s : ℝ} (hs : c.transitTime ≤ s) :
    c.D.flow s c.z₀ ∈ c.e.χ '' {y | morseNorm n y < c.D.rm p c.hp} := by
  have := flow_mem_modelBall_of_index_zero c.hkp c.flow_transitTime_mem_modelBall (t := s - c.transitTime)
    (by linarith)
  rwa [flow_flow, add_sub_cancel] at this

theorem flow_z₀_ray_general {s : ℝ} (hs : c.transitTime ≤ s) :
    ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ c.D.flow s c.z₀ = c.e.χ (l • c.y₀) := by
  obtain ⟨l, hl0, hl1, hl⟩ := flow_ray_of_index_zero c.hkp c.morseNorm_y₀_lt (t := s - c.transitTime)
    (by linarith)
  refine ⟨l, hl0, hl1, ?_⟩
  rw [c.chart_y₀, flow_flow, add_sub_cancel] at hl
  exact hl

theorem flow_z₀_ray {s : ℝ} (hs₁ : c.transitTime ≤ s) (hs₂ : s < c.transitTime + (c.ε - c.e.r₀ ^ 2 / 2)) :
    c.D.flow s c.z₀ =
      c.e.χ ((Real.sqrt (2 * c.ε - 2 * (s - c.transitTime)) / Real.sqrt (2 * c.ε)) • c.y₀) := by
  obtain ⟨l, hl0, hl1, hl⟩ := c.flow_z₀_ray_general hs₁
  have hf1 : f (c.D.flow s c.z₀) = f q - c.ε - s :=
    c.f_flow_z₀' (c.transitTime_pos.le.trans hs₁) hs₂
  have hnorm : morseNorm n (l • c.y₀) ≤ c.e.R := by
    rw [ModelField.morseNorm_smul, abs_of_pos hl0]
    have := c.morseNorm_y₀_lt.le.trans (c.D.hrm p c.hp).2
    have := ModelField.morseNorm_nonneg c.y₀
    nlinarith
  have hf2 := c.f_chart_p hnorm
  rw [← hl, hf1, ModelField.morseNorm_smul, abs_of_pos hl0, mul_pow, c.morseNorm_y₀_sq] at hf2
  have hsq : l ^ 2 = (2 * c.ε - 2 * (s - c.transitTime)) / (2 * c.ε) := by
    have hε := c.hε
    have hT : c.transitTime = f q - f p - 2 * c.ε := rfl
    rw [hT]
    field_simp
    linarith
  have hl' : l = Real.sqrt (2 * c.ε - 2 * (s - c.transitTime)) / Real.sqrt (2 * c.ε) := by
    rw [← Real.sqrt_div (by nlinarith [c.hε, sq_nonneg l]), ← hsq, Real.sqrt_sq hl0.le]
  rw [hl, hl']

def ε₁ : ℝ := (c.e.r₀ ^ 2 / 2 + c.ε) / 2

def ε₂ : ℝ := (c.d.r₀ ^ 2 / 2 + c.ε) / 2

def c₁ : ℝ := f p + c.ε₁

def c₂ : ℝ := f q - c.ε₂

def η : ℝ := min (c.ε₁ - c.e.r₀ ^ 2 / 2) (c.ε₂ - c.d.r₀ ^ 2 / 2) / 2

def ρa : ℝ := (2 * c.e.r₀ + Real.sqrt (2 * c.ε₁)) / 3

def ρb : ℝ := (c.e.r₀ + 2 * Real.sqrt (2 * c.ε₁)) / 3

def ua : ℝ := (2 * c.d.r₀ + Real.sqrt (2 * c.ε₂)) / 3

def ub : ℝ := (c.d.r₀ + 2 * Real.sqrt (2 * c.ε₂)) / 3

def m : ℝ := 2 / c.e.r₀ + 2 / c.d.r₀ + 1

theorem r₀p_sq_half_lt_ε₁ : c.e.r₀ ^ 2 / 2 < c.ε₁ := by
  unfold ε₁; linarith [c.hr₀p]

theorem ε₁_lt_ε : c.ε₁ < c.ε := by
  unfold ε₁; linarith [c.hr₀p]

theorem ε₁_pos : 0 < c.ε₁ :=
  lt_of_le_of_lt (by positivity) c.r₀p_sq_half_lt_ε₁

theorem r₀q_sq_half_lt_ε₂ : c.d.r₀ ^ 2 / 2 < c.ε₂ := by
  unfold ε₂; linarith [c.hr₀q]

theorem ε₂_lt_ε : c.ε₂ < c.ε := by
  unfold ε₂; linarith [c.hr₀q]

theorem ε₂_pos : 0 < c.ε₂ :=
  lt_of_le_of_lt (by positivity) c.r₀q_sq_half_lt_ε₂

theorem c₁_lt_c₂ : c.c₁ < c.c₂ := by
  unfold c₁ c₂; linarith [c.ε₁_lt_ε, c.ε₂_lt_ε, c.hlt]

theorem η_pos : 0 < c.η := by
  unfold η
  have := c.r₀p_sq_half_lt_ε₁
  have := c.r₀q_sq_half_lt_ε₂
  exact half_pos (lt_min (by linarith) (by linarith))

theorem η_lt_left : c.η < c.ε₁ - c.e.r₀ ^ 2 / 2 := by
  unfold η
  have := c.r₀p_sq_half_lt_ε₁
  have := c.r₀q_sq_half_lt_ε₂
  have h := min_le_left (c.ε₁ - c.e.r₀ ^ 2 / 2) (c.ε₂ - c.d.r₀ ^ 2 / 2)
  have h' := lt_min (by linarith : 0 < c.ε₁ - c.e.r₀ ^ 2 / 2)
    (by linarith : 0 < c.ε₂ - c.d.r₀ ^ 2 / 2)
  linarith

theorem η_lt_right : c.η < c.ε₂ - c.d.r₀ ^ 2 / 2 := by
  unfold η
  have := c.r₀p_sq_half_lt_ε₁
  have := c.r₀q_sq_half_lt_ε₂
  have h := min_le_right (c.ε₁ - c.e.r₀ ^ 2 / 2) (c.ε₂ - c.d.r₀ ^ 2 / 2)
  have h' := lt_min (by linarith : 0 < c.ε₁ - c.e.r₀ ^ 2 / 2)
    (by linarith : 0 < c.ε₂ - c.d.r₀ ^ 2 / 2)
  linarith

theorem f_p_add_lt_c₁_sub_η : f p + c.e.r₀ ^ 2 / 2 < c.c₁ - c.η := by
  unfold c₁; linarith [c.η_lt_left]

theorem c₂_add_η_lt_f_q_sub : c.c₂ + c.η < f q - c.d.r₀ ^ 2 / 2 := by
  unfold c₂; linarith [c.η_lt_right]

theorem a'_lt_c₁_sub_η : a' < c.c₁ - c.η := by
  have := c.f_p_add_lt_c₁_sub_η
  have := c.f_p_mem.1
  nlinarith [sq_nonneg c.e.r₀]

theorem c₂_add_η_lt_b' : c.c₂ + c.η < b' := by
  have := c.c₂_add_η_lt_f_q_sub
  have := c.f_q_mem.2
  nlinarith [sq_nonneg c.d.r₀]

theorem c₁_sub_η_lt_c₂_add_η : c.c₁ - c.η < c.c₂ + c.η := by
  linarith [c.c₁_lt_c₂, c.η_pos]

theorem levels_avoid_smallBall {y : M} (hy : f y ∈ Icc (c.c₁ - c.η) (c.c₂ + c.η)) :
    ∀ p' hp', y ∉ c.D.smallBall p' hp' :=
  c.avoid_smallBall ⟨c.f_p_add_lt_c₁_sub_η.trans_le hy.1, hy.2.trans_lt c.c₂_add_η_lt_f_q_sub⟩

theorem levels_avoid_closedSmallBall {y : M} (hy : f y ∈ Icc (c.c₁ - c.η) (c.c₂ + c.η)) :
    ∀ p' hp', y ∉ c.D.closedSmallBall p' hp' := by
  intro p' hp' hmem
  have h := abs_f_sub_le_of_mem_closedSmallBall hmem
  have h1 := c.f_p_add_lt_c₁_sub_η
  have h2 := c.c₂_add_η_lt_f_q_sub
  rcases mem_pair_iff.1 hp' with rfl | rfl
  · rw [abs_le] at h
    linarith [hy.1, h.2]
  · rw [abs_le] at h
    linarith [hy.2, h.1]

theorem tube_subset_regularFlowDomain : {x | f x ∈ Icc (c.c₁ - c.η) (c.c₂ + c.η)} ⊆ c.D.regularFlowDomain c.c₂ := by
  intro x hx
  have hx' : f x ∈ Icc (c.c₁ - c.η) (c.c₂ + c.η) := hx
  refine ⟨⟨c.a'_lt_c₁_sub_η.trans_le hx'.1, hx'.2.trans_lt c.c₂_add_η_lt_b'⟩, fun s hs p' hp' => ?_⟩
  apply c.levels_avoid_closedSmallBall
  have hmem := f_flow_mem_uIcc c.hfs (D := c.D) x s
  have hη := c.η_pos
  rw [mem_uIcc] at hmem hs
  have hc := c.c₁_lt_c₂
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hs with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    constructor <;> linarith [hx'.1, hx'.2]

theorem r₀p_lt_sqrt : c.e.r₀ < Real.sqrt (2 * c.ε₁) := by
  rw [Real.lt_sqrt c.e.hr₀.le]; linarith [c.r₀p_sq_half_lt_ε₁]

theorem r₀q_lt_sqrt : c.d.r₀ < Real.sqrt (2 * c.ε₂) := by
  rw [Real.lt_sqrt c.d.hr₀.le]; linarith [c.r₀q_sq_half_lt_ε₂]

theorem sqrt_two_ε₁_lt : Real.sqrt (2 * c.ε₁) < Real.sqrt (2 * c.ε) :=
  Real.sqrt_lt_sqrt (by linarith [c.ε₁_pos]) (by linarith [c.ε₁_lt_ε])

theorem sqrt_two_ε₂_lt : Real.sqrt (2 * c.ε₂) < Real.sqrt (2 * c.ε) :=
  Real.sqrt_lt_sqrt (by linarith [c.ε₂_pos]) (by linarith [c.ε₂_lt_ε])

theorem r₀p_lt_ρa : c.e.r₀ < c.ρa := by
  unfold ρa; linarith [c.r₀p_lt_sqrt]

theorem ρa_lt_ρb : c.ρa < c.ρb := by
  unfold ρa ρb; linarith [c.r₀p_lt_sqrt]

theorem ρb_lt_sqrt : c.ρb < Real.sqrt (2 * c.ε₁) := by
  unfold ρb; linarith [c.r₀p_lt_sqrt]

theorem ρb_lt_rm : c.ρb < c.D.rm p c.hp / 2 := by
  linarith [c.ρb_lt_sqrt, c.sqrt_two_ε₁_lt, c.sqrt_two_ε_lt_rmp]

theorem ρa_pos : 0 < c.ρa := c.e.hr₀.trans c.r₀p_lt_ρa

theorem r₀q_lt_ua : c.d.r₀ < c.ua := by
  unfold ua; linarith [c.r₀q_lt_sqrt]

theorem ua_lt_ub : c.ua < c.ub := by
  unfold ua ub; linarith [c.r₀q_lt_sqrt]

theorem ub_lt_sqrt : c.ub < Real.sqrt (2 * c.ε₂) := by
  unfold ub; linarith [c.r₀q_lt_sqrt]

theorem ub_lt_rm : c.ub < c.D.rm q c.hq / 2 := by
  linarith [c.ub_lt_sqrt, c.sqrt_two_ε₂_lt, c.sqrt_two_ε_lt_rmq]

theorem ua_pos : 0 < c.ua := c.d.hr₀.trans c.r₀q_lt_ua

theorem two_div_r₀p_lt_m : 2 / c.e.r₀ < c.m := by
  unfold m
  have := c.d.hr₀
  have : 0 < 2 / c.d.r₀ := by positivity
  linarith

theorem two_div_r₀q_lt_m : 2 / c.d.r₀ < c.m := by
  unfold m
  have := c.e.hr₀
  have : 0 < 2 / c.e.r₀ := by positivity
  linarith

theorem m_pos : 0 < c.m := by
  have := c.two_div_r₀p_lt_m
  have := c.e.hr₀
  have : 0 < 2 / c.e.r₀ := by positivity
  linarith

theorem theta_mul_lt_m_p {y : Fin n → ℝ} (hy : c.e.r₀ / 2 ≤ morseNorm n y) :
    ModelField.theta c.e.r₀ y * morseNorm n y < c.m := by
  rw [ModelField.theta_eq c.e.hr₀ hy]
  have hr := c.e.hr₀
  have hpos : 0 < morseNorm n y := by linarith
  have h1 : (morseNorm n y ^ 2)⁻¹ * morseNorm n y = 1 / morseNorm n y := by
    field_simp
  rw [h1]
  calc 1 / morseNorm n y ≤ 2 / c.e.r₀ := by
        rw [div_le_div_iff₀ hpos hr]; linarith
    _ < c.m := c.two_div_r₀p_lt_m

theorem theta_mul_lt_m_q {y : Fin n → ℝ} (hy : c.d.r₀ / 2 ≤ morseNorm n y) :
    ModelField.theta c.d.r₀ y * morseNorm n y < c.m := by
  rw [ModelField.theta_eq c.d.hr₀ hy]
  have hr := c.d.hr₀
  have hpos : 0 < morseNorm n y := by linarith
  have h1 : (morseNorm n y ^ 2)⁻¹ * morseNorm n y = 1 / morseNorm n y := by
    field_simp
  rw [h1]
  calc 1 / morseNorm n y ≤ 2 / c.d.r₀ := by
        rw [div_le_div_iff₀ hpos hr]; linarith
    _ < c.m := c.two_div_r₀q_lt_m

theorem exists_η₀ : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ p' hp',
    ∀ x ∈ (c.D.chart p' hp').χ '' {y | morseNorm n y ≤ (c.D.chart p' hp').R},
      a' + η₀ < f x ∧ f x < b' - η₀ := by
  have hfc := c.hfs.continuous
  set Kp := c.e.χ '' {y | morseNorm n y ≤ c.e.R} with hKp
  set Kq := c.d.χ '' {y | morseNorm n y ≤ c.d.R} with hKq
  have hKpc : IsCompact Kp := c.e.isCompact_image_le c.e.hRR'
  have hKqc : IsCompact Kq := c.d.isCompact_image_le c.d.hRR'
  have hKp' : Kp ⊆ f ⁻¹' Ioo a' b' :=
    (image_mono (c.e.le_subset_ball c.e.hRR')).trans (c.D.inStrip p c.hp)
  have hKq' : Kq ⊆ f ⁻¹' Ioo a' b' :=
    (image_mono (c.d.le_subset_ball c.d.hRR')).trans (c.D.inStrip q c.hq)
  set S := f '' Kp ∪ f '' Kq with hS
  have hSc : IsCompact S := (hKpc.image hfc).union (hKqc.image hfc)
  have hSsub : S ⊆ Ioo a' b' := by
    rintro z (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact hKp' hx
    · exact hKq' hx
  obtain ⟨δ, hδ, hδS⟩ := hSc.exists_cthickening_subset_open isOpen_Ioo hSsub
  refine ⟨δ, hδ, fun p' hp' x hx => ?_⟩
  have hxS : f x ∈ S := by
    rcases mem_pair_iff.1 hp' with rfl | rfl
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  have h1 : f x - δ ∈ Metric.cthickening δ S :=
    Metric.mem_cthickening_of_dist_le _ _ δ S hxS
      (by rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hδ])
  have h2 : f x + δ ∈ Metric.cthickening δ S :=
    Metric.mem_cthickening_of_dist_le _ _ δ S hxS
      (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ])
  have h1' := hδS h1
  have h2' := hδS h2
  exact ⟨by linarith [h1'.1], by linarith [h2'.2]⟩

def η₀ : ℝ := c.exists_η₀.choose

theorem η₀_pos : 0 < c.η₀ := c.exists_η₀.choose_spec.1

theorem η₀_spec : ∀ p' hp',
    ∀ x ∈ (c.D.chart p' hp').χ '' {y | morseNorm n y ≤ (c.D.chart p' hp').R},
      a' + c.η₀ < f x ∧ f x < b' - c.η₀ :=
  c.exists_η₀.choose_spec.2

theorem a'_add_η₀_lt_f_p : a' + c.η₀ < f p := by
  have := (c.η₀_spec p c.hp p ⟨0, by simp [morseNorm_zero, c.e.R_pos.le], c.e.hχ0⟩).1
  exact this

theorem f_q_add_η₀_lt_b' : f q + c.η₀ < b' := by
  have := (c.η₀_spec q c.hq q ⟨0, by simp [morseNorm_zero, c.d.R_pos.le], c.d.hχ0⟩).2
  linarith

end IndexZeroCancellingPair

end GradientLikeStrip

end

end DifferentialGeometry.Topology
