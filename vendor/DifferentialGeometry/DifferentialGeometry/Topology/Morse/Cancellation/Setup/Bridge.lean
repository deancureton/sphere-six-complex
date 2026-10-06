module

public import DifferentialGeometry.Topology.Morse.Strip.Terminal
public import DifferentialGeometry.Topology.Morse.Rearrangement.EqualIndexPosition
public import DifferentialGeometry.Topology.Morse.Strip.StripConnected
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm
  morseNorm_piNorm_le negPart posPart morseNorm_sq_eq_negPart_add_posPart morseNormalForm_split
  recombine recombine_decompose morseNorm_recombine_sq)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {a b : ℝ}

namespace MorseNormalChart

variable {q : M} (d : MorseNormalChart I f q)

def armPt (hk : d.k = 1) (ε : ℝ) (i : Fin 2) : Fin n → ℝ :=
  recombine d.hk (((if i = 0 then 1 else -1) * Real.sqrt (2 * ε)) •
    EuclideanSpace.single (⟨0, by omega⟩ : Fin d.k) 1) 0

theorem armPt_mem_leftModelSphere (hk : d.k = 1) {ε : ℝ} (hε : 0 ≤ ε) (i : Fin 2) :
    d.armPt hk ε i ∈ d.leftModelSphere ε := by
  refine ⟨ModelField.posPart_recombine d.hk _ _, ?_⟩
  rw [armPt, ModelField.negPart_recombine, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by linarith)]
  split_ifs <;> ring

theorem eq_armPt_of_mem_leftModelSphere (hk : d.k = 1) {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℝ}
    (hy : y ∈ d.leftModelSphere ε) : y = d.armPt hk ε 0 ∨ y = d.armPt hk ε 1 := by
  obtain ⟨hv, hu⟩ := hy
  set i₀ : Fin d.k := ⟨0, by omega⟩ with hi₀
  have hi : ∀ i : Fin d.k, i = i₀ := fun i => Fin.ext (by have := i.isLt; omega)
  have hdec := recombine_decompose d.hk y
  have hneg : negPart d.hk y = (negPart d.hk y i₀) • EuclideanSpace.single i₀ 1 := by
    ext j
    rw [hi j]
    simp
  rw [hneg, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, sq_abs,
    ← Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * ε), sq_eq_sq_iff_eq_or_eq_neg] at hu
  rcases hu with h | h
  · left
    rw [← hdec, hv, hneg, h, armPt]
    simp [hi₀]
  · right
    rw [← hdec, hv, hneg, h, armPt]
    simp [hi₀]

theorem armPt_zero_eq_sphereParam (hk : d.k = 1) (ε : ℝ) :
    d.armPt hk ε 0 = d.sphereParam ε (fun _ => 1) := by
  set i₀ : Fin d.k := ⟨0, by omega⟩ with hi₀
  have hi : ∀ i : Fin d.k, i = i₀ := fun i => Fin.ext (by have := i.isLt; omega)
  have htoE : d.toE (fun _ => 1) = EuclideanSpace.single i₀ 1 := by
    ext j
    rw [hi j]
    simp [toE]
  rw [sphereParam, htoE, PiLp.norm_single, norm_one, div_one, armPt]
  simp [hi₀]

theorem armPt_one_eq_sphereParam (hk : d.k = 1) (ε : ℝ) :
    d.armPt hk ε 1 = d.sphereParam ε (-fun _ => 1) := by
  set i₀ : Fin d.k := ⟨0, by omega⟩ with hi₀
  have hi : ∀ i : Fin d.k, i = i₀ := fun i => Fin.ext (by have := i.isLt; omega)
  have htoE : d.toE (-fun _ => 1) = -EuclideanSpace.single i₀ 1 := by
    ext j
    rw [hi j]
    simp [toE]
  rw [sphereParam, htoE, norm_neg, PiLp.norm_single, norm_one, div_one, armPt, smul_neg]
  simp [hi₀]

theorem armPt_eq_ite (hk : d.k = 1) (ε : ℝ) (i : Fin 2) :
    d.armPt hk ε i = fun j : Fin n =>
      if (j : ℕ) = 0 then (if i = 0 then 1 else -1) * Real.sqrt (2 * ε) else 0 := by
  funext j
  unfold armPt recombine
  by_cases hj : (j : ℕ) < d.k
  · rw [dite_eq_left hj, ite_eq_left (by omega : (j : ℕ) = 0)]
    have hj0 : (⟨(j : ℕ), hj⟩ : Fin d.k) = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [hj0]
    split_ifs <;> simp
  · rw [dite_eq_right hj, ite_eq_right (by omega : ¬ (j : ℕ) = 0)]
    rfl

theorem armPt_congr {d' : MorseNormalChart I f q} (hk : d.k = 1) (hk' : d'.k = 1) (ε : ℝ)
    (i : Fin 2) : d.armPt hk ε i = d'.armPt hk' ε i := by
  rw [armPt_eq_ite, armPt_eq_ite]

theorem isPreconnected_leftModelSphere (hk : 2 ≤ d.k) {ε : ℝ} (hε : 0 < ε) :
    IsPreconnected (d.leftModelSphere ε) := by
  have himage : d.leftModelSphere ε = d.sphereParam ε '' {w | w ≠ 0} := by
    ext y
    constructor
    · intro hy
      obtain ⟨hne, heq⟩ := d.sphereParam_of_mem hε hy
      exact ⟨_, hne, heq⟩
    · rintro ⟨w, hw, rfl⟩
      exact d.sphereParam_mem_leftModelSphere hε.le hw
  rw [himage]
  have hrank : 1 < Module.rank ℝ (Fin d.k → ℝ) := by
    rw [rank_fin_fun]
    exact_mod_cast (by omega : 1 < d.k)
  have hconn : IsPreconnected {w : Fin d.k → ℝ | w ≠ 0} := by
    rw [← Set.compl_singleton_eq]
    exact (isConnected_compl_singleton_of_one_lt_rank hrank 0).isPreconnected
  exact hconn.image _ fun w hw => (d.contDiffAt_sphereParam ε hw).continuousAt.continuousWithinAt

theorem leftModelSphere_nonempty (hk : 1 ≤ d.k) {ε : ℝ} (hε : 0 ≤ ε) :
    (d.leftModelSphere ε).Nonempty := by
  have hne : (fun _ : Fin d.k => (1 : ℝ)) ≠ 0 := fun h => by
    have := congrFun h ⟨0, hk⟩
    simp at this
  exact ⟨_, d.sphereParam_mem_leftModelSphere hε hne⟩

end MorseNormalChart

variable [IsManifold I ∞ M] {crit : Finset M}

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless] {D : GradientLikeStrip I f a b crit}

def goodPair (D : GradientLikeStrip I f a b crit) (ε : ℝ) (p q : M) (hp : p ∈ crit)
    (hq : q ∈ crit) : Prop :=
  (D.chart p hp).k = 0 ∧ ∃ hk : (D.chart q hq).k = 1, ∃ i : Fin 2,
    (D.chart q hq).χ ((D.chart q hq).armPt hk ε i) ∈ D.basin p hp ∧
    (D.chart q hq).χ ((D.chart q hq).armPt hk ε (i + 1)) ∉ D.basin p hp

def armsAgree (D : GradientLikeStrip I f a b crit) (ε : ℝ) : Prop :=
  ∀ q hq (hk : (D.chart q hq).k = 1),
    (∀ i, (D.chart q hq).χ ((D.chart q hq).armPt hk ε i) ∈ D.bottom) ∨
    ∃ p hp, (D.chart p hp).k = 0 ∧
      ∀ i, (D.chart q hq).χ ((D.chart q hq).armPt hk ε i) ∈ D.basin p hp

theorem f_le_of_mem_captured (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {r : M} {hr : r ∈ crit} {x : M}
    (hx : x ∈ D.captured r hr) (t : ℝ) : f r ≤ f (D.flow t x) := by
  obtain ⟨T, z, ⟨hz1, hz2⟩, hzT⟩ := hx
  have hfz : f r ≤ f (D.flow T x) := by
    rw [← hzT, (D.chart r hr).hnorm z (hz1.le.trans (D.hrm r hr).2), morseNormalForm_split, hz2,
      norm_zero]
    nlinarith [sq_nonneg ‖posPart (D.chart r hr).hk z‖]
  rcases le_or_gt t T with h | h
  · exact hfz.trans (f_flow_antitone hf x h)
  · have := f_p_le_f_flow_of_negPart_eq_zero (D := D) hr hz1 hz2 (t := t - T) (by linarith)
    rwa [hzT, flow_flow, add_sub_cancel] at this

theorem notMem_captured_of_f_flow_lt (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {r : M} {hr : r ∈ crit}
    {x : M} {t : ℝ} (h : f (D.flow t x) < f r) : x ∉ D.captured r hr :=
  fun hx => absurd (f_le_of_mem_captured hf hx t) (not_le.2 h)

theorem exists_f_flow_lt_of_mem_captured {r : M} {hr : r ∈ crit} {x : M}
    (hx : x ∈ D.captured r hr) {η : ℝ} (hη : 0 < η) : ∃ T, f (D.flow T x) < f r + η := by
  have hρ : 0 < min (Real.sqrt η) (D.rm r hr) := lt_min (Real.sqrt_pos.2 hη) (D.rm_pos r hr)
  obtain ⟨T, hT⟩ := captured_eventually_small hx hρ
  obtain ⟨z, ⟨hz1, hz2⟩, hzT⟩ := hT T le_rfl
  refine ⟨T, ?_⟩
  have hzrm : morseNorm n z < D.rm r hr := hz1.trans_le (min_le_right _ _)
  have hzη : morseNorm n z < Real.sqrt η := hz1.trans_le (min_le_left _ _)
  have hzsq : morseNorm n z ^ 2 < η := (Real.lt_sqrt (ModelField.morseNorm_nonneg z)).1 hzη
  have hsq := morseNorm_sq_eq_negPart_add_posPart (D.chart r hr).hk z
  rw [hz2, norm_zero] at hsq
  rw [← hzT, (D.chart r hr).hnorm z (hzrm.le.trans (D.hrm r hr).2), morseNormalForm_split, hz2,
    norm_zero]
  nlinarith

theorem disjoint_bottom_captured (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (r : M) (hr : r ∈ crit) :
    Disjoint D.bottom (D.captured r hr) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, -, hlt⟩ hx
  have h1 := f_le_of_mem_captured hf hx t
  have h2 := (D.f_mem_Ioo r hr).1
  linarith

theorem disjoint_basin_captured {p r : M} {hp : p ∈ crit} {hr : r ∈ crit}
    (hk : (D.chart p hp).k = 0) (hpr : p ≠ r) : Disjoint (D.basin p hp) (D.captured r hr) := by
  rw [Set.disjoint_left]
  rintro x hxp hxr
  obtain ⟨s, hs, hmem⟩ := hxp
  obtain ⟨T, hT⟩ := mem_captured_iff_eventually.1 hxr
  have h1 := flow_mem_modelBall_of_index_zero hk hmem (t := max s T - s)
    (by linarith [le_max_left s T])
  rw [flow_flow, add_sub_cancel] at h1
  have h2 := hT (max s T) (le_max_right _ _)
  exact Set.disjoint_left.1 (D.disjoint p hp r hr hpr) (D.modelBall_subset_image_ball p hp h1)
    (D.modelBall_subset_image_ball r hr (image_mono (fun z hz => hz.1) h2))

omit [T2Space M] [I.Boundaryless] in
theorem f_chart_of_mem_leftModelSphere' {r : M} (hr : r ∈ crit) {ε : ℝ}
    (hrm : 8 * ε < D.rm r hr ^ 2) {y : Fin n → ℝ} (hy : y ∈ (D.chart r hr).leftModelSphere ε) :
    f ((D.chart r hr).χ y) = f r - ε := by
  have hrm0 := D.rm_pos r hr
  have hεR : 2 * ε ≤ (D.chart r hr).R ^ 2 := by
    have := pow_le_pow_left₀ hrm0.le (D.hrm r hr).2 2
    linarith [pow_pos hrm0 2]
  exact (D.chart r hr).f_chart_of_mem_leftModelSphere hεR hy

omit [T2Space M] [I.Boundaryless] in
theorem morseNorm_lt_rm_of_mem_leftModelSphere {r : M} (hr : r ∈ crit) {ε : ℝ}
    (hrm : 8 * ε < D.rm r hr ^ 2) {y : Fin n → ℝ} (hy : y ∈ (D.chart r hr).leftModelSphere ε) :
    morseNorm n y < D.rm r hr := by
  have hrm0 := D.rm_pos r hr
  have hysq := (D.chart r hr).morseNorm_sq_of_mem_leftModelSphere hy
  apply lt_of_pow_lt_pow_left₀ 2 hrm0.le
  linarith [pow_pos hrm0 2]

theorem leftSphere_terminal (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) {r : M} (hr : r ∈ crit)
    {w : M} (hw : w ∈ (D.chart r hr).χ '' (D.chart r hr).leftModelSphere ε) :
    w ∈ D.bottom ∨ ∃ r' hr', r' ≠ r ∧ f r' < f r ∧ w ∈ D.captured r' hr' := by
  obtain ⟨y, hy, rfl⟩ := hw
  set d := D.chart r hr with hd
  have hfx : f (d.χ y) = f r - ε := f_chart_of_mem_leftModelSphere' hr (hεr r hr).2 hy
  have hyrm : morseNorm n y < D.rm r hr :=
    morseNorm_lt_rm_of_mem_leftModelSphere hr (hεr r hr).2 hy
  have hx : f (d.χ y) ∈ Icc a b := by
    have := D.modelBall_subset_strip r hr ⟨y, hyrm, rfl⟩
    exact ⟨this.1.le, this.2.le⟩
  rcases D.trichotomy hf hε hεr hx with hb | ⟨r', hr', T, hT⟩
  · exact Or.inl hb
  obtain ⟨z, ⟨hz1, hz2⟩, hzT⟩ := hT
  have hrR : morseNorm n z ≤ (D.chart r' hr').R := hz1.le.trans (D.hrm r' hr').2
  have hfz : f r' ≤ f ((D.chart r' hr').χ z) := by
    rw [(D.chart r' hr').hnorm z hrR, morseNormalForm_split, hz2, norm_zero]
    nlinarith [sq_nonneg ‖posPart (D.chart r' hr').hk z‖]
  rcases lt_or_ge T 0 with hT0 | hT0
  · exfalso
    by_cases hrq : r' = r
    · subst hrq
      have := f_p_le_f_flow_of_negPart_eq_zero (D := D) hr' hz1 hz2 (t := -T) (by linarith)
      rw [hzT, flow_neg_flow] at this
      linarith
    · have h1 := flow_mem_of_posPart_eq_zero (D := D) hr hyrm hy.1 hT0.le
      have h2 : D.flow T (d.χ y) ∈ d.χ '' Metric.ball 0 d.R' :=
        image_mono (fun w hw => d.mem_ball_of_le (hw.1.trans (hyrm.le.trans (D.hrm r hr).2))) h1
      have h3 : D.flow T (d.χ y) ∈ (D.chart r' hr').χ '' Metric.ball 0 (D.chart r' hr').R' := by
        rw [← hzT]
        exact ⟨z, (D.chart r' hr').mem_ball_of_le hrR, rfl⟩
      exact Set.disjoint_left.1 (D.disjoint r hr r' hr' (Ne.symm hrq)) h2 h3
  · right
    have hfr : f r' < f r := by
      have := f_flow_le (D := D) hf (d.χ y) hT0
      rw [hzT] at hfz
      linarith
    exact ⟨r', hr', fun h => by rw [h] at hfr; exact lt_irrefl _ hfr, hfr, T, z, ⟨hz1, hz2⟩, hzT⟩

structure IsClassFun (D : GradientLikeStrip I f a b crit) (cls : M → Option M) (c : ℝ) :
    Prop where
  bottom_eq : ∀ x ∈ D.bottom, cls x = none
  basin_eq : ∀ p hp, (D.chart p hp).k = 0 → ∀ x ∈ D.basin p hp, cls x = some p
  flow_eq : ∀ x t, cls (D.flow t x) = cls x
  locallyConstant : ∀ x, (x ∈ D.bottom ∨ (∃ p hp, (D.chart p hp).k = 0 ∧ x ∈ D.basin p hp) ∨
    ∃ r hr, 1 ≤ (D.chart r hr).k ∧ f r < c ∧ x ∈ D.captured r hr) →
    ∀ᶠ y in 𝓝 x, cls y = cls x

theorem exists_isClassFun_base (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hc : ∀ r hr, 1 ≤ (D.chart r hr).k → ¬ f r < c) : ∃ cls, IsClassFun D cls c := by
  classical
  set cls : M → Option M := fun x =>
    if x ∈ D.bottom then none
    else if h : ∃ p, ∃ hp : p ∈ crit, (D.chart p hp).k = 0 ∧ x ∈ D.basin p hp then some h.choose
    else none with hcls
  have hbot : ∀ x ∈ D.bottom, cls x = none := fun x hx => by
    simp only [hcls, ite_eq_left hx]
  have hbas : ∀ p hp, (D.chart p hp).k = 0 → ∀ x ∈ D.basin p hp, cls x = some p := by
    intro p hp hk x hx
    have hxb : x ∉ D.bottom := fun h => Set.disjoint_left.1 (disjoint_bottom_basin hf hk) h hx
    have hex : ∃ p, ∃ hp : p ∈ crit, (D.chart p hp).k = 0 ∧ x ∈ D.basin p hp := ⟨p, hp, hk, hx⟩
    simp only [hcls, ite_eq_right hxb, dite_eq_left hex]
    obtain ⟨hp', hk', hx'⟩ := hex.choose_spec
    congr 1
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_basin_basin hk' hk hne) hx' hx
  have hnone : ∀ x, x ∉ D.bottom → (∀ p hp, (D.chart p hp).k = 0 → x ∉ D.basin p hp) →
      cls x = none := by
    intro x hxb hxp
    have hex : ¬ ∃ p, ∃ hp : p ∈ crit, (D.chart p hp).k = 0 ∧ x ∈ D.basin p hp :=
      fun ⟨p, hp, hk, hx⟩ => hxp p hp hk hx
    simp only [hcls, ite_eq_right hxb, dite_eq_right hex]
  refine ⟨cls, hbot, hbas, ?_, ?_⟩
  · intro x t
    by_cases hxb : x ∈ D.bottom
    · rw [hbot _ hxb, hbot _ ((flow_mem_bottom_iff hf t).2 hxb)]
    · by_cases hxp : ∃ p, ∃ hp : p ∈ crit, (D.chart p hp).k = 0 ∧ x ∈ D.basin p hp
      · obtain ⟨p, hp, hk, hx⟩ := hxp
        rw [hbas p hp hk x hx, hbas p hp hk _ ((flow_mem_basin_iff hk t).2 hx)]
      · push Not at hxp
        rw [hnone x hxb hxp, hnone (D.flow t x) (fun h => hxb ((flow_mem_bottom_iff hf t).1 h))
          (fun p hp hk h => hxp p hp hk ((flow_mem_basin_iff hk t).1 h))]
  · intro x hx
    rcases hx with hb | ⟨p, hp, hk, hbas'⟩ | ⟨r, hr, hk, hlt, -⟩
    · filter_upwards [(D.isOpen_bottom hf.continuous).eventually_mem hb] with y hy
      rw [hbot y hy, hbot x hb]
    · filter_upwards [(D.isOpen_basin p hp).eventually_mem hbas'] with y hy
      rw [hbas p hp hk y hy, hbas p hp hk x hbas']
    · exact absurd hlt (hc r hr hk)

theorem IsClassFun.extend (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2) {cls : M → Option M}
    {r : M} {hr : r ∈ crit} (hk : 1 ≤ (D.chart r hr).k) (hcls : IsClassFun D cls (f r))
    {v : Option M} (hv : ∀ w ∈ (D.chart r hr).χ '' (D.chart r hr).leftModelSphere ε, cls w = v)
    {c : ℝ} (hc : ∀ r' hr', 1 ≤ (D.chart r' hr').k → f r' < c → f r' < f r ∨ r' = r) :
    ∃ cls', IsClassFun D cls' c := by
  classical
  have hkr : (D.chart r hr).k ≠ 0 := by omega
  have hpr : ∀ p (hp : p ∈ crit), (D.chart p hp).k = 0 → p ≠ r := fun p hp hkp h =>
    hkr (by subst h; exact hkp)
  set d := D.chart r hr with hd
  set cls' : M → Option M := fun x => if x ∈ D.captured r hr then v else cls x with hcls'
  have hmem : ∀ x ∈ D.captured r hr, cls' x = v := fun x hx => by
    simp only [hcls', ite_eq_left hx]
  have hnot : ∀ x ∉ D.captured r hr, cls' x = cls x := fun x hx => by
    simp only [hcls', ite_eq_right hx]
  have hfr : f r < b := (D.f_mem_Ioo r hr).2
  have hflow : ∀ x t, cls' (D.flow t x) = cls' x := by
    intro x t
    by_cases hx : x ∈ D.captured r hr
    · rw [hmem _ hx, hmem _ ((flow_mem_captured_iff t).2 hx)]
    · rw [hnot _ hx, hnot _ (fun h => hx ((flow_mem_captured_iff t).1 h)), hcls.flow_eq]
  have hA : ∀ w ∈ d.χ '' d.leftModelSphere ε, ∀ᶠ y in 𝓝 w, cls' y = v := by
    intro w hw
    have hfw : f w < f r := by
      obtain ⟨y, hy, rfl⟩ := hw
      rw [f_chart_of_mem_leftModelSphere' hr (hεr r hr).2 hy]
      linarith
    have hloc : ∀ᶠ y in 𝓝 w, cls y = cls w := by
      apply hcls.locallyConstant
      rcases leftSphere_terminal hf hε hεr hr hw with hb | ⟨r', hr', -, hlt, hc'⟩
      · exact Or.inl hb
      · rcases Nat.eq_zero_or_pos (D.chart r' hr').k with hk0 | hk1
        · exact Or.inr (Or.inl ⟨r', hr', hk0, by rwa [← captured_index_zero_eq_basin hk0]⟩)
        · exact Or.inr (Or.inr ⟨r', hr', hk1, hlt, hc'⟩)
    have hlt : ∀ᶠ y in 𝓝 w, f y < f r := (hf.continuous.tendsto w).eventually (gt_mem_nhds hfw)
    filter_upwards [hloc, hlt] with y hy hy'
    have hy'' : y ∉ D.captured r hr :=
      notMem_captured_of_f_flow_lt hf (t := 0) (by rwa [flow_zero])
    rw [hnot _ hy'', hy, hv w hw]
  set U : Set M := {w | ∀ᶠ y in 𝓝 w, cls' y = v} with hU
  have hUopen : IsOpen U := isOpen_setOfPred_eventually_nhds
  have hUS : D.leftSphere r hr ε (f r - ε) ⊆ U := by
    rw [leftSphere_self_level]
    exact hA
  have hUv : ∀ w ∈ U, cls' w = v := fun w hw => hw.self_of_nhds
  obtain ⟨ρ, hρ, hρU⟩ := exists_uniform_exit hf r hr hε (hεr r hr).2 hUopen hUS
  set ρ' := min ρ (D.rm r hr) with hρ'def
  have hρ' : 0 < ρ' := lt_min hρ (D.rm_pos r hr)
  have hB : ∀ y, morseNorm n y < ρ' → cls' (d.χ y) = v := by
    intro y hy
    by_cases hu : negPart d.hk y = 0
    · exact hmem _ (mem_captured_of_mem_stable ⟨y, ⟨hy.trans_le (min_le_right _ _), hu⟩, rfl⟩)
    · obtain ⟨t, -, htU, -⟩ := hρU y (hy.trans_le (min_le_left _ _)) hu
      rw [← hflow _ t]
      exact hUv _ htU
  have hC : ∀ x ∈ D.captured r hr, ∀ᶠ y in 𝓝 x, cls' y = cls' x := by
    intro x hx
    rw [hmem _ hx]
    obtain ⟨T, hT⟩ := captured_eventually_small hx hρ'
    have hO : IsOpen (d.χ '' {y | morseNorm n y < ρ'}) :=
      d.isOpen_image_of_lt ((min_le_right _ _).trans (D.rm_lt_R' r hr).le)
    have hxT : D.flow T x ∈ d.χ '' {y | morseNorm n y < ρ'} :=
      image_mono (fun z hz => hz.1) (hT T le_rfl)
    have hev : ∀ᶠ y in 𝓝 x, D.flow T y ∈ d.χ '' {y | morseNorm n y < ρ'} :=
      ((D.continuous_flow T).tendsto x).eventually (hO.eventually_mem hxT)
    filter_upwards [hev] with y hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [← hflow y T, ← hzy]
    exact hB z hz
  have hbot' : ∀ x ∈ D.bottom, cls' x = none := fun x hx => by
    rw [hnot _ (Set.disjoint_left.1 (disjoint_bottom_captured hf r hr) hx), hcls.bottom_eq x hx]
  have hbas' : ∀ p hp, (D.chart p hp).k = 0 → ∀ x ∈ D.basin p hp, cls' x = some p := by
    intro p hp hkp x hx
    rw [hnot _ (Set.disjoint_left.1 (disjoint_basin_captured hkp (hpr p hp hkp)) hx),
      hcls.basin_eq p hp hkp x hx]
  refine ⟨cls', ⟨hbot', hbas', hflow, ?_⟩⟩
  intro x hx
  rcases hx with hb | ⟨p, hp, hkp, hbas⟩ | ⟨r', hr', hk', hlt', hc'⟩
  · filter_upwards [(D.isOpen_bottom hf.continuous).eventually_mem hb] with y hy
    rw [hbot' y hy, hbot' x hb]
  · filter_upwards [(D.isOpen_basin p hp).eventually_mem hbas] with y hy
    rw [hbas' p hp hkp y hy, hbas' p hp hkp x hbas]
  · rcases hc r' hr' hk' hlt' with hlt | rfl
    · have hloc := hcls.locallyConstant x (Or.inr (Or.inr ⟨r', hr', hk', hlt, hc'⟩))
      obtain ⟨T, hT⟩ := exists_f_flow_lt_of_mem_captured hc' (η := f r - f r') (by linarith)
      have hT' : f (D.flow T x) < f r := by linarith
      have hev : ∀ᶠ y in 𝓝 x, f (D.flow T y) < f r :=
        ((hf.continuous.comp (D.continuous_flow T)).tendsto x).eventually (gt_mem_nhds hT')
      filter_upwards [hloc, hev] with y hy hy'
      rw [hnot _ (notMem_captured_of_f_flow_lt hf hy'),
        hnot _ (notMem_captured_of_f_flow_lt hf hT'), hy]
    · exact hC x hc'

theorem IsClassFun.exists_const_leftSphere (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (harms : armsAgree D ε) {cls : M → Option M} {r : M} {hr : r ∈ crit}
    (hk : 1 ≤ (D.chart r hr).k) (hcls : IsClassFun D cls (f r)) :
    ∃ v, ∀ w ∈ (D.chart r hr).χ '' (D.chart r hr).leftModelSphere ε, cls w = v := by
  set d := D.chart r hr with hd
  have hloc : ∀ w ∈ d.χ '' d.leftModelSphere ε, ∀ᶠ y in 𝓝 w, cls y = cls w := by
    intro w hw
    apply hcls.locallyConstant
    rcases leftSphere_terminal hf hε hεr hr hw with hb | ⟨r', hr', -, hlt, hc'⟩
    · exact Or.inl hb
    · rcases Nat.eq_zero_or_pos (D.chart r' hr').k with hk0 | hk1
      · exact Or.inr (Or.inl ⟨r', hr', hk0, by rwa [← captured_index_zero_eq_basin hk0]⟩)
      · exact Or.inr (Or.inr ⟨r', hr', hk1, hlt, hc'⟩)
  rcases Nat.lt_or_ge d.k 2 with hk1 | hk2
  · have hk1' : d.k = 1 := by omega
    refine ⟨cls (d.χ (d.armPt hk1' ε 0)), fun w hw => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hw
    rcases d.eq_armPt_of_mem_leftModelSphere hk1' hε hy with rfl | rfl
    · rfl
    · rcases harms r hr hk1' with h | ⟨p, hp, hkp, h⟩
      · rw [hcls.bottom_eq _ (h 1), hcls.bottom_eq _ (h 0)]
      · rw [hcls.basin_eq p hp hkp _ (h 1), hcls.basin_eq p hp hkp _ (h 0)]
  · have hrm0 := D.rm_pos r hr
    have hεR : 2 * ε ≤ d.R ^ 2 := by
      have := pow_le_pow_left₀ hrm0.le (D.hrm r hr).2 2
      linarith [(hεr r hr).2, pow_pos hrm0 2]
    have hpre : IsPreconnected (d.χ '' d.leftModelSphere ε) := by
      refine (d.isPreconnected_leftModelSphere hk2 hε).image _ (d.χ.continuousOn.mono ?_)
      intro y hy
      exact d.hball (d.mem_ball_of_le (d.morseNorm_le_R_of_mem_leftModelSphere hεR hy))
    obtain ⟨y₀, hy₀⟩ := d.leftModelSphere_nonempty (by omega) hε.le
    exact ⟨cls (d.χ y₀), fun w hw =>
      eq_of_eventually_eq_of_isPreconnected hpre hloc hw ⟨y₀, hy₀, rfl⟩⟩

theorem exists_isClassFun (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (hinj : InjOn f (crit : Set M)) (harms : armsAgree D ε) (c : ℝ) :
    ∃ cls, IsClassFun D cls c := by
  classical
  suffices key : ∀ N : ℕ, ∀ c : ℝ,
      (crit.attach.filter fun r => 1 ≤ (D.chart r.1 r.2).k ∧ f r.1 < c).card = N →
        ∃ cls, IsClassFun D cls c from key _ c rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro c hN
  set S := crit.attach.filter fun r => 1 ≤ (D.chart r.1 r.2).k ∧ f r.1 < c with hS
  rcases S.eq_empty_or_nonempty with hemp | hne
  · refine exists_isClassFun_base hf fun r hr hk hlt => ?_
    have : (⟨r, hr⟩ : {r // r ∈ crit}) ∈ S :=
      Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hk, hlt⟩
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty _)
  · obtain ⟨r, hrS, hmax⟩ := S.exists_max_image (fun r => f r.1) hne
    obtain ⟨-, hk, hlt⟩ := Finset.mem_filter.1 hrS
    set S' := crit.attach.filter fun r' => 1 ≤ (D.chart r'.1 r'.2).k ∧ f r'.1 < f r.1 with hS'
    have hsub : S' ⊆ S := fun r' hr' => by
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hr'
      exact Finset.mem_filter.2 ⟨h1, h2, h3.trans hlt⟩
    have hss : S' ⊂ S := by
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨r, hrS, fun h => lt_irrefl _ (Finset.mem_filter.1 h).2.2⟩
    have hcard := Finset.card_lt_card hss
    rw [hN] at hcard
    obtain ⟨cls, hcls⟩ := ih _ hcard (f r.1) rfl
    obtain ⟨v, hv⟩ := hcls.exists_const_leftSphere hf hε hεr harms hk
    refine hcls.extend hf hε hεr hk hv fun r' hr' hk' hlt' => ?_
    have hmem : (⟨r', hr'⟩ : {r // r ∈ crit}) ∈ S :=
      Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hk', hlt'⟩
    rcases (hmax _ hmem).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr (hinj hr' r.2 h)

theorem exists_cls (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (hinj : InjOn f (crit : Set M)) (harms : armsAgree D ε) :
    ∃ cls : M → Option M, (∀ x ∈ D.bottom, cls x = none) ∧
      (∀ p hp, (D.chart p hp).k = 0 → ∀ x ∈ D.basin p hp, cls x = some p) ∧
      (∀ x t, cls (D.flow t x) = cls x) ∧
      ∀ x, f x ∈ Icc a b → ∀ᶠ y in 𝓝 x, cls y = cls x := by
  obtain ⟨cls, hcls⟩ := exists_isClassFun hf hε hεr hinj harms b
  refine ⟨cls, hcls.bottom_eq, hcls.basin_eq, hcls.flow_eq, fun x hx => ?_⟩
  apply hcls.locallyConstant
  rcases D.trichotomy hf hε hεr hx with hb | ⟨r, hr, hc⟩
  · exact Or.inl hb
  · rcases Nat.eq_zero_or_pos (D.chart r hr).k with hk0 | hk1
    · exact Or.inr (Or.inl ⟨r, hr, hk0, by rwa [← captured_index_zero_eq_basin hk0]⟩)
    · exact Or.inr (Or.inr ⟨r, hr, hk1, (D.f_mem_Ioo r hr).2, hc⟩)

theorem armsAgree_of_not_goodPair (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε r' : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (hr' : 0 < r') (hidx : ∀ p hp q hq, (D.chart p hp).k < (D.chart q hq).k → f p < f q)
    (harm : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
        D.flow t x ∉ (D.chart p hp).χ '' {y | morseNorm n y < r'})
    (hnb : ∀ p q hp hq, ¬ goodPair D ε p q hp hq) : armsAgree D ε := by
  intro q hq hk
  set d := D.chart q hq with hd
  have hmemS : ∀ i, d.χ (d.armPt hk ε i) ∈ D.leftSphere q hq ε (f q - ε) := fun i => by
    rw [leftSphere_self_level]
    exact ⟨_, d.armPt_mem_leftModelSphere hk hε.le i, rfl⟩
  have hqa : a ≤ f q - ε := by
    have := D.modelBall_subset_strip q hq ⟨_, morseNorm_lt_rm_of_mem_leftModelSphere hq
      (hεr q hq).2 (d.armPt_mem_leftModelSphere hk hε.le 0), rfl⟩
    rw [mem_preimage, f_chart_of_mem_leftModelSphere' hq (hεr q hq).2
      (d.armPt_mem_leftModelSphere hk hε.le 0)] at this
    exact this.1.le
  have hdir := leftSphere_direct hf D hε hεr hr' hidx harm hq hk hqa
  have hiff : ∀ p hp, (D.chart p hp).k = 0 → ∀ i, d.χ (d.armPt hk ε i) ∈ D.basin p hp →
      d.χ (d.armPt hk ε (i + 1)) ∈ D.basin p hp := by
    intro p hp hkp i hi
    by_contra h
    exact hnb p q hp hq ⟨hkp, hk, i, hi, h⟩
  have h11 : (1 : Fin 2) + 1 = 0 := by decide
  have h01 : (0 : Fin 2) + 1 = 1 := by decide
  rcases hdir _ (hmemS 0) with hb | ⟨p, hp, hkp, hbas⟩
  · left
    intro i
    fin_cases i
    · exact hb
    · rcases hdir _ (hmemS 1) with hb' | ⟨p, hp, hkp, hbas'⟩
      · exact hb'
      · exfalso
        have := hiff p hp hkp 1 hbas'
        rw [h11] at this
        exact Set.disjoint_left.1 (disjoint_bottom_basin hf hkp) hb this
  · right
    refine ⟨p, hp, hkp, fun i => ?_⟩
    fin_cases i
    · exact hbas
    · have := hiff p hp hkp 0 hbas
      rwa [h01] at this

omit [T2Space M] [I.Boundaryless] in
theorem k_lt_imp_f_lt_of_selfIndexing (D : GradientLikeStrip I f a b crit)
    (hsi : isSelfIndexing I f a b)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) :
    ∀ p hp q hq, (D.chart p hp).k < (D.chart q hq).k → f p < f q := fun p hp q hq h =>
  hsi p q ((hcrit p).1 hp).1 ((hcrit q).1 hq).1 ((hcrit p).1 hp).2 ((hcrit q).1 hq).2
    (by rw [(D.chart p hp).hkidx, (D.chart q hq).hkidx]; exact h)

theorem exists_bridge (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε r' : ℝ} (hε : 0 < ε)
    (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (hr' : 0 < r') (hidx : ∀ p hp q hq, (D.chart p hp).k < (D.chart q hq).k → f p < f q)
    (harm : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
        D.flow t x ∉ (D.chart p hp).χ '' {y | morseNorm n y < r'})
    (hinj : InjOn f (crit : Set M)) (hconn : ConnectedSpace (f ⁻¹' Icc a b))
    (ha : (f ⁻¹' {a}).Nonempty) {p₀ : M} (hp₀ : p₀ ∈ crit) (hk₀ : (D.chart p₀ hp₀).k = 0) :
    ∃ p q hp hq, goodPair D ε p q hp hq := by
  by_contra hnb
  push Not at hnb
  have harms := armsAgree_of_not_goodPair hf hε hεr hr' hidx harm hnb
  obtain ⟨cls, hbot, hbas, -, hloc⟩ := exists_cls hf hε hεr hinj harms
  have hconst := constant_of_locallyConstant hconn hloc
  have hab : a < b := (D.f_mem_Ioo p₀ hp₀).1.trans (D.f_mem_Ioo p₀ hp₀).2
  obtain ⟨x, hx, t, ht, hlt⟩ := D.exists_bottom_point hf hab ha
  have h1 : cls p₀ = some p₀ := hbas p₀ hp₀ hk₀ p₀ (crit_mem_basin p₀ hp₀)
  have h2 : cls x = none := hbot x ⟨t, ht, hlt⟩
  have := hconst p₀ x (Ioo_subset_Icc_self (D.f_mem_Ioo p₀ hp₀)) (Ioo_subset_Icc_self hx)
  rw [h1, h2] at this
  exact Option.some_ne_none _ this

end GradientLikeStrip

end

end DifferentialGeometry.Topology
