module

public import DifferentialGeometry.Topology.Morse.Rearrangement.Transversality
public import DifferentialGeometry.Topology.Morse.Strip.Terminal
public import Mathlib.Topology.Algebra.Module.Cardinality

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

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ}
  {crit : Finset M}

namespace ModelField

theorem exists_avoid_finite {l : ℕ} (hl : 1 ≤ l) {F : Set (EuclideanSpace ℝ (Fin l))}
    (hF : F.Finite) (z₀ : EuclideanSpace ℝ (Fin l)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z, ‖z - z₀‖ < ρ ∧ z ∉ F := by
  have : Nontrivial (EuclideanSpace ℝ (Fin l)) := by
    refine ⟨⟨EuclideanSpace.single ⟨0, hl⟩ 1, 0, fun h => ?_⟩⟩
    have := congrFun (congrArg (fun v : EuclideanSpace ℝ (Fin l) => (v : Fin l → ℝ)) h) ⟨0, hl⟩
    simp at this
  have hdense := Set.Countable.dense_compl ℝ hF.countable
  obtain ⟨z, hz, hzmem⟩ := hdense.exists_mem_open Metric.isOpen_ball ⟨z₀, Metric.mem_ball_self hρ⟩
  exact ⟨z, by simpa [dist_eq_norm] using hzmem, hz⟩

end ModelField

namespace MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {q : M} (e : MorseNormalChart I f q)

theorem toE_smul (t : ℝ) (w : Fin e.k → ℝ) : e.toE (t • w) = t • e.toE w :=
  (EuclideanSpace.equiv (Fin e.k) ℝ).symm.map_smul t w

theorem sphereParam_smul (ε : ℝ) {t : ℝ} (ht : 0 < t) {w : Fin e.k → ℝ} (hw : w ≠ 0) :
    e.sphereParam ε (t • w) = e.sphereParam ε w := by
  unfold sphereParam
  rw [toE_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht, smul_smul]
  congr 2
  have h : ‖e.toE w‖ ≠ 0 := norm_ne_zero_iff.2 (e.toE_ne_zero hw)
  field_simp

theorem sphereParam_index_one (hk : e.k = 1) (ε : ℝ) {w : Fin e.k → ℝ} (hw : w ≠ 0) :
    e.sphereParam ε w = e.sphereParam ε (fun _ => 1) ∨
      e.sphereParam ε w = e.sphereParam ε (-fun _ => 1) := by
  have hi : ∀ i : Fin e.k, i = ⟨0, by omega⟩ := fun i => Fin.ext (by have := i.isLt; omega)
  set i₀ : Fin e.k := ⟨0, by omega⟩
  have hw' : w = w i₀ • (fun _ => (1 : ℝ)) := by
    funext i; rw [hi i]; simp
  have hne : w i₀ ≠ 0 := fun h => hw (by rw [hw', h, zero_smul])
  have hone : (fun _ : Fin e.k => (1 : ℝ)) ≠ 0 := fun h => by
    have := congrFun h i₀; simp at this
  rcases lt_or_gt_of_ne hne with h | h
  · right
    have : w = (-w i₀) • (-fun _ : Fin e.k => (1 : ℝ)) := by rw [smul_neg, neg_smul, neg_neg, ← hw']
    rw [this, e.sphereParam_smul ε (by linarith) (neg_ne_zero.2 hone)]
  · left
    rw [hw', e.sphereParam_smul ε h hone]

end MorseNormalChart

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless] {D : GradientLikeStrip I f a b crit}

section SardOne

variable (p : M) {q : M} (hq : q ∈ crit) (ε c η : ℝ) (hp : p ∈ crit)

theorem sardMap_image_subset_index_one (hk : (D.chart q hq).k = 1) :
    D.sardMap p hq ε c η hp '' D.sardDom p hq ε c η hp ⊆
      {D.sardMap p hq ε c η hp (fun _ => 1), D.sardMap p hq ε c η hp (-fun _ => 1)} := by
  rintro _ ⟨w, ⟨hw0, -⟩, rfl⟩
  have hw0' : w ≠ 0 := hw0
  rcases (D.chart q hq).sphereParam_index_one hk ε hw0' with h | h
  · left; simp only [sardMap, landing, h]
  · right; simp only [sardMap, landing, h, mem_singleton_iff]

theorem exists_sard_z_index_one (hkq : (D.chart q hq).k = 1) (hkp : 1 ≤ (D.chart p hp).k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z : EuclideanSpace ℝ (Fin (D.chart p hp).k), ‖z‖ < ρ ∧
      z ∉ D.sardMap p hq ε c η hp '' D.sardDom p hq ε c η hp := by
  obtain ⟨z, hz, hz'⟩ := ModelField.exists_avoid_finite hkp
    ((Set.finite_singleton _).insert _) 0 hρ
  exact ⟨z, by simpa using hz, fun h => hz' (sardMap_image_subset_index_one p hq ε c η hp hkq h)⟩

end SardOne

section GeneralPositionOfAvoid

theorem exists_gradientLike_generalPosition_of_avoid (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hpq : p ≠ q)
    {ε c : ℝ} (hε : 0 < ε)
    (hr₀p : (D.chart p hp).r₀ ^ 2 < 2 * ε) (hr₀q : (D.chart q hq).r₀ ^ 2 < 2 * ε)
    (hrmp : 24 * ε < D.rm p hp ^ 2) (hrmq : 4 * ε < D.rm q hq ^ 2)
    (hc : f p + 8 * ε < c) (hcq : c < f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp')
    (hsard : ∀ ρ, 0 < ρ → ∃ z : EuclideanSpace ℝ (Fin (D.chart p hp).k), ‖z‖ < ρ ∧
      z ∉ D.sardMap p hq ε c (8 * ε) hp '' D.sardDom p hq ε c (8 * ε) hp) :
    ∃ D' : GradientLikeStrip I f a b crit,
      (∀ p' hp', (D'.chart p' hp').χ = (D.chart p' hp').χ ∧
        (D'.chart p' hp').k = (D.chart p' hp').k ∧ (D'.chart p' hp').R = (D.chart p' hp').R ∧
        (D'.chart p' hp').R' = (D.chart p' hp').R') ∧
      (∀ p' hp', (D'.chart p' hp').r₀ ≤ (D.chart p' hp').r₀) ∧
      D'.rm p hp ^ 2 = 8 * ε ∧ (∀ p' hp', p' ≠ p → D'.rm p' hp' = D.rm p' hp') ∧
      (∀ x, x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' →
        x ∉ (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' → D'.V x = D.V x) ∧
      (∀ x, (f x ≤ f p + 4 * ε ∨ f p + 8 * ε ≤ f x) →
        x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2} →
        x ∉ (D.chart q hq).χ '' {y | morseNorm n y ≤ (D.chart q hq).r₀ / 2} → D'.V x = D.V x) ∧
      D'.leftSphere q hq ε c = D.leftSphere q hq ε c ∧
      Disjoint (D'.rightSphere p hp ε c) (D'.leftSphere q hq ε c) ∧
      ∃ r', 0 < r' ∧ (D'.chart p hp).r₀ < r' ∧ (D'.chart q hq).r₀ < r' ∧ r' ^ 2 < ε ∧
        (∀ x ∈ (D'.chart p hp).χ '' {y | morseNorm n y < r'}, ∀ t,
          D'.flow t x ∉ (D'.chart q hq).χ '' {y | morseNorm n y < r'}) ∧
        ∃ δ, 0 < δ ∧ δ ≤ ε ∧ r' ^ 4 ≤ 2 * ε * δ ∧
          Disjoint (D'.flow (f p + ε - c) '' ((D'.chart p hp).χ '' D'.rightTube p hp ε δ))
            (D'.flow (f q - ε - c) '' ((D'.chart q hq).χ '' D'.leftTube q hq ε δ)) := by
  have hpa : a < f p := (D.f_mem_Ioo p hp).1
  have hqb : f q < b := (D.f_mem_Ioo q hq).2
  have hpq' : q ≠ p := Ne.symm hpq
  have hrmp0 := D.rm_pos p hp
  have hrmq0 := D.rm_pos q hq
  have hrmpR : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 := pow_le_pow_left₀ hrmp0.le (D.hrm p hp).2 2
  have hrmqR : D.rm q hq ^ 2 ≤ (D.chart q hq).R ^ 2 := pow_le_pow_left₀ hrmq0.le (D.hrm q hq).2 2
  have hr₀p0 := (D.chart p hp).hr₀
  have hr₀q0 := (D.chart q hq).hr₀
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 8 * ε := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ε := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hρ : 0 < ρ := by rw [hρdef]; exact hε
  have hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2 := by
    rw [hρdef, hηdef]
    have : 18 * ε ^ 2 / (8 * ε) = 9 * ε / 4 := by field_simp; ring
    rw [this]; linarith
  have hηrm : η ≤ D.rm p hp ^ 2 := by rw [hηdef]; linarith
  have hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η := by rw [hηdef]; linarith
  have hεη : ε ≤ η / 2 := by rw [hηdef]; linarith
  have hr₀ε : (D.chart p hp).r₀ ^ 2 ≤ 8 * ε := by linarith
  have hB : 2 * η + ρ ^ 2 / ε < D.rm p hp ^ 2 := by
    rw [hρdef, hηdef]
    have : ε ^ 2 / ε = ε := by field_simp
    rw [this]; linarith
  have hεq : 2 * ε ≤ (D.chart q hq).R ^ 2 := by linarith
  have hεp : 2 * ε ≤ (D.chart p hp).R ^ 2 := by linarith
  have hηc : f p + η < c := by rw [hηdef]; exact hc
  have hlevη : ∀ y, f y ∈ Icc (f p + η) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp' :=
    fun y hy => hlev y ⟨by rw [hηdef] at hy; linarith [hy.1], hy.2⟩
  obtain ⟨z, hzρ, hzF⟩ : ∃ z : EuclideanSpace ℝ (Fin (D.chart p hp).k), ‖z‖ < ρ ∧
      z ∉ D.sardMap p hq ε c η hp '' D.sardDom p hq ε c η hp := by
    rw [hηdef]; exact hsard ρ hρ
  have hz : ‖z‖ ≤ ρ := hzρ.le
  have hsep := disjoint_spheres_twisted hf hη hρ hsupp hηrm hr₀η hq hε hεη hr₀ε hz hB hεq hηc hcq
    hlevη hzF
  have hleft := leftSphere_twisted (z := z) hf hη hρ hsupp hηrm hr₀η hq hεq hηc hcq.le (ε := ε)
  obtain ⟨Dt, hDt⟩ : ∃ Dt : GradientLikeStrip I f a b crit,
    twisted (z := z) hf hη hρ hsupp hηrm hr₀η = Dt := ⟨_, rfl⟩
  have hDtchart : Dt.chart = D.chart := by rw [← hDt]; rfl
  have hDtrmp : Dt.rm p hp = Real.sqrt η := by rw [← hDt]; exact twisted_rm_self _ _ _ _ _ _
  have hDtrmq : ∀ p' hp', p' ≠ p → Dt.rm p' hp' = D.rm p' hp' := fun p' hp' h => by
    rw [← hDt]; exact twisted_rm_of_ne _ _ _ _ _ _ hp' h
  have hDtsmall : ∀ p' hp', Dt.smallBall p' hp' = D.smallBall p' hp' := fun p' hp' => by
    rw [← hDt]; rfl
  have hDtV_ge : ∀ x, f p + η ≤ f x → Dt.V x = D.V x := fun x hx => by
    rw [← hDt]; exact twistedV_eq_of_level_ge hη hρ hsupp hx
  have hDtV_le : ∀ x, f x ≤ f p + η / 2 → Dt.V x = D.V x := fun x hx => by
    rw [← hDt]; exact twistedV_eq_of_level_le hη hρ hsupp hx
  have hDtV_out : ∀ x, x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' → Dt.V x = D.V x :=
    fun x hx => by rw [← hDt]; exact twistedV_of_notMem hx
  rw [hDt] at hsep hleft
  have hDtrmp2 : Dt.rm p hp ^ 2 = 8 * ε := by
    rw [hDtrmp, Real.sq_sqrt hη.le, hηdef]
  have hDtrmq2 : Dt.rm q hq = D.rm q hq := hDtrmq q hq hpq'
  obtain ⟨δ₀, hδ₀, htube₀⟩ := exists_tube_disjoint Dt p hp q hq hε (by rw [hDtchart]; exact hεp)
    (by rw [hDtchart]; exact hεq) hsep
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₀ ε := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min hδ₀ hε
  have hδε : δ ≤ ε := by rw [hδdef]; exact min_le_right _ _
  have hδδ₀ : δ ≤ δ₀ := by rw [hδdef]; exact min_le_left _ _
  have htube : Disjoint (Dt.flow (f p + ε - c) '' ((Dt.chart p hp).χ '' Dt.rightTube p hp ε δ))
      (Dt.flow (f q - ε - c) '' ((Dt.chart q hq).χ '' Dt.leftTube q hq ε δ)) := by
    refine htube₀.mono (image_mono (image_mono fun y hy => And.intro hy.1 (hy.2.trans hδδ₀)))
      (image_mono (image_mono fun y hy => And.intro hy.1 (hy.2.trans hδδ₀)))
  obtain ⟨r', hr', hr'p, hr'q, hr'ε, hr'δ⟩ := exists_small_radius hr₀p0 hr₀q0 hε
    (show 0 < 2 * ε * δ by positivity)
  have hr₁ : 0 < r' / 2 := by positivity
  have hle₁ : r' / 2 ≤ (Dt.chart p hp).r₀ := by rw [hDtchart]; linarith
  have hle₂ : r' / 2 ≤ (Dt.chart q hq).r₀ := by rw [hDtchart]; linarith
  obtain ⟨D', hD'⟩ : ∃ D' : GradientLikeStrip I f a b crit,
    shrink₂ (D := Dt) hf hp hq hpq' hr₁ hle₁ hr₁ hle₂ = D' := ⟨_, rfl⟩
  have hχ : ∀ p' hp', (D'.chart p' hp').χ = (Dt.chart p' hp').χ := fun p' hp' => by
    rw [← hD']; rfl
  have hk : ∀ p' hp', (D'.chart p' hp').k = (Dt.chart p' hp').k := fun p' hp' => by
    rw [← hD']; rfl
  have hR : ∀ p' hp', (D'.chart p' hp').R = (Dt.chart p' hp').R := fun p' hp' => by
    rw [← hD']; rfl
  have hR' : ∀ p' hp', (D'.chart p' hp').R' = (Dt.chart p' hp').R' := fun p' hp' => by
    rw [← hD']; rfl
  have hrm : D'.rm = Dt.rm := by rw [← hD']; rfl
  have hr₀p' : (D'.chart p hp).r₀ = r' / 2 := by
    rw [← hD']; exact shrink₂_r₀_p _ _ _ _ _ _ _ _
  have hr₀q' : (D'.chart q hq).r₀ = r' / 2 := by
    rw [← hD']; exact shrink₂_r₀_q _ _ _ _ _ _ _ _
  have hr₀' : ∀ p' hp', p' ≠ p → p' ≠ q → (D'.chart p' hp').r₀ = (Dt.chart p' hp').r₀ :=
    fun p' hp' h1 h2 => by rw [← hD']; exact shrink₂_r₀_of_ne _ _ _ _ _ _ _ _ hp' h1 h2
  have hsmall : ∀ p' hp', D'.smallBall p' hp' ⊆ Dt.smallBall p' hp' := fun p' hp' => by
    rw [← hD']; exact smallBall_shrink₂_subset _ _ _ _ _ _ _ _ p' hp'
  have hεp' : (Dt.chart p hp).r₀ ^ 2 < 4 * ε := by rw [hDtchart]; linarith
  have hεq' : (Dt.chart q hq).r₀ ^ 2 < 4 * ε := by rw [hDtchart]; linarith
  have hV : ∀ x, f p + ε / 2 ≤ f x → f x ≤ f q - ε / 2 → D'.V x = Dt.V x := fun x hx1 hx2 => by
    rw [← hD']; exact shrink₂_V_eq _ _ _ _ _ _ _ _ hεp' hεq' hx1 hx2
  have hV_out : ∀ x, x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' →
      x ∉ (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' → D'.V x = Dt.V x :=
    fun x hxp hxq => by
      rw [← hD']
      exact shrink₂_V_of_notMem _ _ _ _ _ _ _ _ (by rw [hDtchart]; exact hxp)
        (by rw [hDtchart]; exact hxq)
  have hV_half : ∀ x, x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2} →
      x ∉ (D.chart q hq).χ '' {y | morseNorm n y ≤ (D.chart q hq).r₀ / 2} → D'.V x = Dt.V x :=
    fun x hxp hxq => by
      rw [← hD']
      exact shrink₂_V_of_notMem_half _ _ _ _ _ _ _ _ (by rw [hDtchart]; exact hxp)
        (by rw [hDtchart]; exact hxq)
  have hUo := isOpen_between (M := M) hf.continuous (f p + ε / 2) (f q - ε / 2)
  have hV' : ∀ x ∈ {x : M | f p + ε / 2 < f x ∧ f x < f q - ε / 2}, Dt.V x = D'.V x :=
    fun x hx => (hV x hx.1.le hx.2.le).symm
  have hcab : c ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hunitL : ∀ y, f y ∈ uIcc (f q - ε) c → ∀ p' hp', y ∉ Dt.smallBall p' hp' := by
    intro y hy p' hp'
    rw [uIcc_of_ge hcq.le] at hy
    rw [hDtsmall]
    exact hlev y ⟨by linarith [hy.1], hy.2⟩ p' hp'
  have hunitR : ∀ y, f y ∈ uIcc (f p + ε) c → ∀ p' hp', y ∉ Dt.smallBall p' hp' := by
    intro y hy p' hp'
    rw [uIcc_of_le (by linarith)] at hy
    rw [hDtsmall]
    exact hlev y ⟨hy.1, by linarith [hy.2]⟩ p' hp'
  have hUL : ∀ y, f y ∈ uIcc (f q - ε) c → y ∈ {x : M | f p + ε / 2 < f x ∧ f x < f q - ε / 2} := by
    intro y hy
    rw [uIcc_of_ge hcq.le] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hUR : ∀ y, f y ∈ uIcc (f p + ε) c → y ∈ {x : M | f p + ε / 2 < f x ∧ f x < f q - ε / 2} := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hℓL : f q - ε ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hℓR : f p + ε ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hleftD' : D'.leftSphere q hq ε c = Dt.leftSphere q hq ε c := by
    unfold leftSphere
    rw [hχ q hq, leftModelSphere_eq (hk q hq)]
    exact flow_image_eq_of_agree_levels hf hℓL hcab hunitL hUo hV' hUL fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Dt.chart q hq).f_chart_of_mem_leftModelSphere (by rw [hDtchart]; exact hεq) hy
  have hrightD' : D'.rightSphere p hp ε c = Dt.rightSphere p hp ε c := by
    unfold rightSphere
    rw [hχ p hp, rightModelSphere_eq (hk p hp)]
    exact flow_image_eq_of_agree_levels hf hℓR hcab hunitR hUo hV' hUR fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Dt.chart p hp).f_chart_of_mem_rightModelSphere (by rw [hDtchart]; exact hεp) hy
  have hlevel_tube : ∀ (p' : M) (hp' : p' ∈ crit) (y : Fin n → ℝ), morseNorm n y ^ 2 ≤ 4 * ε →
      4 * ε ≤ (Dt.chart p' hp').R ^ 2 → f ((Dt.chart p' hp').χ y) =
        morseNormalForm (Dt.chart p' hp').hk (f p') y := fun p' hp' y hy hR =>
    (Dt.chart p' hp').hnorm y (MorseNormalChart.morseNorm_le_of_sq_le (Dt.chart p' hp').R_pos.le
      (hy.trans hR))
  have htubeD' : D'.flow (f p + ε - c) '' ((D'.chart p hp).χ '' D'.rightTube p hp ε δ) =
      Dt.flow (f p + ε - c) '' ((Dt.chart p hp).χ '' Dt.rightTube p hp ε δ) := by
    rw [hχ p hp, rightTube_eq hp (hk p hp)]
    exact flow_image_eq_of_agree_levels hf hℓR hcab hunitR hUo hV' hUR fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hlevel_tube p hp y ?_ (by rw [hDtchart]; linarith)]
      · exact hy.1
      · have h1 := ModelField.nf_sub_eq (Dt.chart p hp).hk (f p) y
        rw [hy.1] at h1
        rw [morseNorm_sq_eq_negPart_add_posPart (Dt.chart p hp).hk]
        linarith [hy.2]
  have htubeD'L : D'.flow (f q - ε - c) '' ((D'.chart q hq).χ '' D'.leftTube q hq ε δ) =
      Dt.flow (f q - ε - c) '' ((Dt.chart q hq).χ '' Dt.leftTube q hq ε δ) := by
    rw [hχ q hq, leftTube_eq hq (hk q hq)]
    exact flow_image_eq_of_agree_levels hf hℓL hcab hunitL hUo hV' hUL fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hlevel_tube q hq y ?_ (by rw [hDtchart]; linarith)]
      · exact hy.1
      · have h1 := ModelField.nf_sub_eq (Dt.chart q hq).hk (f q) y
        rw [hy.1] at h1
        rw [morseNorm_sq_eq_negPart_add_posPart (Dt.chart q hq).hk]
        linarith [hy.2]
  have hnocommon := nocommon_of_agree (D := Dt) (D' := D') hf hp hq hpq' hχ hk hsmall hε hr' hr'ε
    hr'δ (by rw [hrm, hDtrmp2]; linarith) (by rw [hrm, hDtrmq2]; exact hrmq) hV (by linarith) hcq
    (fun y hy p' hp' => by rw [hDtsmall]; exact hlev y hy p' hp') htube
  refine ⟨D', fun p' hp' => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, r', hr', ?_, ?_, hr'ε,
    hnocommon, δ, hδ, hδε, hr'δ, ?_⟩
  · rw [hχ, hDtchart]
  · rw [hk, hDtchart]
  · rw [hR, hDtchart]
  · rw [hR', hDtchart]
  · intro p' hp'
    by_cases h1 : p' = p
    · subst h1; rw [hr₀p']; linarith
    · by_cases h2 : p' = q
      · subst h2; rw [hr₀q']; linarith
      · rw [hr₀' p' hp' h1 h2, hDtchart]
  · rw [hrm, hDtrmp2]
  · intro p' hp' h
    rw [hrm, hDtrmq p' hp' h]
  · intro x hxp hxq
    rw [hV_out x hxp hxq, hDtV_out x hxp]
  · intro x hx hxp hxq
    rw [hV_half x hxp hxq]
    rcases hx with hx | hx
    · exact hDtV_le x (by rw [hηdef]; linarith)
    · exact hDtV_ge x (by rw [hηdef]; exact hx)
  · rw [hleftD', hleft]
  · rw [hrightD', hleftD']; exact hsep
  · rw [hr₀p']; linarith
  · rw [hr₀q']; linarith
  · rw [htubeD', htubeD'L]; exact htube

theorem exists_gradientLike_generalPosition_index_one (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (D : GradientLikeStrip I f a b crit) {p q : M} (hp : p ∈ crit) (hq : q ∈ crit) (hpq : p ≠ q)
    (hk : (D.chart p hp).k = 1 ∧ (D.chart q hq).k = 1) {ε c : ℝ} (hε : 0 < ε)
    (hr₀p : (D.chart p hp).r₀ ^ 2 < 2 * ε) (hr₀q : (D.chart q hq).r₀ ^ 2 < 2 * ε)
    (hrmp : 24 * ε < D.rm p hp ^ 2) (hrmq : 4 * ε < D.rm q hq ^ 2)
    (hc : f p + 8 * ε < c) (hcq : c < f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp') :
    ∃ D' : GradientLikeStrip I f a b crit,
      (∀ p' hp', (D'.chart p' hp').χ = (D.chart p' hp').χ ∧
        (D'.chart p' hp').k = (D.chart p' hp').k ∧ (D'.chart p' hp').R = (D.chart p' hp').R ∧
        (D'.chart p' hp').R' = (D.chart p' hp').R') ∧
      (∀ p' hp', (D'.chart p' hp').r₀ ≤ (D.chart p' hp').r₀) ∧
      D'.rm p hp ^ 2 = 8 * ε ∧ (∀ p' hp', p' ≠ p → D'.rm p' hp' = D.rm p' hp') ∧
      (∀ x, x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' →
        x ∉ (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' → D'.V x = D.V x) ∧
      (∀ x, (f x ≤ f p + 4 * ε ∨ f p + 8 * ε ≤ f x) →
        x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2} →
        x ∉ (D.chart q hq).χ '' {y | morseNorm n y ≤ (D.chart q hq).r₀ / 2} → D'.V x = D.V x) ∧
      D'.leftSphere q hq ε c = D.leftSphere q hq ε c ∧
      Disjoint (D'.rightSphere p hp ε c) (D'.leftSphere q hq ε c) ∧
      ∃ r', 0 < r' ∧ (D'.chart p hp).r₀ < r' ∧ (D'.chart q hq).r₀ < r' ∧ r' ^ 2 < ε ∧
        (∀ x ∈ (D'.chart p hp).χ '' {y | morseNorm n y < r'}, ∀ t,
          D'.flow t x ∉ (D'.chart q hq).χ '' {y | morseNorm n y < r'}) ∧
        ∃ δ, 0 < δ ∧ δ ≤ ε ∧ r' ^ 4 ≤ 2 * ε * δ ∧
          Disjoint (D'.flow (f p + ε - c) '' ((D'.chart p hp).χ '' D'.rightTube p hp ε δ))
            (D'.flow (f q - ε - c) '' ((D'.chart q hq).χ '' D'.leftTube q hq ε δ)) :=
  exists_gradientLike_generalPosition_of_avoid hf D hp hq hpq hε hr₀p hr₀q hrmp hrmq hc hcq hlev
    fun ρ hρ => exists_sard_z_index_one p hq ε c (8 * ε) hp hk.2 (by rw [hk.1]) hρ

end GeneralPositionOfAvoid

end GradientLikeStrip

namespace MorseNormalChart

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {p : M} (d : MorseNormalChart I f p)

theorem f_mem_Icc_of_morseNorm_le {r : ℝ} (hr : r ≤ d.R) {y : Fin n → ℝ}
    (hy : morseNorm n y ≤ r) : f (d.χ y) ∈ Icc (f p - r ^ 2 / 2) (f p + r ^ 2 / 2) := by
  rw [d.hnorm y (hy.trans hr), morseNormalForm_split]
  have h1 := morseNorm_sq_eq_negPart_add_posPart d.hk y
  have h2 := sq_nonneg ‖negPart d.hk y‖
  have h3 := sq_nonneg ‖posPart d.hk y‖
  have h4 : morseNorm n y ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (ModelField.morseNorm_nonneg y) hy 2
  constructor <;> linarith

theorem f_mem_Icc_of_mem_image_le {r : ℝ} (hr : r ≤ d.R) {x : M}
    (hx : x ∈ d.χ '' {y | morseNorm n y ≤ r}) :
    f x ∈ Icc (f p - r ^ 2 / 2) (f p + r ^ 2 / 2) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact d.f_mem_Icc_of_morseNorm_le hr hy

theorem f_mem_Icc_of_mem_image_lt {r : ℝ} (hr : r ≤ d.R) {x : M}
    (hx : x ∈ d.χ '' {y | morseNorm n y < r}) :
    f x ∈ Icc (f p - r ^ 2 / 2) (f p + r ^ 2 / 2) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact d.f_mem_Icc_of_morseNorm_le hr (le_of_lt hy)

end MorseNormalChart

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless]

omit [T2Space M] [I.Boundaryless] in
theorem f_mem_Icc_of_mem_smallBall (D : GradientLikeStrip I f a b crit) {p : M} {hp : p ∈ crit}
    {x : M} (hx : x ∈ D.smallBall p hp) :
    f x ∈ Icc (f p - (D.chart p hp).r₀ ^ 2 / 2) (f p + (D.chart p hp).r₀ ^ 2 / 2) :=
  (D.chart p hp).f_mem_Icc_of_mem_image_lt (D.r₀_lt_R p hp).le hx

omit [T2Space M] [I.Boundaryless] in
theorem isCompact_halfBall (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) :
    IsCompact ((D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}) :=
  (D.chart p hp).isCompact_image_le (by linarith [D.r₀_lt_R' p hp, (D.chart p hp).hr₀])

omit [I.Boundaryless] in
theorem exists_shrinkAll (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {ρ : ℝ} (hρ : 0 < ρ) (hle : ∀ p hp, ρ ≤ (D.chart p hp).r₀) :
    ∃ E : GradientLikeStrip I f a b crit,
      (∀ p hp, (E.chart p hp).χ = (D.chart p hp).χ ∧ (E.chart p hp).k = (D.chart p hp).k ∧
        (E.chart p hp).R = (D.chart p hp).R ∧ (E.chart p hp).R' = (D.chart p hp).R') ∧
      (∀ p hp, (E.chart p hp).r₀ = ρ / 2) ∧ (∀ p hp, E.rm p hp = D.rm p hp) ∧
      ∀ x, (∀ p hp, x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}) →
        E.V x = D.V x := by
  classical
  have key : ∀ S : Finset M, S ⊆ crit → ∃ E : GradientLikeStrip I f a b crit,
      (∀ p hp, (E.chart p hp).χ = (D.chart p hp).χ ∧ (E.chart p hp).k = (D.chart p hp).k ∧
        (E.chart p hp).R = (D.chart p hp).R ∧ (E.chart p hp).R' = (D.chart p hp).R') ∧
      (∀ p hp, p ∈ S → (E.chart p hp).r₀ = ρ / 2) ∧
      (∀ p hp, p ∉ S → (E.chart p hp).r₀ = (D.chart p hp).r₀) ∧
      (∀ p hp, E.rm p hp = D.rm p hp) ∧
      ∀ x, (∀ p hp, p ∈ S →
        x ∉ (D.chart p hp).χ '' {y | morseNorm n y ≤ (D.chart p hp).r₀ / 2}) →
        E.V x = D.V x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨D, fun p hp => ⟨rfl, rfl, rfl, rfl⟩, fun p hp h => absurd h (Finset.notMem_empty p),
        fun p hp _ => rfl, fun p hp => rfl, fun x _ => rfl⟩
    | insert q S hqS ih =>
      intro hsub
      have hq : q ∈ crit := hsub (Finset.mem_insert_self q S)
      obtain ⟨E, hE1, hE2, hE3, hE4, hE5⟩ := ih ((Finset.subset_insert q S).trans hsub)
      have hr₀' : 0 < ρ / 2 := by positivity
      have hleq : ρ / 2 ≤ (E.chart q hq).r₀ := by
        rw [hE3 q hq hqS]; linarith [hle q hq]
      refine ⟨shrinkAt (D := E) hf hr₀' hleq, fun p hp => ?_, fun p hp hpS => ?_,
        fun p hp hpS => ?_, fun p hp => ?_, fun x hx => ?_⟩
      · rw [shrinkAt_chart_χ, shrinkAt_chart_k, shrinkAt_chart_R, shrinkAt_chart_R']
        exact hE1 p hp
      · by_cases h : p = q
        · subst h; exact shrinkAt_chart_r₀_self hf hr₀' hleq
        · rw [shrinkAt_chart_r₀_of_ne hf hr₀' hleq hp h]
          exact hE2 p hp (Finset.mem_of_mem_insert_of_ne hpS h)
      · have h : p ≠ q := fun h => hpS (h ▸ Finset.mem_insert_self q S)
        rw [shrinkAt_chart_r₀_of_ne hf hr₀' hleq hp h]
        exact hE3 p hp fun h' => hpS (Finset.mem_insert_of_mem h')
      · rw [shrinkAt_rm]; exact hE4 p hp
      · rw [shrinkAt_V, shrunkV_of_notMem_image hr₀' hleq ?_]
        · exact hE5 x fun p hp hpS => hx p hp (Finset.mem_insert_of_mem hpS)
        · rw [(hE1 q hq).1, hE3 q hq hqS]
          exact hx q hq (Finset.mem_insert_self q S)
  obtain ⟨E, hE1, hE2, -, hE4, hE5⟩ := key crit le_rfl
  exact ⟨E, hE1, fun p hp => hE2 p hp hp, hE4, fun x hx => hE5 x fun p hp _ => hx p hp⟩

theorem flow_eq_of_agree_above {D₁ D₂ : GradientLikeStrip I f a b crit} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {L : ℝ} (hV : ∀ x, L < f x → D₁.V x = D₂.V x) {x : M} {t : ℝ}
    (hx : L < f (D₁.flow t x)) : ∀ s ∈ Icc 0 t, D₂.flow s x = D₁.flow s x :=
  flow_eq_of_agree (isOpen_lt continuous_const hf.continuous) hV fun _ hs =>
    lt_of_lt_of_le hx (f_flow_antitone hf x hs.2.le)

theorem flow_eq_of_agree_above_neg {D₁ D₂ : GradientLikeStrip I f a b crit}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {L : ℝ} (hV : ∀ x, L < f x → D₁.V x = D₂.V x) {x : M}
    (hx : L < f x) {T : ℝ} (hT : 0 ≤ T) : ∀ s ∈ Icc (-T) 0, D₂.flow s x = D₁.flow s x :=
  flow_eq_of_agree_neg (isOpen_lt continuous_const hf.continuous) hV hT fun _ hs =>
    lt_of_lt_of_le hx (le_f_flow_of_nonpos hf x hs.2.le)

theorem flow_eq_of_agree_above_of_le {D₁ D₂ : GradientLikeStrip I f a b crit}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {L : ℝ} (hV : ∀ x, L < f x → D₁.V x = D₂.V x) {x : M}
    {T : ℝ} (hx : L < f x - T) : ∀ s ∈ Icc 0 T, D₂.flow s x = D₁.flow s x :=
  flow_eq_of_agree (isOpen_lt continuous_const hf.continuous) hV fun s hs => by
    have := sub_le_f_flow (D := D₁) hf x hs.1
    change L < f (D₁.flow s x)
    linarith [hs.2]

theorem exists_twist_stage (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {p : M} (hp : p ∈ crit) (hkp : (D.chart p hp).k = 1) (Q : Finset M) (hQ : ∀ q ∈ Q, q ∈ crit)
    (hkQ : ∀ q (hq : q ∈ crit), q ∈ Q → (D.chart q hq).k = 1) {ε c : ℝ} (hε : 0 < ε)
    (hεR : ∀ q hq, 2 * ε ≤ (D.chart q hq).R ^ 2) (hr₀p : 4 * (D.chart p hp).r₀ ^ 2 < 32 * ε)
    (hrmp : 65 * ε < D.rm p hp ^ 2) (hc : f p + 32 * ε < c) (hcb : c ≤ b)
    (hcQ : ∀ q ∈ Q, c ≤ f q - ε)
    (hlev : ∀ y, f y ∈ Icc (f p + 32 * ε) c → ∀ p' hp', y ∉ D.smallBall p' hp') :
    ∃ D' : GradientLikeStrip I f a b crit,
      D'.chart = D.chart ∧
      D'.rm p hp ^ 2 = 32 * ε ∧ (∀ q hq, q ≠ p → D'.rm q hq = D.rm q hq) ∧
      (∀ x, f p + 32 * ε ≤ f x → D'.V x = D.V x) ∧
      (∀ x, x ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R' → D'.V x = D.V x) ∧
      ∀ q hq, q ∈ Q → Disjoint (D'.rightSphere p hp ε c) (D'.leftSphere q hq ε c) := by
  classical
  have hpa : a < f p := (D.f_mem_Ioo p hp).1
  have hrmp0 := D.rm_pos p hp
  have hrmpR : D.rm p hp ^ 2 ≤ (D.chart p hp).R ^ 2 := pow_le_pow_left₀ hrmp0.le (D.hrm p hp).2 2
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 32 * ε := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ε := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hρ : 0 < ρ := by rw [hρdef]; exact hε
  have hsupp : 2 * η + 18 * ρ ^ 2 / η < (D.chart p hp).R ^ 2 := by
    rw [hρdef, hηdef]
    have : 18 * ε ^ 2 / (32 * ε) = 9 * ε / 16 := by field_simp; ring
    rw [this]; linarith
  have hηrm : η ≤ D.rm p hp ^ 2 := by rw [hηdef]; linarith
  have hr₀η : 4 * (D.chart p hp).r₀ ^ 2 < η := by rw [hηdef]; exact hr₀p
  have hεη : ε ≤ η / 2 := by rw [hηdef]; linarith
  have hr₀ε : (D.chart p hp).r₀ ^ 2 ≤ 8 * ε := by linarith
  have hB : 2 * η + ρ ^ 2 / ε < D.rm p hp ^ 2 := by
    rw [hρdef, hηdef]
    have : ε ^ 2 / ε = ε := by field_simp
    rw [this]; linarith
  have hηc : f p + η < c := by rw [hηdef]; exact hc
  have hlevη : ∀ y, f y ∈ Icc (f p + η) c → ∀ p' hp', y ∉ D.smallBall p' hp' :=
    fun y hy => hlev y (by rw [hηdef] at hy; exact hy)
  set F : Set (EuclideanSpace ℝ (Fin (D.chart p hp).k)) := ⋃ q : {q // q ∈ Q},
    D.sardMap p (hQ q.1 q.2) ε c η hp '' D.sardDom p (hQ q.1 q.2) ε c η hp with hF
  have hFfin : F.Finite := Set.finite_iUnion fun q => (Set.toFinite _).subset
    (sardMap_image_subset_index_one p (hQ q.1 q.2) ε c η hp (hkQ q.1 (hQ q.1 q.2) q.2))
  obtain ⟨z, hzρ, hzF⟩ := ModelField.exists_avoid_finite (by rw [hkp]) hFfin 0 hρ
  have hz : ‖z‖ ≤ ρ := by simpa using hzρ.le
  have hzF' : ∀ q hq, q ∈ Q → z ∉ D.sardMap p hq ε c η hp '' D.sardDom p hq ε c η hp :=
    fun q hq hqQ h => hzF (mem_iUnion.2 ⟨⟨q, hqQ⟩, h⟩)
  refine ⟨twisted (z := z) hf hη hρ hsupp hηrm hr₀η, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [twisted_rm_self, Real.sq_sqrt hη.le, hηdef]
  · intro q hq h; exact twisted_rm_of_ne _ _ _ _ _ _ hq h
  · intro x hx
    rw [twisted_V]
    exact twistedV_eq_of_level_ge hη hρ hsupp (by rw [hηdef]; exact hx)
  · intro x hx
    rw [twisted_V]
    exact twistedV_of_notMem hx
  intro q hq hqQ
  have hεq : 2 * ε ≤ (D.chart q hq).R ^ 2 := hεR q hq
  have hcq : c ≤ f q - ε := hcQ q hqQ
  rw [leftSphere_twisted hf hη hρ hsupp hηrm hr₀η hq hεq hηc hcq]
  refine Set.disjoint_left.2 fun x hxR hxL => ?_
  have hxR' := rightSphere_twisted_subset hf hη hρ hsupp hηrm hr₀η hε hεη hr₀ε hz hB hηc hcb
    hlevη hxR
  obtain ⟨_, ⟨y₁, ⟨hy₁S, hy₁nf, hy₁J⟩, rfl⟩, rfl⟩ := hxR'
  obtain ⟨_, ⟨y₂, hy₂, rfl⟩, hx⟩ := hxL
  obtain ⟨hw0, hsp⟩ := (D.chart q hq).sphereParam_of_mem hε hy₂
  have hy₁R : morseNorm n y₁ < (D.chart p hp).R := by
    have := lt_of_pow_lt_pow_left₀ 2 (D.rm_pos p hp).le
      (lt_of_le_of_lt (show morseNorm n y₁ ^ 2 ≤ _ from hy₁S) hB)
    exact this.trans_le (D.hrm p hp).2
  have hland : D.landing p hq ε c η ((EuclideanSpace.equiv (Fin (D.chart q hq).k) ℝ)
      (negPart (D.chart q hq).hk y₂)) = (D.chart p hp).χ y₁ := by
    unfold landing
    rw [hsp, hx, flow_flow, show f p + η - c + (c - (f p + η)) = 0 by ring, flow_zero]
  apply hzF' q hq hqQ
  refine ⟨_, ⟨hw0, ?_⟩, ?_⟩
  · change D.landing p hq ε c η _ ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}
    rw [hland]
    exact ⟨y₁, hy₁R, rfl⟩
  · unfold sardMap
    rw [hland, (D.chart p hp).χ.left_inv ((D.chart p hp).hsrc y₁ hy₁R.le)]
    exact hy₁J

theorem leftSphere_eq_of_flow_eq {D₁ D₂ : GradientLikeStrip I f a b crit} {q : M} {hq : q ∈ crit}
    (hχ : (D₂.chart q hq).χ = (D₁.chart q hq).χ) (hk : (D₂.chart q hq).k = (D₁.chart q hq).k)
    {ε c : ℝ} (hflow : ∀ x ∈ (D₁.chart q hq).χ '' (D₁.chart q hq).leftModelSphere ε,
      D₂.flow (f q - ε - c) x = D₁.flow (f q - ε - c) x) :
    D₂.leftSphere q hq ε c = D₁.leftSphere q hq ε c := by
  unfold leftSphere
  rw [hχ, leftModelSphere_eq hk]
  exact image_congr hflow

theorem rightSphere_eq_of_flow_eq {D₁ D₂ : GradientLikeStrip I f a b crit} {p : M} {hp : p ∈ crit}
    (hχ : (D₂.chart p hp).χ = (D₁.chart p hp).χ) (hk : (D₂.chart p hp).k = (D₁.chart p hp).k)
    {ε c : ℝ} (hflow : ∀ x ∈ (D₁.chart p hp).χ '' (D₁.chart p hp).rightModelSphere ε,
      D₂.flow (f p + ε - c) x = D₁.flow (f p + ε - c) x) :
    D₂.rightSphere p hp ε c = D₁.rightSphere p hp ε c := by
  unfold rightSphere
  rw [hχ, rightModelSphere_eq hk]
  exact image_congr hflow

omit [T2Space M] [I.Boundaryless] in
theorem rightTube_mono' (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) (ε : ℝ)
    {δ δ' : ℝ} (h : δ ≤ δ') : D.rightTube p hp ε δ ⊆ D.rightTube p hp ε δ' :=
  fun _ hy => ⟨hy.1, hy.2.trans h⟩

omit [T2Space M] [I.Boundaryless] in
theorem leftTube_mono' (D : GradientLikeStrip I f a b crit) (q : M) (hq : q ∈ crit) (ε : ℝ)
    {δ δ' : ℝ} (h : δ ≤ δ') : D.leftTube q hq ε δ ⊆ D.leftTube q hq ε δ' :=
  fun _ hy => ⟨hy.1, hy.2.trans h⟩

omit [T2Space M] [I.Boundaryless] in
theorem leftModelSphere_subset_leftTube (D : GradientLikeStrip I f a b crit) (q : M)
    (hq : q ∈ crit) {ε δ : ℝ} (hδ : 0 ≤ δ) :
    (D.chart q hq).leftModelSphere ε ⊆ D.leftTube q hq ε δ := fun y hy =>
  ⟨(D.chart q hq).nf_of_mem_leftModelSphere hy, by rw [hy.1, norm_zero]; simpa using hδ⟩

theorem exists_uniform_tube_disjoint (D : GradientLikeStrip I f a b crit) {p : M} (hp : p ∈ crit)
    (T : Finset M) (hT : ∀ q ∈ T, q ∈ crit) {ε c : ℝ}
    (h : ∀ q hq, q ∈ T → ∃ δ, 0 < δ ∧
      Disjoint (D.flow (f p + ε - c) '' ((D.chart p hp).χ '' D.rightTube p hp ε δ))
        (D.flow (f q - ε - c) '' ((D.chart q hq).χ '' D.leftTube q hq ε δ))) :
    ∃ δ, 0 < δ ∧ ∀ q hq, q ∈ T →
      Disjoint (D.flow (f p + ε - c) '' ((D.chart p hp).χ '' D.rightTube p hp ε δ))
        (D.flow (f q - ε - c) '' ((D.chart q hq).χ '' D.leftTube q hq ε δ)) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun q _ hqT => absurd hqT (Finset.notMem_empty q)⟩
  | insert q T _ ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih (fun q' hq' => hT q' (Finset.mem_insert_of_mem hq'))
      fun q' hq' hq'T => h q' hq' (Finset.mem_insert_of_mem hq'T)
    obtain ⟨δ₂, hδ₂, h₂⟩ := h q (hT q (Finset.mem_insert_self q T)) (Finset.mem_insert_self q T)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun q' hq' hq'T => ?_⟩
    rcases Finset.mem_insert.1 hq'T with rfl | hq'T
    · exact h₂.mono (image_mono (image_mono (rightTube_mono' _ _ _ _ (min_le_right _ _))))
        (image_mono (image_mono (leftTube_mono' _ _ _ _ (min_le_right _ _))))
    · exact (h₁ q' hq' hq'T).mono
        (image_mono (image_mono (rightTube_mono' _ _ _ _ (min_le_left _ _))))
        (image_mono (image_mono (leftTube_mono' _ _ _ _ (min_le_left _ _))))

def portPrivate_1aa78447_stageInv (D₀ D : GradientLikeStrip I f a b crit) (crit₁ S : Finset M) (ε : ℝ) : Prop :=
  (∀ q hq, (D.chart q hq).χ = (D₀.chart q hq).χ ∧ (D.chart q hq).k = (D₀.chart q hq).k ∧
    (D.chart q hq).R = (D₀.chart q hq).R ∧ (D.chart q hq).R' = (D₀.chart q hq).R') ∧
  (∀ q hq, (D.chart q hq).r₀ ≤ (D₀.chart q hq).r₀) ∧
  (∀ q hq, q ∈ S → D.rm q hq ^ 2 = 32 * ε) ∧
  (∀ q hq, q ∉ S → D.rm q hq = D₀.rm q hq) ∧
  (∀ q hq, q ∈ S → ∀ q' hq', q' ∈ crit₁ → f q < f q' →
    Disjoint (D.rightSphere q hq ε (f q + 33 * ε)) (D.leftSphere q' hq' ε (f q + 33 * ε))) ∧
  (∀ q hq, q ∈ S → ∀ q' hq', q' ∈ crit₁ → f q < f q' →
    ∀ x ∈ (D.chart q' hq').χ '' (D.chart q' hq').leftModelSphere ε, ∀ t, 0 ≤ t →
      D.flow t x ∉ D.smallBall q hq)

structure portPrivate_1aa78447_StageSetup (D₀ : GradientLikeStrip I f a b crit) (crit₁ : Finset M) (ε : ℝ) : Prop where
  hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f
  hε : 0 < ε
  hcrit₁ : ∀ q, q ∈ crit₁ ↔ q ∈ crit ∧ morseIndex I f q = 1
  hgap : ∀ p ∈ crit, ∀ q ∈ crit, f p < f q → f p + 40 * ε < f q
  hab : ∀ p ∈ crit, a + 40 * ε < f p ∧ f p + 40 * ε < b
  hinj : ∀ p ∈ crit, ∀ q ∈ crit, f p = f q → p = q
  hmid : ∀ m ∈ crit, ∀ q ∈ crit₁, ∀ q' ∈ crit₁, f q < f m → f m < f q' → m ∈ crit₁
  hR : ∀ q hq, 2 * ε ≤ (D₀.chart q hq).R ^ 2
  hr₀ : ∀ q hq, (D₀.chart q hq).r₀ ^ 2 < ε / 2
  hrm : ∀ q hq, 65 * ε < D₀.rm q hq ^ 2

variable {D₀ : GradientLikeStrip I f a b crit} {crit₁ : Finset M} {ε : ℝ}

theorem portPrivate_1aa78447_stageInv.f_mem_of_mem_smallBall {D : GradientLikeStrip I f a b crit} {S : Finset M}
    (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) (hD : portPrivate_1aa78447_stageInv D₀ D crit₁ S ε) {q : M} {hq : q ∈ crit} {x : M}
    (hx : x ∈ D.smallBall q hq) : f x ∈ Icc (f q - ε / 4) (f q + ε / 4) := by
  have h := D.f_mem_Icc_of_mem_smallBall hx
  have h1 := hD.2.1 q hq
  have h2 := hS.hr₀ q hq
  have h3 : (D.chart q hq).r₀ ^ 2 ≤ (D₀.chart q hq).r₀ ^ 2 :=
    pow_le_pow_left₀ (D.chart q hq).hr₀.le h1 2
  constructor <;> linarith [h.1, h.2]

theorem portPrivate_1aa78447_stageInv.k_eq_one {D : GradientLikeStrip I f a b crit} {S : Finset M}
    (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) (_hD : portPrivate_1aa78447_stageInv D₀ D crit₁ S ε) {q : M} (hq₁ : q ∈ crit₁)
    (hq : q ∈ crit) : (D.chart q hq).k = 1 := by
  rw [← (D.chart q hq).hkidx]; exact ((hS.hcrit₁ q).1 hq₁).2

theorem portPrivate_1aa78447_stageInv.r₀_sq_lt {D : GradientLikeStrip I f a b crit} {S : Finset M}
    (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) (hD : portPrivate_1aa78447_stageInv D₀ D crit₁ S ε) (q : M) (hq : q ∈ crit) :
    (D.chart q hq).r₀ ^ 2 < ε / 2 :=
  lt_of_le_of_lt (pow_le_pow_left₀ (D.chart q hq).hr₀.le (hD.2.1 q hq) 2) (hS.hr₀ q hq)

theorem portPrivate_1aa78447_stageInv.R_sq {D : GradientLikeStrip I f a b crit} {S : Finset M}
    (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) (hD : portPrivate_1aa78447_stageInv D₀ D crit₁ S ε) (q : M) (hq : q ∈ crit) :
    2 * ε ≤ (D.chart q hq).R ^ 2 := by
  rw [(hD.1 q hq).2.2.1]; exact hS.hR q hq

theorem portPrivate_1aa78447_stageInv.f_arm {D : GradientLikeStrip I f a b crit} {S : Finset M}
    (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) (hD : portPrivate_1aa78447_stageInv D₀ D crit₁ S ε) {q' : M} {hq' : q' ∈ crit}
    {x : M} (hx : x ∈ (D.chart q' hq').χ '' (D.chart q' hq').leftModelSphere ε) :
    f x = f q' - ε := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact (D.chart q' hq').f_chart_of_mem_leftModelSphere (hD.R_sq hS q' hq') hy

theorem portPrivate_1aa78447_stageInv.base (_hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) : portPrivate_1aa78447_stageInv D₀ D₀ crit₁ ∅ ε :=
  ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ => le_rfl,
    fun q _ h => absurd h (Finset.notMem_empty q), fun _ _ _ => rfl,
    fun q _ h => absurd h (Finset.notMem_empty q), fun q _ h => absurd h (Finset.notMem_empty q)⟩

theorem arm_avoids_of_tube (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε : ℝ} (hε : 0 < ε)
    {D' Dt : GradientLikeStrip I f a b crit} {q q' : M} (hq : q ∈ crit) (hq' : q' ∈ crit)
    (hlt : f q < f q') {c : ℝ} (hcdef : c = f q + 33 * ε) (hcab : c ∈ Icc a b) {δ : ℝ}
    {r' : ℝ} (hr'0 : 0 < r') (hr'ε : r' ^ 2 < ε) (hr'δ : r' ^ 4 ≤ 2 * ε * δ)
    (hrm'p : D'.rm q hq ^ 2 = 32 * ε)
    (hχt : ∀ q hq, (D'.chart q hq).χ = (Dt.chart q hq).χ)
    (hkt : ∀ q hq, (D'.chart q hq).k = (Dt.chart q hq).k)
    (hV't : ∀ x, f q + ε / 2 ≤ f x → D'.V x = Dt.V x)
    (hsb'' : ∀ p' hp' x, x ∈ D'.smallBall p' hp' → f x ∈ Icc (f p' - ε / 4) (f p' + ε / 4))
    (hfar : ∀ p' ∈ crit, p' ≠ q → f p' + 40 * ε < f q ∨ f q + 40 * ε < f p')
    (hq'ab : a + 40 * ε < f q' ∧ f q' + 40 * ε < b) (hqab : a + 40 * ε < f q ∧ f q + 40 * ε < b)
    (hδdisj : Disjoint (Dt.flow (f q + ε - c) '' ((Dt.chart q hq).χ '' Dt.rightTube q hq ε δ))
      (Dt.flow (f q' - ε - c) '' ((Dt.chart q' hq').χ '' Dt.leftTube q' hq' ε δ)))
    {x : M} (hx : x ∈ (D'.chart q' hq').χ '' D'.leftTube q' hq' ε δ)
    (hfx : f x = f q' - ε)
    (hmid : ∀ p' hp', f q < f p' → f p' < f q' → ∀ s ∈ Icc 0 (f q' - ε - c),
      D'.flow s x ∉ D'.smallBall p' hp')
    {t : ℝ} (ht : 0 ≤ t) :
    D'.flow t x ∉ (D'.chart q hq).χ '' {z | morseNorm n z < r' / 2} := by
  intro hmem
  have hq'q : q' ≠ q := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  have hgap' : f q + 40 * ε < f q' := by
    rcases hfar q' hq' hq'q with h | h <;> linarith
  have hcq' : c ≤ f q' - ε := by rw [hcdef]; linarith
  have hcU : ∀ p' hp', ∀ y ∈ D'.smallBall p' hp', f y ≠ c := by
    intro p' hp' y hy hyc
    have h := hsb'' p' hp' y hy
    by_cases hpp : p' = q
    · subst hpp; linarith [h.2]
    · rcases hfar p' hp' hpp with h' | h' <;> linarith [h.1, h.2]
  have harmt : (D'.chart q' hq').χ '' D'.leftTube q' hq' ε δ =
      (Dt.chart q' hq').χ '' Dt.leftTube q' hq' ε δ := by
    rw [hχt q' hq', leftTube_eq (D := Dt) hq' (hkt q' hq')]
  obtain ⟨y, hy, hyx⟩ := hmem
  have hy : morseNorm n y < r' / 2 := hy
  have hrm'0 : 0 < D'.rm q hq := D'.rm_pos q hq
  have hysq' : morseNorm n y ^ 2 < (r' / 2) ^ 2 :=
    pow_lt_pow_left₀ hy (ModelField.morseNorm_nonneg y) two_ne_zero
  have hhalf : (r' / 2) ^ 2 = r' ^ 2 / 4 := by ring
  have hysq : morseNorm n y ^ 2 < ε / 4 := by linarith
  have hsq := morseNorm_sq_eq_negPart_add_posPart (D'.chart q hq).hk y
  have hu0 := sq_nonneg ‖negPart (D'.chart q hq).hk y‖
  have hv0 := sq_nonneg ‖posPart (D'.chart q hq).hk y‖
  have hyrm : morseNorm n y < D'.rm q hq := by
    apply lt_of_pow_lt_pow_left₀ 2 hrm'0.le; rw [hrm'p]; linarith
  have hyR : morseNorm n y ≤ (D'.chart q hq).R := hyrm.le.trans (D'.hrm q hq).2
  have hnfy := morseNormalForm_split (D'.chart q hq).hk (f q) y
  have hv : posPart (D'.chart q hq).hk y ≠ 0 := by
    intro hv0'
    have := f_flow_le_f_p_of_posPart_eq_zero (D := D') hq hyrm hv0' (t := -t) (by linarith)
    rw [hyx, flow_neg_flow] at this
    linarith
  obtain ⟨t₂, ht₂, hft₂, hstay, hprod⟩ := exists_exit_asc (D := D') hf hq hε (y := y)
    (by rw [hrm'p]; linarith) hv (by rw [hnfy]; linarith)
  obtain ⟨e', he'⟩ : ∃ e' : M, D'.flow (-t₂) ((D'.chart q hq).χ y) = e' := ⟨_, rfl⟩
  have he'x : e' = D'.flow (t - t₂) x := by rw [← he', hyx, flow_flow, sub_eq_add_neg]
  have hfe' : f e' = f q + ε := by rw [← he']; exact hft₂
  have hs₁ : 0 ≤ t - t₂ := by
    by_contra hneg
    have := le_f_flow_of_nonpos (D := D') hf x (t := t - t₂) (by linarith)
    rw [← he'x, hfe', hfx] at this
    linarith
  obtain ⟨y₂, hy₂, hy₂e⟩ := hstay (-t₂) (left_mem_Icc.2 (by linarith))
  rw [he'] at hy₂e
  have hy₂sq : morseNorm n y₂ ^ 2 ≤ 2 * ε + 2 * ‖negPart (D'.chart q hq).hk y‖ ^ 2 := hy₂
  have hy₂R : morseNorm n y₂ ≤ (D'.chart q hq).R := by
    have h2 : D'.rm q hq ^ 2 ≤ (D'.chart q hq).R ^ 2 :=
      pow_le_pow_left₀ hrm'0.le (D'.hrm q hq).2 2
    refine MorseNormalChart.morseNorm_le_of_sq_le (D'.chart q hq).R_pos.le ?_
    rw [hrm'p] at h2; linarith
  have hsymm : (D'.chart q hq).χ.symm e' = y₂ := by
    rw [← hy₂e, (D'.chart q hq).χ.left_inv ((D'.chart q hq).hsrc y₂ hy₂R)]
  rw [he', hsymm] at hprod
  have he'T : e' ∈ (D'.chart q hq).χ '' D'.rightTube q hq ε δ := by
    refine ⟨y₂, ⟨?_, ?_⟩, hy₂e⟩
    · rw [← (D'.chart q hq).hnorm y₂ hy₂R, hy₂e]; exact hfe'
    · have hprod' : ‖negPart (D'.chart q hq).hk y‖ ^ 2 *
          ‖posPart (D'.chart q hq).hk y‖ ^ 2 ≤ r' ^ 4 := by
        have h1 : ‖negPart (D'.chart q hq).hk y‖ ^ 2 ≤ r' ^ 2 := by
          linarith [sq_nonneg r']
        have h2 : ‖posPart (D'.chart q hq).hk y‖ ^ 2 ≤ r' ^ 2 := by
          linarith [sq_nonneg r']
        calc _ ≤ r' ^ 2 * r' ^ 2 := mul_le_mul h1 h2 hv0 (by positivity)
          _ = r' ^ 4 := by ring
      exact le_of_mul_le_mul_left (hprod.trans (hprod'.trans hr'δ)) (by positivity)
  have hT₁ : f q + ε - c = -(32 * ε) := by rw [hcdef]; ring
  have hfe'T : f (D'.flow (f q + ε - c) e') = c := by
    have := f_flow_eq_sub_of_levels hf (D := D') (x := e') (T := f q + ε - c)
      (by rw [hfe']; exact ⟨by linarith [hqab.1], by linarith [hqab.2]⟩)
      (by rw [hfe', sub_sub_cancel]; exact hcab) (by
        intro y hy p' hp' hmem
        rw [hfe', sub_sub_cancel, uIcc_of_le (by linarith)] at hy
        have h := hsb'' p' hp' y hmem
        by_cases hpp : p' = q
        · subst hpp; linarith [hy.1, h.2]
        · rcases hfar p' hp' hpp with h' | h' <;> linarith [hy.1, hy.2, h.1, h.2])
      _ right_mem_uIcc
    rw [this, hfe']; ring
  have hVt : ∀ x, f q + ε / 2 < f x → Dt.V x = D'.V x := fun x hx => (hV't x hx.le).symm
  have he'Tt : D'.flow (f q + ε - c) e' = Dt.flow (f q + ε - c) e' :=
    flow_eq_of_agree_above_neg hf hVt (x := e') (by rw [hfe']; linarith) (T := 32 * ε)
      (by positivity) _ ⟨by rw [hT₁], by rw [hT₁]; linarith⟩
  have he'R : Dt.flow (f q + ε - c) e' ∈
      Dt.flow (f q + ε - c) '' ((Dt.chart q hq).χ '' Dt.rightTube q hq ε δ) := by
    refine ⟨e', ?_, rfl⟩
    rw [← hχt q hq, ← rightTube_eq (D := Dt) hq (hkt q hq)]; exact he'T
  have hT₂ : 0 ≤ f q' - ε - c := by linarith
  have hxab : f x ∈ Icc a b := by
    rw [hfx]; exact ⟨by linarith [hq'ab.1], by linarith [hq'ab.2]⟩
  have hfxT : f (D'.flow (f q' - ε - c) x) = c := by
    have := f_flow_eq_sub_of_avoid_uIcc hf (D := D') (x := x) (T := f q' - ε - c) hxab
      (by rw [hfx]; exact ⟨by linarith [hcab.1], by linarith [hcab.2]⟩) (by
        intro s hs p' hp' hmem
        rw [uIcc_of_le hT₂] at hs
        have hlevm := hsb'' p' hp' _ hmem
        have hup : f (D'.flow s x) ≤ f x := f_flow_le hf x hs.1
        have hlow : f x - s ≤ f (D'.flow s x) := sub_le_f_flow hf x hs.1
        by_cases hpp : p' = q
        · subst hpp; linarith [hlevm.2, hs.2]
        · rcases hfar p' hp' hpp with h' | h'
          · linarith [hlevm.2, hs.2]
          · rcases lt_or_ge (f p') (f q') with h'' | h''
            · exact hmid p' hp' (by linarith) h'' s hs hmem
            · linarith [hlevm.1]) _ right_mem_uIcc
    rw [this, hfx]; ring
  have hxTt : D'.flow (f q' - ε - c) x = Dt.flow (f q' - ε - c) x :=
    flow_eq_of_agree_above_of_le hf hVt (T := f q' - ε - c) (by rw [hfx]; linarith) _
      (right_mem_Icc.2 hT₂)
  have hxL : Dt.flow (f q' - ε - c) x ∈
      Dt.flow (f q' - ε - c) '' ((Dt.chart q' hq').χ '' Dt.leftTube q' hq' ε δ) := by
    refine ⟨x, ?_, rfl⟩
    rw [harmt] at hx
    exact hx
  have hcU' : ∀ y, f y = c → dfV I f D'.V y = -1 := fun y hy =>
    D'.dfV_eq_neg_one_of_level hcab hcU hy
  have heq : D'.flow (f q + ε - c) e' = D'.flow (f q' - ε - c) x := by
    rw [he'x, flow_flow] at hfe'T ⊢
    rw [flow_level_unique hf hcU' hfe'T hfxT]
  exact Set.disjoint_left.1 hδdisj he'R (by rw [← he'Tt, heq, hxTt]; exact hxL)

open Classical in
theorem portPrivate_1aa78447_stageInv.step (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) {S' : Finset M} (hS' : S' ⊆ crit₁)
    {p : M} (hp₁ : p ∈ crit₁) (hpS : p ∉ S') (hpmin : ∀ q ∈ S', f p < f q)
    (hup' : ∀ q' ∈ crit₁, f p < f q' → q' ∈ S') {D : GradientLikeStrip I f a b crit}
    (hD : portPrivate_1aa78447_stageInv D₀ D crit₁ S' ε) :
    ∃ D' : GradientLikeStrip I f a b crit, portPrivate_1aa78447_stageInv D₀ D' crit₁ (insert p S') ε := by
  classical
  have hf := hS.hf
  have hε := hS.hε
  obtain ⟨hD1, hD2, -, hD4, hD5, hD6⟩ := id hD
  have hp : p ∈ crit := ((hS.hcrit₁ p).1 hp₁).1
  have hkp : (D.chart p hp).k = 1 := hD.k_eq_one hS hp₁ hp
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = f p + 33 * ε := ⟨_, rfl⟩
  have hpab := hS.hab p hp
  have hpa : a < f p := by linarith [hpab.1]
  have hcb : c ≤ b := by linarith [hpab.2]
  have hcab : c ∈ Icc a b := ⟨by linarith, hcb⟩
  have hsb : ∀ q hq x, x ∈ D.smallBall q hq → f x ∈ Icc (f q - ε / 4) (f q + ε / 4) :=
    fun _ _ _ hx => hD.f_mem_of_mem_smallBall hS hx
  have hfar : ∀ q ∈ crit, q ≠ p → f q + 40 * ε < f p ∨ f p + 40 * ε < f q := by
    intro q hq hqp
    rcases lt_trichotomy (f q) (f p) with h | h | h
    · exact Or.inl (hS.hgap q hq p hp h)
    · exact absurd (hS.hinj q hq p hp h) hqp
    · exact Or.inr (hS.hgap p hp q hq h)
  have hQ : ∀ q ∈ S', q ∈ crit := fun q hq => ((hS.hcrit₁ q).1 (hS' hq)).1
  have hkQ : ∀ q (hq : q ∈ crit), q ∈ S' → (D.chart q hq).k = 1 :=
    fun q hq hqS => hD.k_eq_one hS (hS' hqS) hq
  have hεR : ∀ q hq, 2 * ε ≤ (D.chart q hq).R ^ 2 := hD.R_sq hS
  have hr₀p : 4 * (D.chart p hp).r₀ ^ 2 < 32 * ε := by linarith [hD.r₀_sq_lt hS p hp]
  have hrmp : 65 * ε < D.rm p hp ^ 2 := by rw [hD4 p hp hpS]; exact hS.hrm p hp
  have hc : f p + 32 * ε < c := by rw [hcdef]; linarith
  have hcQ : ∀ q ∈ S', c ≤ f q - ε := fun q hq => by
    have := hS.hgap p hp q (hQ q hq) (hpmin q hq); rw [hcdef]; linarith
  have hlev : ∀ y, f y ∈ Icc (f p + 32 * ε) c → ∀ p' hp', y ∉ D.smallBall p' hp' := by
    intro y hy p' hp' hmem
    have h := hsb p' hp' y hmem
    by_cases hpp : p' = p
    · subst hpp; linarith [hy.1, h.2]
    · rcases hfar p' hp' hpp with h' | h' <;> linarith [hy.1, hy.2, h.1, h.2]
  obtain ⟨Dt, hDt_chart, hDt_rmp, hDt_rm, hDt_Vge, -, hDt_disj⟩ :=
    exists_twist_stage hf D hp hkp S' hQ hkQ hε hεR hr₀p hrmp hc hcb hcQ hlev
  have htube : ∀ q hq, q ∈ S' → ∃ δ, 0 < δ ∧
      Disjoint (Dt.flow (f p + ε - c) '' ((Dt.chart p hp).χ '' Dt.rightTube p hp ε δ))
        (Dt.flow (f q - ε - c) '' ((Dt.chart q hq).χ '' Dt.leftTube q hq ε δ)) := by
    intro q hq hqS
    exact exists_tube_disjoint Dt p hp q hq hε (by rw [hDt_chart]; exact hεR p hp)
      (by rw [hDt_chart]; exact hεR q hq) (hDt_disj q hq hqS)
  obtain ⟨δ, hδ, hδdisj⟩ := exists_uniform_tube_disjoint Dt hp S' hQ htube
  have hr₀0 := (Dt.chart p hp).hr₀
  obtain ⟨r', hr'0, hr'A, -, hr'ε, hr'δ⟩ :=
    exists_small_radius hr₀0 hr₀0 hε (show 0 < 2 * ε * δ by positivity)
  have hr₀'pos : 0 < r' / 2 := by positivity
  have hle : r' / 2 ≤ (Dt.chart p hp).r₀ := by linarith
  obtain ⟨D', hD'def⟩ : ∃ D' : GradientLikeStrip I f a b crit,
    shrinkAt (D := Dt) hf hr₀'pos hle = D' := ⟨_, rfl⟩
  have hχt : ∀ q hq, (D'.chart q hq).χ = (Dt.chart q hq).χ := fun q hq => by
    rw [← hD'def]; rfl
  have hkt : ∀ q hq, (D'.chart q hq).k = (Dt.chart q hq).k := fun q hq => by
    rw [← hD'def]; rfl
  have hχ' : ∀ q hq, (D'.chart q hq).χ = (D.chart q hq).χ := fun q hq => by
    rw [hχt, hDt_chart]
  have hk' : ∀ q hq, (D'.chart q hq).k = (D.chart q hq).k := fun q hq => by
    rw [hkt, hDt_chart]
  have hR' : ∀ q hq, (D'.chart q hq).R = (D.chart q hq).R := fun q hq => by
    rw [← hD'def, shrinkAt_chart_R, hDt_chart]
  have hR'' : ∀ q hq, (D'.chart q hq).R' = (D.chart q hq).R' := fun q hq => by
    rw [← hD'def, shrinkAt_chart_R', hDt_chart]
  have hr₀'p : (D'.chart p hp).r₀ = r' / 2 := by
    rw [← hD'def]; exact shrinkAt_chart_r₀_self hf hr₀'pos hle
  have hr₀'ne : ∀ q hq, q ≠ p → (D'.chart q hq).r₀ = (D.chart q hq).r₀ := fun q hq h => by
    rw [← hD'def, shrinkAt_chart_r₀_of_ne hf hr₀'pos hle hq h, hDt_chart]
  have hrm' : ∀ q hq, D'.rm q hq = Dt.rm q hq := fun q hq => by rw [← hD'def]; rfl
  have hV't : ∀ x, f p + ε / 2 ≤ f x → D'.V x = Dt.V x := fun x hx => by
    rw [← hD'def, shrinkAt_V]
    exact shrunkV_eq_of_level hr₀'pos hle (ε₁ := ε / 2)
      (by rw [hDt_chart]; linarith [hD.r₀_sq_lt hS p hp]) (Or.inl hx)
  have hV' : ∀ x, f p + 32 * ε ≤ f x → D'.V x = D.V x := fun x hx => by
    rw [hV't x (by linarith), hDt_Vge x hx]
  have hle' : r' / 2 ≤ (D.chart p hp).r₀ := by rw [hDt_chart] at hle; exact hle
  have hsb' : ∀ q hq, D'.smallBall q hq ⊆ D.smallBall q hq := by
    intro q hq
    unfold smallBall
    rw [hχ' q hq]
    refine image_mono fun y (hy : morseNorm n y < _) => show morseNorm n y < _ from
      lt_of_lt_of_le hy ?_
    by_cases h : q = p
    · subst h; rw [hr₀'p]; exact hle'
    · rw [hr₀'ne q hq h]
  have hrm'p : D'.rm p hp ^ 2 = 32 * ε := by rw [hrm', hDt_rmp]
  have hrm'ne : ∀ q hq, q ≠ p → D'.rm q hq = D.rm q hq := fun q hq h => by
    rw [hrm', hDt_rm q hq h]
  have harm : ∀ q' hq', (D'.chart q' hq').χ '' (D'.chart q' hq').leftModelSphere ε =
      (D.chart q' hq').χ '' (D.chart q' hq').leftModelSphere ε := fun q' hq' => by
    rw [hχ' q' hq', leftModelSphere_eq (hk' q' hq')]
  have hsb'' : ∀ q hq x, x ∈ D'.smallBall q hq → f x ∈ Icc (f q - ε / 4) (f q + ε / 4) :=
    fun q hq x hx => hsb q hq x (hsb' q hq hx)
  refine ⟨D', fun q hq => ⟨?_, ?_, ?_, ?_⟩, fun q hq => ?_, fun q hq hqS => ?_,
    fun q hq hqS => ?_, fun q hq hqS q' hq' hq'₁ hlt => ?_, fun q hq hqS q' hq' hq'₁ hlt => ?_⟩
  · rw [hχ']; exact (hD1 q hq).1
  · rw [hk']; exact (hD1 q hq).2.1
  · rw [hR']; exact (hD1 q hq).2.2.1
  · rw [hR'']; exact (hD1 q hq).2.2.2
  · by_cases h : q = p
    · subst h; rw [hr₀'p]; exact hle'.trans (hD2 q hq)
    · rw [hr₀'ne q hq h]; exact hD2 q hq
  · rcases Finset.mem_insert.1 hqS with rfl | hqS
    · exact hrm'p
    · have h : q ≠ p := fun h => hpS (h ▸ hqS)
      rw [hrm'ne q hq h]; exact hD.2.2.1 q hq hqS
  · have h : q ≠ p := fun h => hqS (h ▸ Finset.mem_insert_self p S')
    rw [hrm'ne q hq h]; exact hD4 q hq fun h' => hqS (Finset.mem_insert_of_mem h')
  · rcases Finset.mem_insert.1 hqS with rfl | hqS
    · have hq'S : q' ∈ S' := hup' q' hq'₁ hlt
      have hcq' : c ≤ f q' - ε := hcQ q' hq'S
      have hVt : ∀ x, f q + ε / 2 < f x → Dt.V x = D'.V x := fun x hx => (hV't x hx.le).symm
      have hRq : D'.rightSphere q hq ε (f q + 33 * ε) = Dt.rightSphere q hq ε c := by
        rw [← hcdef]
        refine rightSphere_eq_of_flow_eq (hχt q hq) (hkt q hq) fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := hx
        have hfx : f ((Dt.chart q hq).χ y) = f q + ε :=
          (Dt.chart q hq).f_chart_of_mem_rightModelSphere (by rw [hDt_chart]; exact hεR q hq) hy
        exact flow_eq_of_agree_above_neg hf hVt (x := (Dt.chart q hq).χ y) (by linarith)
          (T := 32 * ε) (by positivity) (f q + ε - c) ⟨by rw [hcdef]; linarith, by linarith⟩
      have hLq : D'.leftSphere q' hq' ε (f q + 33 * ε) = Dt.leftSphere q' hq' ε c := by
        rw [← hcdef]
        refine leftSphere_eq_of_flow_eq (hχt q' hq') (hkt q' hq') fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := hx
        have hfx : f ((Dt.chart q' hq').χ y) = f q' - ε :=
          (Dt.chart q' hq').f_chart_of_mem_leftModelSphere (by rw [hDt_chart]; exact hεR q' hq') hy
        exact flow_eq_of_agree_above_of_le hf hVt (T := f q' - ε - c) (by linarith) _
          (right_mem_Icc.2 (by linarith))
      rw [hRq, hLq]
      exact hDt_disj q' hq' hq'S
    · have h : q ≠ p := fun h => hpS (h ▸ hqS)
      have hfq : f p + 40 * ε < f q := hS.hgap p hp q hq (hpmin q hqS)
      have hV : ∀ x, f p + 32 * ε < f x → D.V x = D'.V x := fun x hx => (hV' x hx.le).symm
      have hRq : D'.rightSphere q hq ε (f q + 33 * ε) = D.rightSphere q hq ε (f q + 33 * ε) := by
        refine rightSphere_eq_of_flow_eq (hχ' q hq) (hk' q hq) fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := hx
        have hfx : f ((D.chart q hq).χ y) = f q + ε :=
          (D.chart q hq).f_chart_of_mem_rightModelSphere (hεR q hq) hy
        exact flow_eq_of_agree_above_neg hf hV (x := (D.chart q hq).χ y) (by linarith)
          (T := 32 * ε) (by positivity) (f q + ε - (f q + 33 * ε)) ⟨by linarith, by linarith⟩
      have hLq : D'.leftSphere q' hq' ε (f q + 33 * ε) = D.leftSphere q' hq' ε (f q + 33 * ε) := by
        refine leftSphere_eq_of_flow_eq (hχ' q' hq') (hk' q' hq') fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := hx
        have hfx : f ((D.chart q' hq').χ y) = f q' - ε :=
          (D.chart q' hq').f_chart_of_mem_leftModelSphere (hεR q' hq') hy
        have hgap' := hS.hgap q hq q' hq' hlt
        exact flow_eq_of_agree_above_of_le hf hV (T := f q' - ε - (f q + 33 * ε)) (by linarith) _
          (right_mem_Icc.2 (by linarith))
      rw [hRq, hLq]
      exact hD5 q hq hqS q' hq' hq'₁ hlt
  · intro x hx t ht hmem
    have hxD : x ∈ (D.chart q' hq').χ '' (D.chart q' hq').leftModelSphere ε := by
      rw [← harm]; exact hx
    have hfx : f x = f q' - ε := hD.f_arm hS hxD
    rcases Finset.mem_insert.1 hqS with rfl | hqS
    · have hq'S : q' ∈ S' := hup' q' hq'₁ hlt
      have hV : ∀ x, f q + 32 * ε < f x → D'.V x = D.V x := fun x hx => hV' x hx.le
      have hflowD : ∀ s ∈ Icc 0 (f q' - ε - c), D.flow s x = D'.flow s x :=
        flow_eq_of_agree_above_of_le hf hV (T := f q' - ε - c)
          (by rw [hfx]; linarith [hcQ q' hq'S])
      have hmem' : D'.flow t x ∈ (D'.chart q hq).χ '' {z | morseNorm n z < r' / 2} := by
        unfold smallBall at hmem; rw [hr₀'p] at hmem; exact hmem
      refine arm_avoids_of_tube hf hε hq hq' hlt hcdef hcab hr'0 hr'ε hr'δ hrm'p hχt hkt
        hV't hsb'' hfar (hS.hab q' hq') (hS.hab q hq) (hδdisj q' hq' hq'S)
        (image_mono (leftModelSphere_subset_leftTube D' q' hq' hδ.le) hx) hfx ?_ ht hmem'
      intro p' hp' hfq hfq' s hs hmem'
      have hp'₁ : p' ∈ crit₁ := hS.hmid p' hp' q hp₁ q' hq'₁ hfq hfq'
      have hp'S : p' ∈ S' := hup' p' hp'₁ hfq
      have := hD6 p' hp' hp'S q' hq' hq'₁ hfq' x hxD s hs.1
      rw [hflowD s hs] at this
      exact this (hsb' p' hp' hmem')
    · have h : q ≠ p := fun h => hpS (h ▸ hqS)
      have hfq : f p + 40 * ε < f q := hS.hgap p hp q hq (hpmin q hqS)
      have hmemD : D'.flow t x ∈ D.smallBall q hq := hsb' q hq hmem
      have hlevm := hsb q hq _ hmemD
      have hV : ∀ x, f p + 32 * ε < f x → D'.V x = D.V x := fun x hx => hV' x hx.le
      have := flow_eq_of_agree_above hf hV (x := x) (t := t) (by linarith [hlevm.1]) t
        (right_mem_Icc.2 ht)
      rw [← this] at hmemD
      exact hD6 q hq hqS q' hq' hq'₁ hlt x hxD t ht hmemD

end GradientLikeStrip

theorem exists_pos_le_forall_finset {α : Type*} (T : Finset α) (g : α → ℝ)
    (hg : ∀ x ∈ T, 0 < g x) : ∃ ρ, 0 < ρ ∧ ∀ x ∈ T, ρ ≤ g x := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert y T _ ih =>
    obtain ⟨ρ, hρ, hρT⟩ := ih fun x hx => hg x (Finset.mem_insert_of_mem hx)
    refine ⟨min ρ (g y), lt_min hρ (hg y (Finset.mem_insert_self y T)), fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hρT x hx)

theorem exists_pos_forall_small_finset {α : Type*} (T : Finset α) (P : α → ℝ → Prop)
    (h : ∀ x ∈ T, ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → P x δ) :
    ∃ δ₀, 0 < δ₀ ∧ ∀ x ∈ T, ∀ δ, 0 < δ → δ ≤ δ₀ → P x δ := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert y T _ ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    obtain ⟨δ₂, hδ₂, h₂⟩ := h y (Finset.mem_insert_self y T)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx δ hδ hδle => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact h₂ δ hδ (hδle.trans (min_le_right _ _))
    · exact h₁ x hx δ hδ (hδle.trans (min_le_left _ _))

namespace GradientLikeStrip

variable [T2Space M] [I.Boundaryless] {D₀ : GradientLikeStrip I f a b crit} {crit₁ : Finset M}
  {ε : ℝ}

theorem portPrivate_1aa78447_exists_stageInv_all (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) :
    ∃ D : GradientLikeStrip I f a b crit, portPrivate_1aa78447_stageInv D₀ D crit₁ crit₁ ε := by
  classical
  have key : ∀ N : ℕ, ∀ S : Finset M, S ⊆ crit₁ →
      (∀ q ∈ S, ∀ q' ∈ crit₁, f q < f q' → q' ∈ S) → S.card = N →
      ∃ D : GradientLikeStrip I f a b crit, portPrivate_1aa78447_stageInv D₀ D crit₁ S ε := by
    intro N
    induction N with
    | zero =>
      intro S _ _ hcard
      rw [Finset.card_eq_zero] at hcard
      subst hcard
      exact ⟨D₀, portPrivate_1aa78447_stageInv.base hS⟩
    | succ N ih =>
      intro S hSsub hup hcard
      have hne : S.Nonempty := by rw [← Finset.card_pos, hcard]; exact Nat.succ_pos N
      obtain ⟨p, hpS, hpmin⟩ := Finset.exists_min_image S f hne
      have hS'sub : S.erase p ⊆ crit₁ := (Finset.erase_subset p S).trans hSsub
      have hup' : ∀ q ∈ S.erase p, ∀ q' ∈ crit₁, f q < f q' → q' ∈ S.erase p := by
        intro q hq q' hq' hlt
        have hqS := (Finset.mem_erase.1 hq).2
        refine Finset.mem_erase.2 ⟨fun h => ?_, hup q hqS q' hq' hlt⟩
        subst h
        exact absurd (hpmin q hqS) (not_le.2 hlt)
      have hcard' : (S.erase p).card = N := by
        rw [Finset.card_erase_of_mem hpS, hcard]; rfl
      obtain ⟨D, hD⟩ := ih (S.erase p) hS'sub hup' hcard'
      have hp₁ : p ∈ crit₁ := hSsub hpS
      have hpS' : p ∉ S.erase p := fun h => (Finset.mem_erase.1 h).1 rfl
      have hpmin' : ∀ q ∈ S.erase p, f p < f q := by
        intro q hq
        obtain ⟨hqp, hqS⟩ := Finset.mem_erase.1 hq
        rcases (hpmin q hqS).lt_or_eq with h | h
        · exact h
        · exact absurd (hS.hinj p ((hS.hcrit₁ p).1 hp₁).1 q ((hS.hcrit₁ q).1 (hSsub hqS)).1 h)
            (Ne.symm hqp)
      have hup'' : ∀ q' ∈ crit₁, f p < f q' → q' ∈ S.erase p := by
        intro q' hq' hlt
        refine Finset.mem_erase.2 ⟨fun h => ?_, hup p hpS q' hq' hlt⟩
        subst h; exact lt_irrefl _ hlt
      obtain ⟨D', hD'⟩ := hD.step hS hS'sub hp₁ hpS' hpmin' hup''
      rw [Finset.insert_erase hpS] at hD'
      exact ⟨D', hD'⟩
  exact key crit₁.card crit₁ le_rfl (fun _ _ q' hq' _ => hq') rfl

omit [T2Space M] [I.Boundaryless] in
theorem exists_leftTube_subset_open (D : GradientLikeStrip I f a b crit) (q : M) (hq : q ∈ crit)
    {ε : ℝ} (hε : 0 < ε) {W : Set (Fin n → ℝ)} (hW : IsOpen W)
    (hSW : (D.chart q hq).leftModelSphere ε ⊆ W) :
    ∃ δ, 0 < δ ∧ D.leftTube q hq ε δ ⊆ W := by
  obtain ⟨η, hη, hth⟩ :=
    ((D.chart q hq).isCompact_leftModelSphere ε).exists_thickening_subset_open hW hSW
  set δ := min 1 (η ^ 2 * ε / (2 * ε + 1)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ η ^ 2 * ε / (2 * ε + 1) := min_le_right _ _
  have hkey : δ + δ ^ 2 / (2 * ε) < η ^ 2 := by
    have h1 : δ ^ 2 ≤ δ := by nlinarith
    have h2 : δ * (2 * ε + 1) ≤ η ^ 2 * ε := by
      rw [le_div_iff₀ (by positivity)] at hδ2; exact hδ2
    have h3 : δ + δ ^ 2 / (2 * ε) ≤ δ + δ / (2 * ε) := by gcongr
    have h4 : δ + δ / (2 * ε) = δ * (2 * ε + 1) / (2 * ε) := by field_simp
    have h5 : δ * (2 * ε + 1) / (2 * ε) ≤ η ^ 2 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h6 : 0 < η ^ 2 := by positivity
    linarith
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  obtain ⟨y₀, hy₀, hyy₀⟩ := (D.chart q hq).exists_near_leftModelSphere hε hδpos.le hy.1 hy.2
  have hdist : dist y y₀ < η := by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (morseNorm_piNorm_le (y - y₀)) ?_
    exact lt_of_pow_lt_pow_left₀ 2 hη.le (hyy₀.trans_lt hkey)
  exact hth (Metric.mem_thickening_iff.2 ⟨y₀, hy₀, hdist⟩)

def halfBalls (D : GradientLikeStrip I f a b crit) : Set M :=
  ⋃ m : {m : M // m ∈ crit}, (D.chart m.1 m.2).χ '' {z | morseNorm n z ≤ (D.chart m.1 m.2).r₀ / 2}

omit [I.Boundaryless] in
theorem isClosed_halfBalls (D : GradientLikeStrip I f a b crit) : IsClosed D.halfBalls :=
  (isCompact_iUnion fun m : {m : M // m ∈ crit} => D.isCompact_halfBall m.1 m.2).isClosed

omit [T2Space M] [I.Boundaryless] in
theorem mem_halfBalls_iff (D : GradientLikeStrip I f a b crit) {x : M} :
    x ∈ D.halfBalls ↔ ∃ m hm, x ∈ (D.chart m hm).χ '' {z | morseNorm n z ≤ (D.chart m hm).r₀ / 2} := by
  simp only [halfBalls, mem_iUnion]
  exact ⟨fun ⟨m, h⟩ => ⟨m.1, m.2, h⟩, fun ⟨m, hm, h⟩ => ⟨⟨m, hm⟩, h⟩⟩

theorem portPrivate_1aa78447_stageInv.f_mem_of_mem_halfBall {D : GradientLikeStrip I f a b crit} {S : Finset M}
    (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) (hD : portPrivate_1aa78447_stageInv D₀ D crit₁ S ε) {m : M} {hm : m ∈ crit} {x : M}
    (hx : x ∈ (D.chart m hm).χ '' {z | morseNorm n z ≤ (D.chart m hm).r₀ / 2}) :
    f x ∈ Icc (f m - ε / 16) (f m + ε / 16) := by
  have h := (D.chart m hm).f_mem_Icc_of_mem_image_le
    (by linarith [D.r₀_lt_R m hm, (D.chart m hm).hr₀]) hx
  have h1 := hD.r₀_sq_lt hS m hm
  have h2 : ((D.chart m hm).r₀ / 2) ^ 2 = (D.chart m hm).r₀ ^ 2 / 4 := by ring
  rw [h2] at h
  constructor <;> linarith [h.1, h.2]

theorem portPrivate_1aa78447_stageInv.halfBall_subset_smallBall {D : GradientLikeStrip I f a b crit} {S : Finset M}
    (_hD : portPrivate_1aa78447_stageInv D₀ D crit₁ S ε) (m : M) (hm : m ∈ crit) :
    (D.chart m hm).χ '' {z | morseNorm n z ≤ (D.chart m hm).r₀ / 2} ⊆ D.smallBall m hm :=
  image_mono fun z (hz : morseNorm n z ≤ _) => show morseNorm n z < _ by
    linarith [(D.chart m hm).hr₀]

theorem exists_pair_tube (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) {D : GradientLikeStrip I f a b crit}
    (hD : portPrivate_1aa78447_stageInv D₀ D crit₁ crit₁ ε) {q q' : M} (hq : q ∈ crit) (hq' : q' ∈ crit)
    (hq₁ : q ∈ crit₁) (hq'₁ : q' ∈ crit₁) (hlt : f q < f q') :
    ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
      Disjoint (D.flow (f q + ε - (f q + 33 * ε)) '' ((D.chart q hq).χ '' D.rightTube q hq ε δ))
        (D.flow (f q' - ε - (f q + 33 * ε)) '' ((D.chart q' hq').χ '' D.leftTube q' hq' ε δ)) ∧
      ∀ y ∈ D.leftTube q' hq' ε δ, ∀ s ∈ Icc 0 (f q' - ε - (f q + 33 * ε)),
        D.flow s ((D.chart q' hq').χ y) ∉ D.halfBalls := by
  have hf := hS.hf
  have hε := hS.hε
  obtain ⟨-, -, -, -, hD5, hD6⟩ := id hD
  have hgap := hS.hgap q hq q' hq' hlt
  obtain ⟨δ₁, hδ₁, hdisj₁⟩ := exists_tube_disjoint D q hq q' hq' hε (hD.R_sq hS q hq)
    (hD.R_sq hS q' hq') (hD5 q hq hq₁ q' hq' hq'₁ hlt)
  set T := f q' - ε - (f q + 33 * ε) with hT
  have hT0 : 0 ≤ T := by rw [hT]; linarith
  set d := D.chart q' hq' with hd
  set W : Set (Fin n → ℝ) := {y | y ∈ Metric.ball (0 : Fin n → ℝ) d.R' ∧
    ∀ s ∈ Icc 0 T, D.flow s (d.χ y) ∉ D.halfBalls} with hW
  have hK := D.isClosed_halfBalls
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    rintro y₀ ⟨hy₀b, hy₀⟩
    have hχc : ContinuousAt d.χ y₀ :=
      d.χ.continuousOn.continuousAt (d.χ.open_source.mem_nhds (d.hball hy₀b))
    have hG : ∀ s, ContinuousAt (fun z : (Fin n → ℝ) × ℝ => D.flow z.2 (d.χ z.1)) (y₀, s) :=
      fun s => D.continuous_flow_joint.continuousAt.comp
        (continuousAt_snd.prodMk (hχc.comp continuousAt_fst))
    have hev : ∀ s ∈ Icc (0 : ℝ) T, ∀ᶠ z : (Fin n → ℝ) × ℝ in 𝓝 (y₀, s),
        D.flow z.2 (d.χ z.1) ∉ D.halfBalls := fun s hs =>
      (hG s).eventually_mem (hK.isOpen_compl.mem_nhds (hy₀ s hs))
    have h1 := isCompact_Icc.eventually_forall_of_forall_eventually
      (P := fun (y : Fin n → ℝ) (s : ℝ) => D.flow s (d.χ y) ∉ D.halfBalls) hev
    filter_upwards [h1, Metric.isOpen_ball.mem_nhds hy₀b] with y hy hyb
    exact ⟨hyb, hy⟩
  have hSW : d.leftModelSphere ε ⊆ W := by
    intro y hy
    refine ⟨d.mem_ball_of_le (d.morseNorm_le_R_of_mem_leftModelSphere (hD.R_sq hS q' hq') hy),
      fun s hs hmem => ?_⟩
    obtain ⟨m, hm, hmem⟩ := D.mem_halfBalls_iff.1 hmem
    have hfx : f (d.χ y) = f q' - ε := d.f_chart_of_mem_leftModelSphere (hD.R_sq hS q' hq') hy
    have hlev := hD.f_mem_of_mem_halfBall hS hmem
    have hup : f (D.flow s (d.χ y)) ≤ f q' - ε := hfx ▸ f_flow_le hf _ hs.1
    have hlow : f q + 33 * ε ≤ f (D.flow s (d.χ y)) := by
      have := sub_le_f_flow (D := D) hf (d.χ y) hs.1
      rw [hfx] at this; linarith [hs.2]
    by_cases hm₁ : m ∈ crit₁ ∧ f m < f q'
    · exact hD6 m hm hm₁.1 q' hq' hq'₁ hm₁.2 (d.χ y) ⟨y, hy, rfl⟩ s hs.1
        (hD.halfBall_subset_smallBall m hm hmem)
    · rcases lt_or_ge (f m) (f q') with h | h
      · have hm₁' : m ∉ crit₁ := fun h' => hm₁ ⟨h', h⟩
        rcases lt_trichotomy (f m) (f q) with h' | h' | h'
        · linarith [hlev.2]
        · exact hm₁' (hS.hinj m hm q hq h' ▸ hq₁)
        · exact hm₁' (hS.hmid m hm q hq₁ q' hq'₁ h' h)
      · linarith [hlev.1]
  obtain ⟨δ₂, hδ₂, hδ₂W⟩ := D.exists_leftTube_subset_open q' hq' hε hWo hSW
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδle => ⟨?_, fun y hy s hs => ?_⟩⟩
  · exact hdisj₁.mono
      (image_mono (image_mono (rightTube_mono' _ _ _ _ (hδle.trans (min_le_left _ _)))))
      (image_mono (image_mono (leftTube_mono' _ _ _ _ (hδle.trans (min_le_left _ _)))))
  · exact (hδ₂W (leftTube_mono' _ _ _ _ (hδle.trans (min_le_right _ _)) hy)).2 s hs

omit [T2Space M] [I.Boundaryless] in
theorem f_mem_of_mem_rightTube (D : GradientLikeStrip I f a b crit) {q : M} {hq : q ∈ crit}
    {ε δ : ℝ} (hδ : δ ≤ ε) (hR : 4 * ε ≤ (D.chart q hq).R ^ 2) {y : Fin n → ℝ}
    (hy : y ∈ D.rightTube q hq ε δ) :
    morseNorm n y ≤ (D.chart q hq).R ∧ f ((D.chart q hq).χ y) = f q + ε := by
  have h1 := ModelField.nf_sub_eq (D.chart q hq).hk (f q) y
  rw [hy.1] at h1
  have hsq := morseNorm_sq_eq_negPart_add_posPart (D.chart q hq).hk y
  have hyR : morseNorm n y ≤ (D.chart q hq).R := by
    refine MorseNormalChart.morseNorm_le_of_sq_le (D.chart q hq).R_pos.le ?_
    linarith [hy.2]
  exact ⟨hyR, by rw [(D.chart q hq).hnorm y hyR]; exact hy.1⟩

omit [T2Space M] [I.Boundaryless] in
theorem f_mem_of_mem_leftTube (D : GradientLikeStrip I f a b crit) {q : M} {hq : q ∈ crit}
    {ε δ : ℝ} (hδ : δ ≤ ε) (hR : 4 * ε ≤ (D.chart q hq).R ^ 2) {y : Fin n → ℝ}
    (hy : y ∈ D.leftTube q hq ε δ) :
    morseNorm n y ≤ (D.chart q hq).R ∧ f ((D.chart q hq).χ y) = f q - ε := by
  have h1 := ModelField.nf_sub_eq (D.chart q hq).hk (f q) y
  rw [hy.1] at h1
  have hsq := morseNorm_sq_eq_negPart_add_posPart (D.chart q hq).hk y
  have hyR : morseNorm n y ≤ (D.chart q hq).R := by
    refine MorseNormalChart.morseNorm_le_of_sq_le (D.chart q hq).R_pos.le ?_
    linarith [hy.2]
  exact ⟨hyR, by rw [(D.chart q hq).hnorm y hyR]; exact hy.1⟩

theorem exists_gradientLikeStrip_disjoint_tubes (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) {D : GradientLikeStrip I f a b crit}
    (hD : portPrivate_1aa78447_stageInv D₀ D crit₁ crit₁ ε) :
    ∃ E : GradientLikeStrip I f a b crit, ∃ ρ, 0 < ρ ∧ 4 * ρ ^ 2 < ε ∧
      (∀ q hq, (E.chart q hq).χ = (D₀.chart q hq).χ ∧ (E.chart q hq).k = (D₀.chart q hq).k ∧
        (E.chart q hq).R = (D₀.chart q hq).R ∧ (E.chart q hq).R' = (D₀.chart q hq).R') ∧
      (∀ q hq, (E.chart q hq).r₀ = ρ / 2) ∧
      (∀ q hq, q ∈ crit₁ → E.rm q hq ^ 2 = 32 * ε) ∧
      (∀ q hq, q ∉ crit₁ → E.rm q hq = D₀.rm q hq) ∧
      ∃ δ₀, 0 < δ₀ ∧ δ₀ ≤ ε ∧ (2 * ρ) ^ 4 ≤ 2 * ε * δ₀ ∧
        ∀ q hq q' hq', q ∈ crit₁ → q' ∈ crit₁ → f q < f q' →
          Disjoint
            (E.flow (f q + ε - (f q + 33 * ε)) '' ((E.chart q hq).χ '' E.rightTube q hq ε δ₀))
            (E.flow (f q' - ε - (f q + 33 * ε)) ''
              ((E.chart q' hq').χ '' E.leftTube q' hq' ε δ₀)) := by
  classical
  have hf := hS.hf
  have hε := hS.hε
  obtain ⟨hD1, -, hD3, hD4, -, -⟩ := id hD
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := exists_pos_forall_small_finset (crit₁ ×ˢ crit₁)
    (fun x δ => ∀ (hq : x.1 ∈ crit) (hq' : x.2 ∈ crit), f x.1 < f x.2 →
      Disjoint
        (D.flow (f x.1 + ε - (f x.1 + 33 * ε)) '' ((D.chart x.1 hq).χ '' D.rightTube x.1 hq ε δ))
        (D.flow (f x.2 - ε - (f x.1 + 33 * ε)) ''
          ((D.chart x.2 hq').χ '' D.leftTube x.2 hq' ε δ)) ∧
      ∀ y ∈ D.leftTube x.2 hq' ε δ, ∀ s ∈ Icc 0 (f x.2 - ε - (f x.1 + 33 * ε)),
        D.flow s ((D.chart x.2 hq').χ y) ∉ D.halfBalls) (by
      rintro ⟨q, q'⟩ hx
      obtain ⟨hq₁, hq'₁⟩ := Finset.mem_product.1 hx
      by_cases hlt : f q < f q'
      · obtain ⟨δ₀, hδ₀, h⟩ := exists_pair_tube hS hD ((hS.hcrit₁ q).1 hq₁).1
          ((hS.hcrit₁ q').1 hq'₁).1 hq₁ hq'₁ hlt
        exact ⟨δ₀, hδ₀, fun δ hδ hδle _ _ _ => h δ hδ hδle⟩
      · exact ⟨1, one_pos, fun _ _ _ _ _ h => absurd h hlt⟩)
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℝ, δ₀ = min δ₁ ε := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; exact lt_min hδ₁ hε
  have hδ₀ε : δ₀ ≤ ε := by rw [hδ₀def]; exact min_le_right _ _
  have hδ₀₁ : δ₀ ≤ δ₁ := by rw [hδ₀def]; exact min_le_left _ _
  have hpair : ∀ q hq q' hq', q ∈ crit₁ → q' ∈ crit₁ → f q < f q' →
      Disjoint
        (D.flow (f q + ε - (f q + 33 * ε)) '' ((D.chart q hq).χ '' D.rightTube q hq ε δ₀))
        (D.flow (f q' - ε - (f q + 33 * ε)) '' ((D.chart q' hq').χ '' D.leftTube q' hq' ε δ₀)) ∧
      ∀ y ∈ D.leftTube q' hq' ε δ₀, ∀ s ∈ Icc 0 (f q' - ε - (f q + 33 * ε)),
        D.flow s ((D.chart q' hq').χ y) ∉ D.halfBalls :=
    fun q hq q' hq' hq₁ hq'₁ hlt =>
      hδ₁P (q, q') (Finset.mem_product.2 ⟨hq₁, hq'₁⟩) δ₀ hδ₀ hδ₀₁ hq hq' hlt
  obtain ⟨ρ₁, hρ₁, hρ₁le⟩ := exists_pos_le_forall_finset crit.attach
    (fun m => (D.chart m.1 m.2).r₀) fun m _ => (D.chart m.1 m.2).hr₀
  obtain ⟨ρ, hρ, hρA, -, hρε, hρδ⟩ := exists_small_radius hρ₁ hρ₁ (show 0 < ε / 4 by positivity)
    (show 0 < 2 * ε * δ₀ / 16 by positivity)
  have hle : ∀ m hm, ρ ≤ (D.chart m hm).r₀ := fun m hm =>
    hρA.trans (hρ₁le ⟨m, hm⟩ (Finset.mem_attach _ _))
  obtain ⟨E, hE1, hE2, hE3, hE4⟩ := exists_shrinkAll hf D hρ hle
  have hV : ∀ x ∈ D.halfBallsᶜ, D.V x = E.V x := fun x hx =>
    (hE4 x fun m hm h => hx (D.mem_halfBalls_iff.2 ⟨m, hm, h⟩)).symm
  have hKo : IsOpen D.halfBallsᶜ := D.isClosed_halfBalls.isOpen_compl
  refine ⟨E, ρ, hρ, by linarith, fun q hq => ?_, hE2, fun q hq hq₁ => ?_, fun q hq hq₁ => ?_,
    δ₀, hδ₀, hδ₀ε, ?_, fun q hq q' hq' hq₁ hq'₁ hlt => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hE1 q hq
    obtain ⟨h1', h2', h3', h4'⟩ := hD1 q hq
    exact ⟨h1.trans h1', h2.trans h2', h3.trans h3', h4.trans h4'⟩
  · rw [hE3, hD3 q hq hq₁]
  · rw [hE3, hD4 q hq hq₁]
  · have : (2 * ρ) ^ 4 = 16 * ρ ^ 4 := by ring
    rw [this]; linarith
  obtain ⟨hdisj, havoid⟩ := hpair q hq q' hq' hq₁ hq'₁ hlt
  have hR4 : ∀ m hm, m ∈ crit₁ → 4 * ε ≤ (D.chart m hm).R ^ 2 := fun m hm hm₁ => by
    have h1 : D.rm m hm ^ 2 ≤ (D.chart m hm).R ^ 2 :=
      pow_le_pow_left₀ (D.rm_pos m hm).le (D.hrm m hm).2 2
    rw [hD3 m hm hm₁] at h1; linarith
  have hgap := hS.hgap q hq q' hq' hlt
  have hfar : ∀ m ∈ crit, m ≠ q → f m + 40 * ε < f q ∨ f q + 40 * ε < f m := by
    intro m hm hmq
    rcases lt_trichotomy (f m) (f q) with h | h | h
    · exact Or.inl (hS.hgap m hm q hq h)
    · exact absurd (hS.hinj m hm q hq h) hmq
    · exact Or.inr (hS.hgap q hq m hm h)
  have hRT : E.flow (f q + ε - (f q + 33 * ε)) '' ((E.chart q hq).χ '' E.rightTube q hq ε δ₀) =
      D.flow (f q + ε - (f q + 33 * ε)) '' ((D.chart q hq).χ '' D.rightTube q hq ε δ₀) := by
    rw [(hE1 q hq).1, rightTube_eq (D := D) hq (hE1 q hq).2.1]
    refine image_congr fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨-, hfy⟩ := D.f_mem_of_mem_rightTube hδ₀ε (hR4 q hq hq₁) hy
    refine flow_eq_of_agree_neg (D₁ := D) (D₂ := E) hKo hV (T := 32 * ε) (by positivity)
      (fun s hs hmem => ?_) _ ⟨by linarith, by linarith⟩
    obtain ⟨m, hm, hmem⟩ := D.mem_halfBalls_iff.1 hmem
    have hlev := hD.f_mem_of_mem_halfBall hS hmem
    have h1 := le_f_flow_of_nonpos (D := D) hf ((D.chart q hq).χ y) hs.2.le
    have h2 := f_flow_le_sub_of_nonpos (D := D) hf ((D.chart q hq).χ y) hs.2.le
    rw [hfy] at h1 h2
    by_cases hmq : m = q
    · subst hmq; linarith [hlev.2]
    · rcases hfar m hm hmq with h | h <;> linarith [hlev.1, hlev.2, hs.1]
  have hLT : E.flow (f q' - ε - (f q + 33 * ε)) ''
        ((E.chart q' hq').χ '' E.leftTube q' hq' ε δ₀) =
      D.flow (f q' - ε - (f q + 33 * ε)) '' ((D.chart q' hq').χ '' D.leftTube q' hq' ε δ₀) := by
    rw [(hE1 q' hq').1, leftTube_eq (D := D) hq' (hE1 q' hq').2.1]
    refine image_congr fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    exact flow_eq_of_agree (D₁ := D) (D₂ := E) hKo hV
      (fun s hs => havoid y hy s (Ico_subset_Icc_self hs)) _ (right_mem_Icc.2 (by linarith))
  rw [hRT, hLT]
  exact hdisj

theorem no_ball_of_tube_point (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) {E : GradientLikeStrip I f a b crit}
    {ρ : ℝ} (hρ : 0 < ρ) (hρε : 4 * ρ ^ 2 < ε)
    (hE2 : ∀ q hq, (E.chart q hq).r₀ = ρ / 2)
    (hE3 : ∀ q hq, q ∈ crit₁ → E.rm q hq ^ 2 = 32 * ε)
    {δ₀ : ℝ} (hδ₀ε : δ₀ ≤ ε) (hρδ : (2 * ρ) ^ 4 ≤ 2 * ε * δ₀)
    (htube : ∀ q hq q' hq', q ∈ crit₁ → q' ∈ crit₁ → f q < f q' →
      Disjoint
        (E.flow (f q + ε - (f q + 33 * ε)) '' ((E.chart q hq).χ '' E.rightTube q hq ε δ₀))
        (E.flow (f q' - ε - (f q + 33 * ε)) '' ((E.chart q' hq').χ '' E.leftTube q' hq' ε δ₀)))
    {q' : M} (hq' : q' ∈ crit) (hq'₁ : q' ∈ crit₁) {e : M}
    (he : e ∈ (E.chart q' hq').χ '' E.leftTube q' hq' ε δ₀) :
    ∀ q hq, q ∈ crit₁ → f q < f q' → ∀ t, 0 ≤ t →
      E.flow t e ∉ (E.chart q hq).χ '' {z | morseNorm n z < ρ} := by
  classical
  have hf := hS.hf
  have hε := hS.hε
  have hR4 : ∀ m hm, m ∈ crit₁ → 4 * ε ≤ (E.chart m hm).R ^ 2 := fun m hm hm₁ => by
    have h1 : E.rm m hm ^ 2 ≤ (E.chart m hm).R ^ 2 :=
      pow_le_pow_left₀ (E.rm_pos m hm).le (E.hrm m hm).2 2
    rw [hE3 m hm hm₁] at h1; linarith
  have hfe : f e = f q' - ε := by
    obtain ⟨y, hy, rfl⟩ := he
    exact (E.f_mem_of_mem_leftTube hδ₀ε (hR4 q' hq' hq'₁) hy).2
  have hsbE : ∀ m hm x, x ∈ E.smallBall m hm → f x ∈ Icc (f m - ε / 4) (f m + ε / 4) := by
    intro m hm x hx
    have h := E.f_mem_Icc_of_mem_smallBall hx
    rw [hE2 m hm] at h
    have : (ρ / 2) ^ 2 = ρ ^ 2 / 4 := by ring
    rw [this] at h
    constructor <;> linarith [h.1, h.2]
  have hfar : ∀ q, q ∈ crit → ∀ m ∈ crit, m ≠ q → f m + 40 * ε < f q ∨ f q + 40 * ε < f m := by
    intro q hq m hm hmq
    rcases lt_trichotomy (f m) (f q) with h | h | h
    · exact Or.inl (hS.hgap m hm q hq h)
    · exact absurd (hS.hinj m hm q hq h) hmq
    · exact Or.inr (hS.hgap q hq m hm h)
  intro q hq hq₁ hlt t ht hmem
  set A : Finset M := crit₁.filter fun m => f q ≤ f m ∧ f m < f q' ∧
    ∃ t, 0 ≤ t ∧ ∃ hm : m ∈ crit, E.flow t e ∈ (E.chart m hm).χ '' {z | morseNorm n z < ρ}
    with hA
  have hqA : q ∈ A := Finset.mem_filter.2 ⟨hq₁, le_rfl, hlt, t, ht, hq, hmem⟩
  obtain ⟨m₀, hm₀A, hm₀max⟩ := Finset.exists_max_image A f ⟨q, hqA⟩
  obtain ⟨hm₀₁, -, hm₀lt, t₀, ht₀, hm₀, hmem₀⟩ := Finset.mem_filter.1 hm₀A
  have hm₀ab := hS.hab m₀ hm₀
  refine arm_avoids_of_tube (D' := E) (Dt := E) hf hε hm₀ hq' hm₀lt (c := f m₀ + 33 * ε) rfl
    ⟨by linarith [hm₀ab.1], by linarith [hm₀ab.2]⟩ (r' := 2 * ρ) (by positivity) (by nlinarith)
    hρδ (hE3 m₀ hm₀ hm₀₁) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) hsbE (hfar m₀ hm₀)
    (hS.hab q' hq') hm₀ab (htube m₀ hm₀ q' hq' hm₀₁ hq'₁ hm₀lt) he hfe ?_ ht₀ ?_
  · intro p' hp' hfm hfq' s hs hmem'
    have hp'₁ : p' ∈ crit₁ := hS.hmid p' hp' m₀ hm₀₁ q' hq'₁ hfm hfq'
    have hp'A : p' ∈ A := Finset.mem_filter.2 ⟨hp'₁, by linarith [hm₀max q hqA], hfq', s, hs.1,
      hp', image_mono (fun z (hz : morseNorm n z < _) => show morseNorm n z < ρ by
        rw [hE2 p' hp'] at hz; linarith) hmem'⟩
    exact absurd (hm₀max p' hp'A) (not_le.2 hfm)
  · have : 2 * ρ / 2 = ρ := by ring
    rw [this]; exact hmem₀

theorem exists_allPairs_of_setup (hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε) :
    ∃ E : GradientLikeStrip I f a b crit, ∃ r', 0 < r' ∧ r' ^ 2 < ε ∧
      (∀ q hq, (E.chart q hq).R = (D₀.chart q hq).R ∧ (E.chart q hq).r₀ < r' ∧
        24 * ε < E.rm q hq ^ 2) ∧
      (∀ p hp q hq, (E.chart p hp).k = 1 → (E.chart q hq).k = 1 → f p < f q →
        ∀ x ∈ (E.chart p hp).χ '' {y | morseNorm n y < r'}, ∀ t,
          E.flow t x ∉ (E.chart q hq).χ '' {y | morseNorm n y < r'}) ∧
      (∀ p hp q hq, (E.chart p hp).k = 1 → (E.chart q hq).k = 1 → f p < f q →
        ∀ x ∈ (E.chart q hq).χ '' (E.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
          E.flow t x ∉ (E.chart p hp).χ '' {y | morseNorm n y < r'}) := by
  have hf := hS.hf
  have hε := hS.hε
  obtain ⟨D, hD⟩ := portPrivate_1aa78447_exists_stageInv_all hS
  obtain ⟨E, ρ, hρ, hρε, hE1, hE2, hE3, hE4, δ₀, hδ₀, hδ₀ε, hρδ, htube⟩ :=
    exists_gradientLikeStrip_disjoint_tubes hS hD
  have hk₁ : ∀ q hq, (E.chart q hq).k = 1 ↔ q ∈ crit₁ := fun q hq => by
    rw [hS.hcrit₁, ← (E.chart q hq).hkidx]; exact ⟨fun h => ⟨hq, h⟩, fun h => h.2⟩
  have hR4 : ∀ m hm, m ∈ crit₁ → 4 * ε ≤ (E.chart m hm).R ^ 2 := fun m hm hm₁ => by
    have h1 : E.rm m hm ^ 2 ≤ (E.chart m hm).R ^ 2 :=
      pow_le_pow_left₀ (E.rm_pos m hm).le (E.hrm m hm).2 2
    rw [hE3 m hm hm₁] at h1; linarith
  have hnoball : ∀ q' hq', q' ∈ crit₁ → ∀ e, e ∈ (E.chart q' hq').χ '' E.leftTube q' hq' ε δ₀ →
      ∀ q hq, q ∈ crit₁ → f q < f q' → ∀ t, 0 ≤ t →
        E.flow t e ∉ (E.chart q hq).χ '' {z | morseNorm n z < ρ} :=
    fun q' hq' hq'₁ _ he => no_ball_of_tube_point hS hρ hρε hE2 hE3 hδ₀ε hρδ htube hq' hq'₁ he
  refine ⟨E, ρ, hρ, by linarith, fun q hq => ⟨(hE1 q hq).2.2.1, by rw [hE2]; linarith, ?_⟩,
    fun p hp q hq hkp hkq hlt x hx t hmem => ?_, fun p hp q hq hkp hkq hlt x hx t ht => ?_⟩
  · by_cases hq₁ : q ∈ crit₁
    · rw [hE3 q hq hq₁]; linarith
    · rw [hE4 q hq hq₁]; linarith [hS.hrm q hq]
  · have hp₁ := (hk₁ p hp).1 hkp
    have hq₁ := (hk₁ q hq).1 hkq
    have hgap := hS.hgap p hp q hq hlt
    have hρR : ρ ≤ (E.chart q hq).R := by
      have h := hR4 q hq hq₁
      nlinarith [(E.chart q hq).R_pos]
    have hρR' : ρ ≤ (E.chart p hp).R := by
      have h := hR4 p hp hp₁
      nlinarith [(E.chart p hp).R_pos]
    obtain ⟨x', hx'⟩ : ∃ x' : M, E.flow t x = x' := ⟨_, rfl⟩
    have hxx' : E.flow (-t) x' = x := by rw [← hx', flow_neg_flow]
    rw [hx'] at hmem
    rw [← hxx'] at hx
    clear hx' hxx'
    have hfx := (E.chart q hq).f_mem_Icc_of_mem_image_lt hρR hmem
    have hft := (E.chart p hp).f_mem_Icc_of_mem_image_lt hρR' hx
    have ht : 0 ≤ -t := by
      by_contra hneg
      have := le_f_flow_of_nonpos (D := E) hf x' (not_le.1 hneg).le
      linarith [hfx.1, hft.2]
    obtain ⟨y, hy, rfl⟩ := hmem
    have hy : morseNorm n y < ρ := hy
    have hysq : morseNorm n y ^ 2 < ρ ^ 2 :=
      pow_lt_pow_left₀ hy (ModelField.morseNorm_nonneg y) two_ne_zero
    have hsq := morseNorm_sq_eq_negPart_add_posPart (E.chart q hq).hk y
    have hu0 := sq_nonneg ‖negPart (E.chart q hq).hk y‖
    have hv0 := sq_nonneg ‖posPart (E.chart q hq).hk y‖
    have hrmq := hE3 q hq hq₁
    have hrmq0 := E.rm_pos q hq
    have hyrm : morseNorm n y < E.rm q hq := by
      apply lt_of_pow_lt_pow_left₀ 2 hrmq0.le; rw [hrmq]; linarith
    have hyR : morseNorm n y ≤ (E.chart q hq).R := hyrm.le.trans (E.hrm q hq).2
    have hnfy : morseNormalForm (E.chart q hq).hk (f q) y = f ((E.chart q hq).χ y) :=
      ((E.chart q hq).hnorm y hyR).symm
    have hpq : p ≠ q := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    have hu : negPart (E.chart q hq).hk y ≠ 0 := by
      intro hu0'
      have h1 := flow_mem_of_negPart_eq_zero (D := E) hq hyrm hu0' ht
      have h2 : E.flow (-t) ((E.chart q hq).χ y) ∈
          (E.chart q hq).χ '' Metric.ball 0 (E.chart q hq).R' :=
        image_mono (fun z hz => (E.chart q hq).mem_ball_of_le (hz.1.trans hyR)) h1
      have h3 : E.flow (-t) ((E.chart q hq).χ y) ∈
          (E.chart p hp).χ '' Metric.ball 0 (E.chart p hp).R' :=
        image_mono (fun z (hz : morseNorm n z < ρ) =>
          (E.chart p hp).mem_ball_of_le (hz.le.trans hρR')) hx
      exact Set.disjoint_left.1 (E.disjoint q hq p hp (Ne.symm hpq)) h2 h3
    obtain ⟨t₁, ht₁, hft₁, hstay, hprod⟩ := exists_exit_desc (D := E) hf hq hε (y := y)
      (by rw [hrmq]; linarith) hu (by rw [hnfy]; linarith [hfx.1])
    obtain ⟨y₁, hy₁, hy₁e⟩ := hstay t₁ (right_mem_Icc.2 ht₁)
    have hy₁sq : morseNorm n y₁ ^ 2 ≤ 2 * ε + 2 * ‖posPart (E.chart q hq).hk y‖ ^ 2 := hy₁
    have hy₁R : morseNorm n y₁ ≤ (E.chart q hq).R := by
      have h2 : E.rm q hq ^ 2 ≤ (E.chart q hq).R ^ 2 :=
        pow_le_pow_left₀ hrmq0.le (E.hrm q hq).2 2
      refine MorseNormalChart.morseNorm_le_of_sq_le (E.chart q hq).R_pos.le ?_
      rw [hrmq] at h2; linarith
    have hsymm : (E.chart q hq).χ.symm (E.flow t₁ ((E.chart q hq).χ y)) = y₁ := by
      rw [← hy₁e, (E.chart q hq).χ.left_inv ((E.chart q hq).hsrc y₁ hy₁R)]
    rw [hsymm] at hprod
    have he : E.flow t₁ ((E.chart q hq).χ y) ∈ (E.chart q hq).χ '' E.leftTube q hq ε δ₀ := by
      refine ⟨y₁, ⟨?_, ?_⟩, hy₁e⟩
      · rw [← (E.chart q hq).hnorm y₁ hy₁R, hy₁e]; exact hft₁
      · have hprod' : ‖negPart (E.chart q hq).hk y‖ ^ 2 * ‖posPart (E.chart q hq).hk y‖ ^ 2 ≤
            (2 * ρ) ^ 4 / 16 := by
          have h1 : ‖negPart (E.chart q hq).hk y‖ ^ 2 ≤ ρ ^ 2 := by linarith
          have h2 : ‖posPart (E.chart q hq).hk y‖ ^ 2 ≤ ρ ^ 2 := by linarith
          calc _ ≤ ρ ^ 2 * ρ ^ 2 := mul_le_mul h1 h2 hv0 (by positivity)
            _ = (2 * ρ) ^ 4 / 16 := by ring
        have h3 : (2 * ρ) ^ 4 / 16 ≤ 2 * ε * δ₀ :=
          (div_le_self (by positivity) (by norm_num)).trans hρδ
        exact le_of_mul_le_mul_left (hprod.trans (hprod'.trans h3)) (by positivity)
    have htt₁ : t₁ ≤ -t := by
      by_contra hneg
      have := f_flow_antitone (D := E) hf ((E.chart q hq).χ y) (not_le.1 hneg).le
      simp only at this
      rw [hft₁] at this
      linarith [hft.2]
    have := hnoball q hq hq₁ _ he p hp hp₁ hlt (-t - t₁) (by linarith)
    rw [flow_flow, add_sub_cancel] at this
    exact this hx
  · have hp₁ := (hk₁ p hp).1 hkp
    have hq₁ := (hk₁ q hq).1 hkq
    exact hnoball q hq hq₁ x (image_mono (leftModelSphere_subset_leftTube E q hq hδ₀.le) hx) p hp
      hp₁ hlt t ht

theorem exists_gradientLike_allPairs [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (hsi : isSelfIndexing I f a b) (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})
    (crit : Finset M) (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {R₀ : ℝ}
    (hR₀ : 0 < R₀) :
    ∃ D : GradientLikeStrip I f a b crit, ∃ ε, 0 < ε ∧ ∃ r', 0 < r' ∧ r' ^ 2 < ε ∧
      (∀ p hp, (D.chart p hp).R ≤ R₀ ∧ (D.chart p hp).r₀ ^ 2 < 2 * ε ∧
        24 * ε < D.rm p hp ^ 2 ∧ (D.chart p hp).r₀ < r') ∧
      (∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
        ∀ x ∈ (D.chart p hp).χ '' {y | morseNorm n y < r'}, ∀ t,
          D.flow t x ∉ (D.chart q hq).χ '' {y | morseNorm n y < r'}) ∧
      (∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
        ∀ x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
          D.flow t x ∉ (D.chart p hp).χ '' {y | morseNorm n y < r'}) := by
  classical
  obtain ⟨D, hR, hrm, -⟩ :=
    exists_gradientLikeStrip hf le_rfl hf.lt le_rfl hf.regular crit hcrit hR₀
  have hfs := hf.smooth
  obtain ⟨ρa, hρa, hρaT⟩ := exists_pos_le_forall_finset crit (fun p => min (f p - a) (b - f p))
    fun p hp => lt_min (sub_pos.2 ((hcrit p).1 hp).1.1) (sub_pos.2 ((hcrit p).1 hp).1.2)
  obtain ⟨ρg, hρg, hρgT⟩ := exists_pos_le_forall_finset
    ((crit ×ˢ crit).filter fun x => f x.1 < f x.2) (fun x => f x.2 - f x.1)
    fun x hx => sub_pos.2 (Finset.mem_filter.1 hx).2
  obtain ⟨ρR, hρR, hρRT⟩ := exists_pos_le_forall_finset crit.attach
    (fun p => (D.chart p.1 p.2).R ^ 2) fun p _ => pow_pos (D.chart p.1 p.2).R_pos 2
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (min ρa ρg) ρR / 80 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hεa : 80 * ε ≤ ρa := by
    rw [hεdef]; linarith [min_le_left (min ρa ρg) ρR, min_le_left ρa ρg]
  have hεg : 80 * ε ≤ ρg := by
    rw [hεdef]; linarith [min_le_left (min ρa ρg) ρR, min_le_right ρa ρg]
  have hεR : 80 * ε ≤ ρR := by rw [hεdef]; linarith [min_le_right (min ρa ρg) ρR]
  have hgap : ∀ p ∈ crit, ∀ q ∈ crit, f p < f q → f p + 40 * ε < f q := by
    intro p hp q hq hlt
    have := hρgT (p, q) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hp, hq⟩, hlt⟩)
    simp only at this
    linarith
  have hab : ∀ p ∈ crit, a + 40 * ε < f p ∧ f p + 40 * ε < b := by
    intro p hp
    have := hρaT p hp
    constructor <;> linarith [min_le_left (f p - a) (b - f p), min_le_right (f p - a) (b - f p)]
  have hRsq : ∀ p hp, 80 * ε ≤ (D.chart p hp).R ^ 2 := fun p hp =>
    hεR.trans (hρRT ⟨p, hp⟩ (Finset.mem_attach _ _))
  obtain ⟨ρ₀, hρ₀, hρ₀T⟩ := exists_pos_le_forall_finset crit.attach
    (fun p => (D.chart p.1 p.2).r₀) fun p _ => (D.chart p.1 p.2).hr₀
  obtain ⟨ρi, hρi, hρiA, -, hρiε, -⟩ := exists_small_radius hρ₀ hρ₀ hε one_pos
  obtain ⟨D₀, hD₀1, hD₀2, hD₀3, -⟩ := exists_shrinkAll hfs D hρi fun p hp =>
    hρiA.trans (hρ₀T ⟨p, hp⟩ (Finset.mem_attach _ _))
  set crit₁ : Finset M := crit.filter fun q => morseIndex I f q = 1 with hcrit₁def
  have hcrit₁ : ∀ q, q ∈ crit₁ ↔ q ∈ crit ∧ morseIndex I f q = 1 := fun q => Finset.mem_filter
  have hS : portPrivate_1aa78447_StageSetup D₀ crit₁ ε :=
    { hf := hfs
      hε := hε
      hcrit₁ := hcrit₁
      hgap := hgap
      hab := hab
      hinj := fun p hp q hq h => hinj ((hcrit p).1 hp) ((hcrit q).1 hq) h
      hmid := by
        intro m hm q hq₁ q' hq'₁ h1 h2
        obtain ⟨hq, hqi⟩ := (hcrit₁ q).1 hq₁
        obtain ⟨hq', hq'i⟩ := (hcrit₁ q').1 hq'₁
        refine (hcrit₁ m).2 ⟨hm, ?_⟩
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := hsi m q ((hcrit m).1 hm).1 ((hcrit q).1 hq).1 ((hcrit m).1 hm).2
            ((hcrit q).1 hq).2 (by rw [hqi]; exact h)
          linarith
        · have := hsi q' m ((hcrit q').1 hq').1 ((hcrit m).1 hm).1 ((hcrit q').1 hq').2
            ((hcrit m).1 hm).2 (by rw [hq'i]; exact h)
          linarith
      hR := fun q hq => by rw [(hD₀1 q hq).2.2.1]; linarith [hRsq q hq]
      hr₀ := fun q hq => by
        rw [hD₀2 q hq]
        have : (ρi / 2) ^ 2 = ρi ^ 2 / 4 := by ring
        rw [this]; linarith
      hrm := fun q hq => by rw [hD₀3 q hq, hrm q hq]; linarith [hRsq q hq] }
  obtain ⟨E, r', hr', hr'ε, hE1, hE2, hE3⟩ := exists_allPairs_of_setup hS
  refine ⟨E, ε, hε, r', hr', hr'ε, fun p hp => ⟨?_, ?_, (hE1 p hp).2.2, (hE1 p hp).2.1⟩,
    hE2, hE3⟩
  · rw [(hE1 p hp).1, (hD₀1 p hp).2.2.1]; exact hR p hp
  · have h1 := (hE1 p hp).2.1
    have h2 := (E.chart p hp).hr₀
    nlinarith

theorem leftSphere_direct (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (D : GradientLikeStrip I f a b crit)
    {ε r' : ℝ} (hε : 0 < ε) (hεr : ∀ p hp, (D.chart p hp).r₀ ^ 2 < 2 * ε ∧ 8 * ε < D.rm p hp ^ 2)
    (hr' : 0 < r') (hidx : ∀ p hp q hq, (D.chart p hp).k < (D.chart q hq).k → f p < f q)
    (harm : ∀ p hp q hq, (D.chart p hp).k = 1 → (D.chart q hq).k = 1 → f p < f q →
      ∀ x ∈ (D.chart q hq).χ '' (D.chart q hq).leftModelSphere ε, ∀ t, 0 ≤ t →
        D.flow t x ∉ (D.chart p hp).χ '' {y | morseNorm n y < r'})
    {q : M} (hq : q ∈ crit) (hk : (D.chart q hq).k = 1) (hqa : a ≤ f q - ε) :
    ∀ x ∈ D.leftSphere q hq ε (f q - ε),
      x ∈ D.bottom ∨ ∃ p hp, (D.chart p hp).k = 0 ∧ x ∈ D.basin p hp := by
  intro x hx
  rw [leftSphere_self_level] at hx
  have hqb : f q < b := (D.f_mem_Ioo q hq).2
  have hrmq := (hεr q hq).2
  have hrmq0 := D.rm_pos q hq
  have hεR : 2 * ε ≤ (D.chart q hq).R ^ 2 := by
    have := pow_le_pow_left₀ hrmq0.le (D.hrm q hq).2 2
    linarith
  obtain ⟨y, hy, rfl⟩ := hx
  have hfx : f ((D.chart q hq).χ y) = f q - ε :=
    (D.chart q hq).f_chart_of_mem_leftModelSphere hεR hy
  have hysq := (D.chart q hq).morseNorm_sq_of_mem_leftModelSphere hy
  have hyrm : morseNorm n y < D.rm q hq := by
    apply lt_of_pow_lt_pow_left₀ 2 hrmq0.le; linarith
  rcases D.trichotomy hf hε hεr (x := (D.chart q hq).χ y) ⟨by linarith, by linarith⟩ with
    hb | ⟨r, hr, T, hT⟩
  · exact Or.inl hb
  obtain ⟨z, ⟨hz1, hz2⟩, hzT⟩ := hT
  have hrR : morseNorm n z ≤ (D.chart r hr).R := hz1.le.trans (D.hrm r hr).2
  have hfz : f r ≤ f ((D.chart r hr).χ z) := by
    rw [(D.chart r hr).hnorm z hrR, morseNormalForm_split, hz2, norm_zero]
    nlinarith [sq_nonneg ‖posPart (D.chart r hr).hk z‖]
  rcases lt_or_ge T 0 with hT0 | hT0
  · exfalso
    by_cases hrq : r = q
    · subst hrq
      have := f_p_le_f_flow_of_negPart_eq_zero (D := D) hr hz1 hz2 (t := -T) (by linarith)
      rw [hzT, flow_neg_flow] at this
      linarith
    · have h1 := flow_mem_of_posPart_eq_zero (D := D) hq hyrm hy.1 hT0.le
      have h2 : D.flow T ((D.chart q hq).χ y) ∈ (D.chart q hq).χ '' Metric.ball 0 (D.chart q hq).R' :=
        image_mono (fun w hw => (D.chart q hq).mem_ball_of_le
          (hw.1.trans (hyrm.le.trans (D.hrm q hq).2))) h1
      have h3 : D.flow T ((D.chart q hq).χ y) ∈ (D.chart r hr).χ '' Metric.ball 0 (D.chart r hr).R' := by
        rw [← hzT]
        exact ⟨z, (D.chart r hr).mem_ball_of_le hrR, rfl⟩
      exact Set.disjoint_left.1 (D.disjoint q hq r hr (Ne.symm hrq)) h2 h3
  · have hfr : f r < f q := by
      have := f_flow_le (D := D) hf ((D.chart q hq).χ y) hT0
      rw [hzT] at hfz
      linarith
    rcases Nat.lt_trichotomy (D.chart r hr).k 1 with hk0 | hk1 | hk2
    · right
      have hk0' : (D.chart r hr).k = 0 := by omega
      refine ⟨r, hr, hk0', ?_⟩
      rw [← captured_index_zero_eq_basin hk0']
      exact ⟨T, z, ⟨hz1, hz2⟩, hzT⟩
    · exfalso
      have hcap : (D.chart q hq).χ y ∈ D.captured r hr := ⟨T, z, ⟨hz1, hz2⟩, hzT⟩
      obtain ⟨T', hT'⟩ := captured_eventually_small hcap hr'
      have := hT' (max T' 0) (le_max_left _ _)
      exact harm r hr q hq hk1 hk (hfr) _ ⟨y, hy, rfl⟩ (max T' 0) (le_max_right _ _)
        (image_mono (fun w hw => hw.1) this)
    · exfalso
      have := hidx q hq r hr (by rw [hk]; exact hk2)
      linarith

end GradientLikeStrip

end

end DifferentialGeometry.Topology
