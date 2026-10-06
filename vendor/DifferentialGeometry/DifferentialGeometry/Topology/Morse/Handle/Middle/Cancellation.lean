module

public import DifferentialGeometry.Topology.Morse.Handle.Middle.Geometry.MiddleSlide

@[expose] public section

set_option autoImplicit false

open Set Filter
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

namespace BlockConfig

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] {f : M → ℝ} {a b : ℝ} {ℓ : ℕ}

omit [SigmaCompactSpace M] in
theorem exists_transverse (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ) :
    ∃ B' : BlockConfig I f a b ℓ, B'.crit = B.crit ∧ B'.transverse ∧
      B'.c = B.c ∧ B'.α = B.α ∧ B'.β = B.β ∧ B'.ε ≤ B.ε ∧
      (∀ x (hx : x ∈ B.crit) (hx' : x ∈ B'.crit), (B'.D.chart x hx').χ = (B.D.chart x hx).χ ∧
        (B'.D.chart x hx').k = (B.D.chart x hx).k) ∧
      (∀ q ∈ B.upperIndexCriticalPoints, ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
        B'.D.leftSphereMap q (ℓ + 1) B'.ε B.c y = B.D.leftSphereMap q (ℓ + 1) B.ε B.c y) ∧
      ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ z, f z ≤ B.α → B'.D.V z = φ z • B.D.V z := by
  classical
  have key : ∀ S : Finset M, S ⊆ B.lowerIndexCriticalPoints →
      ∃ B' : BlockConfig I f a b ℓ, B'.crit = B.crit ∧
        (∀ p ∈ S, ∀ q ∈ B.upperIndexCriticalPoints, B'.pairTransverse p q) ∧
        B'.c = B.c ∧ B'.α = B.α ∧ B'.β = B.β ∧ B'.ε ≤ B.ε ∧
        (∀ x (hx : x ∈ B.crit) (hx' : x ∈ B'.crit), (B'.D.chart x hx').χ = (B.D.chart x hx).χ ∧
          (B'.D.chart x hx').k = (B.D.chart x hx).k) ∧
        (∀ q ∈ B.upperIndexCriticalPoints, ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
          B'.D.leftSphereMap q (ℓ + 1) B'.ε B.c y = B.D.leftSphereMap q (ℓ + 1) B.ε B.c y) ∧
        ∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
          ∀ z, f z ≤ B.α → B'.D.V z = φ z • B.D.V z := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨B, rfl, by simp, rfl, rfl, rfl, le_rfl, fun x hx hx' => ⟨rfl, rfl⟩,
        fun q _ y _ => rfl, fun _ => 1, continuous_const, ⟨1, 1, one_pos, fun _ => ⟨le_rfl, le_rfl⟩⟩,
        fun z _ => by simp⟩
    | @insert p S hpS ih =>
      intro hsub
      obtain ⟨B₁, hcr₁, htr₁, hc₁, hα₁, hβ₁, hε₁, hch₁, hsph₁, φ₁, hφ₁c, ⟨m₁, M₁, hm₁, hφ₁b⟩, hφ₁⟩ :=
        ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have hpP : p ∈ B.lowerIndexCriticalPoints := hsub (Finset.mem_insert_self p S)
      have hpP₁ : p ∈ B₁.lowerIndexCriticalPoints := by rw [B.lowerIndexCriticalPoints_eq_of_crit_eq hcr₁]; exact hpP
      have hQ₁ : B₁.upperIndexCriticalPoints = B.upperIndexCriticalPoints := B.upperIndexCriticalPoints_eq_of_crit_eq hcr₁
      have hP₁ : B₁.lowerIndexCriticalPoints = B.lowerIndexCriticalPoints := B.lowerIndexCriticalPoints_eq_of_crit_eq hcr₁
      obtain ⟨B₂, hcr₂, htrp, hoth, hc₂, hα₂, hβ₂, hε₂, hch₂, hsph₂, φ₂, hφ₂c,
          ⟨m₂, M₂, hm₂, hφ₂b⟩, hφ₂⟩ := B₁.exists_twist_row hf hpP₁
      refine ⟨B₂, hcr₂.trans hcr₁, ?_, hc₂.trans hc₁, hα₂.trans hα₁, hβ₂.trans hβ₁,
        hε₂.trans hε₁, ?_, ?_, fun z => φ₂ z * φ₁ z, hφ₂c.mul hφ₁c, ⟨m₂ * m₁, M₂ * M₁,
          mul_pos hm₂ hm₁, fun x => ⟨?_, ?_⟩⟩, ?_⟩
      · intro p' hp' q hq
        rcases Finset.mem_insert.1 hp' with rfl | hp'S
        · exact htrp q (hQ₁ ▸ hq)
        · have hne : p' ≠ p := fun h => hpS (h ▸ hp'S)
          have hp'P₁ : p' ∈ B₁.lowerIndexCriticalPoints := by
            rw [hP₁]; exact hsub (Finset.mem_insert_of_mem hp'S)
          exact ((hoth p' hp'P₁ hne q (hQ₁ ▸ hq)).1).2 (htr₁ p' hp'S q hq)
      · intro x hx hx''
        have hx' : x ∈ B₁.crit := hcr₁ ▸ hx
        obtain ⟨h1, h2⟩ := hch₂ x hx' hx''
        obtain ⟨h3, h4⟩ := hch₁ x hx hx'
        exact ⟨h1.trans h3, h2.trans h4⟩
      · intro q hq y hy
        have := hsph₂ q (hQ₁ ▸ hq) y hy
        rw [hc₁] at this
        rw [this]
        exact hsph₁ q hq y hy
      · exact mul_le_mul (hφ₂b x).1 (hφ₁b x).1 hm₁.le (hm₂.le.trans (hφ₂b x).1)
      · exact mul_le_mul (hφ₂b x).2 (hφ₁b x).2 (hm₁.le.trans (hφ₁b x).1)
          ((hm₂.le.trans (hφ₂b x).1).trans (hφ₂b x).2)
      · intro z hz
        rw [hφ₂ z (by rw [hα₁]; exact hz), hφ₁ z hz, smul_smul]
  obtain ⟨B', hcr, htr, hc, hα, hβ, hε, hch, hsph, hφ⟩ := key B.lowerIndexCriticalPoints subset_rfl
  refine ⟨B', hcr, ?_, hc, hα, hβ, hε, hch, hsph, hφ⟩
  intro p hp q hq
  rw [B.lowerIndexCriticalPoints_eq_of_crit_eq hcr] at hp
  rw [B.upperIndexCriticalPoints_eq_of_crit_eq hcr] at hq
  exact htr p hp q hq

theorem exists_lowered_stage (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) {q₁ q₂ : M} (hq₁ : q₁ ∈ B.upperIndexCriticalPoints) (hq₂ : q₂ ∈ B.upperIndexCriticalPoints)
    (hne : q₁ ≠ q₂) :
    ∃ g₁ : M → ℝ, ModifiedWithin f a b g₁ ∧ ModifiedWithin f B.c b g₁ ∧ MorseStrip I g₁ a b ∧
      sameCritIn I f g₁ a b ∧ (∀ x ∈ B.crit, x ≠ q₂ → g₁ x = f x) ∧
      (∀ x, x ∈ B.crit ↔ g₁ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₁ x) ∧
      ∃ D₁ : GradientLikeStrip I g₁ a b B.crit, ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ B.ε ∧
        (∀ x hx, (D₁.chart x hx).r₀ ^ 2 < 2 * ε₁ ∧ 8 * ε₁ < D₁.rm x hx ^ 2) ∧
        (∀ x (hx : x ∈ B.crit), (D₁.chart x hx).χ = (B.D.chart x hx).χ ∧
          (D₁.chart x hx).k = (B.D.chart x hx).k) ∧
        B.c < g₁ q₂ - ε₁ ∧ g₁ q₂ + ε₁ < g₁ q₁ - ε₁ ∧
        (∀ y, g₁ y ∈ Icc B.c (g₁ q₂ - ε₁) ∪ Icc (g₁ q₂ + ε₁) (g₁ q₁ - ε₁) →
          ∀ x hx, y ∉ D₁.smallBall x hx) ∧
        (∀ x ∈ B.crit, g₁ x ∈ Icc B.c (g₁ q₁ - ε₁) → x = q₂) ∧
        (∀ x (hx : x ∈ B.crit), g₁ x = g₁ q₁ → ∃ r > 0, D₁.noCommon x hx q₂ (B.mem_upperIndexCriticalPoints.1 hq₂).1 r r) ∧
        (∀ x hx, D₁.rm x hx ^ 2 < g₁ q₁ - g₁ q₂ - 2 * ε₁) ∧
        (∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
          ∀ z, f z ≤ B.c → D₁.V z = φ z • B.D.V z) ∧
        (∀ q ∈ B.upperIndexCriticalPoints, q ≠ q₂ → ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
          D₁.leftSphereHit q (ℓ + 1) ε₁ B.c y = B.D.leftSphereMap q (ℓ + 1) B.ε B.c y) ∧
        ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
          D₁.leftSphereMap q₂ (ℓ + 1) ε₁ B.c y = B.D.leftSphereMap q₂ (ℓ + 1) B.ε B.c y := by
  classical
  have _hℓ := hℓ
  have _hℓn := hℓn
  have hq₁c : q₁ ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq₁).1
  have hq₂c : q₂ ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq₂).1
  have hfq₁ : f q₁ = B.β := B.hQ q₁ hq₁c (B.mem_upperIndexCriticalPoints.1 hq₁).2
  have hfq₂ : f q₂ = B.β := B.hQ q₂ hq₂c (B.mem_upperIndexCriticalPoints.1 hq₂).2
  have hlevels : ∀ x ∈ B.crit, f x = B.α ∨ f x = B.β ∨ B.β < f x := by
    intro x hx
    have hm := B.hmin x hx
    rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with h | h
    · exact Or.inr (Or.inr (B.hhigh x hx h))
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · exact Or.inr (Or.inl (B.hQ x hx h'))
      · exact Or.inl (B.hP x hx (by omega))
  have hBε := B.hε
  have hαc := B.hαc
  have hcβ := B.hcβ
  have haα := B.haα
  have hβb := B.hβb
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ > 0, ∀ x ∈ B.crit, B.β < f x → B.β + δ < f x := by
    by_cases hne : (B.crit.filter (fun x => B.β < f x)).Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := (B.crit.filter (fun x => B.β < f x)).exists_min_image f hne
      rw [Finset.mem_filter] at hx₀
      refine ⟨(f x₀ - B.β) / 2, by linarith [hx₀.2], fun x hx hβx => ?_⟩
      have := hmin x (Finset.mem_filter.2 ⟨hx, hβx⟩)
      linarith [hx₀.2]
    · exact ⟨1, one_pos, fun x hx hβx => absurd ⟨x, Finset.mem_filter.2 ⟨hx, hβx⟩⟩ hne⟩
  set d : ℝ := min (min ((B.β - B.c) / 8) ((b - B.β) / 2)) (δ / 2) with hd_def
  have hd0 : 0 < d := by
    simp only [hd_def, lt_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  have hd1 : d ≤ (B.β - B.c) / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : d ≤ (b - B.β) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : d ≤ δ / 2 := min_le_right _ _
  set t₂ : ℝ := B.β - 3 * d with ht₂_def
  have hεr₀ : ∀ x hx, (B.D.chart x hx).r₀ ^ 2 < 2 * B.ε ∧ 8 * B.ε < B.D.rm x hx ^ 2 :=
    fun x hx => ⟨B.hr₀ x hx, B.hrm x hx⟩
  obtain ⟨g₁, hmod, hg₁, hsame, hSt, hoff, D', hresc', hχ', ε', hε'0, hε'B, hεr', -⟩ :=
    exists_vertical_move I hf B.hcrit B.D B.hε hεr₀ {q₂}
      (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hq₂c)
      (s₀ := B.β) (u := B.c + d) (v := B.β + d) (t := t₂)
      (by intro x hx; rw [Finset.mem_singleton] at hx; rw [hx, hfq₂])
      (by linarith) (by linarith) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (by
        intro x hx hxw
        rcases hlevels x hx with h | h | h
        · exfalso; rw [h] at hxw; linarith [hxw.1]
        · exact Or.inl h
        · exfalso; have := hgap x hx h; linarith [hxw.2])
      (fun _ _ => 1) (fun _ _ => one_pos)
      (by
        intro x hx y hy _ _ hyt
        exfalso
        rcases hlevels y hy with h | h | h
        · rw [h] at hyt; linarith
        · rw [h] at hyt; linarith
        · rw [hyt] at h; linarith)
  have hg₁s : ContMDiff I 𝓘(ℝ, ℝ) ∞ g₁ := hg₁.smooth
  have hg₁q₂ : g₁ q₂ = t₂ := hSt q₂ (Finset.mem_singleton_self _)
  have hg₁off : ∀ x ∈ B.crit, x ≠ q₂ → g₁ x = f x :=
    fun x hx hne => hoff x hx (by rw [Finset.mem_singleton]; exact hne)
  have hg₁q₁ : g₁ q₁ = B.β := (hg₁off q₁ hq₁c hne).trans hfq₁
  set ε₁ : ℝ := min ε' (d / 16) with hε₁_def
  have hε₁0 : 0 < ε₁ := lt_min hε'0 (by linarith)
  have hε₁ε' : ε₁ ≤ ε' := min_le_left _ _
  have hε₁d : ε₁ ≤ d / 16 := min_le_right _ _
  have hε₁B : ε₁ ≤ B.ε := hε₁ε'.trans hε'B
  set ρ : ℝ := Real.sqrt d with hρ_def
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hd0
  have hρsq : ρ ^ 2 = d := Real.sq_sqrt hd0.le
  obtain ⟨D₁, hresc₁, hχ₁, hr₁, -⟩ := GradientLikeStrip.exists_shrink_field hg₁s D'
    hε₁0 hρ0 (by rw [hρsq]; linarith)
    (fun x hx => by linarith [(hεr' x hx).2])
  have hχ₁B : ∀ x (hx : x ∈ B.crit), (D₁.chart x hx).χ = (B.D.chart x hx).χ ∧
      (D₁.chart x hx).k = (B.D.chart x hx).k := fun x hx =>
    ⟨(hχ₁ x hx).1.trans (hχ' x hx).1, (hχ₁ x hx).2.1.trans (hχ' x hx).2.1⟩
  have hεr₁ : ∀ x hx, (D₁.chart x hx).r₀ ^ 2 < 2 * ε₁ ∧ 8 * ε₁ < D₁.rm x hx ^ 2 := by
    intro x hx
    refine ⟨(hr₁ x hx).1, ?_⟩
    rw [(hr₁ x hx).2]
    rcases min_choice ρ (D'.rm x hx) with h | h
    · rw [h, hρsq]; linarith
    · rw [h]; linarith [(hεr' x hx).2]
  have hrm₁d : ∀ x hx, D₁.rm x hx ^ 2 ≤ d := by
    intro x hx
    rw [← hρsq]
    exact pow_le_pow_left₀ (D₁.rm_pos x hx).le ((hr₁ x hx).2 ▸ min_le_left _ _) 2
  obtain ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hφ⟩ := hresc₁
  obtain ⟨φ', hφ'c, ⟨m', M₀', hm', hφ'b⟩, hφ'⟩ := hresc'
  have hψb : ∀ x, m' * m ≤ φ' x * φ x ∧ φ' x * φ x ≤ M₀' * M₀ := by
    intro x
    have h1 := hφb x
    have h2 := hφ'b x
    constructor
    · exact mul_le_mul h2.1 h1.1 hm.le (hm'.le.trans h2.1)
    · exact mul_le_mul h2.2 h1.2 (hm.le.trans h1.1) ((hm'.le.trans h2.1).trans h2.2)
  have hresc : D₁.isRescaleOf B.D := by
    refine ⟨fun x => φ' x * φ x, hφ'c.mul hφc, ⟨m' * m, M₀' * M₀, mul_pos hm' hm, hψb⟩,
      fun x => ?_⟩
    rw [hφ' x, hφ x, smul_smul]
  have hψpos : ∀ x, 0 < φ' x * φ x := fun x => (mul_pos hm' hm).trans_le (hψb x).1
  have hV₁ : ∀ z, D₁.V z = (φ' z * φ z)⁻¹ • B.D.V z := by
    intro z
    rw [hφ' z, hφ z, smul_smul, smul_smul, mul_assoc (φ' z * φ z)⁻¹, inv_mul_cancel₀ (hψpos z).ne',
      one_smul]
  have hsub : ∀ z, g₁ z ≤ B.c ↔ f z ≤ B.c := by
    intro z
    by_cases hz : f z ∈ Ioo (B.c + d) (B.β + d)
    · have hz' := hmod.mapsTo hz
      constructor <;> intro h
      · exfalso; linarith [hz'.1]
      · exfalso; linarith [hz.1]
    · rw [hmod.eqOn hz]
  have hlevc : ∀ z, f z = B.c ↔ g₁ z = B.c := by
    intro z
    by_cases hz : f z ∈ Ioo (B.c + d) (B.β + d)
    · have hz' := hmod.mapsTo hz
      constructor <;> intro h
      · exfalso; linarith [hz.1]
      · exfalso; linarith [hz'.1]
    · rw [hmod.eqOn hz]
  have hcritlev : ∀ x ∈ B.crit, x ≠ q₂ → g₁ x = B.α ∨ B.β ≤ g₁ x := by
    intro x hx hxq
    rw [hg₁off x hx hxq]
    rcases hlevels x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr h.ge
    · exact Or.inr h.le
  have hunit : ∀ y, g₁ y ∈ Icc B.c (g₁ q₂ - ε₁) ∪ Icc (g₁ q₂ + ε₁) (g₁ q₁ - ε₁) →
      ∀ x hx, y ∉ D₁.smallBall x hx := by
    intro y hy x hx hyx
    have habs := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hyx
    have hr := (hεr₁ x hx).1
    rw [abs_lt] at habs
    rw [hg₁q₂, hg₁q₁] at hy
    by_cases hxq : x = q₂
    · subst hxq
      rw [hg₁q₂] at habs
      rcases hy with hy | hy
      · linarith [hy.2]
      · linarith [hy.1]
    · rcases hcritlev x hx hxq with h | h
      · rw [h] at habs
        rcases hy with hy | hy
        · linarith [hy.1]
        · linarith [hy.1]
      · rcases hy with hy | hy
        · linarith [hy.2]
        · linarith [hy.2]
  have hmodab : ModifiedWithin f a b g₁ := hmod.mono (by linarith) (by linarith)
  have hmodcb : ModifiedWithin f B.c b g₁ := hmod.mono (by linarith) (by linarith)
  have hkQ : ∀ q (hq : q ∈ B.upperIndexCriticalPoints), (B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).k = ℓ + 1 := fun q hq =>
    (B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).hkidx.symm.trans (B.mem_upperIndexCriticalPoints.1 hq).2
  have hRB : ∀ q (hq : q ∈ B.crit), 2 * B.ε ≤ (B.D.chart q hq).R ^ 2 := by
    intro q hq
    have h1 := (B.D.hrm q hq).2
    have h2 := pow_le_pow_left₀ (B.D.rm_pos q hq).le h1 2
    linarith [hεr₀ q hq]
  refine ⟨g₁, hmodab, hmodcb, hg₁, hsame, hg₁off, ?_, D₁, ε₁, hε₁0, hε₁B, hεr₁, hχ₁B, ?_, ?_,
    hunit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [B.hcrit x]
    have hI : g₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := Set.ext_iff.1 hmodab.preimage_Ioo x
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := hI.2 h1
      exact ⟨h1', (hsame.1 x h1).2 h2⟩
    · rintro ⟨h1, h2⟩
      have h1' := hI.1 h1
      exact ⟨h1', (hsame.1 x h1').1 h2⟩
  · rw [hg₁q₂]; linarith
  · rw [hg₁q₂, hg₁q₁]; linarith
  · intro x hx hxI
    by_contra hxq
    rw [hg₁q₁] at hxI
    rcases hcritlev x hx hxq with h | h
    · rw [h] at hxI; linarith [hxI.1]
    · linarith [hxI.2]
  · intro x hx hxg
    have hxq : x ≠ q₂ := by
      rintro rfl
      rw [hg₁q₂, hg₁q₁] at hxg
      linarith
    have hfx : f x = B.β := by rw [← hg₁off x hx hxq, hxg, hg₁q₁]
    refine ⟨Real.sqrt B.ε, Real.sqrt_pos.2 hBε, ?_⟩
    have hsq : Real.sqrt B.ε ^ 2 < 2 * B.ε := by rw [Real.sq_sqrt hBε.le]; linarith
    have h0 := GradientLikeStrip.noCommon_sameLevel hf.smooth B.D hBε hεr₀ hx hq₂c hxq
      (hfx.trans hfq₂.symm) hsq hsq
    exact GradientLikeStrip.noCommon.of_rescale hresc (fun x hx => (hχ₁B x hx).1) h0
  · intro x hx
    rw [hg₁q₁, hg₁q₂]
    linarith [hrm₁d x hx]
  · refine ⟨fun z => (φ' z * φ z)⁻¹, (hφ'c.mul hφc).inv₀ (fun z => (hψpos z).ne'),
      ⟨(M₀' * M₀)⁻¹, (m' * m)⁻¹, inv_pos.2 ((hψpos q₁).trans_le (hψb q₁).2), fun z => ?_⟩,
      fun z _ => hV₁ z⟩
    exact ⟨inv_anti₀ (hψpos z) (hψb z).2, inv_anti₀ (mul_pos hm' hm) (hψb z).1⟩
  · intro q hq hqq y hy
    have hqc := (B.mem_upperIndexCriticalPoints.1 hq).1
    have hk := hkQ q hq
    have hfq : f q = B.β := B.hQ q hqc (B.mem_upperIndexCriticalPoints.1 hq).2
    have hg₁q : g₁ q = B.β := (hg₁off q hqc hqq).trans hfq
    have hU : ∀ y, f y ∈ Icc B.c (f q - B.ε) → ∀ x hx, y ∉ B.D.smallBall x hx := by
      intro y hy
      rw [hfq] at hy
      exact B.hlev y ⟨by linarith [hy.1], hy.2⟩
    have hreach : ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 → ∃ s, 0 ≤ s ∧
        f (B.D.flow s ((B.D.chart q hqc).χ ((B.D.chart q hqc).sphereParam B.ε
          (Handle.reidx y)))) ≤ B.c := by
      intro y hy
      refine ⟨f q - B.ε - B.c, by rw [hfq]; linarith, ?_⟩
      have hw : (Handle.reidx y : Fin (B.D.chart q hqc).k → ℝ) ≠ 0 := by
        intro h0
        apply hy
        ext i
        have := congrFun h0 ⟨i.1, by rw [hk]; exact i.2⟩
        simp only [Handle.reidx, i.isLt, dite_true] at this
        exact this
      have hmem := (B.D.chart q hqc).sphereParam_mem_leftModelSphere hBε.le hw
      have hsub' := B.D.leftSphere_subset_level hf.smooth q hqc (hRB q hqc)
        (c := B.c) ⟨by linarith, by linarith⟩ (by
          intro y hy
          rw [uIcc_of_ge (by rw [hfq]; linarith)] at hy
          exact hU y hy) ⟨_, ⟨_, hmem, rfl⟩, rfl⟩
      exact le_of_eq hsub'
    rw [GradientLikeStrip.leftSphereHit_eq_of_rescale hf.smooth hg₁s B.D D₁ hresc hχ₁B hqc hk hBε
      hε₁0 (by linarith [hεr₀ q hqc]) (by linarith [(hεr₁ q hqc).2]) (by rw [hfq]; linarith)
      (by rw [hg₁q]; linarith) hsub hreach y hy]
    exact GradientLikeStrip.leftSphereHit_eq_leftSphereMap hf.smooth B.D hqc hk hBε
      (by linarith [hεr₀ q hqc]) (by linarith) (by rw [hfq]; linarith) hU y hy
  · intro y hy
    exact GradientLikeStrip.leftSphereMap_eq_of_rescale hf.smooth hg₁s B.D D₁ hresc hχ₁B hq₂c
      (hkQ q₂ hq₂) hBε hε₁0 (by linarith [hεr₀ q₂ hq₂c]) (by linarith [(hεr₁ q₂ hq₂c).2])
      (by linarith) (by rw [hfq₂]; linarith) (by rw [hg₁q₂]; linarith)
      (by
        intro y hy
        rw [hfq₂] at hy
        exact B.hlev y ⟨by linarith [hy.1], hy.2⟩)
      (fun y hy => hunit y (Or.inl hy)) hlevc y hy

theorem exists_merged_stage (B : BlockConfig I f a b ℓ) {q₂ : M} (hq₂ : q₂ ∈ B.upperIndexCriticalPoints)
    {g₁ : M → ℝ} (hg₁ : MorseStrip I g₁ a b)
    (hcrit₁ : ∀ x, x ∈ B.crit ↔ g₁ x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g₁ x)
    (hidx₁ : ∀ x ∈ B.crit, morseIndex I g₁ x = morseIndex I f x)
    (hlev₁ : ∀ x ∈ B.crit, x ≠ q₂ → g₁ x = f x)
    (E : GradientLikeStrip I g₁ a b B.crit) {ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁B : ε₁ ≤ B.ε)
    (hεr : ∀ x hx, (E.chart x hx).r₀ ^ 2 < 2 * ε₁ ∧ 8 * ε₁ < E.rm x hx ^ 2)
    (hq₂lev : B.c < g₁ q₂ - ε₁ ∧ g₁ q₂ + ε₁ < B.β - ε₁)
    (hnoc : ∃ ρ > 0, ∀ x (hx : x ∈ B.crit), g₁ x = B.β → x ≠ q₂ →
      E.noCommon q₂ (B.mem_upperIndexCriticalPoints.1 hq₂).1 x hx ρ ρ) :
    ∃ g : M → ℝ, ModifiedWithin g₁ a b g ∧ ModifiedWithin g₁ B.c b g ∧ MorseStrip I g a b ∧
      sameCritIn I g₁ g a b ∧
      ∃ B' : BlockConfig I g a b ℓ, B'.crit = B.crit ∧ B'.c = B.c ∧ B'.α = B.α ∧ B'.ε ≤ ε₁ ∧
        (∀ x (hx : x ∈ B.crit) (hx' : x ∈ B'.crit), (B'.D.chart x hx').χ = (E.chart x hx).χ ∧
          (B'.D.chart x hx').k = (E.chart x hx).k) ∧
        (∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
          ∀ z, B'.D.V z = φ z • E.V z) ∧
        (∀ q ∈ B.upperIndexCriticalPoints, q ≠ q₂ → ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
          B'.D.leftSphereMap q (ℓ + 1) B'.ε B.c y = E.leftSphereHit q (ℓ + 1) ε₁ B.c y) ∧
        ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
          B'.D.leftSphereMap q₂ (ℓ + 1) B'.ε B.c y = E.leftSphereMap q₂ (ℓ + 1) ε₁ B.c y := by
  classical
  obtain ⟨hq₂c, hq₂Q⟩ := B.mem_upperIndexCriticalPoints.1 hq₂
  have hBε := B.hε
  have hBαc := B.hαc
  have hBcβ := B.hcβ
  have hBβb := B.hβb
  have hBaα := B.haα
  obtain ⟨hq₂c', hq₂β'⟩ := hq₂lev
  have hlevs : ∀ x ∈ B.crit, x ≠ q₂ → g₁ x = B.α ∨ g₁ x = B.β ∨ B.β < g₁ x := by
    intro x hx hne
    rw [hlev₁ x hx hne]
    rcases lt_trichotomy (morseIndex I f x) (ℓ + 1) with h | h | h
    · left
      exact B.hP x hx (by have := B.hmin x hx; omega)
    · right; left
      exact B.hQ x hx h
    · right; right
      exact B.hhigh x hx h
  obtain ⟨d, hd0, hdε, hdb, hdhigh⟩ : ∃ d : ℝ, 0 < d ∧ d < ε₁ ∧ B.β + d < b ∧
      ∀ x ∈ B.crit, B.β < g₁ x → B.β + d < g₁ x := by
    have h1 : ∀ᶠ d in 𝓝[>] (0 : ℝ), ∀ x ∈ B.crit, B.β < g₁ x → B.β + d < g₁ x := by
      rw [Filter.eventually_all_finset]
      intro x _
      by_cases hxβ : B.β < g₁ x
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < g₁ x - B.β by linarith)] with d hd _
        linarith [hd.2]
      · exact Filter.Eventually.of_forall (fun d h => absurd h hxβ)
    have h2 : ∀ᶠ d in 𝓝[>] (0 : ℝ), d ∈ Ioo 0 (min ε₁ (b - B.β)) :=
      Ioo_mem_nhdsGT (lt_min hε₁ (by linarith))
    obtain ⟨d, hd1, hd2⟩ := (h1.and h2).exists
    exact ⟨d, hd2.1, lt_of_lt_of_le hd2.2 (min_le_left _ _),
      by linarith [hd2.2, min_le_right ε₁ (b - B.β)], hd1⟩
  obtain ⟨ρ, hρ, hnoc'⟩ := hnoc
  have hwin : ∀ x ∈ B.crit, g₁ x ∈ Icc (g₁ q₂ - d) (B.β + d) → g₁ x = g₁ q₂ ∨ g₁ x = B.β := by
    intro x hx hxw
    by_cases hxq : x = q₂
    · left; rw [hxq]
    · rcases hlevs x hx hxq with h | h | h
      · exfalso; linarith [hxw.1]
      · right; exact h
      · exfalso; linarith [hxw.2, hdhigh x hx h]
  have hnocm : ∀ x (hx : x ∈ B.crit) y (hy : y ∈ B.crit), x ∈ ({q₂} : Finset M) →
      y ∉ ({q₂} : Finset M) → g₁ y = B.β →
      E.noCommon x hx y hy ((fun _ _ => ρ) x hx) ((fun _ _ => ρ) y hy) := by
    intro x hx y hy hxS hyS hyβ
    obtain rfl := Finset.mem_singleton.1 hxS
    exact hnoc' y hy hyβ (fun h => hyS (Finset.mem_singleton.2 h))
  obtain ⟨g, hmod, hg, hsame, hgS, hgoff, D', hresc, hχ', ε', hε', hε'ε, hεr', -⟩ :=
    exists_vertical_move I hg₁ hcrit₁ E hε₁ hεr {q₂}
      (fun x hx => by rw [Finset.mem_singleton.1 hx]; exact hq₂c) (s₀ := g₁ q₂)
      (u := g₁ q₂ - d) (v := B.β + d) (t := B.β)
      (fun x hx => by rw [Finset.mem_singleton.1 hx]) (by linarith) hdb
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hwin (fun _ _ => ρ)
      (fun _ _ => hρ) hnocm
  have hgq₂ : g q₂ = B.β := hgS q₂ (Finset.mem_singleton_self q₂)
  have hgoff' : ∀ x ∈ B.crit, x ≠ q₂ → g x = g₁ x := fun x hx hne =>
    hgoff x hx (fun h => hne (Finset.mem_singleton.1 h))
  have hmodab : ModifiedWithin g₁ a b g := hmod.mono (by linarith) hdb.le
  have hmodc : ModifiedWithin g₁ B.c b g := hmod.mono (by linarith) hdb.le
  have hcritg : ∀ x, x ∈ B.crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
    intro x
    rw [hcrit₁ x]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hmodab.mapsTo h1, (hsame.1 x h1).2 h2⟩
    · rintro ⟨h1, h2⟩
      have h1' : g₁ x ∈ Ioo a b := (Set.ext_iff.1 hmodab.preimage_Ioo x).1 h1
      exact ⟨h1', (hsame.1 x h1').1 h2⟩
  have hidxg : ∀ x ∈ B.crit, morseIndex I g x = morseIndex I f x := by
    intro x hx
    obtain ⟨h1, h2⟩ := (hcrit₁ x).1 hx
    rw [hsame.2 x h1 h2, hidx₁ x hx]
  have hq₂ne : ∀ x ∈ B.crit, morseIndex I f x ≠ ℓ + 1 → x ≠ q₂ := by
    intro x _ h hxq
    rw [hxq] at h
    exact h hq₂Q
  obtain ⟨B', hBcrit, hBα, hBβ, hBc, hBε', hBch, φ', hφ'c, ⟨m', M', hm', hφ'b⟩, hBV⟩ :=
    exists_blockConfig_of_levels I hg hcritg D' hε' hεr' (ℓ := ℓ) (α := B.α) (β := B.β)
      (c := B.c)
      (fun x hx => by rw [hidxg x hx]; exact B.hmin x hx) hBaα (by linarith) (by linarith)
      hBβb
      (fun x hx h => by
        rw [hidxg x hx] at h
        rw [hgoff' x hx (hq₂ne x hx (by omega)), hlev₁ x hx (hq₂ne x hx (by omega))]
        exact B.hP x hx h)
      (fun x hx h => by
        rw [hidxg x hx] at h
        by_cases hxq : x = q₂
        · rw [hxq, hgq₂]
        · rw [hgoff' x hx hxq, hlev₁ x hx hxq]
          exact B.hQ x hx h)
      (fun x hx h => by
        rw [hidxg x hx] at h
        rw [hgoff' x hx (hq₂ne x hx (by omega)), hlev₁ x hx (hq₂ne x hx (by omega))]
        exact B.hhigh x hx h)
  obtain ⟨φ, hφc, ⟨m, M₀, hm, hφb⟩, hD'V⟩ := hresc
  have hφpos : ∀ x, 0 < φ x := fun x => lt_of_lt_of_le hm (hφb x).1
  have hφ₀ : ∃ φ₀ : M → ℝ, Continuous φ₀ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ₀ x ∧ φ₀ x ≤ M₀) ∧
      ∀ z, B'.D.V z = φ₀ z • E.V z := by
    have hM₀ : 0 < M₀ := lt_of_lt_of_le (hφpos q₂) (hφb q₂).2
    refine ⟨fun z => φ' z * (φ z)⁻¹, hφ'c.mul (hφc.inv₀ fun x => (hφpos x).ne'),
      ⟨m' * M₀⁻¹, M' * m⁻¹, mul_pos hm' (inv_pos.2 hM₀), fun x => ⟨?_, ?_⟩⟩, fun z => ?_⟩
    · exact mul_le_mul (hφ'b x).1 (inv_anti₀ (hφpos x) (hφb x).2) (inv_pos.2 hM₀).le
        (by linarith [(hφ'b x).1])
    · exact mul_le_mul (hφ'b x).2 (inv_anti₀ hm (hφb x).1) (inv_pos.2 (hφpos x)).le
        (by linarith [(hφ'b x).1, (hφ'b x).2])
    · change B'.D.V z = (φ' z * (φ z)⁻¹) • E.V z
      rw [hBV z, hD'V z, smul_smul, mul_assoc, inv_mul_cancel₀ (hφpos z).ne', mul_one]
  have hac : a ≤ B.c := by linarith
  have hsub : ∀ z, g₁ z ≤ B.c ↔ g z ≤ B.c := fun z =>
    (Set.ext_iff.1 hmodc.preimage_Iic_left z).symm
  have hlevc : ∀ z, g₁ z = B.c ↔ g z = B.c := fun z =>
    (Set.ext_iff.1 hmodc.preimage_singleton_left z).symm
  have hkQ : ∀ x (hx : x ∈ B.crit), morseIndex I f x = ℓ + 1 → (E.chart x hx).k = ℓ + 1 := by
    intro x hx h
    rw [← (E.chart x hx).hkidx, hidx₁ x hx, h]
  have key : ∀ (cr : Finset M) (hcr : cr = B.crit) (D₀ : GradientLikeStrip I g a b cr) (ε₀ : ℝ),
      0 < ε₀ → (∀ x hx, 8 * ε₀ < D₀.rm x hx ^ 2) → B.α + ε₀ < B.c → B.c < B.β - ε₀ →
      (∀ y, g y ∈ Icc (B.α + ε₀) (B.β - ε₀) → ∀ x hx, y ∉ D₀.smallBall x hx) →
      (∀ x (hx : x ∈ B.crit) (hx' : x ∈ cr), (D₀.chart x hx').χ = (E.chart x hx).χ ∧
        (D₀.chart x hx').k = (E.chart x hx).k) →
      (∃ φ₀ : M → ℝ, Continuous φ₀ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ₀ x ∧ φ₀ x ≤ M₀) ∧
          ∀ z, D₀.V z = φ₀ z • E.V z) →
      (∀ q ∈ B.upperIndexCriticalPoints, q ≠ q₂ → ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
          D₀.leftSphereMap q (ℓ + 1) ε₀ B.c y = E.leftSphereHit q (ℓ + 1) ε₁ B.c y) ∧
        ∀ y : EuclideanSpace ℝ (Fin (ℓ + 1)), y ≠ 0 →
          D₀.leftSphereMap q₂ (ℓ + 1) ε₀ B.c y = E.leftSphereMap q₂ (ℓ + 1) ε₁ B.c y := by
    intro cr hcr D₀ ε₀ hε₀ hrm₀ hαc₀ hcβ₀ hlev₀ hch hφ₀'
    subst hcr
    obtain ⟨φ₀, hφ₀c, ⟨m₀, M₁, hm₀, hφ₀b⟩, hD₀V⟩ := hφ₀'
    have hφ₀pos : ∀ x, 0 < φ₀ x := fun x => lt_of_lt_of_le hm₀ (hφ₀b x).1
    have hM₁ : 0 < M₁ := lt_of_lt_of_le (hφ₀pos q₂) (hφ₀b q₂).2
    have hresc₁ : D₀.isRescaleOf E := by
      refine ⟨fun z => (φ₀ z)⁻¹, hφ₀c.inv₀ fun x => (hφ₀pos x).ne',
        ⟨M₁⁻¹, m₀⁻¹, inv_pos.2 hM₁, fun x => ⟨inv_anti₀ (hφ₀pos x) (hφ₀b x).2,
          inv_anti₀ hm₀ (hφ₀b x).1⟩⟩, fun z => ?_⟩
      change E.V z = (φ₀ z)⁻¹ • D₀.V z
      rw [hD₀V z, smul_smul, inv_mul_cancel₀ (hφ₀pos z).ne', one_smul]
    have hresc₂ : E.isRescaleOf D₀ := ⟨φ₀, hφ₀c, ⟨m₀, M₁, hm₀, hφ₀b⟩, hD₀V⟩
    have hχ₁ : ∀ x hx, (D₀.chart x hx).χ = (E.chart x hx).χ ∧
        (D₀.chart x hx).k = (E.chart x hx).k := fun x hx => hch x hx hx
    have hχ₂ : ∀ x hx, (E.chart x hx).χ = (D₀.chart x hx).χ ∧
        (E.chart x hx).k = (D₀.chart x hx).k := fun x hx =>
      ⟨(hch x hx hx).1.symm, (hch x hx hx).2.symm⟩
    refine ⟨fun q hq hne y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨hqc, hqQ⟩ := B.mem_upperIndexCriticalPoints.1 hq
      have hqβ : g₁ q = B.β := (hlev₁ q hqc hne).trans (B.hQ q hqc hqQ)
      have hgq : g q = B.β := (hgoff' q hqc hne).trans hqβ
      have hμ₀ : (D₀.chart q hqc).k = ℓ + 1 := (hch q hqc hqc).2.trans (hkQ q hqc hqQ)
      have hU₀ : ∀ y, g y ∈ Icc B.c (g q - ε₀) → ∀ x hx, y ∉ D₀.smallBall x hx := by
        intro y hy
        rw [hgq] at hy
        exact hlev₀ y ⟨by linarith [hy.1], hy.2⟩
      rw [← GradientLikeStrip.leftSphereHit_eq_leftSphereMap hg.smooth D₀ hqc hμ₀ hε₀
        (by linarith [hrm₀ q hqc]) hac (by rw [hgq]; exact hcβ₀) hU₀ y hy]
      refine (GradientLikeStrip.leftSphereHit_eq_of_rescale hg.smooth hg₁.smooth D₀ E hresc₂
        hχ₂ hqc hμ₀ hε₀ hε₁ (by linarith [hrm₀ q hqc]) (by linarith [(hεr q hqc).2])
        (by rw [hgq]; exact hcβ₀) (by rw [hqβ]; linarith) hsub ?_ y hy).symm
      intro w hw
      have hw' : (Handle.reidx w : Fin (D₀.chart q hqc).k → ℝ) ≠ 0 := by
        intro h0
        apply hw
        ext j
        have := congrFun h0 ⟨j, by rw [hμ₀]; exact j.isLt⟩
        have hj : (j : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp j.isLt
        simpa [Handle.reidx, hj] using this
      have hz := GradientLikeStrip.f_chart_of_mem_leftModelSphere' hqc (hrm₀ q hqc)
        ((D₀.chart q hqc).sphereParam_mem_leftModelSphere hε₀.le hw')
      refine ⟨g q - ε₀ - B.c, by linarith, ?_⟩
      have hfl := GradientLikeStrip.f_flow_eq_sub_of_levels (D := D₀) hg.smooth
        (x := (D₀.chart q hqc).χ ((D₀.chart q hqc).sphereParam ε₀ (Handle.reidx w)))
        (T := g q - ε₀ - B.c) (by rw [hz, hgq]; constructor <;> linarith)
        (by rw [hz]; constructor <;> linarith) (by
          intro y hy
          rw [hz, uIcc_of_ge (by linarith)] at hy
          rw [hgq] at hy
          exact hlev₀ y ⟨by linarith [hy.1], by linarith [hy.2]⟩)
        (g q - ε₀ - B.c) right_mem_uIcc
      rw [hfl, hz]
      linarith
    · have hμ : (E.chart q₂ hq₂c).k = ℓ + 1 := hkQ q₂ hq₂c hq₂Q
      refine GradientLikeStrip.leftSphereMap_eq_of_rescale hg₁.smooth hg.smooth E D₀ hresc₁
        hχ₁ hq₂c hμ hε₁ hε₀ (by linarith [(hεr q₂ hq₂c).2]) (by linarith [hrm₀ q₂ hq₂c]) hac
        hq₂c' (by rw [hgq₂]; exact hcβ₀) ?_ ?_ hlevc y hy
      · intro y hy x hx hyx
        have h := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hyx
        have hr := (hεr x hx).1
        rw [abs_lt] at h
        by_cases hxq : x = q₂
        · subst hxq
          linarith [hy.2]
        · rcases hlevs x hx hxq with h' | h' | h'
          · rw [h'] at h
            linarith [hy.1, hy.2]
          · rw [h'] at h
            linarith [hy.1, hy.2]
          · linarith [hy.1, hy.2]
      · intro y hy
        rw [hgq₂] at hy
        exact hlev₀ y ⟨by linarith [hy.1], hy.2⟩
  have hBlev : ∀ y, g y ∈ Icc (B.α + B'.ε) (B.β - B'.ε) → ∀ x hx, y ∉ B'.D.smallBall x hx := by
    intro y hy
    rw [← hBα, ← hBβ] at hy
    exact B'.hlev y hy
  obtain ⟨k₁, k₂⟩ := key B'.crit hBcrit B'.D B'.ε B'.hε B'.hrm
    (by have := B'.hαc; rw [hBα, hBc] at this; exact this)
    (by have := B'.hcβ; rw [hBβ, hBc] at this; exact this) hBlev
    (fun x hx hx' => ⟨(hBch x hx hx').1.trans (hχ' x hx).1,
      (hBch x hx hx').2.trans (hχ' x hx).2.1⟩) hφ₀
  exact ⟨g, hmodab, hmodc, hg, hsame, B', hBcrit, hBc, hBα, hBε'.trans hε'ε,
    fun x hx hx' => ⟨(hBch x hx hx').1.trans (hχ' x hx).1,
      (hBch x hx hx').2.trans (hχ' x hx).2.1⟩, hφ₀, k₁, k₂⟩

theorem exists_slide_classes (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) (hV₀ : PathConnectedSpace (f ⁻¹' {a})) {q₁ q₂ : M}
    (hq₁ : q₁ ∈ B.upperIndexCriticalPoints) (hq₂ : q₂ ∈ B.upperIndexCriticalPoints) (hne : q₁ ≠ q₂) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    (gD' : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift (Disk (ℓ + 1))))
      (ULift.down ⁻¹' diskSphere (ℓ + 1)) (ℓ + 1)) (hgD' : Handle.isGen gD') :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ sameCritIn I f g a b ∧
      ModifiedWithin f B.c b g ∧
      ∃ B' : BlockConfig I g a b ℓ, B'.crit = B.crit ∧ B'.c = B.c ∧ B'.α = B.α ∧ B'.ε ≤ B.ε ∧
        (∀ x (hx : x ∈ B.crit) (hx' : x ∈ B'.crit), (B'.D.chart x hx').χ = (B.D.chart x hx).χ ∧
          (B'.D.chart x hx').k = (B.D.chart x hx).k) ∧
        (∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
          ∀ z, f z ≤ B.c → B'.D.V z = φ z • B.D.V z) ∧
        Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a})
            (B'.D.leftSphereMap q₁ (ℓ + 1) B'.ε B.c) (Handle.boundaryGen gD') =
          Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a})
              (B.D.leftSphereMap q₁ (ℓ + 1) B.ε B.c) (Handle.boundaryGen gD') +
            δ • Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a})
              (B.D.leftSphereMap q₂ (ℓ + 1) B.ε B.c) (Handle.boundaryGen gD') ∧
        ∀ q ∈ B.upperIndexCriticalPoints, q ≠ q₁ →
          Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a})
              (B'.D.leftSphereMap q (ℓ + 1) B'.ε B.c) (Handle.boundaryGen gD') =
            Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a})
              (B.D.leftSphereMap q (ℓ + 1) B.ε B.c) (Handle.boundaryGen gD') := by
  classical
  have hq₁c : q₁ ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq₁).1
  have hq₂c : q₂ ∈ B.crit := (B.mem_upperIndexCriticalPoints.1 hq₂).1
  obtain ⟨g₁, hmod₁, hmod₁c, hg₁, hsame₁, hlev₁, hcrit₁, D₁, ε₁, hε₁, hε₁B, hεr₁, hchart₁,
    hcq₂, hq₂q₁, hunit₁, hslab₁, hnoc₁, hrmgap₁, ⟨φ₁, hφ₁c, ⟨m₁, M₁, hm₁, hφ₁b⟩, hφ₁V⟩,
    hsph₁, hsph₂⟩ := exists_lowered_stage hf B hℓ hℓn hq₁ hq₂ hne
  have hfq₁ : f q₁ = B.β := B.hQ q₁ hq₁c (B.mem_upperIndexCriticalPoints.1 hq₁).2
  have hg₁q₁ : g₁ q₁ = B.β := by rw [hlev₁ q₁ hq₁c hne, hfq₁]
  have hidx₁ : ∀ x ∈ B.crit, morseIndex I g₁ x = morseIndex I f x := fun x hx =>
    hsame₁.2 x ((B.hcrit x).1 hx).1 ((B.hcrit x).1 hx).2
  have hkq : ∀ q (hq : q ∈ B.upperIndexCriticalPoints), (D₁.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).k = ℓ + 1 := fun q hq => by
    rw [(hchart₁ q (B.mem_upperIndexCriticalPoints.1 hq).1).2, ← (B.D.chart q (B.mem_upperIndexCriticalPoints.1 hq).1).hkidx]
    exact (B.mem_upperIndexCriticalPoints.1 hq).2
  have hac : a < B.c := by linarith [B.haα, B.hαc, B.hε]
  have hq₁b : g₁ q₁ < b := by rw [hg₁q₁]; exact B.hβb
  have hαβ : B.α < B.β := by linarith [B.hαc, B.hcβ, B.hε]
  have hidxL : ∀ x ∈ B.crit, g₁ x = g₁ q₁ → morseIndex I g₁ x = ℓ + 1 := by
    intro x hx hxl
    rw [hidx₁ x hx]
    by_cases hxq₂ : x = q₂
    · subst hxq₂; exact (B.mem_upperIndexCriticalPoints.1 hq₂).2
    · have hfx : f x = B.β := by rw [← hlev₁ x hx hxq₂, hxl, hg₁q₁]
      have h1 := B.hmin x hx
      rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with h2 | h2
      · exact absurd (B.hhigh x hx h2) (by rw [hfx]; exact lt_irrefl _)
      · rcases Nat.lt_or_ge (morseIndex I f x) (ℓ + 1) with h3 | h3
        · have h4 : morseIndex I f x = ℓ := by omega
          have := B.hP x hx h4
          linarith
        · omega
  have hidx : ∀ x ∈ B.crit, g₁ x < g₁ q₁ →
      2 ≤ morseIndex I g₁ x ∧ morseIndex I g₁ x + 2 ≤ n := by
    intro x hx hxl
    rw [hidx₁ x hx]
    have h1 := B.hmin x hx
    have h2 : morseIndex I f x ≤ ℓ + 1 := by
      by_cases hxq₂ : x = q₂
      · subst hxq₂; exact (B.mem_upperIndexCriticalPoints.1 hq₂).2.le
      · have hfx : f x < B.β := by rw [← hlev₁ x hx hxq₂, ← hg₁q₁]; exact hxl
        by_contra h3
        have := B.hhigh x hx (by omega)
        linarith
    omega
  have hV₀' : PathConnectedSpace ↥(g₁ ⁻¹' {a}) := by
    rw [hmod₁.preimage_singleton_left]; exact hV₀
  obtain ⟨E, hEchart, hErm, ⟨c₂, κ, hc₂lo, hc₂hi, hEV⟩, hclass, hothers, hq₂sph, ⟨ρ, hρ, hnocE⟩⟩ :=
    GradientLikeStrip.exists_slideField hg₁ D₁ hcrit₁ hε₁ hεr₁ hℓ hℓn hq₁c hq₂c hne
      (hkq q₁ hq₁) (hkq q₂ hq₂) hac hcq₂ hq₂q₁ hq₁b hunit₁ hslab₁ hidxL hidx hnoc₁ hrmgap₁ hV₀' hδ
      gD' hgD'
  have hεrE : ∀ x hx, (E.chart x hx).r₀ ^ 2 < 2 * ε₁ ∧ 8 * ε₁ < E.rm x hx ^ 2 := by
    intro x hx; rw [hEchart x hx, hErm x hx]; exact hεr₁ x hx
  have hq₂lev : B.c < g₁ q₂ - ε₁ ∧ g₁ q₂ + ε₁ < B.β - ε₁ := ⟨hcq₂, by rw [← hg₁q₁]; exact hq₂q₁⟩
  have hnocE' : ∃ ρ > 0, ∀ x (hx : x ∈ B.crit), g₁ x = B.β → x ≠ q₂ →
      E.noCommon q₂ (B.mem_upperIndexCriticalPoints.1 hq₂).1 x hx ρ ρ :=
    ⟨ρ, hρ, fun x hx hxβ hxq₂ => hnocE x hx (by rw [hxβ, hg₁q₁]) hxq₂⟩
  obtain ⟨g, hmod₂, hmod₂c, hg, hsame₂, B', hB'crit, hB'c, hB'α, hB'ε, hB'chart,
    ⟨φ₃, hφ₃c, ⟨m₃, M₃, hm₃, hφ₃b⟩, hφ₃V⟩, hsph'q, hsph'q₂⟩ :=
    exists_merged_stage B hq₂ hg₁ hcrit₁ hidx₁ hlev₁ E hε₁ hε₁B hεrE hq₂lev hnocE'
  have hIcc : g₁ ⁻¹' Icc a B.c = f ⁻¹' Icc a B.c := by
    ext x
    by_cases hx : f x ∈ Ioo B.c b
    · have hg := hmod₁c.mapsTo hx
      simp only [mem_preimage, mem_Icc]
      constructor
      · intro h; exact absurd h.2 (not_le.2 hg.1)
      · intro h; exact absurd h.2 (not_le.2 hx.1)
    · simp only [mem_preimage, hmod₁c.eqOn hx]
  have hsing : g₁ ⁻¹' {a} = f ⁻¹' {a} := hmod₁.preimage_singleton_left
  have hSne : ∀ z ∈ SingularPair.unitSphere ℓ, z ≠ 0 := by
    intro z hz h
    subst h
    simp at hz
  have key : ∀ {F G : EuclideanSpace ℝ (Fin (ℓ + 1)) → M}, (∀ y, y ≠ 0 → F y = G y) →
      Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a}) F (Handle.boundaryGen gD') =
        Handle.sphereClass (f ⁻¹' Icc a B.c) (f ⁻¹' {a}) G (Handle.boundaryGen gD') :=
    fun h => Handle.sphereClass_congr _ _ (fun z hz => h z (hSne z hz)) _
  have hclass' := hclass
  rw [hIcc, hsing] at hclass'
  refine ⟨g, hmod₁.trans hmod₂, hg, hsame₁.trans hmod₁ hsame₂, hmod₁c.trans hmod₂c, B', hB'crit,
    hB'c, hB'α, hB'ε.trans hε₁B, ?_, ?_, ?_, ?_⟩
  · intro x hx hx'
    rw [(hB'chart x hx hx').1, (hB'chart x hx hx').2, hEchart x hx]
    exact hchart₁ x hx
  · refine ⟨fun z => φ₃ z * φ₁ z, hφ₃c.mul hφ₁c, ⟨m₃ * m₁, M₃ * M₁, mul_pos hm₃ hm₁, fun x => ?_⟩,
      fun z hz => ?_⟩
    · obtain ⟨h31, h32⟩ := hφ₃b x
      obtain ⟨h11, h12⟩ := hφ₁b x
      exact ⟨mul_le_mul h31 h11 hm₁.le (hm₃.le.trans h31),
        mul_le_mul h32 h12 (hm₁.le.trans h11) ((hm₃.le.trans h31).trans h32)⟩
    · have hg₁z : g₁ z = f z := hmod₁c.eqOn (fun h => absurd h.1 (not_lt.2 hz))
      have hEz : E.V z = D₁.V z := by
        apply hEV
        intro h
        have := h.1
        linarith
      rw [hφ₃V z, hEz, hφ₁V z hz, smul_smul]
  · rw [key (hsph'q q₁ hq₁ hne), hclass', key (hsph₁ q₁ hq₁ hne), key hsph₂]
  · intro q hq hqq₁
    by_cases hqq₂ : q = q₂
    · subst hqq₂
      rw [key hsph'q₂, key hq₂sph, key hsph₂]
    · have hgq : g₁ q = g₁ q₁ := by
        rw [hlev₁ q (B.mem_upperIndexCriticalPoints.1 hq).1 hqq₂, B.hQ q (B.mem_upperIndexCriticalPoints.1 hq).1 (B.mem_upperIndexCriticalPoints.1 hq).2, hg₁q₁]
      rw [key (hsph'q q hq hqq₂), key (hothers q (B.mem_upperIndexCriticalPoints.1 hq).1 hgq hqq₁),
        key (hsph₁ q hq hqq₂)]

open Classical in
theorem exists_slide (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ) (htr : B.transverse)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) (hV₀ : PathConnectedSpace (f ⁻¹' {a}))
    {p₀ : M} (hp₀ : p₀ ∈ B.lowerIndexCriticalPoints) {q₁ q₂ : M} (hq₁ : q₁ ∈ B.upperIndexCriticalPoints) (hq₂ : q₂ ∈ B.upperIndexCriticalPoints) (hne : q₁ ≠ q₂)
    {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ sameCritIn I f g a b ∧
      ∃ B' : BlockConfig I g a b ℓ, B'.crit = B.crit ∧ B'.lowerIndexCriticalPoints = B.lowerIndexCriticalPoints ∧ B'.upperIndexCriticalPoints = B.upperIndexCriticalPoints ∧
        B'.transverse ∧ ∀ q ∈ B.upperIndexCriticalPoints, |B'.count p₀ q| = |colOp (B.count p₀) q₁ q₂ s q| := by
  classical
  have hlevel : ∀ (F : M → ℝ) (C : BlockConfig I F a b ℓ), ∀ x ∈ C.crit,
      C.α ≤ F x ∧ (F x ≤ C.c → F x = C.α ∧ morseIndex I F x = ℓ) := by
    intro F C x hx
    have hm := C.hmin x hx
    have h1 := C.hαc
    have h2 := C.hcβ
    have h3 := C.hε
    rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I F x) with hlt | hle
    · have := C.hhigh x hx hlt
      exact ⟨by linarith, fun h => absurd h (by linarith)⟩
    · rcases Nat.eq_or_lt_of_le hm with heq | hlt
      · have := C.hP x hx heq.symm
        exact ⟨this.ge, fun _ => ⟨this, heq.symm⟩⟩
      · have hq : morseIndex I F x = ℓ + 1 := by omega
        have := C.hQ x hx hq
        exact ⟨by linarith, fun h => absurd h (by linarith)⟩
  have hlow : ∀ (F : M → ℝ) (C : BlockConfig I F a b ℓ) (y : M), F y ≤ C.α - C.ε →
      ∀ x (hx : x ∈ C.crit), y ∉ C.D.smallBall x hx := by
    intro F C y hy x hx hmem
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hmem
    have h2 := C.hr₀ x hx
    have h3 := (hlevel F C x hx).1
    rw [abs_lt] at h1
    linarith
  obtain ⟨ε₁, hε₁, hε₁ε, hε₁a⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ B.ε ∧ a < B.α - ε₁ :=
    ⟨min B.ε ((B.α - a) / 2), lt_min B.hε (by linarith [B.haα]), min_le_left _ _,
      by have := min_le_right B.ε ((B.α - a) / 2); linarith [B.haα]⟩
  obtain ⟨B₀, hcrit₀, hα₀, -, -, hεB₀, -, -, -, -, -, -, hpair₀⟩ :=
    B.exists_shrink hf hε₁ hε₁ε (ρ := 8 * ε₁ + 1) (by linarith) (by nlinarith)
  have hP₀ : B₀.lowerIndexCriticalPoints = B.lowerIndexCriticalPoints := BlockConfig.lowerIndexCriticalPoints_eq_of_crit_eq B hcrit₀
  have hQ₀ : B₀.upperIndexCriticalPoints = B.upperIndexCriticalPoints := BlockConfig.upperIndexCriticalPoints_eq_of_crit_eq B hcrit₀
  have htr₀ : B₀.transverse := by
    intro p hp q hq
    rw [hP₀] at hp
    rw [hQ₀] at hq
    exact (hpair₀ p hp q hq).1.2 (htr p hp q hq)
  have hq₁₀ : q₁ ∈ B₀.upperIndexCriticalPoints := by rw [hQ₀]; exact hq₁
  have hq₂₀ : q₂ ∈ B₀.upperIndexCriticalPoints := by rw [hQ₀]; exact hq₂
  have hp₀₀ : p₀ ∈ B₀.lowerIndexCriticalPoints := by rw [hP₀]; exact hp₀
  obtain ⟨gD', hgD', hgS⟩ := Handle.exists_disc_generator.{u_2} ℓ (by omega)
  have hgen : ∃ gD : SingularPair.relativeHomology SingularPair.integerCoefficients (TopCat.of (ULift.{u_2} (Disk ℓ)))
      (ULift.down ⁻¹' diskSphere ℓ) ℓ, Handle.isGen gD := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    subst hk
    obtain ⟨g, hg, -⟩ := Handle.exists_disc_generator k (by omega)
    exact ⟨g, hg⟩
  obtain ⟨gD, hgD⟩ := hgen
  obtain ⟨s₀, hs₀, hsum₀⟩ := B₀.sphereClass_eq_sum hf htr₀ (by omega)
    (by rw [hα₀, hεB₀]; exact hε₁a) (Handle.boundaryGen gD') hgS gD hgD
  obtain ⟨g, hmod, hg, hsame, hmodc, B', hcrit', hc', hα', hε', hchart', hφ', hcl₁, hcl⟩ :=
    B₀.exists_slide_classes hf hℓ hℓn hV₀ hq₁₀ hq₂₀ hne hs gD' hgD'
  obtain ⟨B'', hcrit'', htr'', hc'', hα'', -, hε'', hchart'', hsph'', hφ''⟩ :=
    B'.exists_transverse hg
  obtain ⟨s₂, hs₂, hsum₂⟩ := B''.sphereClass_eq_sum hg htr'' (by omega)
    (by rw [hα'', hα', hα₀]; linarith) (Handle.boundaryGen gD') hgS gD hgD
  have hgf : ∀ y, f y ≤ B₀.c → g y = f y := fun y hy =>
    hmodc.eqOn (show y ∈ (f ⁻¹' Ioo B₀.c b)ᶜ from fun h => absurd hy (not_le.2 h.1))
  have hXc : g ⁻¹' Icc a B₀.c = f ⁻¹' Icc a B₀.c := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Icc]
    by_cases hy : f y ≤ B₀.c
    · rw [hgf y hy]
    · rw [not_le] at hy
      have hgy : B₀.c < g y := by
        by_cases hyb : f y < b
        · exact (hmodc.mapsTo (show y ∈ f ⁻¹' Ioo B₀.c b from ⟨hy, hyb⟩)).1
        · rw [hmodc.eqOn (show y ∈ (f ⁻¹' Ioo B₀.c b)ᶜ from fun h => hyb h.2)]; exact hy
      constructor <;> intro h <;> exfalso <;> linarith [h.2]
  have hV : g ⁻¹' {a} = f ⁻¹' {a} := hmod.preimage_singleton_left
  have hidx : ∀ x ∈ B.crit, morseIndex I g x = morseIndex I f x := fun x hx =>
    hsame.2 x ((B.hcrit x).1 hx).1 ((B.hcrit x).1 hx).2
  have hPQ : ∀ C : BlockConfig I g a b ℓ, C.crit = B.crit → C.lowerIndexCriticalPoints = B.lowerIndexCriticalPoints ∧ C.upperIndexCriticalPoints = B.upperIndexCriticalPoints := by
    intro C hC
    constructor
    · ext x
      rw [BlockConfig.mem_lowerIndexCriticalPoints, BlockConfig.mem_lowerIndexCriticalPoints, hC]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨hx, (hidx x hx).symm.trans h⟩
      · rintro ⟨hx, h⟩; exact ⟨hx, (hidx x hx).trans h⟩
    · ext x
      rw [BlockConfig.mem_upperIndexCriticalPoints, BlockConfig.mem_upperIndexCriticalPoints, hC]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨hx, (hidx x hx).symm.trans h⟩
      · rintro ⟨hx, h⟩; exact ⟨hx, (hidx x hx).trans h⟩
  have hcritB' : B'.crit = B.crit := hcrit'.trans hcrit₀
  have hcritB'' : B''.crit = B.crit := hcrit''.trans hcritB'
  obtain ⟨hP', hQ'⟩ := hPQ B' hcritB'
  obtain ⟨hP'', hQ''⟩ := hPQ B'' hcritB''
  have hdisc : ∀ (c₂ : Finset M) (D₂ : GradientLikeStrip I g a b c₂), c₂ = B₀.crit →
      ∀ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ B₀.ε →
      (∀ x (hx : x ∈ B₀.crit) (hx' : x ∈ c₂), (D₂.chart x hx').χ = (B₀.D.chart x hx).χ ∧
        (D₂.chart x hx').k = (B₀.D.chart x hx).k) →
      (∀ x (hx : x ∈ c₂), 8 * ε₂ < D₂.rm x hx ^ 2) →
      (∃ φ : M → ℝ, Continuous φ ∧ (∃ m M₀ : ℝ, 0 < m ∧ ∀ x, m ≤ φ x ∧ φ x ≤ M₀) ∧
        ∀ z, f z ≤ B₀.α → D₂.V z = φ z • B₀.D.V z) →
      (∀ y, g y ≤ B₀.α - ε₂ → ∀ x hx, y ∉ D₂.smallBall x hx) →
      ∀ p ∈ B₀.lowerIndexCriticalPoints, Handle.discClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a}) (D₂.leftDiscMap p ℓ ε₂ a) gD =
        Handle.discClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a}) (B₀.D.leftDiscMap p ℓ B₀.ε a) gD := by
    intro c₂ D₂ hc₂ ε₂ hε₂ hε₂B hχ hrm₂ hφ hU₂ p hp
    subst hc₂
    obtain ⟨hpc, hpidx⟩ := (BlockConfig.mem_lowerIndexCriticalPoints B₀).1 hp
    have hfp : f p = B₀.α := B₀.hP p hpc hpidx
    have hαc₀ := B₀.hαc
    have hε₀ := B₀.hε
    have hfg : ∀ y, f y ≤ f p → g y = f y := fun y hy => hgf y (by linarith)
    have hgp : g p = f p := hfg p le_rfl
    obtain ⟨φ, hφc, hφb, hφV⟩ := hφ
    refine GradientLikeStrip.discClass_leftDisc_eq_of_rescale hf.smooth hg.smooth B₀.D D₂
      (fun x hx => hχ x hx hx) hpc ((B₀.D.chart p hpc).hkidx.symm.trans hpidx) B₀.hε hε₂
      (B₀.hrm p hpc) (hrm₂ p hpc) hgp hfg ⟨φ, hφc, hφb, fun z hz => hφV z (hz.trans hfp.le)⟩
      ?_ (by linarith) (fun y hy x hx => hlow f B₀ y (by rw [← hfp]; exact hy.2) x hx)
      (fun y hy x hx => hU₂ y (by rw [hgp, hfp] at hy; exact hy.2) x hx) gD
    rw [max_eq_left hε₂B, hfp, hα₀, hεB₀]
    exact hε₁a
  have hdisc'' : ∀ p ∈ B₀.lowerIndexCriticalPoints,
      Handle.discClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a}) (B''.D.leftDiscMap p ℓ B''.ε a) gD =
        Handle.discClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a}) (B₀.D.leftDiscMap p ℓ B₀.ε a) gD := by
    refine hdisc B''.crit B''.D (hcrit''.trans hcrit') B''.ε B''.hε (hε''.trans hε')
      (fun x hx hx'' => ?_) B''.hrm ?_ (fun y hy x hx => hlow g B'' y (by rw [hα'', hα']; exact hy) x hx)
    · have hx' : x ∈ B'.crit := by rw [hcrit']; exact hx
      exact ⟨(hchart'' x hx' hx'').1.trans (hchart' x hx hx').1,
        (hchart'' x hx' hx'').2.trans (hchart' x hx hx').2⟩
    · obtain ⟨φ₁, hφ₁c, ⟨m₁, M₁, hm₁, hb₁⟩, hφ₁⟩ := hφ'
      obtain ⟨φ₂, hφ₂c, ⟨m₂, M₂, hm₂, hb₂⟩, hφ₂⟩ := hφ''
      refine ⟨fun z => φ₂ z * φ₁ z, hφ₂c.mul hφ₁c, ⟨m₂ * m₁, M₂ * M₁, mul_pos hm₂ hm₁,
        fun x => ⟨mul_le_mul (hb₂ x).1 (hb₁ x).1 hm₁.le (hm₂.trans_le (hb₂ x).1).le,
          mul_le_mul (hb₂ x).2 (hb₁ x).2 (hm₁.le.trans (hb₁ x).1)
            ((hm₂.le.trans (hb₂ x).1).trans (hb₂ x).2)⟩⟩, fun z hz => ?_⟩
      have hαc₀ := B₀.hαc
      have hε₀ := B₀.hε
      have hz' : f z ≤ B₀.c := by linarith
      have hgz : g z = f z := hgf z hz'
      rw [hφ₂ z (by rw [hgz, hα']; exact hz), hφ₁ z hz', smul_smul]
  have hmain : ∀ q ∈ B.upperIndexCriticalPoints,
      ∑ p ∈ B.lowerIndexCriticalPoints, (s₂ * B''.count p q) •
          Handle.discClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a}) (B₀.D.leftDiscMap p ℓ B₀.ε a) gD =
        ∑ p ∈ B.lowerIndexCriticalPoints, (s₀ * colOp (B₀.count p) q₁ q₂ s q) •
          Handle.discClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a}) (B₀.D.leftDiscMap p ℓ B₀.ε a) gD := by
    intro q hq
    have hq'' : q ∈ B''.upperIndexCriticalPoints := by rw [hQ'']; exact hq
    have hq' : q ∈ B'.upperIndexCriticalPoints := by rw [hQ']; exact hq
    have hq0 : q ∈ B₀.upperIndexCriticalPoints := by rw [hQ₀]; exact hq
    have e2 := hsum₂ q hq''
    rw [hc'', hc', hXc, hV, hP''] at e2
    have hS : Handle.sphereClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a})
          (B''.D.leftSphereMap q (ℓ + 1) B''.ε B₀.c) (Handle.boundaryGen gD') =
        Handle.sphereClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a})
          (B'.D.leftSphereMap q (ℓ + 1) B'.ε B₀.c) (Handle.boundaryGen gD') := by
      refine Handle.sphereClass_congr _ _ (fun z hz => ?_) _
      have hz0 : z ≠ 0 := by
        intro h0
        rw [h0] at hz
        simp at hz
      have := hsph'' q hq' z hz0
      rwa [hc'] at this
    calc ∑ p ∈ B.lowerIndexCriticalPoints, (s₂ * B''.count p q) •
          Handle.discClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a}) (B₀.D.leftDiscMap p ℓ B₀.ε a) gD
        = ∑ p ∈ B.lowerIndexCriticalPoints, (s₂ * B''.count p q) •
          Handle.discClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a}) (B''.D.leftDiscMap p ℓ B''.ε a) gD :=
          Finset.sum_congr rfl (fun p hp => by rw [hdisc'' p (by rw [hP₀]; exact hp)])
      _ = Handle.sphereClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a})
          (B''.D.leftSphereMap q (ℓ + 1) B''.ε B₀.c) (Handle.boundaryGen gD') := e2.symm
      _ = Handle.sphereClass (f ⁻¹' Icc a B₀.c) (f ⁻¹' {a})
          (B'.D.leftSphereMap q (ℓ + 1) B'.ε B₀.c) (Handle.boundaryGen gD') := hS
      _ = _ := by
        by_cases hqq : q = q₁
        · rw [hqq, hcl₁, hsum₀ q₁ hq₁₀, hsum₀ q₂ hq₂₀, hP₀]
          have hzs : ∀ (N : Type u_2) [AddCommGroup N] (t : Finset M) (F : M → N) (r : ℤ),
              r • ∑ i ∈ t, F i = ∑ i ∈ t, r • F i := fun N _ t F r => Finset.smul_sum
          rw [hzs]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [smul_smul, ← add_zsmul]
          congr 1
          simp only [colOp, Function.update_self]
          ring
        · rw [hcl q hq0 hqq, hsum₀ q hq0, hP₀]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          simp only [colOp, Function.update_of_ne hqq]
  have hαc₀ := B₀.hαc
  have hcβ₀ := B₀.hcβ
  have hβb₀ := B₀.hβb
  have hε₀ := B₀.hε
  obtain ⟨-, hind⟩ := GradientLikeStrip.slab_discClass_basis hf.smooth B₀.D B₀.hcrit B₀.hε
    (fun x hx => ⟨B₀.hr₀ x hx, B₀.hrm x hx⟩) (t := a) (τ := B₀.α) (t' := B₀.c) le_rfl
    (by rw [hεB₀, hα₀]; exact hε₁a) hαc₀ (by linarith)
    (fun x hx h => ((hlevel f B₀ x hx).2 h.2).1)
    (fun y hy w hw => by
      rcases hy with hy | hy
      · exact hlow f B₀ y hy.2 w hw
      · exact B₀.hlev y ⟨hy.1, by linarith [hy.2]⟩ w hw)
    (μ := ℓ) (fun x hx h => (B₀.D.chart x hx).hkidx.symm.trans
      ((hlevel f B₀ x hx).2 (by linarith)).2) (by omega) gD hgD
  rw [Set.Icc_self] at hind
  have hfilt : B₀.crit.filter (fun x => f x = B₀.α) = B.lowerIndexCriticalPoints := by
    rw [← hP₀]
    ext x
    rw [Finset.mem_filter, BlockConfig.mem_lowerIndexCriticalPoints]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, ((hlevel f B₀ x hx).2 (by linarith)).2⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, B₀.hP x hx h⟩
  rw [hfilt] at hind
  refine ⟨g, hmod, hg, hsame, B'', hcritB'', hP'', hQ'', htr'', fun q hq => ?_⟩
  have hzero := hind (fun p => s₂ * B''.count p q - s₀ * colOp (B₀.count p) q₁ q₂ s q)
    (by
      have hsub : ∀ (N : Type u_2) [AddCommGroup N] (t : Finset M) (F G : M → N),
          ∑ i ∈ t, (F i + -G i) = ∑ i ∈ t, F i + -∑ i ∈ t, G i := by
        intro N _ t F G
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_congr rfl (fun p _ => sub_zsmul _ _ _), hsub, hmain q hq, add_neg_cancel])
    p₀ hp₀
  have habs : ∀ t : ℤ, (t = 1 ∨ t = -1) → |t| = 1 := by
    rintro t (rfl | rfl) <;> simp
  have heq : |B''.count p₀ q| = |colOp (B₀.count p₀) q₁ q₂ s q| := by
    have h1 : s₂ * B''.count p₀ q = s₀ * colOp (B₀.count p₀) q₁ q₂ s q := sub_eq_zero.1 hzero
    have h2 := congrArg abs h1
    rwa [abs_mul, abs_mul, habs s₂ hs₂, habs s₀ hs₀, one_mul, one_mul] at h2
  rw [heq]
  have hrow : ∀ q' ∈ B.upperIndexCriticalPoints, B₀.count p₀ q' = B.count p₀ q' := fun q' hq' => (hpair₀ p₀ hp₀ q' hq').2.1
  simp only [colOp, Function.update_apply]
  split_ifs with h
  · rw [hrow q₁ hq₁, hrow q₂ hq₂]
  · rw [hrow q hq]

omit [SigmaCompactSpace M] in
theorem simplyConnected_level (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) :
    SimplyConnectedSpace (f ⁻¹' {B.c}) := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hεr : ∀ x hx, (B.D.chart x hx).r₀ ^ 2 < 2 * B.ε ∧ 8 * B.ε < B.D.rm x hx ^ 2 :=
    fun x hx => ⟨B.hr₀ x hx, B.hrm x hx⟩
  have hαβ : B.α < B.β := by linarith [B.hαc, B.hcβ, B.hε]
  have hcritα : ∀ x ∈ B.crit, B.α ≤ f x := by
    intro x hx
    rcases lt_trichotomy (morseIndex I f x) (ℓ + 1) with h | h | h
    · have : morseIndex I f x = ℓ := le_antisymm (by omega) (B.hmin x hx)
      exact (B.hP x hx this).ge
    · rw [B.hQ x hx h]; exact hαβ.le
    · exact (hαβ.trans (B.hhigh x hx h)).le
  have hcritc : ∀ x ∈ B.crit, f x ≤ B.c → morseIndex I f x = ℓ := by
    intro x hx hxc
    rcases lt_trichotomy (morseIndex I f x) (ℓ + 1) with h | h | h
    · exact le_antisymm (by omega) (B.hmin x hx)
    · rw [B.hQ x hx h] at hxc; linarith [B.hcβ, B.hε]
    · have := B.hhigh x hx h; linarith [B.hcβ, B.hε]
  have hmemP : ∀ x, x ∈ B.lowerIndexCriticalPoints ↔ x ∈ B.crit ∧ f x = B.α := by
    intro x
    rw [B.mem_lowerIndexCriticalPoints]
    constructor
    · rintro ⟨hx, hidx⟩; exact ⟨hx, B.hP x hx hidx⟩
    · rintro ⟨hx, hfx⟩
      exact ⟨hx, hcritc x hx (by rw [hfx]; linarith [B.hαc, B.hε])⟩
  have hbelow : ∀ y, f y ≤ B.α - B.ε → ∀ x hx, y ∉ B.D.smallBall x hx := by
    intro y hy x hx hmem
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hmem
    have h2 := B.hr₀ x hx
    have h3 := hcritα x hx
    rw [abs_lt] at h1
    linarith [h1.1]
  have hcb : B.c ≤ b := by linarith [B.hcβ, B.hβb, B.hε]
  by_cases hPne : B.lowerIndexCriticalPoints.Nonempty
  · obtain ⟨p, hp⟩ := hPne
    have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
    have hpα : f p = B.α := B.hP p hpc (B.mem_lowerIndexCriticalPoints.1 hp).2
    have hk1 : 1 ≤ (B.D.chart p hpc).k := by
      rw [← (B.D.chart p hpc).hkidx, (B.mem_lowerIndexCriticalPoints.1 hp).2]; omega
    obtain ⟨y, hy⟩ := (B.D.chart p hpc).leftModelSphere_nonempty hk1 B.hε.le
    have hfy := GradientLikeStrip.f_chart_of_mem_leftModelSphere' hpc (B.hrm p hpc) hy
    have hyrm := GradientLikeStrip.morseNorm_lt_rm_of_mem_leftModelSphere hpc (B.hrm p hpc) hy
    have hyball : y ∈ Metric.ball (0 : Fin n → ℝ) (B.D.chart p hpc).R' :=
      (B.D.chart p hpc).mem_ball_of_le (hyrm.le.trans (B.D.hrm p hpc).2)
    have hstrip := B.D.inStrip p hpc ⟨y, hyball, rfl⟩
    have haαε : a < B.α - B.ε := by
      have := hstrip.1
      rw [hfy, hpα] at this
      exact this
    set α' : ℝ := (a + (B.α - B.ε)) / 2 with hα'
    have haα' : a < α' := by rw [hα']; linarith
    have hα'α : α' < B.α - B.ε := by rw [hα']; linarith
    obtain ⟨e₁⟩ := GradientLikeStrip.nonempty_homeomorph_levels hfs B.D (c₁ := a) (c₂ := α')
      le_rfl haα'.le (by linarith [B.hαc, B.hε]) (fun y hy x hx =>
        hbelow y (by linarith [hy.2]) x hx)
    have hsc₁ : SimplyConnectedSpace ↥(f ⁻¹' {α'} ∩ univ) := by
      rw [inter_univ]
      exact e₁.toHomotopyEquiv.simplyConnectedSpace
    set κ : ℝ := (α' - a) / 2 with hκ
    have hκ0 : 0 < κ := by rw [hκ]; linarith
    have hsc₂ := GradientLikeStrip.simplyConnected_level_diff hfs B.D B.hε hεr hκ0
      (c := α') ⟨by rw [hκ]; linarith, by rw [hκ]; linarith [B.hαc, B.hε, B.hcβ, B.hβb]⟩
      (fun y hy x hx => hbelow y (by rw [hκ] at hy; linarith [hy.2]) x hx) B.lowerIndexCriticalPoints ∅
      (fun q hq hqP => by
        have hqα : f q = B.α := ((hmemP q).1 hqP).2
        refine ⟨by rw [hqα, hκ]; linarith, ?_⟩
        rw [← (B.D.chart q hq).hkidx, (B.mem_lowerIndexCriticalPoints.1 hqP).2]; omega)
      (fun p _ hp => absurd hp (Finset.notMem_empty p)) isOpen_univ hsc₁
    obtain ⟨e₃⟩ := GradientLikeStrip.nonempty_homeomorph_level_diff hfs B.D B.hcrit B.hε hεr
      (c₁ := α') (τ := B.α) (c₂ := B.c) haα'.le hα'α B.hαc hcb
      (fun x hx hxI => by
        have := hcritc x hx hxI.2
        exact B.hP x hx this)
      (fun y hy x hx => by
        rcases hy with hy | hy
        · exact hbelow y hy.2 x hx
        · exact B.hlev y ⟨hy.1, by linarith [hy.2, B.hcβ]⟩ x hx)
    have hset₂ : (f ⁻¹' {α'} ∩ univ) \ B.D.sphereUnion B.lowerIndexCriticalPoints ∅ B.ε α' =
        f ⁻¹' {α'} \ ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.α), B.D.leftSphere x hx B.ε α' := by
      rw [inter_univ]
      congr 1
      ext z
      simp only [GradientLikeStrip.sphereUnion, Set.mem_union, Set.mem_iUnion, exists_prop,
        Finset.notMem_empty, hmemP]
      constructor
      · rintro (⟨x, hx, ⟨_, hfx⟩, hz⟩ | ⟨x, _, hfalse, _⟩)
        · exact ⟨x, hx, hfx, hz⟩
        · exact hfalse.elim
      · rintro ⟨x, hx, hfx, hz⟩; exact Or.inl ⟨x, hx, ⟨hx, hfx⟩, hz⟩
    have hsc₃ : SimplyConnectedSpace
        ↥(f ⁻¹' {B.c} \ ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.α),
          B.D.rightSphere x hx B.ε B.c) := by
      have := hsc₂
      have : SimplyConnectedSpace ↥(f ⁻¹' {α'} \ ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.α),
          B.D.leftSphere x hx B.ε α') :=
        (Homeomorph.setCongr hset₂.symm).toHomotopyEquiv.simplyConnectedSpace
      exact e₃.toHomotopyEquiv.simplyConnectedSpace
    set κ' : ℝ := min ((B.c - (B.α + B.ε)) / 2) ((B.β - B.ε - B.c) / 2) with hκ'
    have hκ'0 : 0 < κ' := by
      rw [hκ']; exact lt_min (by linarith [B.hαc]) (by linarith [B.hcβ])
    have hκ'1 : κ' ≤ (B.c - (B.α + B.ε)) / 2 := min_le_left _ _
    have hκ'2 : κ' ≤ (B.β - B.ε - B.c) / 2 := min_le_right _ _
    have hset₄ : (f ⁻¹' {B.c} ∩ univ) \ B.D.sphereUnion ∅ B.lowerIndexCriticalPoints B.ε B.c =
        f ⁻¹' {B.c} \ ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.α),
          B.D.rightSphere x hx B.ε B.c := by
      rw [inter_univ]
      congr 1
      ext z
      simp only [GradientLikeStrip.sphereUnion, Set.mem_union, Set.mem_iUnion, exists_prop,
        Finset.notMem_empty, hmemP]
      constructor
      · rintro (⟨x, _, hfalse, _⟩ | ⟨x, hx, ⟨_, hfx⟩, hz⟩)
        · exact hfalse.elim
        · exact ⟨x, hx, hfx, hz⟩
      · rintro ⟨x, hx, hfx, hz⟩; exact Or.inr ⟨x, hx, ⟨hx, hfx⟩, hz⟩
    have hsc₄ : SimplyConnectedSpace ↥((f ⁻¹' {B.c} ∩ univ) \ B.D.sphereUnion ∅ B.lowerIndexCriticalPoints B.ε B.c) :=
      (Homeomorph.setCongr hset₄).toHomotopyEquiv.simplyConnectedSpace
    have hsc₅ := GradientLikeStrip.simplyConnected_level_of_diff hfs B.D B.hε hεr hκ'0
      (c := B.c) ⟨by linarith [B.hαc, B.hε, B.haα], by linarith [B.hβb, B.hcβ, B.hε]⟩
      (fun y hy x hx => B.hlev y ⟨by linarith [hy.1], by linarith [hy.2]⟩ x hx) ∅ B.lowerIndexCriticalPoints
      (fun q _ hq => absurd hq (Finset.notMem_empty q))
      (fun p hp hpP => by
        have hpα' : f p = B.α := ((hmemP p).1 hpP).2
        refine ⟨by rw [hpα']; linarith, ?_⟩
        rw [← (B.D.chart p hp).hkidx, (B.mem_lowerIndexCriticalPoints.1 hpP).2]; exact hℓ)
      isOpen_univ hsc₄
    rw [inter_univ] at hsc₅
    exact hsc₅
  · have hnone : ∀ x ∈ B.crit, B.β ≤ f x := by
      intro x hx
      by_contra hlt
      have hlt' : f x < B.β := not_le.1 hlt
      rcases lt_trichotomy (morseIndex I f x) (ℓ + 1) with h | h | h
      · have hidx : morseIndex I f x = ℓ := le_antisymm (by omega) (B.hmin x hx)
        exact hPne ⟨x, B.mem_lowerIndexCriticalPoints.2 ⟨hx, hidx⟩⟩
      · rw [B.hQ x hx h] at hlt'; exact lt_irrefl _ hlt'
      · have := B.hhigh x hx h; linarith
    obtain ⟨e⟩ := GradientLikeStrip.nonempty_homeomorph_levels hfs B.D (c₁ := a) (c₂ := B.c)
      le_rfl (by linarith [B.haα, B.hαc, B.hε]) hcb (fun y hy x hx hmem => by
        have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hmem
        have h2 := B.hr₀ x hx
        have h3 := hnone x hx
        rw [abs_lt] at h1
        linarith [h1.1, hy.2, B.hcβ])
    exact e.toHomotopyEquiv.simplyConnectedSpace

omit [SigmaCompactSpace M] in
theorem simplyConnected_level_diff_rightSphere (hf : MorseStrip I f a b)
    (B : BlockConfig I f a b ℓ) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) {p : M} (hp : p ∈ B.lowerIndexCriticalPoints) :
    SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.rightSphere p) := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hεr : ∀ x hx, (B.D.chart x hx).r₀ ^ 2 < 2 * B.ε ∧ 8 * B.ε < B.D.rm x hx ^ 2 :=
    fun x hx => ⟨B.hr₀ x hx, B.hrm x hx⟩
  have hε := B.hε
  have hαc := B.hαc
  have hcβ := B.hcβ
  have hpc : p ∈ B.crit := (B.mem_lowerIndexCriticalPoints.1 hp).1
  have hpα : f p = B.α := B.hP p hpc (B.mem_lowerIndexCriticalPoints.1 hp).2
  have hcases : ∀ x ∈ B.crit, (morseIndex I f x = ℓ ∧ f x = B.α) ∨
      (morseIndex I f x = ℓ + 1 ∧ f x = B.β) ∨ (ℓ + 1 < morseIndex I f x ∧ B.β < f x) := by
    intro x hx
    have h1 := B.hmin x hx
    rcases (by omega : morseIndex I f x = ℓ ∨ morseIndex I f x = ℓ + 1 ∨
        ℓ + 1 < morseIndex I f x) with h | h | h
    · exact Or.inl ⟨h, B.hP x hx h⟩
    · exact Or.inr (Or.inl ⟨h, B.hQ x hx h⟩)
    · exact Or.inr (Or.inr ⟨h, B.hhigh x hx h⟩)
  have hge : ∀ x ∈ B.crit, B.α ≤ f x := by
    intro x hx
    rcases hcases x hx with h | h | h
    · exact h.2.ge
    · linarith [h.2]
    · linarith [h.2]
  have hPiff : ∀ x ∈ B.crit, (f x = B.α ↔ x ∈ B.lowerIndexCriticalPoints) := by
    intro x hx
    constructor
    · intro hfx
      rcases hcases x hx with h | h | h
      · exact B.mem_lowerIndexCriticalPoints.2 ⟨hx, h.1⟩
      · exfalso; linarith [h.2]
      · exfalso; linarith [h.2]
    · intro hxP
      exact B.hP x hx (B.mem_lowerIndexCriticalPoints.1 hxP).2
  have hball : ∀ x hx, ∀ y ∈ B.D.smallBall x hx, B.α - B.ε < f y := by
    intro x hx y hy
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall (D := B.D) hx hy
    have h2 := B.hr₀ x hx
    have h3 := hge x hx
    rw [abs_lt] at h1
    linarith [h1.1]
  have haε : a < B.α - B.ε := by
    have hk : 1 ≤ (B.D.chart p hpc).k := by
      rw [← (B.D.chart p hpc).hkidx, (B.mem_lowerIndexCriticalPoints.1 hp).2]; omega
    obtain ⟨y, hy⟩ := (B.D.chart p hpc).leftModelSphere_nonempty hk B.hε.le
    have hfy := GradientLikeStrip.f_chart_of_mem_leftModelSphere' (D := B.D) hpc (B.hrm p hpc) hy
    have hny := GradientLikeStrip.morseNorm_lt_rm_of_mem_leftModelSphere (D := B.D) hpc
      (B.hrm p hpc) hy
    have hin := B.D.inStrip p hpc (B.D.modelBall_subset_image_ball p hpc ⟨y, hny, rfl⟩)
    have hin' : f ((B.D.chart p hpc).χ y) ∈ Ioo a b := hin
    rw [hfy, hpα] at hin'
    exact hin'.1
  set α' : ℝ := (a + (B.α - B.ε)) / 2 with hα'
  set κ₁ : ℝ := ((B.α - B.ε) - a) / 4 with hκ₁
  have hκ₁0 : 0 < κ₁ := by rw [hκ₁]; linarith
  have hβb := B.hβb
  have hSC1 : SimplyConnectedSpace ↥(f ⁻¹' {α'}) := by
    obtain ⟨e⟩ := GradientLikeStrip.nonempty_homeomorph_levels hfs B.D (c₁ := a) (c₂ := α')
      le_rfl (by rw [hα']; linarith) (by rw [hα']; linarith)
      (fun y hy x hx hyx => by
        have := hball x hx y hyx
        rw [hα'] at hy
        linarith [hy.2])
    exact e.toHomotopyEquiv.simplyConnectedSpace
  have hSC2 : SimplyConnectedSpace
      ↥((f ⁻¹' {α'} ∩ univ) \ B.D.sphereUnion B.lowerIndexCriticalPoints ∅ B.ε α') := by
    refine B.D.simplyConnected_level_diff hfs B.hε hεr hκ₁0 ⟨by rw [hα', hκ₁]; linarith,
      by rw [hα', hκ₁]; linarith⟩ ?_ B.lowerIndexCriticalPoints ∅ ?_ ?_ isOpen_univ ?_
    · intro y hy x hx hyx
      have := hball x hx y hyx
      rw [hα', hκ₁] at hy
      linarith [hy.2]
    · intro q hq hqP
      refine ⟨?_, ?_⟩
      · rw [(hPiff q hq).2 hqP, hα', hκ₁]; linarith
      · rw [← (B.D.chart q hq).hkidx, (B.mem_lowerIndexCriticalPoints.1 hqP).2]; omega
    · intro p' hp' hp'R
      exact absurd hp'R (Finset.notMem_empty p')
    · rw [Set.inter_univ]; exact hSC1
  have hSC3 : SimplyConnectedSpace
      ↥(f ⁻¹' {B.c} \ ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.α), B.D.rightSphere x hx B.ε B.c) := by
    obtain ⟨e⟩ := GradientLikeStrip.nonempty_homeomorph_level_diff hfs B.D B.hcrit B.hε hεr
      (c₁ := α') (τ := B.α) (c₂ := B.c) (by rw [hα']; linarith) (by rw [hα']; linarith)
      B.hαc (by linarith)
      (fun x hx hxI => by
        rcases hcases x hx with h | h | h
        · exact h.2
        · exfalso; linarith [hxI.2, h.2]
        · exfalso; linarith [hxI.2, h.2])
      (fun y hy x hx hyx => by
        rcases hy with hy | hy
        · have := hball x hx y hyx
          linarith [hy.2]
        · exact B.hlev y ⟨hy.1, by linarith [hy.2]⟩ x hx hyx)
    have hLeq : f ⁻¹' {α'} \ ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.α),
        B.D.leftSphere x hx B.ε α' = (f ⁻¹' {α'} ∩ univ) \ B.D.sphereUnion B.lowerIndexCriticalPoints ∅ B.ε α' := by
      ext y
      simp only [GradientLikeStrip.sphereUnion, Set.mem_sdiff, false_and, mem_inter_iff, mem_univ, and_true,
        mem_union, mem_iUnion, Finset.notMem_empty, exists_false, or_false, exists_prop]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rintro ⟨x, hx, hxP, hyx⟩
        exact h2 ⟨x, hx, (hPiff x hx).2 hxP, hyx⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rintro ⟨x, hx, hxα, hyx⟩
        exact h2 ⟨x, hx, (hPiff x hx).1 hxα, hyx⟩
    rw [← hLeq] at hSC2
    exact e.toHomotopyEquiv.simplyConnectedSpace
  set κ₄ : ℝ := min (B.c - (B.α + B.ε)) ((B.β - B.ε) - B.c) / 2 with hκ₄
  have hκ₄a : κ₄ ≤ (B.c - (B.α + B.ε)) / 2 := by
    rw [hκ₄]; linarith [min_le_left (B.c - (B.α + B.ε)) ((B.β - B.ε) - B.c)]
  have hκ₄b : κ₄ ≤ ((B.β - B.ε) - B.c) / 2 := by
    rw [hκ₄]; linarith [min_le_right (B.c - (B.α + B.ε)) ((B.β - B.ε) - B.c)]
  have hκ₄0 : 0 < κ₄ := by
    rw [hκ₄]; exact half_pos (lt_min (by linarith) (by linarith))
  have hRS : B.rightSphere p = B.D.rightSphere p hpc B.ε B.c := by
    simp only [BlockConfig.rightSphere, hpc, ↓reduceDIte]
  have hG : IsOpen (B.rightSphere p)ᶜ := by
    rw [hRS, isOpen_compl_iff]
    refine (B.D.isCompact_rightSphere p hpc ?_ B.c).isClosed
    have hrm0 := B.D.rm_pos p hpc
    have h1 := pow_le_pow_left₀ hrm0.le (B.D.hrm p hpc).2 2
    linarith [B.hrm p hpc]
  have hY : SimplyConnectedSpace
      ↥((f ⁻¹' {B.c} ∩ (B.rightSphere p)ᶜ) \ B.D.sphereUnion ∅ (B.lowerIndexCriticalPoints.erase p) B.ε B.c) := by
    have hReq : f ⁻¹' {B.c} \ ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.α),
        B.D.rightSphere x hx B.ε B.c =
        (f ⁻¹' {B.c} ∩ (B.rightSphere p)ᶜ) \ B.D.sphereUnion ∅ (B.lowerIndexCriticalPoints.erase p) B.ε B.c := by
      rw [hRS]
      ext y
      simp only [GradientLikeStrip.sphereUnion, Set.mem_sdiff, false_and, mem_inter_iff, mem_compl_iff,
        mem_union, mem_iUnion, Finset.notMem_empty, exists_false, false_or, exists_prop,
        Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, fun hyp => h2 ⟨p, hpc, hpα, hyp⟩⟩, ?_⟩
        rintro ⟨x, hx, ⟨-, hxP⟩, hyx⟩
        exact h2 ⟨x, hx, (hPiff x hx).2 hxP, hyx⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, ?_⟩
        rintro ⟨x, hx, hxα, hyx⟩
        by_cases hxp : x = p
        · subst hxp
          exact h2 hyx
        · exact h3 ⟨x, hx, ⟨hxp, (hPiff x hx).1 hxα⟩, hyx⟩
    rw [← hReq]
    exact hSC3
  have hfin := B.D.simplyConnected_level_of_diff hfs B.hε hεr hκ₄0
    ⟨by linarith [B.haα], by linarith⟩
    (fun y hy x hx hyx => B.hlev y ⟨by linarith [hy.1], by linarith [hy.2]⟩ x hx hyx)
    ∅ (B.lowerIndexCriticalPoints.erase p) (fun q hq hqL => absurd hqL (Finset.notMem_empty q))
    (fun p' hp' hp'R => by
      have hp'P := (Finset.mem_erase.1 hp'R).2
      refine ⟨?_, ?_⟩
      · rw [(hPiff p' hp').2 hp'P]; linarith
      · rw [← (B.D.chart p' hp').hkidx, (B.mem_lowerIndexCriticalPoints.1 hp'P).2]; exact hℓ)
    hG hY
  exact hfin

omit [SigmaCompactSpace M] in
theorem simplyConnected_level_diff_leftSphere (hf : MorseStrip I f a b)
    (B : BlockConfig I f a b ℓ) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n)
    (htop : ∀ x ∈ B.crit, morseIndex I f x ≤ ℓ + 1)
    (hV₁ : SimplyConnectedSpace (f ⁻¹' {b})) {q : M} (hq : q ∈ B.upperIndexCriticalPoints) :
    SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.leftSphere q) := by
  classical
  have hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := hf.smooth
  have hεr : ∀ x hx, (B.D.chart x hx).r₀ ^ 2 < 2 * B.ε ∧ 8 * B.ε < B.D.rm x hx ^ 2 :=
    fun x hx => ⟨B.hr₀ x hx, B.hrm x hx⟩
  have hεR : ∀ x hx, 2 * B.ε ≤ (B.D.chart x hx).R ^ 2 := fun x hx => by
    have h0 := B.D.rm_pos x hx
    have h1 := pow_le_pow_left₀ h0.le (B.D.hrm x hx).2 2
    linarith [B.hrm x hx, B.hε]
  have hval : ∀ x ∈ B.crit, (f x = B.α ∧ morseIndex I f x = ℓ) ∨
      (f x = B.β ∧ morseIndex I f x = ℓ + 1) := by
    intro x hx
    have h1 := B.hmin x hx
    have h2 := htop x hx
    by_cases h : morseIndex I f x = ℓ
    · exact Or.inl ⟨B.hP x hx h, h⟩
    · have h' : morseIndex I f x = ℓ + 1 := by omega
      exact Or.inr ⟨B.hQ x hx h', h'⟩
  have hαβ : B.α < B.β := by linarith [B.hαc, B.hcβ, B.hε]
  have hsmall : ∀ x hx, ∀ y ∈ B.D.smallBall x hx, |f y - f x| < B.ε := fun x hx y hy => by
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall (D := B.D) hx hy
    linarith [B.hr₀ x hx]
  have habove : ∀ y, B.β + B.ε ≤ f y → ∀ x hx, y ∉ B.D.smallBall x hx := by
    intro y hy x hx hmem
    have h1 := hsmall x hx y hmem
    rw [abs_lt] at h1
    rcases hval x hx with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
  have hQiff : ∀ x (hx : x ∈ B.crit), x ∈ B.upperIndexCriticalPoints ↔ f x = B.β := by
    intro x hx
    rw [B.mem_upperIndexCriticalPoints]
    constructor
    · rintro ⟨-, h⟩
      exact B.hQ x hx h
    · intro h
      refine ⟨hx, ?_⟩
      rcases hval x hx with ⟨h', -⟩ | ⟨-, h'⟩
      · exfalso; linarith
      · exact h'
  obtain ⟨hqc, hqidx⟩ := B.mem_upperIndexCriticalPoints.1 hq
  have hkQ : ∀ x (hx : x ∈ B.crit), x ∈ B.upperIndexCriticalPoints → (B.D.chart x hx).k = ℓ + 1 := by
    intro x hx hxQ
    exact (B.D.chart x hx).hkidx.symm.trans (B.mem_upperIndexCriticalPoints.1 hxQ).2
  have hβεb : B.β + B.ε < b := by
    have hkq := hkQ q hqc hq
    have hkn : (B.D.chart q hqc).k < n := by omega
    let j : Fin (n - (B.D.chart q hqc).k) := ⟨0, by omega⟩
    let v : EuclideanSpace ℝ (Fin (n - (B.D.chart q hqc).k)) :=
      EuclideanSpace.single j (Real.sqrt (2 * B.ε))
    let y : Fin n → ℝ := recombine (B.D.chart q hqc).hk 0 v
    have hy : y ∈ (B.D.chart q hqc).rightModelSphere B.ε := by
      refine ⟨DifferentialGeometry.Topology.Morse.CellAttachment.negPart_recombine _ _ _, ?_⟩
      rw [DifferentialGeometry.Topology.Morse.CellAttachment.posPart_recombine]
      have hv : ‖v‖ = Real.sqrt (2 * B.ε) := by
        simp only [v, PiLp.norm_single, Real.norm_eq_abs]
        exact abs_of_nonneg (Real.sqrt_nonneg _)
      rw [hv, Real.sq_sqrt (by linarith [B.hε])]
    have hfy := (B.D.chart q hqc).f_chart_of_mem_rightModelSphere (hεR q hqc) hy
    have hstrip : f ((B.D.chart q hqc).χ y) ∈ Ioo a b := B.D.inStrip q hqc ⟨y,
      (B.D.chart q hqc).mem_ball_of_le
        ((B.D.chart q hqc).morseNorm_le_R_of_mem_rightModelSphere (hεR q hqc) hy), rfl⟩
    rw [hfy, B.hQ q hqc hqidx] at hstrip
    exact hstrip.2
  set β' : ℝ := (B.β + B.ε + b) / 2 with hβ'
  set κ : ℝ := (b - B.β - B.ε) / 4 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  have haα := B.haα
  have hαc := B.hαc
  have hcβ := B.hcβ
  have hε := B.hε
  obtain ⟨e₁⟩ := GradientLikeStrip.nonempty_homeomorph_levels hfs B.D (c₁ := β') (c₂ := b)
    (by rw [hβ']; linarith) (by rw [hβ']; linarith) le_rfl
    (fun y hy x hx => habove y (by rw [hβ'] at hy; linarith [hy.1]) x hx)
  have : SimplyConnectedSpace ↥(f ⁻¹' {β'}) := e₁.symm.toHomotopyEquiv.simplyConnectedSpace
  have hsc₁ : SimplyConnectedSpace ↥(f ⁻¹' {β'} ∩ univ) :=
    (Homeomorph.setCongr (inter_univ _)).toHomotopyEquiv.simplyConnectedSpace
  have hsc₂ := GradientLikeStrip.simplyConnected_level_diff hfs B.D B.hε hεr (c := β') (κ := κ)
    hκ ⟨by rw [hβ', hκdef]; linarith, by rw [hβ', hκdef]; linarith⟩
    (fun y hy x hx => habove y (by rw [hβ', hκdef] at hy; linarith [hy.1]) x hx) ∅ B.upperIndexCriticalPoints
    (fun x _ hx => absurd hx (Finset.notMem_empty x))
    (fun x hx hxQ => ⟨by rw [(hQiff x hx).1 hxQ, hβ', hκdef]; linarith,
      by rw [hkQ x hx hxQ]; omega⟩) isOpen_univ hsc₁
  have hU1 : B.D.sphereUnion ∅ B.upperIndexCriticalPoints B.ε β' =
      ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.β), B.D.rightSphere x hx B.ε β' := by
    unfold GradientLikeStrip.sphereUnion
    ext y
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨x, hx, hx', -⟩ | ⟨x, hx, hxQ, hy⟩)
      · exact absurd hx' (Finset.notMem_empty x)
      · exact ⟨x, hx, (hQiff x hx).1 hxQ, hy⟩
    · rintro ⟨x, hx, hxβ, hy⟩
      exact Or.inr ⟨x, hx, (hQiff x hx).2 hxβ, hy⟩
  have h3 : f ⁻¹' {β'} \
      ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.β), B.D.rightSphere x hx B.ε β' =
      (f ⁻¹' {β'} ∩ univ) \ B.D.sphereUnion ∅ B.upperIndexCriticalPoints B.ε β' := by
    rw [hU1, inter_univ]
  have hsc₃ : SimplyConnectedSpace ↥(f ⁻¹' {β'} \
      ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.β), B.D.rightSphere x hx B.ε β') :=
    (Homeomorph.setCongr h3).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨e₂⟩ := GradientLikeStrip.nonempty_homeomorph_level_diff hfs B.D B.hcrit B.hε hεr
    (c₁ := B.c) (τ := B.β) (c₂ := β') (by linarith) hcβ (by rw [hβ']; linarith)
    (by rw [hβ']; linarith)
    (fun x hx hxI => by
      rcases hval x hx with ⟨h, -⟩ | ⟨h, -⟩
      · exfalso; linarith [hxI.1]
      · exact h)
    (fun y hy x hx => by
      rcases hy with hy | hy
      · exact B.hlev y ⟨by linarith [hy.1], hy.2⟩ x hx
      · exact habove y hy.1 x hx)
  have hsc₄ : SimplyConnectedSpace ↥(f ⁻¹' {B.c} \
      ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.β), B.D.leftSphere x hx B.ε B.c) :=
    e₂.symm.toHomotopyEquiv.simplyConnectedSpace
  have hLq : B.leftSphere q = B.D.leftSphere q hqc B.ε B.c := by
    simp only [BlockConfig.leftSphere, hqc, dite_true]
  set κ' : ℝ := min (B.c - B.α - B.ε) (B.β - B.ε - B.c) / 2 with hκ'def
  have hκ'1 : κ' ≤ (B.c - B.α - B.ε) / 2 := by
    rw [hκ'def]; linarith [min_le_left (B.c - B.α - B.ε) (B.β - B.ε - B.c)]
  have hκ'2 : κ' ≤ (B.β - B.ε - B.c) / 2 := by
    rw [hκ'def]; linarith [min_le_right (B.c - B.α - B.ε) (B.β - B.ε - B.c)]
  have hκ' : 0 < κ' := by
    rw [hκ'def]
    have : 0 < min (B.c - B.α - B.ε) (B.β - B.ε - B.c) := lt_min (by linarith) (by linarith)
    linarith
  have hset : (f ⁻¹' {B.c} ∩ (B.leftSphere q)ᶜ) \ B.D.sphereUnion (B.upperIndexCriticalPoints.erase q) ∅ B.ε B.c =
      f ⁻¹' {B.c} \
        ⋃ (x : M) (hx : x ∈ B.crit) (_ : f x = B.β), B.D.leftSphere x hx B.ε B.c := by
    rw [hLq]
    unfold GradientLikeStrip.sphereUnion
    ext y
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, mem_union, mem_iUnion, not_or,
      not_exists]
    constructor
    · rintro ⟨⟨hyc, hyq⟩, hyL, -⟩
      refine ⟨hyc, fun x hx hxβ hyx => ?_⟩
      by_cases hxq : x = q
      · subst hxq
        exact hyq hyx
      · exact hyL x hx (Finset.mem_erase.2 ⟨hxq, (hQiff x hx).2 hxβ⟩) hyx
    · rintro ⟨hyc, hy⟩
      refine ⟨⟨hyc, fun hyq => hy q hqc ((hQiff q hqc).1 hq) hyq⟩,
        fun x hx hxE hyx => hy x hx ((hQiff x hx).1 (Finset.mem_of_mem_erase hxE)) hyx,
        fun x _ hx => absurd hx (Finset.notMem_empty x)⟩
  have hsc₅ : SimplyConnectedSpace
      ↥((f ⁻¹' {B.c} ∩ (B.leftSphere q)ᶜ) \ B.D.sphereUnion (B.upperIndexCriticalPoints.erase q) ∅ B.ε B.c) :=
    (Homeomorph.setCongr hset).toHomotopyEquiv.simplyConnectedSpace
  have hG : IsOpen (B.leftSphere q)ᶜ := by
    rw [hLq]
    exact (B.D.isCompact_leftSphere q hqc (hεR q hqc) B.c).isClosed.isOpen_compl
  have hfin := GradientLikeStrip.simplyConnected_level_of_diff hfs B.D B.hε hεr (c := B.c)
    (κ := κ') hκ' ⟨by linarith, by linarith⟩
    (fun y hy x hx => B.hlev y ⟨by linarith [hy.1], by linarith [hy.2]⟩ x hx) (B.upperIndexCriticalPoints.erase q) ∅
    (fun x hx hxE => ⟨by rw [(hQiff x hx).1 (Finset.mem_of_mem_erase hxE)]; linarith,
      by rw [hkQ x hx (Finset.mem_of_mem_erase hxE)]; omega⟩)
    (fun x _ hx => absurd hx (Finset.notMem_empty x)) hG hsc₅
  exact hfin

omit [SigmaCompactSpace M] in
theorem whitney_pair_removal (h6 : 6 ≤ n) (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints)
    (htr : B.pairTransverse p q) (hlt : (B.count p q).natAbs < B.zerosCard p q)
    (hπ : SimplyConnectedSpace (f ⁻¹' {B.c}))
    (hπR : ℓ = 2 → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.rightSphere p))
    (hπL : ℓ + 3 = n → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.leftSphere q)) :
    ∃ B' : BlockConfig I f a b ℓ, B'.crit = B.crit ∧ B'.pairTransverse p q ∧
      B'.count p q = B.count p q ∧ B'.zerosCard p q + 2 = B.zerosCard p q := by
  classical
  set d : ℝ := min (B.c - B.α) (B.β - B.c) with hd
  have hd0 : 0 < d := lt_min (by linarith [B.hαc, B.hε]) (by linarith [B.hcβ, B.hε])
  set ρ : ℝ := min 1 (d / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (by linarith)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρd : ρ ≤ d / 2 := min_le_right _ _
  have hρ2 : ρ ^ 2 < d := by nlinarith
  set ε₁ : ℝ := min B.ε (ρ ^ 2 / 16) with hε₁def
  have hε₁0 : 0 < ε₁ := lt_min B.hε (by positivity)
  have hε₁ε : ε₁ ≤ B.ε := min_le_left _ _
  have hε₁ρ : 8 * ε₁ < ρ ^ 2 := by
    have : ε₁ ≤ ρ ^ 2 / 16 := min_le_right _ _
    nlinarith [pow_pos hρ0 2]
  obtain ⟨B₁, hcrit, hα₁, hβ₁, hc₁, -, hchart₁, -, -, hL₁, hR₁, -, hdata₁⟩ :=
    B.exists_shrink hf hε₁0 hε₁ε hρ0 hε₁ρ
  have hp₁ : p ∈ B₁.lowerIndexCriticalPoints := by rw [B.lowerIndexCriticalPoints_eq_of_crit_eq hcrit]; exact hp
  have hq₁ : q ∈ B₁.upperIndexCriticalPoints := by rw [B.upperIndexCriticalPoints_eq_of_crit_eq hcrit]; exact hq
  obtain ⟨htr₁iff, hcount₁, hzeros₁⟩ := hdata₁ p hp q hq
  have htr₁ : B₁.pairTransverse p q := htr₁iff.2 htr
  have hlt₁ : (B₁.count p q).natAbs < B₁.zerosCard p q := by rw [hcount₁, hzeros₁]; exact hlt
  have hπ₁ : SimplyConnectedSpace (f ⁻¹' {B₁.c}) := by rw [hc₁]; exact hπ
  have hπR₁ : ℓ = 2 → SimplyConnectedSpace ↥(f ⁻¹' {B₁.c} \ B₁.rightSphere p) := by
    rw [hc₁, hR₁ p hp]; exact hπR
  have hπL₁ : ℓ + 3 = n → SimplyConnectedSpace ↥(f ⁻¹' {B₁.c} \ B₁.leftSphere q) := by
    rw [hc₁, hL₁ q hq]; exact hπL
  have hrm₁ : ∀ x hx, B₁.D.rm x hx ^ 2 < B₁.c - B₁.α ∧ B₁.D.rm x hx ^ 2 < B₁.β - B₁.c := by
    intro x hx
    have hxB : x ∈ B.crit := hcrit ▸ hx
    have h : B₁.D.rm x hx = min ρ (B.D.rm x hxB) := (hchart₁ x hxB).2.2.2.2
    have hpos := B₁.D.rm_pos x hx
    have hle : B₁.D.rm x hx ≤ ρ := by rw [h]; exact min_le_left _ _
    have hlt' : B₁.D.rm x hx ^ 2 < d := lt_of_le_of_lt (pow_le_pow_left₀ hpos.le hle 2) hρ2
    rw [hc₁, hα₁, hβ₁]
    exact ⟨lt_of_lt_of_le hlt' (min_le_left _ _), lt_of_lt_of_le hlt' (min_le_right _ _)⟩
  obtain ⟨w₁, hw₁, w₂, hw₂, hs₁, hs₂⟩ := B₁.exists_opposite_zeros hp₁ hq₁ htr₁ hlt₁
  obtain ⟨η, κ, hη, Ch, hU, hA, hB, hx₁, hx₂⟩ :=
    B₁.exists_whitneyChart h6 hf hℓ hℓn hp₁ hq₁ htr₁ hw₁ hw₂ hs₁ hs₂ hrm₁ hπ₁ hπR₁ hπL₁
  obtain ⟨K, hK, hKdom, Hs, hHs, hbij, hdiff, hsupp, h0, h1, hfin⟩ :=
    exists_whitney_isotopy (n - 1) ℓ (by omega) (by omega) hη
  have hKU : K ⊆ Ch.U := hU ▸ hKdom
  obtain ⟨Z, hZ⟩ := Ch.exists_realizes hf.smooth hK hKU Hs hHs hbij hdiff hsupp h0 h1
  have hZmodel : ∀ x hx, ∀ y, morseNorm n y < B₁.D.rm x hx →
      Z ((B₁.D.chart x hx).χ y) = 0 := by
    intro x hx y hy
    by_contra hne
    have hmem : (B₁.D.chart x hx).χ y ∈ tsupport Z := subset_tsupport _ hne
    obtain ⟨⟨y', s⟩, ⟨hy'K, hs⟩, heq⟩ := hZ.2.2.2.1 hmem
    have heq' : B₁.D.flow s (Ch.φ y') = (B₁.D.chart x hx).χ y := heq
    exact Ch.avoid y' (hKU hy'K) s ⟨hs.1.le, hs.2.le⟩ x hx (heq' ▸ ⟨y, hy, rfl⟩)
  obtain ⟨D', hD'V, hD'chart, hD'rm⟩ :=
    B₁.D.exists_addLevelField Z hZ.1 hZ.2.1 hZ.2.2.1 hZmodel
  obtain ⟨hTr, hCount, hCard⟩ :=
    B₁.whitney_removes_pair hf hp₁ hq₁ htr₁ hw₁ hw₂ hs₁ hs₂ hη Ch hU hA hB hx₁ hx₂ hK hKdom
      (hsupp 1) (hbij 1) hfin hZ D' hD'V hD'chart hD'rm
  let B₂ : BlockConfig I f a b ℓ :=
    { crit := B₁.crit
      hcrit := B₁.hcrit
      D := D'
      α := B₁.α
      β := B₁.β
      ε := B₁.ε
      c := B₁.c
      hε := B₁.hε
      hr₀ := fun x hx => by rw [hD'chart]; exact B₁.hr₀ x hx
      hrm := fun x hx => by rw [hD'rm]; exact B₁.hrm x hx
      haα := B₁.haα
      hαc := B₁.hαc
      hcβ := B₁.hcβ
      hβb := B₁.hβb
      hmin := B₁.hmin
      hP := B₁.hP
      hQ := B₁.hQ
      hhigh := B₁.hhigh
      hlev := fun y hy x hx => by
        unfold GradientLikeStrip.smallBall
        rw [hD'chart]
        exact B₁.hlev y hy x hx }
  have hpc : p ∈ B₁.crit := (B₁.mem_lowerIndexCriticalPoints.1 hp₁).1
  have hqc : q ∈ B₁.crit := (B₁.mem_upperIndexCriticalPoints.1 hq₁).1
  have hpc₂ : p ∈ B₂.crit := hpc
  have hqc₂ : q ∈ B₂.crit := hqc
  have e₂ : B₂.count p q = D'.sardCount p hqc B₁.ε B₁.c hpc := by
    unfold BlockConfig.count
    rw [dite_eq_left hpc₂, dite_eq_left hqc₂]
  have e₁ : B₁.count p q = B₁.D.sardCount p hqc B₁.ε B₁.c hpc := by
    unfold BlockConfig.count
    rw [dite_eq_left hpc, dite_eq_left hqc]
  have z₂ : B₂.zerosCard p q = (D'.sardZeros p hqc B₁.ε B₁.c hpc).ncard := by
    unfold BlockConfig.zerosCard
    rw [dite_eq_left hpc₂, dite_eq_left hqc₂]
  have z₁ : B₁.zerosCard p q = (B₁.D.sardZeros p hqc B₁.ε B₁.c hpc).ncard := by
    unfold BlockConfig.zerosCard
    rw [dite_eq_left hpc, dite_eq_left hqc]
  refine ⟨B₂, hcrit, ⟨hpc₂, hqc₂, hTr⟩, ?_, ?_⟩
  · rw [← hcount₁, e₂, e₁]
    exact hCount
  · rw [← hzeros₁, z₂, z₁]
    exact hCard

theorem exists_isolated [DecidableEq M] (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints) (htr : B.pairTransverse p q)
    (hone : B.zerosCard p q = 1) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ sameCritIn I f g a b ∧
      ∃ a' b' : ℝ, a < a' ∧ b' < b ∧ (∀ x, g x = a' ∨ g x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) ∧
        isCancellingPair I g a' b' p q := by
  have hαβ0 : B.α < B.β := by linarith [B.hαc, B.hcβ, B.hε]
  obtain ⟨ε₀, hε₀def⟩ : ∃ e : ℝ, e = min B.ε (min (B.α - a) (B.β - B.α) / 16) := ⟨_, rfl⟩
  have hm0 : 0 < min (B.α - a) (B.β - B.α) := lt_min (sub_pos.2 B.haα) (sub_pos.2 hαβ0)
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; exact lt_min B.hε (by linarith)
  have hε₀le : ε₀ ≤ B.ε := by rw [hε₀def]; exact min_le_left _ _
  have hε₀m : 16 * ε₀ ≤ min (B.α - a) (B.β - B.α) := by
    have := min_le_right B.ε (min (B.α - a) (B.β - B.α) / 16)
    rw [hε₀def]; linarith
  have hε₀a : 16 * ε₀ ≤ B.α - a := hε₀m.trans (min_le_left _ _)
  have hε₀b : 16 * ε₀ ≤ B.β - B.α := hε₀m.trans (min_le_right _ _)
  obtain ⟨B', hcrit', hα', hβ', -, hε', -, -, -, -, -, -, hdata⟩ :=
    exists_shrink hf B (ρ := 8 * ε₀ + 1) hε₀pos hε₀le (by linarith) (by nlinarith)
  have hpB : p ∈ B'.lowerIndexCriticalPoints := by rw [lowerIndexCriticalPoints_eq_of_crit_eq B hcrit']; exact hp
  have hqB : q ∈ B'.upperIndexCriticalPoints := by rw [upperIndexCriticalPoints_eq_of_crit_eq B hcrit']; exact hq
  obtain ⟨htr', -, hz'⟩ := hdata p hp q hq
  have htrB : B'.pairTransverse p q := htr'.2 htr
  have honeB : B'.zerosCard p q = 1 := hz'.trans hone
  have hA : 16 * B'.ε ≤ B'.α - a := by rw [hε', hα']; exact hε₀a
  have hB : 16 * B'.ε ≤ B'.β - B'.α := by rw [hε', hα', hβ']; exact hε₀b
  have hε := B'.hε
  have hβb := B'.hβb
  obtain ⟨δ, hδ⟩ : ∃ d : ℝ, d = 4 * B'.ε := ⟨_, rfl⟩
  have hpc : p ∈ B'.crit := (B'.mem_lowerIndexCriticalPoints.1 hpB).1
  have hqc : q ∈ B'.crit := (B'.mem_upperIndexCriticalPoints.1 hqB).1
  have hfp : f p = B'.α := B'.hP p hpc (B'.mem_lowerIndexCriticalPoints.1 hpB).2
  have hfq : f q = B'.β := B'.hQ q hqc (B'.mem_upperIndexCriticalPoints.1 hqB).2
  have hPnQ : ∀ x, x ∈ B'.lowerIndexCriticalPoints → x ∈ B'.upperIndexCriticalPoints → False := by
    intro x hxP hxQ
    have h1 := (B'.mem_lowerIndexCriticalPoints.1 hxP).2
    have h2 := (B'.mem_upperIndexCriticalPoints.1 hxQ).2
    omega
  have hPq : ∀ x ∈ B'.lowerIndexCriticalPoints, x ≠ q := by
    intro x hxP hxq
    rw [hxq] at hxP
    exact hPnQ q hxP hqB
  have hpq : p ≠ q := hPq p hpB
  have hclass : ∀ x ∈ B'.crit,
      (x ∈ B'.lowerIndexCriticalPoints ∧ f x = B'.α) ∨ (x ∈ B'.upperIndexCriticalPoints ∧ f x = B'.β) ∨ B'.β < f x := by
    intro x hx
    have h := B'.hmin x hx
    rcases Nat.lt_or_ge (ℓ + 1) (morseIndex I f x) with h1 | h1
    · exact Or.inr (Or.inr (B'.hhigh x hx h1))
    rcases (show morseIndex I f x = ℓ ∨ morseIndex I f x = ℓ + 1 by omega) with h2 | h2
    · exact Or.inl ⟨B'.mem_lowerIndexCriticalPoints.2 ⟨hx, h2⟩, B'.hP x hx h2⟩
    · exact Or.inr (Or.inl ⟨B'.mem_upperIndexCriticalPoints.2 ⟨hx, h2⟩, B'.hQ x hx h2⟩)
  obtain ⟨v₁, hβv, hvb, hvhigh⟩ :
      ∃ v, B'.β < v ∧ v < b ∧ ∀ x ∈ B'.crit, B'.β < f x → v < f x := by
    by_cases hT : (B'.crit.filter (fun x => B'.β < f x)).Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := (B'.crit.filter (fun x => B'.β < f x)).exists_min_image f hT
      have hx₀' := (Finset.mem_filter.1 hx₀).2
      have h1 := lt_min hx₀' hβb
      have h2 := min_le_right (f x₀) b
      have h3 := min_le_left (f x₀) b
      refine ⟨(B'.β + min (f x₀) b) / 2, by linarith, by linarith, ?_⟩
      intro x hx hxβ
      have := hmin x (Finset.mem_filter.2 ⟨hx, hxβ⟩)
      linarith
    · refine ⟨(B'.β + b) / 2, by linarith, by linarith, ?_⟩
      intro x hx hxβ
      exact absurd ⟨x, Finset.mem_filter.2 ⟨hx, hxβ⟩⟩ hT
  have hcritOf : ∀ g : M → ℝ, ModifiedWithin f a b g → sameCritIn I f g a b →
      ∀ x, x ∈ B'.crit ↔ g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := by
    intro g hm hs x
    have hI : g x ∈ Ioo a b ↔ f x ∈ Ioo a b := Set.ext_iff.1 hm.preimage_Ioo x
    rw [B'.hcrit x]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hI.2 h1, (hs.1 x h1).2 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hI.1 h1, (hs.1 x (hI.1 h1)).1 h2⟩
  have hSV : ∀ (g : M → ℝ) (D' : GradientLikeStrip I g a b B'.crit) (ε' : ℝ), 0 < ε' →
      ε' ≤ B'.ε → (∀ x hx, (D'.chart x hx).r₀ ^ 2 < 2 * ε' ∧ 8 * ε' < D'.rm x hx ^ 2) →
      g p = B'.α → g q = B'.β - δ → (∀ x ∈ B'.crit, g x ≤ B'.α ∨ B'.β - δ ≤ g x) →
      D'.sardValid ε' p hqc hpc := by
    intro g D' ε' h0 hle hr hgp hgq hlow
    refine ⟨h0, (hr p hpc).1, (hr q hqc).1, (hr p hpc).2, (hr q hqc).2,
      by rw [hgp, hgq]; linarith, ?_⟩
    intro y hy x hx hyx
    rw [hgp, hgq] at hy
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hyx
    have h2 := (hr x hx).1
    rw [abs_lt] at h1
    rcases hlow x hx with h | h
    · linarith [hy.1, h1.2]
    · linarith [hy.2, h1.1]
  have hwin₁ : ∀ x ∈ B'.crit, f x ∈ Icc (B'.α + δ) v₁ → f x = B'.β ∨ f x = B'.β - δ := by
    intro x hx hI
    rcases hclass x hx with ⟨-, h⟩ | ⟨-, h⟩ | h
    · rw [h] at hI
      exact absurd hI.1 (by linarith)
    · exact Or.inl h
    · exact absurd hI.2 (not_le.2 (hvhigh x hx h))
  obtain ⟨g₁, hmod₁, hf₁, hsc₁, hS₁, hrest₁, D₁, -, -, ε₁, hε₁, hε₁le, hεr₁, hagree₁⟩ :=
    exists_vertical_move I hf B'.hcrit B'.D B'.hε (fun x hx => ⟨B'.hr₀ x hx, B'.hrm x hx⟩) {q}
      (by intro x hx; rw [Finset.mem_singleton.1 hx]; exact hqc)
      (s₀ := B'.β) (u := B'.α + δ) (v := v₁) (t := B'.β - δ)
      (by intro x hx; rw [Finset.mem_singleton.1 hx]; exact hfq) (by linarith [B'.haα]) hvb
      ⟨by linarith, hβv⟩ ⟨by linarith, by linarith⟩ hwin₁ (fun _ _ => 1) (fun _ _ => one_pos)
      (by
        intro x hx y hy _ _ hy'
        exfalso
        rcases hclass y hy with ⟨-, h⟩ | ⟨-, h⟩ | h <;> linarith)
  have hg₁q : g₁ q = B'.β - δ := hS₁ q (Finset.mem_singleton_self q)
  have hg₁ : ∀ x ∈ B'.crit, x ≠ q → g₁ x = f x :=
    fun x hx hxq => hrest₁ x hx (fun h => hxq (Finset.mem_singleton.1 h))
  have hm₁ : ModifiedWithin f a b g₁ := hmod₁.mono (by linarith [B'.haα]) hvb.le
  have hcrit₁ := hcritOf g₁ hm₁ hsc₁
  have hg₁low : ∀ x ∈ B'.crit, g₁ x ≤ B'.α ∨ B'.β - δ ≤ g₁ x := by
    intro x hx
    by_cases hxq : x = q
    · rw [hxq, hg₁q]; right; exact le_rfl
    · rw [hg₁ x hx hxq]
      rcases hclass x hx with ⟨-, h⟩ | ⟨-, h⟩ | h
      · left; exact h.le
      · right; linarith
      · right; linarith
  have hSlev₂ : ∀ x ∈ B'.lowerIndexCriticalPoints.erase p, g₁ x = B'.α := by
    intro x hx
    have hxP := Finset.mem_of_mem_erase hx
    have hxc := (B'.mem_lowerIndexCriticalPoints.1 hxP).1
    rw [hg₁ x hxc (hPq x hxP)]
    exact B'.hP x hxc (B'.mem_lowerIndexCriticalPoints.1 hxP).2
  have hwin₂ : ∀ x ∈ B'.crit, g₁ x ∈ Icc (B'.α - 2 * δ) (B'.α + δ) →
      g₁ x = B'.α ∨ g₁ x = B'.α - δ := by
    intro x hx hI
    by_cases hxq : x = q
    · rw [hxq, hg₁q] at hI
      exact absurd hI.2 (by linarith)
    · rw [hg₁ x hx hxq] at hI ⊢
      rcases hclass x hx with ⟨-, h⟩ | ⟨-, h⟩ | h
      · exact Or.inl h
      · rw [h] at hI
        exact absurd hI.2 (by linarith)
      · exact absurd hI.2 (by linarith)
  obtain ⟨g₂, hmod₂, hf₂, hsc₂, hS₂, hrest₂, D₂, -, -, ε₂, hε₂, hε₂le, hεr₂, hagree₂⟩ :=
    exists_vertical_move I hf₁ hcrit₁ D₁ hε₁ hεr₁ (B'.lowerIndexCriticalPoints.erase p)
      (fun x hx => (B'.mem_lowerIndexCriticalPoints.1 (Finset.mem_of_mem_erase hx)).1)
      (s₀ := B'.α) (u := B'.α - 2 * δ) (v := B'.α + δ) (t := B'.α - δ) hSlev₂
      (by linarith) (by linarith) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hwin₂
      (fun _ _ => 1) (fun _ _ => one_pos)
      (by
        intro x hx y hy _ _ hy'
        exfalso
        by_cases hyq : y = q
        · rw [hyq, hg₁q] at hy'
          linarith
        · rw [hg₁ y hy hyq] at hy'
          rcases hclass y hy with ⟨-, h⟩ | ⟨-, h⟩ | h <;> linarith)
  have hm₂' : ModifiedWithin g₁ a b g₂ := hmod₂.mono (by linarith) (by linarith)
  have hm₂ : ModifiedWithin f a b g₂ := hm₁.trans hm₂'
  have hsc₂' : sameCritIn I f g₂ a b := hsc₁.trans hm₁ hsc₂
  have hcrit₂ := hcritOf g₂ hm₂ hsc₂'
  have hg₂p : g₂ p = B'.α := by
    rw [hrest₂ p hpc (fun h => (Finset.mem_erase.1 h).1 rfl), hg₁ p hpc hpq, hfp]
  have hg₂q : g₂ q = B'.β - δ := by
    rw [hrest₂ q hqc (fun h => hPq q (Finset.mem_of_mem_erase h) rfl), hg₁q]
  have hg₂other : ∀ x ∈ B'.crit, x ≠ p → x ≠ q → g₂ x = B'.α - δ ∨ B'.β ≤ g₂ x := by
    intro x hx hxp hxq
    rcases hclass x hx with ⟨hxP, h⟩ | ⟨hxQ, h⟩ | h
    · left
      exact hS₂ x (Finset.mem_erase.2 ⟨hxp, hxP⟩)
    · right
      rw [hrest₂ x hx (fun h' => hPnQ x (Finset.mem_of_mem_erase h') hxQ), hg₁ x hx hxq, h]
    · right
      have hnot : x ∉ B'.lowerIndexCriticalPoints.erase p := by
        intro h'
        have hxP := Finset.mem_of_mem_erase h'
        have := B'.hP x hx (B'.mem_lowerIndexCriticalPoints.1 hxP).2
        linarith
      rw [hrest₂ x hx hnot, hg₁ x hx hxq]
      exact h.le
  have hg₂low : ∀ x ∈ B'.crit, g₂ x ≤ B'.α ∨ B'.β - δ ≤ g₂ x := by
    intro x hx
    by_cases hxp : x = p
    · rw [hxp, hg₂p]; left; exact le_rfl
    by_cases hxq : x = q
    · rw [hxq, hg₂q]; right; exact le_rfl
    rcases hg₂other x hx hxp hxq with h | h
    · left; linarith
    · right; linarith
  have hv0 := B'.sardValid hpB hqB
  have hv1 := hSV g₁ D₁ ε₁ hε₁ hε₁le hεr₁ (by rw [hg₁ p hpc hpq, hfp]) hg₁q hg₁low
  have hv2 := hSV g₂ D₂ ε₂ hε₂ (hε₂le.trans hε₁le) hεr₂ hg₂p hg₂q hg₂low
  have hA1 := hagree₁ p hpc q hqc hv0 hv1 B'.c (B'.α + δ)
  have hA2 := hagree₂ p hpc q hqc hv1 hv2 (B'.α + δ) (B'.α + δ)
  have htrD : B'.D.isSardTransverse p hqc B'.ε B'.c hpc := by
    obtain ⟨_, _, h⟩ := htrB
    exact h
  have htr₂ := hA2.1.2 (hA1.1.2 htrD)
  have hone0 : (B'.D.sardZeros p hqc B'.ε B'.c hpc).ncard = 1 := by
    have h := honeB
    unfold zerosCard at h
    simp only [hpc, hqc, ↓reduceDIte] at h
    exact h
  have hone₂ := hA2.2.2.trans (hA1.2.2.trans hone0)
  have hidx : morseIndex I g₂ q = morseIndex I g₂ p + 1 := by
    have hpI := (B'.hcrit p).1 hpc
    have hqI := (B'.hcrit q).1 hqc
    rw [hsc₂'.2 q hqI.1 hqI.2, hsc₂'.2 p hpI.1 hpI.2, (B'.mem_lowerIndexCriticalPoints.1 hpB).2, (B'.mem_upperIndexCriticalPoints.1 hqB).2]
  have hε₂B : ε₂ ≤ B'.ε := hε₂le.trans hε₁le
  have honly : ∀ x ∈ B'.crit, g₂ x ∈ Icc (B'.α - δ / 2) (B'.β - δ / 2) → x = p ∨ x = q := by
    intro x hx hI
    by_cases hxp : x = p
    · exact Or.inl hxp
    by_cases hxq : x = q
    · exact Or.inr hxq
    exfalso
    rcases hg₂other x hx hxp hxq with h | h
    · linarith [hI.1]
    · linarith [hI.2]
  have hother : ∀ x (hx : x ∈ B'.crit), x ≠ p → x ≠ q → ∀ y ∈ D₂.smallBall x hx,
      g₂ y ∉ Icc (B'.α - δ / 2) (B'.β - δ / 2) := by
    intro x hx hxp hxq y hy hI
    have h1 := GradientLikeStrip.abs_f_sub_lt_of_mem_smallBall hx hy
    have h2 := (hεr₂ x hx).1
    rw [abs_lt] at h1
    rcases hg₂other x hx hxp hxq with h | h
    · linarith [hI.1, h1.2]
    · linarith [hI.2, h1.1]
  refine ⟨g₂, hm₂, hf₂, hsc₂', B'.α - δ / 2, B'.β - δ / 2, by linarith, by linarith, ?_, ?_⟩
  · intro x hx hcx
    have hx' : g₂ x ∈ Ioo a b := by
      rcases hx with h | h <;> rw [h] <;> constructor <;> linarith
    have hxc := (hcrit₂ x).2 ⟨hx', hcx⟩
    by_cases hxp : x = p
    · rw [hxp, hg₂p] at hx
      rcases hx with h | h <;> linarith
    by_cases hxq : x = q
    · rw [hxq, hg₂q] at hx
      rcases hx with h | h <;> linarith
    rcases hg₂other x hxc hxp hxq with h | h <;> rcases hx with h' | h' <;> linarith
  · exact isCancellingPair_of_isolated I hf₂ hcrit₂ D₂ hpc hqc hv2 (c := B'.α + δ)
      (by rw [hg₂p]; linarith) (by rw [hg₂q]; linarith) htr₂ hone₂ hidx (by linarith)
      (by linarith) (by rw [hg₂p]; linarith) (by rw [hg₂q]; linarith) honly hother

omit [SigmaCompactSpace M] in
theorem exists_single_zero (h6 : 6 ≤ n) (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) (hidx : ∀ x ∈ B.crit, morseIndex I f x + 2 ≤ n)
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    {p q : M} (hp : p ∈ B.lowerIndexCriticalPoints) (hq : q ∈ B.upperIndexCriticalPoints) (htr : B.pairTransverse p q)
    (hcount : (B.count p q).natAbs = 1) :
    ∃ B' : BlockConfig I f a b ℓ, B'.crit = B.crit ∧ B'.pairTransverse p q ∧
      B'.zerosCard p q = 1 := by
  have key : ∀ N : ℕ, ∀ B : BlockConfig I f a b ℓ, B.zerosCard p q = N → p ∈ B.lowerIndexCriticalPoints → q ∈ B.upperIndexCriticalPoints →
      (∀ x ∈ B.crit, morseIndex I f x + 2 ≤ n) → B.pairTransverse p q →
      (B.count p q).natAbs = 1 →
      ∃ B' : BlockConfig I f a b ℓ, B'.crit = B.crit ∧ B'.pairTransverse p q ∧
        B'.zerosCard p q = 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro B hN hp hq hidx htr hcount
    have hle := natAbs_count_le_zerosCard B hp hq htr
    by_cases h1 : B.zerosCard p q = 1
    · exact ⟨B, rfl, htr, h1⟩
    have hlt : (B.count p q).natAbs < B.zerosCard p q := by omega
    have hπ := simplyConnected_level hf B hℓ hℓn hV₀
    have hπR : ℓ = 2 → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.rightSphere p) := fun _ =>
      simplyConnected_level_diff_rightSphere hf B hℓ hℓn hV₀ hp
    have hπL : ℓ + 3 = n → SimplyConnectedSpace ↥(f ⁻¹' {B.c} \ B.leftSphere q) := fun h =>
      simplyConnected_level_diff_leftSphere hf B hℓ hℓn
        (fun x hx => by have := hidx x hx; omega) hV₁ hq
    obtain ⟨B', hcrit', htr', hcount', hcard'⟩ :=
      whitney_pair_removal h6 hf B hℓ hℓn hp hq htr hlt hπ hπR hπL
    have hp' : p ∈ B'.lowerIndexCriticalPoints := by rw [lowerIndexCriticalPoints_eq_of_crit_eq B hcrit']; exact hp
    have hq' : q ∈ B'.upperIndexCriticalPoints := by rw [upperIndexCriticalPoints_eq_of_crit_eq B hcrit']; exact hq
    obtain ⟨B'', hcrit'', htr'', h1''⟩ := ih (B'.zerosCard p q) (by omega) B' rfl hp' hq'
      (by rw [hcrit']; exact hidx) htr' (by rw [hcount']; exact hcount)
    exact ⟨B'', hcrit''.trans hcrit', htr'', h1''⟩
  exact key _ B rfl hp hq hidx htr hcount

theorem exists_unit_count (hf : MorseStrip I f a b) (B : BlockConfig I f a b ℓ)
    (htr : B.transverse) (hℓ : 2 ≤ ℓ) (hℓn : ℓ + 3 ≤ n) (hV₀ : PathConnectedSpace (f ⁻¹' {a}))
    {p₀ : M} (hp₀ : p₀ ∈ B.lowerIndexCriticalPoints) (hgcd : ∃ v : M → ℤ, ∑ q ∈ B.upperIndexCriticalPoints, B.count p₀ q * v q = 1) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ sameCritIn I f g a b ∧
      ∃ B' : BlockConfig I g a b ℓ, B'.crit = B.crit ∧ B'.lowerIndexCriticalPoints = B.lowerIndexCriticalPoints ∧ B'.upperIndexCriticalPoints = B.upperIndexCriticalPoints ∧
        B'.transverse ∧ ∃ q ∈ B.upperIndexCriticalPoints, (B'.count p₀ q).natAbs = 1 := by
  classical
  let R : (M → ℤ) → Prop := fun r =>
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ sameCritIn I f g a b ∧
      ∃ B' : BlockConfig I g a b ℓ, B'.crit = B.crit ∧ B'.lowerIndexCriticalPoints = B.lowerIndexCriticalPoints ∧ B'.upperIndexCriticalPoints = B.upperIndexCriticalPoints ∧
        B'.transverse ∧ r = fun q => B'.count p₀ q
  have hR₀ : R (fun q => B.count p₀ q) :=
    ⟨f, ModifiedWithin.refl f a b, hf, sameCritIn.refl I f a b, B, rfl, rfl, rfl, htr, rfl⟩
  have hstep : ∀ r, R r → ∀ q₁ ∈ B.upperIndexCriticalPoints, ∀ q₂ ∈ B.upperIndexCriticalPoints, q₁ ≠ q₂ → ∀ t : ℤ, (t = 1 ∨ t = -1) →
      ∃ r', R r' ∧ ∀ q ∈ B.upperIndexCriticalPoints, |r' q| = |colOp r q₁ q₂ t q| := by
    rintro r ⟨g, hmod, hg, hsame, B₁, hc₁, hP₁, hQ₁, htr₁, rfl⟩ q₁ hq₁ q₂ hq₂ hne t ht
    have hV₀' : PathConnectedSpace (g ⁻¹' {a}) := by
      rw [hmod.preimage_singleton_left]; exact hV₀
    have hq₁' : q₁ ∈ B₁.upperIndexCriticalPoints := by rw [hQ₁]; exact hq₁
    have hq₂' : q₂ ∈ B₁.upperIndexCriticalPoints := by rw [hQ₁]; exact hq₂
    have hp₀' : p₀ ∈ B₁.lowerIndexCriticalPoints := by rw [hP₁]; exact hp₀
    obtain ⟨g₂, hmod₂, hg₂, hsame₂, B₂, hc₂, hP₂, hQ₂, htr₂, hN₂⟩ :=
      exists_slide hg B₁ htr₁ hℓ hℓn hV₀' hp₀' hq₁' hq₂' hne ht
    refine ⟨fun q => B₂.count p₀ q, ⟨g₂, hmod.trans hmod₂, hg₂, hsame.trans hmod hsame₂, B₂,
      hc₂.trans hc₁, hP₂.trans hP₁, hQ₂.trans hQ₁, htr₂, rfl⟩, fun q hq => ?_⟩
    have hq' : q ∈ B₁.upperIndexCriticalPoints := by rw [hQ₁]; exact hq
    exact hN₂ q hq'
  obtain ⟨r, ⟨g, hmod, hg, hsame, B', hc, hP, hQ, htr', rfl⟩, q, hq, hq1⟩ :=
    exists_row_unit R hstep hR₀ hgcd
  refine ⟨g, hmod, hg, hsame, B', hc, hP, hQ, htr', q, hq, ?_⟩
  have h : |B'.count p₀ q| = 1 := hq1
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

end BlockConfig

theorem middle_target (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h6 : 6 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x →
      2 ≤ morseIndex I f x ∧ morseIndex I f x + 2 ≤ n)
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : relHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a})))
    {p₀ : M} (hp₀ : f p₀ ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p₀) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, g x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x →
        DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∧ morseIndex I g x = morseIndex I f x) ∧
      ∃ p, f p ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p ∧ ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p := by
  classical
  have hS : ∃ k, ∃ x, f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x ∧ morseIndex I f x = k :=
    ⟨_, p₀, hp₀.1, hp₀.2, rfl⟩
  obtain ⟨x₀, hx₀, hcx₀, hx₀ℓ⟩ := Nat.find_spec hS
  set ℓ := Nat.find hS with hℓdef
  have hmin : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → ℓ ≤ morseIndex I f x :=
    fun x hx hc => Nat.find_min' hS ⟨x, hx, hc, rfl⟩
  have hℓ2 : 2 ≤ ℓ := by rw [← hx₀ℓ]; exact (hidx x₀ hx₀ hcx₀).1
  obtain ⟨f₁, hmod₁, hf₁, hsame₁, ⟨B₀⟩⟩ := exists_blockConfig I hf hmin
  obtain ⟨B₁, -, hB₁tr, -⟩ := B₀.exists_transverse hf₁
  have hpre₁ : ∀ x, f₁ x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod₁.preimage_Ioo x
  have hx₀P : x₀ ∈ B₁.lowerIndexCriticalPoints := by
    rw [BlockConfig.mem_lowerIndexCriticalPoints, B₁.hcrit]
    exact ⟨⟨(hpre₁ x₀).2 hx₀, (hsame₁.1 x₀ hx₀).2 hcx₀⟩, (hsame₁.2 x₀ hx₀ hcx₀).trans hx₀ℓ⟩
  have hH₁ : relHomologyVanishes (f₁ ⁻¹' Icc a b) (Subtype.val ⁻¹' (f₁ ⁻¹' {a})) := by
    rw [hmod₁.preimage_singleton_left, hmod₁.preimage_Icc]; exact hH
  obtain ⟨v, hv⟩ := B₁.count_surjective hf₁ hB₁tr hℓ2 hH₁ (fun p => if p = x₀ then 1 else 0)
  have hgcd : ∑ q ∈ B₁.upperIndexCriticalPoints, B₁.count x₀ q * v q = 1 := by simpa using hv x₀ hx₀P
  have hidx₁ : ∀ x ∈ B₁.crit, morseIndex I f₁ x + 2 ≤ n := by
    intro x hx
    obtain ⟨hx1, hc1⟩ := (B₁.hcrit x).1 hx
    obtain ⟨hxf, hcf, heq⟩ := hsame₁.crit_of hmod₁ hx1 hc1
    rw [heq]; exact (hidx x hxf hcf).2
  obtain ⟨q', hq'⟩ : B₁.upperIndexCriticalPoints.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hgcd
    exact zero_ne_one hgcd
  have hℓn : ℓ + 3 ≤ n := by
    obtain ⟨hq'c, hq'i⟩ := (BlockConfig.mem_upperIndexCriticalPoints B₁).1 hq'
    have := hidx₁ q' hq'c
    omega
  have hV₀₁ : PathConnectedSpace (f₁ ⁻¹' {a}) := by
    rw [hmod₁.preimage_singleton_left]; infer_instance
  obtain ⟨f₂, hmod₂, hf₂, hsame₂, B₂, -, hB₂P, hB₂Q, hB₂tr, q, hqQ, hcount₂⟩ :=
    BlockConfig.exists_unit_count hf₁ B₁ hB₁tr hℓ2 hℓn hV₀₁ hx₀P ⟨v, hgcd⟩
  have hmod₁₂ := hmod₁.trans hmod₂
  have hsame₁₂ := hsame₁.trans hmod₁ hsame₂
  have hx₀P₂ : x₀ ∈ B₂.lowerIndexCriticalPoints := by rw [hB₂P]; exact hx₀P
  have hqQ₂ : q ∈ B₂.upperIndexCriticalPoints := by rw [hB₂Q]; exact hqQ
  have hV₀₂ : SimplyConnectedSpace (f₂ ⁻¹' {a}) := by
    rw [hmod₁₂.preimage_singleton_left]; exact hV₀
  have hV₁₂ : SimplyConnectedSpace (f₂ ⁻¹' {b}) := by
    rw [hmod₁₂.preimage_singleton_right]; exact hV₁
  have hidx₂ : ∀ x ∈ B₂.crit, morseIndex I f₂ x + 2 ≤ n := by
    intro x hx
    obtain ⟨hx1, hc1⟩ := (B₂.hcrit x).1 hx
    obtain ⟨hxf, hcf, heq⟩ := hsame₁₂.crit_of hmod₁₂ hx1 hc1
    rw [heq]; exact (hidx x hxf hcf).2
  obtain ⟨B₃, hB₃c, hB₃tr, hB₃one⟩ := B₂.exists_single_zero h6 hf₂ hℓ2 hℓn hidx₂ hV₀₂ hV₁₂
    hx₀P₂ hqQ₂ (hB₂tr x₀ hx₀P₂ q hqQ₂) hcount₂
  have hx₀P₃ : x₀ ∈ B₃.lowerIndexCriticalPoints := by rw [BlockConfig.lowerIndexCriticalPoints_eq_of_crit_eq B₂ hB₃c]; exact hx₀P₂
  have hqQ₃ : q ∈ B₃.upperIndexCriticalPoints := by rw [BlockConfig.upperIndexCriticalPoints_eq_of_crit_eq B₂ hB₃c]; exact hqQ₂
  obtain ⟨f₄, hmod₄, hf₄, hsame₄, a', b', ha', hb', hreg, hpair⟩ :=
    B₃.exists_isolated hf₂ hx₀P₃ hqQ₃ hB₃tr hB₃one
  obtain ⟨g, hmodg', hmodg, hg, hoff, hno⟩ :=
    exists_cancel_pair_strip_of_isCancellingPair I hf₄ ha'.le hb'.le hreg hpair
  have hmod₁₂₄ := hmod₁₂.trans hmod₄
  have hsame₁₂₄ := hsame₁₂.trans hmod₁₂ hsame₄
  refine ⟨g, hmod₁₂₄.trans hmodg, hg, fun x hx hc => ?_, x₀, hx₀, hcx₀, fun hc => ?_⟩
  · have hx₄ : f₄ x ∈ Ioo a b := (Set.ext_iff.1 hmodg.preimage_Ioo x).1 hx
    have hx₄' : f₄ x ∉ Ioo a' b' := fun h => hno x (hmodg'.mapsTo h) hc
    obtain ⟨-, hiff, hidxeq⟩ := hoff x hx₄'
    have hc₄ : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₄ x := hiff.1 hc
    obtain ⟨-, hcf, heq⟩ := hsame₁₂₄.crit_of hmod₁₂₄ hx₄ hc₄
    exact ⟨hcf, (hidxeq hc₄).trans heq⟩
  · have hx₀₄ : f₄ x₀ ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f₄ x₀ :=
      (hpair.2.1 x₀).1 (mem_pair_left x₀ q)
    exact hno x₀ (hmodg'.mapsTo hx₀₄.1) hc

end

end DifferentialGeometry.Topology
