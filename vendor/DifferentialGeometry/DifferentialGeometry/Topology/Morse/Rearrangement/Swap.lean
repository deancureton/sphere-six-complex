module

public import DifferentialGeometry.Topology.Morse.Strip.Foundations.CriticalFinite
public import DifferentialGeometry.Topology.Morse.Rearrangement.DistinctValues
public import DifferentialGeometry.Topology.Morse.Strip.Foundations.GradientLike
public import DifferentialGeometry.Topology.Morse.Strip.StripFlow
public import DifferentialGeometry.Topology.Morse.Strip.TrajectoryCutoff
public import DifferentialGeometry.Topology.Morse.Rearrangement.Rearrange
public import DifferentialGeometry.Topology.Morse.Rearrangement.Transversality

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter DifferentialGeometry
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm)

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M]
  {f : M → ℝ} {a b : ℝ}

namespace Swap

theorem exists_regular_substrip (hf : MorseStrip I f a b)
    (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) {p q : M}
    (hp : f p ∈ Ioo a b) (hq : f q ∈ Ioo a b) (hcp : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p)
    (hcq : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f q)
    (hadj : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → f x ∉ Ioo (f p) (f q)) :
    ∃ a' b' : ℝ, a < a' ∧ a' < f p ∧ f q < b' ∧ b' < b ∧
      (∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      ∀ x, f x ∈ Ioo a' b' → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x = p ∨ x = q := by
  classical
  set T := hf.finite_criticalValues.toFinset with hT
  have hmemT : ∀ x, f x ∈ Icc a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → f x ∈ T := fun x hx hc =>
    (Set.Finite.mem_toFinset _).2 ⟨x, ⟨hx, hc⟩, rfl⟩
  set A := insert a (T.filter fun v => v < f p) with hA
  set B := insert b (T.filter fun v => f q < v) with hB
  have hAne : A.Nonempty := Finset.insert_nonempty _ _
  have hBne : B.Nonempty := Finset.insert_nonempty _ _
  set a₀ := A.max' hAne with ha₀
  set b₀ := B.min' hBne with hb₀
  have haa₀ : a ≤ a₀ := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hbb₀ : b₀ ≤ b := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have ha₀p : a₀ < f p := by
    rw [ha₀, Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hp.1
    · exact (Finset.mem_filter.1 hy).2
  have hqb₀ : f q < b₀ := by
    rw [hb₀, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hq.2
    · exact (Finset.mem_filter.1 hy).2
  have hlea₀ : ∀ x, f x ∈ Icc a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → f x < f p → f x ≤ a₀ := fun x hx hc h =>
    Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hmemT x hx hc, h⟩))
  have hgeb₀ : ∀ x, f x ∈ Icc a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → f q < f x → b₀ ≤ f x := fun x hx hc h =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hmemT x hx hc, h⟩))
  obtain ⟨a', ha', ha'reg⟩ := hf.exists_regular_level haa₀ ha₀p hp.2.le
  obtain ⟨b', hb', hb'reg⟩ := hf.exists_regular_level hq.1.le hqb₀ hbb₀
  refine ⟨a', b', haa₀.trans_lt ha'.1, ha'.2, hb'.1, hb'.2.trans_le hbb₀, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact ha'reg x hx
    · exact hb'reg x hx
  · intro x hx hc
    have hxab : f x ∈ Icc a b :=
      ⟨(haa₀.trans_lt ha'.1).le.trans hx.1.le, hx.2.le.trans (hb'.2.trans_le hbb₀).le⟩
    have hxab' : f x ∈ Ioo a b :=
      ⟨(haa₀.trans_lt ha'.1).trans hx.1, hx.2.trans (hb'.2.trans_le hbb₀)⟩
    have h1 : f p ≤ f x := by
      refine le_of_not_gt fun h => ?_
      have := hlea₀ x hxab hc h
      linarith [ha'.1, hx.1]
    have h2 : f x ≤ f q := by
      refine le_of_not_gt fun h => ?_
      have := hgeb₀ x hxab hc h
      linarith [hb'.2, hx.2]
    have hnot := hadj x hxab' hc
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact absurd ⟨h1, h2⟩ hnot
      · exact Or.inr (hinj ⟨hxab', hc⟩ ⟨hq, hcq⟩ h2)
    · exact Or.inl (hinj ⟨hxab', hc⟩ ⟨hp, hcp⟩ h1.symm)

theorem exists_swap [T2Space M] [SigmaCompactSpace M] (hf : MorseStrip I f a b)
    (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) {p q : M}
    (hp : f p ∈ Ioo a b) (hq : f q ∈ Ioo a b) (hcp : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p)
    (hcq : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f q) (hlt : f p < f q)
    (hadj : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → f x ∉ Ioo (f p) (f q))
    (hidx : morseIndex I f q < morseIndex I f p) :
    ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) ∧
      g p = f p ∧ g q < f p ∧ g q ∈ Ioo a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ q → g x = f x) ∧
      (∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → g q < f x → f p ≤ f x) ∧
      InjOn g {x | g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x} := by
  classical
  have hpq : p ≠ q := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  have hqp : q ≠ p := Ne.symm hpq
  obtain ⟨a', b', haa', ha'p, hqb', hb'b, hreg, hsub⟩ :=
    exists_regular_substrip hf hinj hp hq hcp hcq hadj
  have hab' : a' < b' := by linarith
  set crit : Finset M := {p, q} with hcritdef
  have hpc : p ∈ crit := by simp [hcritdef]
  have hqc : q ∈ crit := by simp [hcritdef]
  have hcrit' : ∀ p' ∈ crit, p' = p ∨ p' = q := fun p' hp' => by
    simpa [hcritdef] using hp'
  have hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x
    constructor
    · intro hx
      rcases hcrit' x hx with rfl | rfl
      · exact ⟨⟨ha'p, by linarith⟩, hcp⟩
      · exact ⟨⟨by linarith, hqb'⟩, hcq⟩
    · rintro ⟨hx, hc⟩
      rcases hsub x hx hc with rfl | rfl
      · exact hpc
      · exact hqc
  obtain ⟨D₀, -, hD₀rm, hD₀r₀⟩ := exists_gradientLikeStrip hf haa'.le hab' hb'b.le hreg crit hcrit
    (R₀ := 1) one_pos
  have hRp : 0 < (D₀.chart p hpc).R := (D₀.chart p hpc).R_pos
  have hRq : 0 < (D₀.chart q hqc).R := (D₀.chart q hqc).R_pos
  set ε : ℝ := min (min ((D₀.chart p hpc).R ^ 2 / 25) ((D₀.chart q hqc).R ^ 2 / 25))
    ((f q - f p) / 10) with hεdef
  have hε : 0 < ε := by
    refine lt_min (lt_min ?_ ?_) ?_ <;> positivity
  have hεRp : ε ≤ (D₀.chart p hpc).R ^ 2 / 25 := (min_le_left _ _).trans (min_le_left _ _)
  have hεRq : ε ≤ (D₀.chart q hqc).R ^ 2 / 25 := (min_le_left _ _).trans (min_le_right _ _)
  have hεpq : ε ≤ (f q - f p) / 10 := min_le_right _ _
  set r₁ : ℝ := min (min (D₀.chart p hpc).r₀ (D₀.chart q hqc).r₀) (Real.sqrt ε) with hr₁def
  have hr₁ : 0 < r₁ :=
    lt_min (lt_min (D₀.chart p hpc).hr₀ (D₀.chart q hqc).hr₀) (Real.sqrt_pos.2 hε)
  have hle₁ : r₁ ≤ (D₀.chart p hpc).r₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hle₂ : r₁ ≤ (D₀.chart q hqc).r₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hr₁ε : r₁ ^ 2 ≤ ε := by
    calc r₁ ^ 2 ≤ Real.sqrt ε ^ 2 := pow_le_pow_left₀ hr₁.le (min_le_right _ _) 2
      _ = ε := Real.sq_sqrt hε.le
  obtain ⟨D, hD⟩ : ∃ D : GradientLikeStrip I f a' b' crit,
    GradientLikeStrip.shrink₂ (D := D₀) hf.smooth hpc hqc hqp hr₁ hle₁ hr₁ hle₂ = D := ⟨_, rfl⟩
  have hDr₀p : (D.chart p hpc).r₀ = r₁ := by
    rw [← hD]; exact GradientLikeStrip.shrink₂_r₀_p _ _ _ _ _ _ _ _
  have hDr₀q : (D.chart q hqc).r₀ = r₁ := by
    rw [← hD]; exact GradientLikeStrip.shrink₂_r₀_q _ _ _ _ _ _ _ _
  have hDrm : D.rm = D₀.rm := by rw [← hD]; rfl
  have hDrmp : D.rm p hpc = (D₀.chart p hpc).R := by rw [hDrm, hD₀rm]
  have hDrmq : D.rm q hqc = (D₀.chart q hqc).R := by rw [hDrm, hD₀rm]
  have hr₀p : (D.chart p hpc).r₀ ^ 2 < 2 * ε := by rw [hDr₀p]; linarith
  have hr₀q : (D.chart q hqc).r₀ ^ 2 < 2 * ε := by rw [hDr₀q]; linarith
  have hrmp : 24 * ε < D.rm p hpc ^ 2 := by rw [hDrmp]; nlinarith
  have hrmq : 4 * ε < D.rm q hqc ^ 2 := by rw [hDrmq]; nlinarith
  set c : ℝ := (f p + 8 * ε + (f q - ε)) / 2 with hcdef
  have hc : f p + 8 * ε < c := by rw [hcdef]; linarith
  have hcq' : c < f q - ε := by rw [hcdef]; linarith
  have hlev : ∀ y, f y ∈ Icc (f p + ε) (f q - ε) → ∀ p' hp', y ∉ D.smallBall p' hp' :=
    D.levels_avoid_pair hpc hqc hcrit' hr₀p.le hr₀q.le
  obtain ⟨D', -, -, hD'rmp, hD'rmne, -, -, -, -, r', hr'0, hr'p, hr'q, hr'ε, hnocommon, -⟩ :=
    GradientLikeStrip.exists_gradientLike_generalPosition hf.smooth D hpc hqc hpq hidx hε hr₀p
      hr₀q hrmp hrmq hc hcq' hlev
  have hD'r₀p : (D'.chart p hpc).r₀ ^ 2 < ε := by
    calc (D'.chart p hpc).r₀ ^ 2 < r' ^ 2 :=
          pow_lt_pow_left₀ hr'p (D'.chart p hpc).hr₀.le two_ne_zero
      _ < ε := hr'ε
  have hD'r₀q : (D'.chart q hqc).r₀ ^ 2 < ε := by
    calc (D'.chart q hqc).r₀ ^ 2 < r' ^ 2 :=
          pow_lt_pow_left₀ hr'q (D'.chart q hqc).hr₀.le two_ne_zero
      _ < ε := hr'ε
  have hD'rmq : D'.rm q hqc = D.rm q hqc := hD'rmne q hqc hqp
  have hε2 : 0 < ε / 2 := by positivity
  have hcab' : c ∈ Ioo a' b' := ⟨by linarith, by linarith⟩
  have hlev' : ∀ y, f y ∈ Icc (f p + ε / 2) (f q - ε / 2) → ∀ p' hp', y ∉ D'.smallBall p' hp' :=
    D'.levels_avoid_pair hpc hqc hcrit' (by linarith) (by linarith)
  have hcU : ∀ p' hp', ∀ y ∈ D'.smallBall p' hp', f y ≠ c := fun p' hp' y hy hyc =>
    hlev' y ⟨by rw [hyc]; linarith, by rw [hyc]; linarith⟩ p' hp' hy
  have hεr : ∀ p' hp', (D'.chart p' hp').r₀ ^ 2 < 2 * (ε / 2) ∧ 8 * (ε / 2) < D'.rm p' hp' ^ 2 := by
    intro p' hp'
    rcases hcrit' p' hp' with rfl | rfl
    · exact ⟨by linarith, by rw [hD'rmp]; linarith⟩
    · exact ⟨by linarith, by rw [hD'rmq]; linarith⟩
  have hcε : ∀ p' ∈ crit, (f p' < c → f p' + ε / 2 < c) ∧ (c < f p' → c < f p' - ε / 2) := by
    intro p' hp'
    rcases hcrit' p' hp' with rfl | rfl
    · exact ⟨fun _ => by linarith, fun h => by linarith⟩
    · exact ⟨fun h => by linarith, fun _ => by linarith⟩
  have hr' : ∀ p' hp', (D'.chart p' hp').r₀ < (fun _ _ => r' : ∀ p ∈ crit, ℝ) p' hp' := by
    intro p' hp'
    rcases hcrit' p' hp' with rfl | rfl
    · exact hr'p
    · exact hr'q
  have hnocommon' : ∀ p' hp' q' hq', p' ∈ ({p} : Set M) → q' ∈ ({q} : Set M) →
      ∀ x ∈ (D'.chart p' hp').χ '' {y | morseNorm n y < (fun _ _ => r' : ∀ p ∈ crit, ℝ) p' hp'},
        ∀ t, D'.flow t x ∉
          (D'.chart q' hq').χ '' {y | morseNorm n y < (fun _ _ => r' : ∀ p ∈ crit, ℝ) q' hq'} := by
    intro p' hp' q' hq' hp'' hq''
    rw [mem_singleton_iff] at hp'' hq''
    subst hp'' hq''
    exact hnocommon
  obtain ⟨μ, hμ, hμ01, hμV, hμ0, hμ1⟩ := exists_trajectoryCutoff hf.smooth D' {p} {q}
    (fun p' hp' => by rcases hcrit' p' hp' with rfl | rfl <;> simp)
    (fun p' hp' hp'' => by rw [mem_singleton_iff] at hp' hp''; exact hpq (hp'.symm.trans hp''))
    hcab' hcU hε2 hεr hcε (fun _ _ => r') hr' hnocommon'
  set a₃ : ℝ := (a' + f p) / 2 with ha₃
  set b₃ : ℝ := (f q + b') / 2 with hb₃
  set y₀ : ℝ := (a₃ + f p) / 2 with hy₀
  have h₃ : a' < a₃ ∧ b₃ < b' := ⟨by rw [ha₃]; linarith, by rw [hb₃]; linarith⟩
  have ha₃p : a₃ < f p := by rw [ha₃]; linarith
  have hqb₃ : f q < b₃ := by rw [hb₃]; linarith
  have hy₀a : a₃ < y₀ := by rw [hy₀]; linarith
  have hy₀p : y₀ < f p := by rw [hy₀]; linarith
  obtain ⟨ρ, hρ, hρ', -, hρid, hρmaps₃, hρq, -⟩ :=
    MonotoneShift.exists_monotoneShift (c₀ := a₃) (x₀ := f q) (y₀ := y₀) (c₁ := b₃)
      ⟨by linarith, hqb₃⟩ ⟨hy₀a, by linarith⟩
  have hρmaps : MapsTo ρ (Ioo a' b') (Ioo a' b') := by
    intro t ht
    by_cases ht' : t ∈ Ioo a₃ b₃
    · have := hρmaps₃ ht'
      exact ⟨h₃.1.trans this.1, this.2.trans h₃.2⟩
    · rw [hρid t ht']
      exact ht
  obtain ⟨-, -, hmod, hstrip, hcritIff, hidxEq, hg0, hg1, hEqOn⟩ :=
    rearrange_of_partition hf haa'.le hab' hb'b.le hreg D' hcrit {p} {q}
      (fun p' hp' => by rcases hcrit' p' hp' with rfl | rfl <;> simp) μ hμ hμ01 hμV hμ0 hμ1 ρ hρ
      hρ' hρid h₃ hρmaps
  set g := Rearrange.rearranged f μ ρ with hgdef
  have hgp : g p = f p := hg0 p hpc rfl
  have hgq : g q = y₀ := by rw [hg1 q hqc rfl, hρq]
  have hgq' : g q < f p := by rw [hgq]; exact hy₀p
  have hother : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ q → g x = f x := by
    intro x hx hxq
    by_cases hx' : f x ∈ Ioo a' b'
    · rcases hsub x hx' hx with rfl | rfl
      · exact hgp
      · exact absurd rfl hxq
    · apply hEqOn
      rcases le_or_gt (f x) a₃ with h | h
      · exact Or.inl h
      · exact Or.inr (le_of_not_gt fun h' => hx' ⟨h₃.1.trans h, h'.trans h₃.2⟩)
  have hsep : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → g q < f x → f p ≤ f x := by
    intro x hx hc hgx
    refine le_of_not_gt fun hcon => ?_
    rw [hgq] at hgx
    have hx' : f x ∈ Ioo a' b' := ⟨by linarith [h₃.1], by linarith⟩
    rcases hsub x hx' hc with rfl | rfl
    · exact lt_irrefl _ hcon
    · exact absurd (hcon.trans hlt) (lt_irrefl _)
  have hpre : ∀ x, g x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod.preimage_Ioo x
  refine ⟨g, hmod, hstrip, hcritIff, hidxEq, hgp, hgq', ⟨by linarith [h₃.1, hy₀a], by linarith⟩,
    hother, hsep, ?_⟩
  intro x hx y hy hxy
  have hcx : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := (hcritIff x).1 hx.2
  have hcy : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f y := (hcritIff y).1 hy.2
  have hfx : f x ∈ Ioo a b := (hpre x).1 hx.1
  have hfy : f y ∈ Ioo a b := (hpre y).1 hy.1
  have key : ∀ z, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f z → z ≠ q → g z = y₀ → False := by
    intro z hz hzq hgz
    rw [hother z hz hzq] at hgz
    have hz' : f z ∈ Ioo a' b' := ⟨by rw [hgz]; linarith [h₃.1], by rw [hgz]; linarith⟩
    rcases hsub z hz' hz with rfl | rfl
    · exact absurd hgz (by linarith)
    · exact hzq rfl
  by_cases hxq : x = q
  · by_cases hyq : y = q
    · rw [hxq, hyq]
    · subst hxq
      exact absurd (hxy.symm.trans hgq) (fun h => key y hcy hyq h)
  · by_cases hyq : y = q
    · subst hyq
      exact absurd (hxy.trans hgq) (fun h => key x hcx hxq h)
    · rw [hother x hcx hxq, hother y hcy hyq] at hxy
      exact hinj ⟨hfx, hcx⟩ ⟨hfy, hcy⟩ hxy

variable (I) in
def invSet (f : M → ℝ) (a b : ℝ) : Set (M × M) :=
  {pq | (f pq.1 ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f pq.1) ∧ (f pq.2 ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f pq.2) ∧
    f pq.1 < f pq.2 ∧ morseIndex I f pq.2 < morseIndex I f pq.1}

theorem invSet_finite (hf : MorseStrip I f a b) : (invSet I f a b).Finite :=
  (hf.finite_critical.prod hf.finite_critical).subset fun _ hpq =>
    ⟨⟨Ioo_subset_Icc_self hpq.1.1, hpq.1.2⟩, ⟨Ioo_subset_Icc_self hpq.2.1.1, hpq.2.1.2⟩⟩

theorem exists_adjacent_inversion (hf : MorseStrip I f a b)
    (hne : (invSet I f a b).Nonempty) :
    ∃ p q : M, f p ∈ Ioo a b ∧ f q ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f q ∧
      f p < f q ∧ morseIndex I f q < morseIndex I f p ∧
      ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → f x ∉ Ioo (f p) (f q) := by
  classical
  have hfin := invSet_finite hf
  obtain ⟨⟨p, q⟩, hpq, hmin⟩ := Finset.exists_min_image hfin.toFinset
    (fun pq : M × M => f pq.2 - f pq.1) (by
      obtain ⟨pq, hpq⟩ := hne
      exact ⟨pq, hfin.mem_toFinset.2 hpq⟩)
  rw [hfin.mem_toFinset] at hpq
  obtain ⟨⟨hp, hcp⟩, ⟨hq, hcq⟩, hlt, hidx⟩ := hpq
  refine ⟨p, q, hp, hq, hcp, hcq, hlt, hidx, fun x hx hcx hmem => ?_⟩
  by_cases h : morseIndex I f x < morseIndex I f p
  · have hmem' : (p, x) ∈ invSet I f a b := ⟨⟨hp, hcp⟩, ⟨hx, hcx⟩, hmem.1, h⟩
    have := hmin (p, x) (hfin.mem_toFinset.2 hmem')
    simp only at this
    linarith [hmem.2]
  · push Not at h
    have hmem' : (x, q) ∈ invSet I f a b := ⟨⟨hx, hcx⟩, ⟨hq, hcq⟩, hmem.2, hidx.trans_le h⟩
    have := hmin (x, q) (hfin.mem_toFinset.2 hmem')
    simp only at this
    linarith [hmem.1]

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem isSelfIndexing_of_invSet_eq_empty
    (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) (h : invSet I f a b = ∅) :
    isSelfIndexing I f a b := by
  intro p q hp hq hcp hcq hidx
  by_contra hlt
  push Not at hlt
  rcases hlt.lt_or_eq with hlt | heq
  · have hmem : (q, p) ∈ invSet I f a b := ⟨⟨hq, hcq⟩, ⟨hp, hcp⟩, hlt, hidx⟩
    rw [h] at hmem
    exact hmem
  · have := hinj ⟨hq, hcq⟩ ⟨hp, hcp⟩ heq
    subst this
    exact lt_irrefl _ hidx

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem invSet_ssubset_of_swap (hinj : InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})
    {p q : M} (hp : f p ∈ Ioo a b) (hq : f q ∈ Ioo a b) (hcp : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p)
    (hcq : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f q) (hlt : f p < f q)
    (hadj : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → f x ∉ Ioo (f p) (f q))
    (hidx : morseIndex I f q < morseIndex I f p) {g : M → ℝ} (hmod : ModifiedWithin f a b g)
    (hcritIff : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hidxEq : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x)
    (hgp : g p = f p) (hgq : g q < f p) (hother : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → x ≠ q → g x = f x)
    (hsep : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → g q < f x → f p ≤ f x) :
    invSet I g a b ⊂ invSet I f a b := by
  have hpre : ∀ x, g x ∈ Ioo a b ↔ f x ∈ Ioo a b := fun x =>
    Set.ext_iff.1 hmod.preimage_Ioo x
  refine Set.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨⟨hgx, hcx⟩, ⟨hgy, hcy⟩, hxy, hixy⟩
    have hcfx : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := (hcritIff x).1 hcx
    have hcfy : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f y := (hcritIff y).1 hcy
    have hfx : f x ∈ Ioo a b := (hpre x).1 hgx
    have hfy : f y ∈ Ioo a b := (hpre y).1 hgy
    rw [hidxEq x hcfx, hidxEq y hcfy] at hixy
    refine ⟨⟨hfx, hcfx⟩, ⟨hfy, hcfy⟩, ?_, hixy⟩
    simp only at hxy ⊢
    by_cases hxq : x = q
    · subst hxq
      by_cases hyq : y = x
      · subst hyq
        exact absurd hxy (lt_irrefl _)
      · rw [hother y hcfy hyq] at hxy
        have h1 : f p ≤ f y := hsep y hfy hcfy hxy
        rcases h1.lt_or_eq with h1 | h1
        · have h2 : f x ≤ f y := by
            by_contra h2
            push Not at h2
            exact hadj y hfy hcfy ⟨h1, h2⟩
          rcases h2.lt_or_eq with h2 | h2
          · exact h2
          · exact absurd (hinj ⟨hfx, hcfx⟩ ⟨hfy, hcfy⟩ h2) (Ne.symm hyq)
        · have := hinj ⟨hp, hcp⟩ ⟨hfy, hcfy⟩ h1
          subst this
          exact absurd (hixy.trans hidx) (lt_irrefl _)
    · by_cases hyq : y = q
      · subst hyq
        rw [hother x hcfx hxq] at hxy
        exact hxy.trans (hgq.trans hlt)
      · rw [hother x hcfx hxq, hother y hcfy hyq] at hxy
        exact hxy
  · intro heq
    have hmem : (p, q) ∈ invSet I f a b := ⟨⟨hp, hcp⟩, ⟨hq, hcq⟩, hlt, hidx⟩
    rw [← heq] at hmem
    have h5 : g p < g q := hmem.2.2.1
    rw [hgp] at h5
    exact absurd (h5.trans hgq) (lt_irrefl _)

theorem exists_selfIndexing_of_injOn [T2Space M] [SigmaCompactSpace M] (N : ℕ) :
    ∀ f : M → ℝ, MorseStrip I f a b → InjOn f {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} →
      (invSet I f a b).ncard = N →
      ∃ g : M → ℝ, ModifiedWithin f a b g ∧ MorseStrip I g a b ∧ isSelfIndexing I g a b ∧
        (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
        (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I g x = morseIndex I f x) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f hf hinj hN
    by_cases h0 : invSet I f a b = ∅
    · exact ⟨f, ModifiedWithin.refl f a b, hf, isSelfIndexing_of_invSet_eq_empty hinj h0,
        fun _ => Iff.rfl, fun _ _ => rfl⟩
    · have hne : (invSet I f a b).Nonempty := nonempty_iff_ne_empty.2 h0
      obtain ⟨p, q, hp, hq, hcp, hcq, hlt, hidx, hadj⟩ := exists_adjacent_inversion hf hne
      obtain ⟨g, hmod, hg, hcritIff, hidxEq, hgp, hgq, -, hother, hsep, hinjg⟩ :=
        exists_swap hf hinj hp hq hcp hcq hlt hadj hidx
      have hss := invSet_ssubset_of_swap hinj hp hq hcp hcq hlt hadj hidx hmod hcritIff hidxEq hgp
        hgq hother hsep
      have hlt' : (invSet I g a b).ncard < N := by
        rw [← hN]
        exact Set.ncard_lt_ncard hss (invSet_finite hf)
      obtain ⟨g', hmod', hg', hself, hcritIff', hidxEq'⟩ := ih _ hlt' g hg hinjg rfl
      refine ⟨g', hmod.trans hmod', hg', hself, fun x => (hcritIff' x).trans (hcritIff x),
        fun x hx => ?_⟩
      rw [hidxEq' x ((hcritIff x).2 hx), hidxEq x hx]

end Swap

end

end DifferentialGeometry.Topology
