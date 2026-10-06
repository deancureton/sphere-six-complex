module

public import DifferentialGeometry.Topology.Morse.Strip.Foundations.RelativePerturbation

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M]
  {f : M → ℝ} {a b : ℝ}

namespace MorseStrip

theorem eventually_fderiv_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x)
    (hinj : Function.Injective (fderiv ℝ (fderiv ℝ g) x)) :
    ∀ᶠ z in 𝓝[≠] x, fderiv ℝ g z ≠ 0 := by
  have hd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x := by
    have : DifferentiableAt ℝ (fderiv ℝ g) x :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact this.hasFDerivAt
  refine hd.eventually_ne ?_
  obtain ⟨K, -, hK⟩ :=
    (fderiv ℝ (fderiv ℝ g) x).toLinearMap.injective_iff_antilipschitz.mp hinj
  exact ⟨K, hK⟩

theorem eventually_not_isCriticalPointAt (hf : MorseStrip I f a b) {p : M} (hp : f p ∈ Ioo a b)
    (hc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p) : ∀ᶠ x in 𝓝[≠] p, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
  set g := MorseExistence.chartRep I f p with hgdef
  set x₀ := extChartAt I p p with hx₀def
  have hpp : p ∈ (extChartAt I p).source := mem_extChartAt_source (I := I) p
  have hg : ContDiffAt ℝ 2 g x₀ :=
    (MorseExistence.contDiffAt_chartRep hf.smooth (mem_extChartAt_target (I := I) p)).of_le
      MorseExistence.two_le_infty
  have hsep : (QuadraticMap.associated (R := ℝ) (DifferentialGeometry.Topology.Morse.chartHessianAt g x₀)).SeparatingLeft :=
    (hf.nondegenerate p hp hc).2
  have hinj : Function.Injective (fderiv ℝ (fderiv ℝ g) x₀) := by
    intro u v huv
    rw [MorseExistence.separatingLeft_assoc_iff hg] at hsep
    have : u - v = 0 := hsep (u - v) fun w => by
      rw [map_sub, sub_apply, huv, sub_self]
    exact sub_eq_zero.mp this
  have hev : ∀ᶠ y in 𝓝[≠] x₀, fderiv ℝ g y ≠ 0 := eventually_fderiv_ne_zero hg hinj
  rw [eventually_nhdsWithin_iff] at hev ⊢
  have hcont : ContinuousAt (extChartAt I p) p := continuousAt_extChartAt (I := I) p
  filter_upwards [hcont.tendsto.eventually hev, extChartAt_source_mem_nhds (I := I) p]
    with x hx hxs hxp
  rw [MorseExistence.isCriticalPointAt_iff_chart hf.smooth hxs]
  refine hx fun heq => hxp ?_
  exact (extChartAt I p).injOn hxs hpp heq

theorem finite_critical (hf : MorseStrip I f a b) :
    {x | f x ∈ Icc a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}.Finite := by
  have hclosed : IsClosed {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} := by
    have := (MorseExistence.isOpen_regular hf.smooth).isClosed_compl
    convert this using 1
    ext x; simp
  have hS : IsCompact (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) :=
    hf.compact.inter_right hclosed
  refine (hS.finite (isDiscrete_iff_forall_mem_exists_isOpen.mpr fun p hp => ?_)).subset
    fun x hx => ⟨hx.1, hx.2⟩
  have hpo : f p ∈ Ioo a b := by
    rcases hp with ⟨⟨h1, h2⟩, hc⟩
    refine ⟨lt_of_le_of_ne h1 fun h => ?_, lt_of_le_of_ne h2 fun h => ?_⟩
    · exact hf.regular p (Or.inl h.symm) hc
    · exact hf.regular p (Or.inr h) hc
  have hev := hf.eventually_not_isCriticalPointAt hpo hp.2
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨u, hu_sub, hu_open, hpu⟩ := mem_nhds_iff.mp hev
  refine ⟨u, hu_open, ?_⟩
  ext x
  constructor
  · rintro ⟨hxu, hxS⟩
    by_contra hxp
    exact hu_sub hxu hxp hxS.2
  · rintro rfl
    exact ⟨hpu, hp⟩

theorem exists_collar (hf : MorseStrip I f a b) :
    ∃ δ > 0, δ ≤ b - a ∧ ∀ x, f x ∈ Icc a b → (f x ≤ a + δ ∨ b - δ ≤ f x) →
      ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
  have hfc : Continuous f := hf.smooth.continuous
  have hclosed : IsClosed {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} := by
    have := (MorseExistence.isOpen_regular hf.smooth).isClosed_compl
    convert this using 1
    ext x; simp
  have hCrit : IsCompact (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) :=
    hf.compact.inter_right hclosed
  have hS : IsCompact (f '' (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x})) := hCrit.image hfc
  have ha : a ∉ f '' (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) := by
    rintro ⟨x, ⟨-, hx2⟩, hx3⟩; exact hf.regular x (Or.inl hx3) hx2
  have hb : b ∉ f '' (f ⁻¹' Icc a b ∩ {x | DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}) := by
    rintro ⟨x, ⟨-, hx2⟩, hx3⟩; exact hf.regular x (Or.inr hx3) hx2
  obtain ⟨δ₁, hδ₁, h1⟩ := Metric.mem_nhds_iff.1 (hS.isClosed.isOpen_compl.mem_nhds ha)
  obtain ⟨δ₂, hδ₂, h2⟩ := Metric.mem_nhds_iff.1 (hS.isClosed.isOpen_compl.mem_nhds hb)
  have hab : 0 < b - a := sub_pos.mpr hf.lt
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

theorem finite_criticalValues (hf : MorseStrip I f a b) :
    (f '' {x | f x ∈ Icc a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}).Finite :=
  hf.finite_critical.image f

theorem exists_regular_level (hf : MorseStrip I f a b) {c₁ c₂ : ℝ} (h₁ : a ≤ c₁)
    (h₁₂ : c₁ < c₂) (h₂ : c₂ ≤ b) :
    ∃ c ∈ Ioo c₁ c₂, ∀ x, f x = c → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
  obtain ⟨c, hc, hcn⟩ := (Set.Ioo_infinite h₁₂).exists_notMem_finite hf.finite_criticalValues
  refine ⟨c, hc, fun x hx hcrit => hcn ⟨x, ⟨?_, hcrit⟩, hx⟩⟩
  rw [hx]
  exact ⟨h₁.trans hc.1.le, hc.2.le.trans h₂⟩

theorem exists_chartBall_no_other_critical (hf : MorseStrip I f a b) {p : M}
    (hp : f p ∈ Ioo a b) (hc : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f p) :
    ∃ ρ > 0, Metric.closedBall (extChartAt I p p) ρ ⊆ (extChartAt I p).target ∧
      (∀ y ∈ Metric.closedBall (extChartAt I p p) ρ, f ((extChartAt I p).symm y) ∈ Ioo a b) ∧
      ∀ y ∈ Metric.closedBall (extChartAt I p p) ρ,
        DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f ((extChartAt I p).symm y) → y = extChartAt I p p := by
  have hfc : Continuous f := hf.smooth.continuous
  have hev := hf.eventually_not_isCriticalPointAt hp hc
  rw [eventually_nhdsWithin_iff] at hev
  have hW : {x | x ≠ p → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} ∩ f ⁻¹' Ioo a b ∈ 𝓝 p :=
    inter_mem hev ((isOpen_Ioo.preimage hfc).mem_nhds hp)
  have hsymm : ContinuousAt (extChartAt I p).symm (extChartAt I p p) :=
    continuousAt_extChartAt_symm (I := I) p
  have hW' : (extChartAt I p).symm ⁻¹' ({x | x ≠ p → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} ∩ f ⁻¹' Ioo a b) ∩
      (extChartAt I p).target ∈ 𝓝 (extChartAt I p p) := by
    refine inter_mem ?_ (extChartAt_target_mem_nhds (I := I) p)
    have := hsymm.preimage_mem_nhds (by rwa [(extChartAt I p).left_inv (mem_extChartAt_source p)])
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW'
  refine ⟨ε / 2, by positivity, ?_, ?_, ?_⟩
  · intro y hy
    exact (hball (Metric.closedBall_subset_ball (by linarith) hy)).2
  · intro y hy
    exact (hball (Metric.closedBall_subset_ball (by linarith) hy)).1.2
  · intro y hy hcrit
    have hy' := hball (Metric.closedBall_subset_ball (by linarith) hy)
    have heq : (extChartAt I p).symm y = p := by
      by_contra hne
      exact hy'.1.1 hne hcrit
    calc y = extChartAt I p ((extChartAt I p).symm y) := ((extChartAt I p).right_inv hy'.2).symm
      _ = extChartAt I p p := by rw [heq]

end MorseStrip

end

end DifferentialGeometry.Topology
