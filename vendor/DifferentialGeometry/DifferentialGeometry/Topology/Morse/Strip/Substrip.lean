module

public import DifferentialGeometry.Topology.Morse.Cancellation.Setup.Isolate

@[expose] public section

open Set Filter

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

section Substrip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : ModelWithCorners ℝ E H}
  {f g : M → ℝ} {a b a' b' : ℝ}

theorem MorseStrip.substrip (hf : MorseStrip I f a b) (ha : a ≤ a') (hab' : a' < b')
    (hb : b' ≤ b) (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) :
    MorseStrip I f a' b' where
  smooth := hf.smooth
  lt := hab'
  compact := hf.compact.of_isClosed_subset (isClosed_Icc.preimage hf.smooth.continuous)
    (preimage_mono (Icc_subset_Icc ha hb))
  regular := hreg
  nondegenerate := fun x hx hc =>
    hf.nondegenerate x ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩ hc

theorem ModifiedWithin.eventuallyEq_of_notMem_Icc (h : ModifiedWithin f a' b' g)
    (hf : Continuous f) {x : M} (hx : f x ∉ Icc a' b') : g =ᶠ[𝓝 x] f := by
  have hopen : IsOpen ((f ⁻¹' Icc a' b')ᶜ) := (isClosed_Icc.preimage hf).isOpen_compl
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact h.eqOn fun hy' => hy (Ioo_subset_Icc_self hy')

theorem ModifiedWithin.morseStrip_of_substrip (hf : MorseStrip I f a b)
    (ha : a ≤ a') (hb : b' ≤ b) (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hmod : ModifiedWithin f a' b' g) (hg : MorseStrip I g a' b') :
    MorseStrip I g a b ∧
      ∀ x, f x ∉ Ioo a' b' → g x = f x ∧ (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
        (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → (DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f x) ∧
          morseIndex I g x = morseIndex I f x) := by
  have hfc : Continuous f := hf.smooth.continuous
  have hmod' : ModifiedWithin f a b g := hmod.mono ha hb
  have hoff : ∀ x, f x ∉ Ioo a' b' → g x = f x ∧ (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → (DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f x) ∧
        morseIndex I g x = morseIndex I f x) := by
    intro x hx
    refine ⟨hmod.eqOn hx, ?_⟩
    by_cases hxI : f x ∈ Icc a' b'
    · have hfx : f x = a' ∨ f x = b' := by
        rcases hxI with ⟨h1, h2⟩
        rcases h1.eq_or_lt with h | h
        · exact Or.inl h.symm
        rcases h2.eq_or_lt with h' | h'
        · exact Or.inr h'
        exact absurd ⟨h, h'⟩ hx
      have hnf : ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := hreg x hfx
      have hng : ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x := hg.regular x (by rwa [hmod.eqOn hx])
      exact ⟨iff_of_false hng hnf, fun h => absurd h hnf⟩
    · have hev := hmod.eventuallyEq_of_notMem_Icc hfc hxI
      exact ⟨MonotoneShift.isCriticalPointAt_congr_nhds hev, fun _ =>
        ⟨MonotoneShift.isNondegenerateCriticalPointAt_congr_nhds hev,
          MonotoneShift.morseIndex_congr_nhds hev⟩⟩
  refine ⟨⟨hg.smooth, hf.lt, ?_, fun x hx => ?_, fun x hx hxc => ?_⟩, hoff⟩
  · rw [hmod'.preimage_Icc]
    exact hf.compact
  · have hfx : f x = a ∨ f x = b := by
      rcases hx with hx | hx
      · left
        have : x ∈ g ⁻¹' {a} := hx
        rwa [hmod'.preimage_singleton_left] at this
      · right
        have : x ∈ g ⁻¹' {b} := hx
        rwa [hmod'.preimage_singleton_right] at this
    have hx' : f x ∉ Ioo a' b' := by
      rcases hfx with h | h
      · rw [h]; exact fun h' => absurd (ha.trans_lt h'.1) (lt_irrefl a)
      · rw [h]; exact fun h' => absurd (h'.2.trans_le hb) (lt_irrefl b)
    rw [(hoff x hx').2.1]
    exact hf.regular x hfx
  · by_cases hx' : f x ∈ Ioo a' b'
    · exact hg.nondegenerate x (hmod.mapsTo hx') hxc
    · have hfx : f x ∈ Ioo a b := by
        have : x ∈ g ⁻¹' Ioo a b := hx
        rwa [hmod'.preimage_Ioo] at this
      have hxf : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := ((hoff x hx').2.1).1 hxc
      exact ((hoff x hx').2.2 hxf).1.2 (hf.nondegenerate x hfx hxf)

end Substrip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} {f : M → ℝ} {a b : ℝ} {crit : Finset M}

namespace GradientLikeStrip

variable [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] {D : GradientLikeStrip I f a b crit}

theorem mem_modelBall_of_mem_basin_index_zero (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {p : M} {hp : p ∈ crit} (hk : (D.chart p hp).k = 0) {z : M} (hz : z ∈ D.basin p hp)
    (hfz : 2 * (f z - f p) < D.rm p hp ^ 2) :
    z ∈ (D.chart p hp).χ '' {y | morseNorm n y < D.rm p hp} := by
  obtain ⟨s, hs, hmem⟩ := hz
  set d := D.chart p hp with hd
  set B := d.χ '' {y | morseNorm n y < D.rm p hp} with hB
  have hBo : IsOpen B := D.isOpen_modelBall p hp
  by_contra hzB
  set γ : ℝ → M := fun u => D.flow (s - u) z with hγ
  have hγc : Continuous γ :=
    D.continuous_flow_joint.comp ((continuous_const.sub continuous_id).prodMk continuous_const)
  have hγs : γ s ∈ Bᶜ := by
    change D.flow (s - s) z ∉ B
    rw [sub_self, D.flow_zero]
    exact hzB
  obtain ⟨s₀, hs₀, hs₀K, hmin⟩ :=
    exists_first_time hBo.isClosed_compl hγc (t := s) ⟨s, ⟨hs, le_rfl⟩, hγs⟩
  have hs₀pos : 0 < s₀ := by
    rcases hs₀.1.eq_or_lt with h | h
    · exfalso
      apply hs₀K
      change D.flow (s - s₀) z ∈ B
      rw [← h, sub_zero]
      exact hmem
    · exact h
  have hrm0 := D.rm_pos p hp
  set ρ := Real.sqrt (2 * (f z - f p)) with hρ
  have hin : ∀ u ∈ Ico 0 s₀, γ u ∈ d.χ '' {y | morseNorm n y ≤ ρ} := by
    intro u hu
    have hB' : γ u ∈ B := not_not.1 (hmin u hu)
    obtain ⟨y, hy, hyγ⟩ := hB'
    refine ⟨y, ?_, hyγ⟩
    have hfγ : f (γ u) ≤ f z := f_flow_le hf z (by linarith [hu.2, hs₀.2])
    have hfy : f (d.χ y) = f p + morseNorm n y ^ 2 / 2 := by
      rw [d.hnorm y (hy.le.trans (D.hrm p hp).2), morseNormalForm_index_zero _ hk]
    rw [← hyγ, hfy] at hfγ
    change morseNorm n y ≤ ρ
    rw [hρ]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hρrm : ρ < D.rm p hp := by
    rw [hρ, Real.sqrt_lt' hrm0]
    exact hfz
  have hK' : IsCompact (d.χ '' {y | morseNorm n y ≤ ρ}) :=
    d.isCompact_image_le (hρrm.trans (D.rm_lt_R' p hp))
  have hlim : γ s₀ ∈ d.χ '' {y | morseNorm n y ≤ ρ} := by
    refine hK'.isClosed.mem_of_tendsto
      (hγc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio s₀))) ?_
    filter_upwards [Ico_mem_nhdsLT hs₀pos] with u hu using hin u hu
  exact hs₀K (image_mono (fun y hy => lt_of_le_of_lt hy hρrm) hlim)

end GradientLikeStrip

end DifferentialGeometry.Topology
