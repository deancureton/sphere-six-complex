module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import DifferentialGeometry.Topology.Morse.Strip.TrajectoryCutoff
public import DifferentialGeometry.Topology.Morse.Rearrangement.MonotoneShift

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open Set Filter

noncomputable section

namespace ModifiedWithin

variable {M : Type*} {f g : M → ℝ}

theorem mono {a' b' a b : ℝ} (h : ModifiedWithin f a' b' g) (ha : a ≤ a') (hb : b' ≤ b) :
    ModifiedWithin f a b g := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · apply h.eqOn
    intro hx'
    exact hx ⟨ha.trans_lt hx'.1, hx'.2.trans_le hb⟩
  · by_cases hx' : f x ∈ Ioo a' b'
    · have := h.mapsTo hx'
      exact ⟨ha.trans_lt this.1, this.2.trans_le hb⟩
    · rw [h.eqOn hx']
      exact hx

end ModifiedWithin

namespace Rearrange

section Pointwise

variable {M : Type*}

def rearranged (f μ : M → ℝ) (ρ : ℝ → ℝ) : M → ℝ := fun x => f x + μ x * (ρ (f x) - f x)

variable {f μ : M → ℝ} {ρ : ℝ → ℝ}

theorem rearranged_apply (x : M) : rearranged f μ ρ x = f x + μ x * (ρ (f x) - f x) := rfl

theorem rearranged_eq_pi : rearranged f μ ρ = f + μ * (ρ ∘ f - f) := rfl

variable {a₃ b₃ : ℝ}

theorem rearranged_eq_of_notMem (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) {x : M}
    (hx : f x ∉ Ioo a₃ b₃) : rearranged f μ ρ x = f x := by
  rw [rearranged_apply, hρid _ hx, sub_self, mul_zero, add_zero]

theorem eqOn_rearranged (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) :
    EqOn (rearranged f μ ρ) f {x | f x ≤ a₃ ∨ b₃ ≤ f x} := by
  intro x hx
  apply rearranged_eq_of_notMem hρid
  intro hx'
  rcases hx with h | h
  · exact absurd hx'.1 (not_lt.2 h)
  · exact absurd hx'.2 (not_lt.2 h)

theorem mem_outer_of_notMem {a' b' : ℝ} (h₃ : a' < a₃ ∧ b₃ < b') {x : M}
    (hx : f x ∉ Ioo a' b') : f x ∈ Iio a₃ ∪ Ioi b₃ := by
  by_contra hcon
  simp only [mem_union, mem_Iio, mem_Ioi, not_or, not_lt] at hcon
  exact hx ⟨h₃.1.trans_le hcon.1, hcon.2.trans_lt h₃.2⟩

theorem modifiedWithin_rearranged {a' b' : ℝ} (hμ01 : ∀ x, μ x ∈ Icc 0 1)
    (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) (h₃ : a' < a₃ ∧ b₃ < b')
    (hρmaps : MapsTo ρ (Ioo a' b') (Ioo a' b')) :
    ModifiedWithin f a' b' (rearranged f μ ρ) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact rearranged_eq_of_notMem hρid fun hx' => hx ⟨h₃.1.trans hx'.1, hx'.2.trans h₃.2⟩
  · have hconv := (convex_Ioo a' b').add_smul_sub_mem hx (hρmaps hx) (hμ01 x)
    simpa [rearranged_apply, smul_eq_mul] using hconv

end Pointwise

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H}

variable {f μ : M → ℝ} {ρ : ℝ → ℝ} {a₃ b₃ : ℝ}

theorem isOpen_outer (hf : Continuous f) (a₃ b₃ : ℝ) :
    IsOpen (f ⁻¹' (Iio a₃ ∪ Ioi b₃)) :=
  (isOpen_Iio.union isOpen_Ioi).preimage hf

theorem rearranged_eventuallyEq_of_mem_outer (hf : Continuous f)
    (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) {x : M} (hx : f x ∈ Iio a₃ ∪ Ioi b₃) :
    rearranged f μ ρ =ᶠ[𝓝 x] f := by
  filter_upwards [(isOpen_outer hf a₃ b₃).mem_nhds hx] with y hy
  apply rearranged_eq_of_notMem hρid
  intro hy'
  rcases hy with h | h
  · exact absurd hy'.1 (not_lt.2 (le_of_lt h))
  · exact absurd hy'.2 (not_lt.2 (le_of_lt h))

theorem rearranged_eventuallyEq_of_notMem (hf : Continuous f)
    (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) {a' b' : ℝ} (h₃ : a' < a₃ ∧ b₃ < b') {x : M}
    (hx : f x ∉ Ioo a' b') : rearranged f μ ρ =ᶠ[𝓝 x] f :=
  rearranged_eventuallyEq_of_mem_outer hf hρid (mem_outer_of_notMem h₃ hx)

theorem contMDiff_rearranged (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a' b' : ℝ}
    (hμ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ μ (f ⁻¹' Ioo a' b')) (hρ : ContDiff ℝ ∞ ρ)
    (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) (h₃ : a' < a₃ ∧ b₃ < b') :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (rearranged f μ ρ) := by
  intro x
  by_cases hx : f x ∈ Ioo a' b'
  · have hμx : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ μ x :=
      hμ.contMDiffAt ((isOpen_Ioo.preimage hf.continuous).mem_nhds hx)
    have hρf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => ρ (f y)) x :=
      ((hρ.contMDiff).comp hf) x
    exact (hf x).add (hμx.mul (hρf.sub (hf x)))
  · exact (hf x).congr_of_eventuallyEq
      (rearranged_eventuallyEq_of_notMem hf.continuous hρid h₃ hx)

theorem mfderiv_rearranged_apply (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hμx : MDifferentiableAt I 𝓘(ℝ, ℝ) μ x) (hρ : ContDiff ℝ ∞ ρ) (v : TangentSpace I x) :
    (NormedSpace.fromTangentSpace (rearranged f μ ρ x))
        ((mfderiv I 𝓘(ℝ, ℝ) (rearranged f μ ρ) x) v) =
      (1 + μ x * (deriv ρ (f x) - 1)) *
          (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) v) +
        (ρ (f x) - f x) * (NormedSpace.fromTangentSpace (μ x)) ((mfderiv I 𝓘(ℝ, ℝ) μ x) v) := by
  have hfx : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := (hf x).mdifferentiableAt (by simp)
  have hρf : MDifferentiableAt I 𝓘(ℝ, ℝ) (ρ ∘ f) x :=
    ((hρ.contMDiff.comp hf) x).mdifferentiableAt (by simp)
  have hρf' : mfderiv I 𝓘(ℝ, ℝ) (ρ ∘ f) x = deriv ρ (f x) • mfderiv I 𝓘(ℝ, ℝ) f x :=
    MonotoneShift.mfderiv_comp_eq_smul hf hρ x
  have h1 := hρf.hasMFDerivAt.sub hfx.hasMFDerivAt
  rw [hρf'] at h1
  have h2 := hμx.hasMFDerivAt.mul h1
  have h3 := hfx.hasMFDerivAt.add h2
  rw [rearranged_eq_pi, h3.mfderiv]
  set A : ℝ := (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) v) with hA
  set B : ℝ := (NormedSpace.fromTangentSpace (μ x)) ((mfderiv I 𝓘(ℝ, ℝ) μ x) v) with hB
  change A + (μ x * (deriv ρ (f x) * A - A) + (ρ (f x) - f x) * B) = _
  ring

theorem mfderiv_rearranged_apply_neg (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hμx : MDifferentiableAt I 𝓘(ℝ, ℝ) μ x) (hρ : ContDiff ℝ ∞ ρ) (hμ01 : μ x ∈ Icc 0 1)
    (hρ' : 0 < deriv ρ (f x)) {v : TangentSpace I x} (hμv : (mfderiv I 𝓘(ℝ, ℝ) μ x) v = 0)
    (hfv : (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) v) < 0) :
    (NormedSpace.fromTangentSpace (rearranged f μ ρ x))
      ((mfderiv I 𝓘(ℝ, ℝ) (rearranged f μ ρ) x) v) < 0 := by
  rw [mfderiv_rearranged_apply hf hμx hρ v, hμv, map_zero, mul_zero, add_zero]
  exact mul_neg_of_pos_of_neg (MonotoneShift.affineComb_deriv_pos hμ01.1 hμ01.2 hρ') hfv

theorem not_isCriticalPointAt_rearranged (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hμx : MDifferentiableAt I 𝓘(ℝ, ℝ) μ x) (hρ : ContDiff ℝ ∞ ρ) (hμ01 : μ x ∈ Icc 0 1)
    (hρ' : 0 < deriv ρ (f x)) {v : TangentSpace I x} (hμv : (mfderiv I 𝓘(ℝ, ℝ) μ x) v = 0)
    (hfv : (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) v) < 0) :
    ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (rearranged f μ ρ) x := by
  intro hcrit
  have h := mfderiv_rearranged_apply_neg hf hμx hρ hμ01 hρ' hμv hfv
  unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt at hcrit
  rw [hcrit] at h
  simp at h

end Rearrange

section Main

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (Fin n → ℝ) H} [I.Boundaryless] [IsManifold I ∞ M]
  {f : M → ℝ} {a b : ℝ}

open Rearrange MonotoneShift

theorem rearrange (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a') (hab' : a' < b')
    (hb : b' ≤ b) (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) {crit : Finset M}
    (D : GradientLikeStrip I f a' b' crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) (μ : M → ℝ)
    (hμ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ μ (f ⁻¹' Ioo a' b')) (hμ01 : ∀ x, μ x ∈ Icc 0 1)
    (hμV : ∀ x ∈ f ⁻¹' Ioo a' b', (mfderiv I 𝓘(ℝ, ℝ) μ x) (D.V x) = 0)
    (hμcrit : ∀ p ∈ crit, ∀ᶠ x in 𝓝 p, μ x = μ p) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρ' : ∀ t, 0 < deriv ρ t) {a₃ b₃ : ℝ} (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t)
    (h₃ : a' < a₃ ∧ b₃ < b') (hρmaps : MapsTo ρ (Ioo a' b') (Ioo a' b')) :
    ModifiedWithin f a' b' (rearranged f μ ρ) ∧ MorseStrip I (rearranged f μ ρ) a' b' ∧
      ModifiedWithin f a b (rearranged f μ ρ) ∧ MorseStrip I (rearranged f μ ρ) a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (rearranged f μ ρ) x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I (rearranged f μ ρ) x = morseIndex I f x) ∧
      (∀ p ∈ crit, rearranged f μ ρ p = f p + μ p * (ρ (f p) - f p)) ∧
      EqOn (rearranged f μ ρ) f {x | f x ≤ a₃ ∨ b₃ ≤ f x} := by
  set g := rearranged f μ ρ with hg
  have hfc : Continuous f := hf.smooth.continuous
  have hmod : ModifiedWithin f a' b' g := modifiedWithin_rearranged hμ01 hρid h₃ hρmaps
  have hmod' : ModifiedWithin f a b g := hmod.mono ha hb
  have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := contMDiff_rearranged hf.smooth hμ hρ hρid h₃
  have hout : ∀ x, f x ∉ Ioo a' b' → g =ᶠ[𝓝 x] f := fun x hx =>
    rearranged_eventuallyEq_of_notMem hfc hρid h₃ hx
  have hnear : ∀ p ∈ crit, g =ᶠ[𝓝 p] fun x => f x + μ p * (ρ (f x) - f x) := by
    intro p hp
    filter_upwards [hμcrit p hp] with x hx
    rw [hg, rearranged_apply, hx]
  have hcritIff : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x
    by_cases hx : f x ∈ Ioo a' b'
    · by_cases hxc : x ∈ crit
      · exact isCriticalPointAt_affineComb_iff hf.smooth hρ
          (affineComb_deriv_pos (hμ01 x).1 (hμ01 x).2 (hρ' (f x))).ne' (hnear x hxc)
      · have hfx : ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := fun h => hxc ((hcrit x).2 ⟨hx, h⟩)
        refine ⟨fun h => absurd h ?_, fun h => absurd h hfx⟩
        have hμx : MDifferentiableAt I 𝓘(ℝ, ℝ) μ x :=
          (hμ.contMDiffAt ((isOpen_Ioo.preimage hfc).mem_nhds hx)).mdifferentiableAt (by simp)
        exact not_isCriticalPointAt_rearranged hf.smooth hμx hρ (hμ01 x) (hρ' (f x)) (hμV x hx)
          (D.neg x (Ioo_subset_Icc_self hx) hxc)
    · exact isCriticalPointAt_congr_nhds (hout x hx)
  have hidx : ∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x →
      (DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I g x ↔ DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f x) ∧
        morseIndex I g x = morseIndex I f x := by
    intro x hxf
    by_cases hx : f x ∈ Ioo a' b'
    · have hxc : x ∈ crit := (hcrit x).2 ⟨hx, hxf⟩
      obtain ⟨_, h2, h3⟩ := morseIndex_affineComb_of_isCriticalPointAt hf.smooth hρ (hμ01 x).1
        (hμ01 x).2 (hρ' (f x)) hxf (hnear x hxc)
      exact ⟨h2, h3⟩
    · exact ⟨isNondegenerateCriticalPointAt_congr_nhds (hout x hx), morseIndex_congr_nhds (hout x hx)⟩
  have hcompact : IsCompact (g ⁻¹' Icc a' b') := by
    rw [hmod.preimage_Icc]
    exact hf.compact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc ha hb))
  have hstrip' : MorseStrip I g a' b' := by
    refine ⟨hsmooth, hab', hcompact, fun x hx => ?_, fun x hx hxc => ?_⟩
    · have hfx : f x = a' ∨ f x = b' := by
        rcases hx with hx | hx
        · left
          have : x ∈ g ⁻¹' {a'} := hx
          rw [hmod.preimage_singleton_left] at this
          exact this
        · right
          have : x ∈ g ⁻¹' {b'} := hx
          rw [hmod.preimage_singleton_right] at this
          exact this
      rw [hcritIff]
      exact hreg x hfx
    · have hfx : f x ∈ Ioo a' b' := by
        have : x ∈ g ⁻¹' Ioo a' b' := hx
        rwa [hmod.preimage_Ioo] at this
      have hxf : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := (hcritIff x).1 hxc
      exact (hidx x hxf).1.2 (hf.nondegenerate x ⟨ha.trans_lt hfx.1, hfx.2.trans_le hb⟩ hxf)
  have hcompact' : IsCompact (g ⁻¹' Icc a b) := by
    rw [hmod'.preimage_Icc]
    exact hf.compact
  have hstrip : MorseStrip I g a b := by
    refine ⟨hsmooth, hf.lt, hcompact', fun x hx => ?_, fun x hx hxc => ?_⟩
    · have hfx : f x = a ∨ f x = b := by
        rcases hx with hx | hx
        · left
          have : x ∈ g ⁻¹' {a} := hx
          rw [hmod'.preimage_singleton_left] at this
          exact this
        · right
          have : x ∈ g ⁻¹' {b} := hx
          rw [hmod'.preimage_singleton_right] at this
          exact this
      rw [hcritIff]
      exact hf.regular x hfx
    · have hfx : f x ∈ Ioo a b := by
        have : x ∈ g ⁻¹' Ioo a b := hx
        rwa [hmod'.preimage_Ioo] at this
      have hxf : DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := (hcritIff x).1 hxc
      exact (hidx x hxf).1.2 (hf.nondegenerate x hfx hxf)
  exact ⟨hmod, hstrip', hmod', hstrip, hcritIff, fun x hx => (hidx x hx).2, fun p _ => rfl,
    eqOn_rearranged hρid⟩

omit [I.Boundaryless] in
theorem GradientLikeStrip.eventually_eq_of_smallBall {crit : Finset M}
    (D : GradientLikeStrip I f a b crit) {μ : M → ℝ} {p : M} (hp : p ∈ crit) {c : ℝ}
    (h : ∀ x ∈ D.smallBall p hp, μ x = c) : ∀ᶠ x in 𝓝 p, μ x = μ p := by
  filter_upwards [(D.isOpen_smallBall p hp).mem_nhds (D.p_mem_smallBall p hp)] with x hx
  rw [h x hx, h p (D.p_mem_smallBall p hp)]

theorem rearrange_of_partition (hf : MorseStrip I f a b) {a' b' : ℝ} (ha : a ≤ a')
    (hab' : a' < b') (hb : b' ≤ b) (hreg : ∀ x, f x = a' ∨ f x = b' → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    {crit : Finset M} (D : GradientLikeStrip I f a' b' crit)
    (hcrit : ∀ x, x ∈ crit ↔ f x ∈ Ioo a' b' ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) (P₀ P₁ : Set M)
    (hP : ∀ p ∈ crit, p ∈ P₀ ∨ p ∈ P₁) (μ : M → ℝ)
    (hμ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ μ (f ⁻¹' Ioo a' b')) (hμ01 : ∀ x, μ x ∈ Icc 0 1)
    (hμV : ∀ x ∈ f ⁻¹' Ioo a' b', (mfderiv I 𝓘(ℝ, ℝ) μ x) (D.V x) = 0)
    (hμ0 : ∀ p hp, p ∈ P₀ → ∀ x ∈ D.smallBall p hp, μ x = 0)
    (hμ1 : ∀ p hp, p ∈ P₁ → ∀ x ∈ D.smallBall p hp, μ x = 1) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρ' : ∀ t, 0 < deriv ρ t) {a₃ b₃ : ℝ}
    (hρid : ∀ t, t ∉ Ioo a₃ b₃ → ρ t = t) (h₃ : a' < a₃ ∧ b₃ < b')
    (hρmaps : MapsTo ρ (Ioo a' b') (Ioo a' b')) :
    ModifiedWithin f a' b' (rearranged f μ ρ) ∧ MorseStrip I (rearranged f μ ρ) a' b' ∧
      ModifiedWithin f a b (rearranged f μ ρ) ∧ MorseStrip I (rearranged f μ ρ) a b ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I (rearranged f μ ρ) x ↔ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x) ∧
      (∀ x, DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x → morseIndex I (rearranged f μ ρ) x = morseIndex I f x) ∧
      (∀ p ∈ crit, p ∈ P₀ → rearranged f μ ρ p = f p) ∧
      (∀ p ∈ crit, p ∈ P₁ → rearranged f μ ρ p = ρ (f p)) ∧
      EqOn (rearranged f μ ρ) f {x | f x ≤ a₃ ∨ b₃ ≤ f x} := by
  have hμcrit : ∀ p ∈ crit, ∀ᶠ x in 𝓝 p, μ x = μ p := by
    intro p hp
    rcases hP p hp with h | h
    · exact D.eventually_eq_of_smallBall hp (hμ0 p hp h)
    · exact D.eventually_eq_of_smallBall hp (hμ1 p hp h)
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := rearrange hf ha hab' hb hreg D hcrit μ hμ hμ01 hμV
    hμcrit ρ hρ hρ' hρid h₃ hρmaps
  refine ⟨h1, h2, h3, h4, h5, h6, fun p hp hp₀ => ?_, fun p hp hp₁ => ?_, h8⟩
  · rw [rearranged_apply, hμ0 p hp hp₀ p (D.p_mem_smallBall p hp), zero_mul, add_zero]
  · rw [rearranged_apply, hμ1 p hp hp₁ p (D.p_mem_smallBall p hp), one_mul, add_sub_cancel]

end Main

end

end DifferentialGeometry.Topology
