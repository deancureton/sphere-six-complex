module

public import DifferentialGeometry.Topology.Morse.Strip.Existence
public import DifferentialGeometry.Topology.Morse.Rearrangement.SelfIndexing
public import DifferentialGeometry.Topology.Morse.Handle.LowHandles
public import DifferentialGeometry.Topology.Morse.Handle.MiddleHandles

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem hcobordism_strip (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h6 : 6 ≤ n)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : relHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a}))) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, Φ '' (f ⁻¹' Iic a) = f ⁻¹' Iic b ∧ Φ '' (f ⁻¹' {a}) = f ⁻¹' {b} := by
  obtain ⟨g₁, hg₁, hM₁⟩ := exists_morseStrip I f hf hab hcompact hreg
  obtain ⟨g₂, hg₂, hM₂, hsi₂, -, -⟩ := exists_selfIndexing I hM₁
  have hf₂ : ModifiedWithin f a b g₂ := hg₁.trans hg₂
  have hconn₂ : ConnectedSpace (g₂ ⁻¹' Icc a b) := by
    rw [hf₂.preimage_Icc]
    infer_instance
  have ha₂ : (g₂ ⁻¹' {a}).Nonempty := by
    rw [hf₂.preimage_singleton_left]
    exact IsSimplyConnected.nonempty hV₀
  have hb₂ : (g₂ ⁻¹' {b}).Nonempty := by
    rw [hf₂.preimage_singleton_right]
    exact IsSimplyConnected.nonempty hV₁
  obtain ⟨g₃, hg₃, hM₃, hsi₃, hidx₃⟩ := exists_no_extremal_index I hM₂ hsi₂ hconn₂ ha₂ hb₂
  have hf₃ : ModifiedWithin f a b g₃ := hf₂.trans hg₃
  have hW₃ : SimplyConnectedSpace (g₃ ⁻¹' Icc a b) := by
    rw [hf₃.preimage_Icc]
    exact hW
  have hV₀₃ : SimplyConnectedSpace (g₃ ⁻¹' {a}) := by
    rw [hf₃.preimage_singleton_left]
    exact hV₀
  have hV₁₃ : SimplyConnectedSpace (g₃ ⁻¹' {b}) := by
    rw [hf₃.preimage_singleton_right]
    exact hV₁
  obtain ⟨g₄, hg₄, hM₄, -, hidx₄⟩ :=
    exists_index_in_middle I (le_trans (by norm_num) h6) hM₃ hsi₃ hidx₃ hW₃ hV₀₃ hV₁₃
  have hf₄ : ModifiedWithin f a b g₄ := hf₃.trans hg₄
  have hV₀₄ : SimplyConnectedSpace (g₄ ⁻¹' {a}) := by
    rw [hf₄.preimage_singleton_left]
    exact hV₀
  have hV₁₄ : SimplyConnectedSpace (g₄ ⁻¹' {b}) := by
    rw [hf₄.preimage_singleton_right]
    exact hV₁
  have hH₄ : relHomologyVanishes (g₄ ⁻¹' Icc a b) (Subtype.val ⁻¹' (g₄ ⁻¹' {a})) := by
    rw [hf₄.preimage_singleton_left, hf₄.preimage_Icc]
    exact hH
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ :=
    product_of_middle_indices I h6 hM₄ hidx₄ hV₀₄ hV₁₄ hH₄
  refine ⟨Φ, ?_, ?_⟩
  · rwa [hf₄.preimage_Iic_left, hf₄.preimage_Iic_right] at hΦ₁
  · rwa [hf₄.preimage_singleton_left, hf₄.preimage_singleton_right] at hΦ₂

theorem hcobordism_strip_of_homotopyEquivInclusion (I : ModelWithCorners ℝ (Fin n → ℝ) H)
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h6 : 6 ≤ n)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x = a ∨ f x = b → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x)
    (hW : SimplyConnectedSpace (f ⁻¹' Icc a b))
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (he₀ : isHomotopyEquivInclusion (f ⁻¹' {a}) (f ⁻¹' Icc a b)) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, Φ '' (f ⁻¹' Iic a) = f ⁻¹' Iic b ∧ Φ '' (f ⁻¹' {a}) = f ⁻¹' {b} :=
  hcobordism_strip I h6 f hf hab hcompact hreg hW hV₀ hV₁ he₀.relHomologyVanishes

end DifferentialGeometry.Topology
