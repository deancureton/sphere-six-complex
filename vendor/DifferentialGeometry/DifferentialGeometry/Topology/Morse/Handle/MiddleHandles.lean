module

public import DifferentialGeometry.Topology.Morse.Strip.Defs
public import DifferentialGeometry.Topology.Morse.Strip.RegularInterval
public import DifferentialGeometry.Topology.Homology.Relative.PairVanishing
public import DifferentialGeometry.Topology.Morse.Handle.Middle.MiddleStep

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

theorem product_of_middle_indices (I : ModelWithCorners ℝ (Fin n → ℝ) H) [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] (h6 : 6 ≤ n)
    {f : M → ℝ} {a b : ℝ} (hf : MorseStrip I f a b)
    (hidx : ∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x →
      2 ≤ morseIndex I f x ∧ morseIndex I f x + 2 ≤ n)
    (hV₀ : SimplyConnectedSpace (f ⁻¹' {a})) (hV₁ : SimplyConnectedSpace (f ⁻¹' {b}))
    (hH : relHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a}))) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, Φ '' (f ⁻¹' Iic a) = f ⁻¹' Iic b ∧ Φ '' (f ⁻¹' {a}) = f ⁻¹' {b} := by
  have key : ∀ N : ℕ, ∀ f : M → ℝ, Set.ncard {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} = N →
      MorseStrip I f a b →
      (∀ x, f x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x →
        2 ≤ morseIndex I f x ∧ morseIndex I f x + 2 ≤ n) →
      SimplyConnectedSpace (f ⁻¹' {a}) → SimplyConnectedSpace (f ⁻¹' {b}) →
      relHomologyVanishes (f ⁻¹' Icc a b) (Subtype.val ⁻¹' (f ⁻¹' {a})) →
      ∃ Φ : M ≃ₘ⟮I, I⟯ M, Φ '' (f ⁻¹' Iic a) = f ⁻¹' Iic b ∧
        Φ '' (f ⁻¹' {a}) = f ⁻¹' {b} := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro f hN hf hidx hV₀ hV₁ hH
    have hfin : {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x}.Finite :=
      hf.finite_critical.subset fun x hx => ⟨Ioo_subset_Icc_self hx.1, hx.2⟩
    by_cases hemp : {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} = ∅
    · apply regular_interval I f hf.smooth hf.lt.le hf.compact
      intro x hx hcrit
      rcases eq_or_ne (f x) a with ha | ha
      · exact hf.regular x (Or.inl ha) hcrit
      rcases eq_or_ne (f x) b with hb | hb
      · exact hf.regular x (Or.inr hb) hcrit
      have hxo : f x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm ha), lt_of_le_of_ne hx.2 hb⟩
      have hmem : x ∈ {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} := ⟨hxo, hcrit⟩
      rw [hemp] at hmem
      exact hmem
    · obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hemp
      obtain ⟨g, hmod, hg, hcrit, p, hpf, hpc, hpg⟩ :=
        exists_middle_cancel_step I h6 hf hidx hV₀ hV₁ hH hp₀
      have hsub : {x | g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x} ⊆
          {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} := by
        intro x hx
        have hx1 : x ∈ g ⁻¹' Ioo a b := hx.1
        rw [hmod.preimage_Ioo] at hx1
        exact ⟨hx1, (hcrit x hx.1 hx.2).1⟩
      have hssub : {x | g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x} ⊂
          {x | f x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x} :=
        ⟨hsub, fun h => hpg (h ⟨hpf, hpc⟩).2⟩
      have hlt : Set.ncard {x | g x ∈ Ioo a b ∧ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x} < N := by
        rw [← hN]
        exact Set.ncard_lt_ncard hssub hfin
      have hidx' : ∀ x, g x ∈ Ioo a b → DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x →
          2 ≤ morseIndex I g x ∧ morseIndex I g x + 2 ≤ n := by
        intro x hx hc
        obtain ⟨hcf, heq⟩ := hcrit x hx hc
        rw [heq]
        have hx1 : x ∈ g ⁻¹' Ioo a b := hx
        rw [hmod.preimage_Ioo] at hx1
        exact hidx x hx1 hcf
      have hV₀' : SimplyConnectedSpace (g ⁻¹' {a}) := by
        rw [hmod.preimage_singleton_left]
        exact hV₀
      have hV₁' : SimplyConnectedSpace (g ⁻¹' {b}) := by
        rw [hmod.preimage_singleton_right]
        exact hV₁
      have hH' : relHomologyVanishes (g ⁻¹' Icc a b) (Subtype.val ⁻¹' (g ⁻¹' {a})) := by
        rw [hmod.preimage_singleton_left, hmod.preimage_Icc]
        exact hH
      obtain ⟨Φ, hΦ₁, hΦ₂⟩ := ih _ hlt g rfl hg hidx' hV₀' hV₁' hH'
      refine ⟨Φ, ?_, ?_⟩
      · rwa [hmod.preimage_Iic_left, hmod.preimage_Iic_right] at hΦ₁
      · rwa [hmod.preimage_singleton_left, hmod.preimage_singleton_right] at hΦ₂
  exact key _ f rfl hf hidx hV₀ hV₁ hH

end DifferentialGeometry.Topology
