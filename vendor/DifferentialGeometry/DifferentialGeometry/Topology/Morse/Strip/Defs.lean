module

public import DifferentialGeometry.Topology.Morse.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff ContinuousMap
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def hessianAt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) : QuadraticForm ℝ E :=
  Morse.chartHessianAt (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)

def morseIndex (I : ModelWithCorners ℝ E H) (f : M → ℝ) (p : M) : ℕ :=
  sigNeg (hessianAt I f p)

structure MorseStrip (I : ModelWithCorners ℝ E H) (f : M → ℝ) (a b : ℝ) : Prop where
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f
  lt : a < b
  compact : IsCompact (f ⁻¹' Icc a b)
  regular : ∀ x, f x = a ∨ f x = b → ¬ Morse.IsCriticalPointAt I f x
  nondegenerate : ∀ x, f x ∈ Ioo a b →
    Morse.IsCriticalPointAt I f x → Morse.IsNondegenerateCriticalPointAt I f x

structure ModifiedWithin (f : M → ℝ) (a b : ℝ) (g : M → ℝ) : Prop where
  eqOn : EqOn g f (f ⁻¹' Ioo a b)ᶜ
  mapsTo : MapsTo g (f ⁻¹' Ioo a b) (Ioo a b)

def isSelfIndexing (I : ModelWithCorners ℝ E H) (f : M → ℝ) (a b : ℝ) : Prop :=
  ∀ p q, f p ∈ Ioo a b → f q ∈ Ioo a b →
    Morse.IsCriticalPointAt I f p → Morse.IsCriticalPointAt I f q →
    morseIndex I f p < morseIndex I f q → f p < f q

def isHomotopyEquivInclusion {X : Type*} [TopologicalSpace X] (A B : Set X) : Prop :=
  ∃ e : A ≃ₕ B, ∀ x : A, (e x : X) = x

namespace ModifiedWithin

variable {f g : M → ℝ} {a b : ℝ}

omit [TopologicalSpace M]

theorem refl (f : M → ℝ) (a b : ℝ) : ModifiedWithin f a b f :=
  ⟨fun _ _ => rfl, fun _ hx => hx⟩

theorem preimage_Ioo (h : ModifiedWithin f a b g) : g ⁻¹' Ioo a b = f ⁻¹' Ioo a b := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · exact ⟨fun _ => hx, fun _ => h.mapsTo hx⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_Icc (h : ModifiedWithin f a b g) : g ⁻¹' Icc a b = f ⁻¹' Icc a b := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    exact ⟨fun _ => Ioo_subset_Icc_self hx, fun _ => Ioo_subset_Icc_self hg⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_singleton_left (h : ModifiedWithin f a b g) : g ⁻¹' {a} = f ⁻¹' {a} := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h' => (hg.1.ne' h').elim, fun h' => (hx.1.ne' h').elim⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_singleton_right (h : ModifiedWithin f a b g) : g ⁻¹' {b} = f ⁻¹' {b} := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h' => (hg.2.ne h').elim, fun h' => (hx.2.ne h').elim⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_Iic_left (h : ModifiedWithin f a b g) : g ⁻¹' Iic a = f ⁻¹' Iic a := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    simp only [mem_preimage, mem_Iic]
    exact ⟨fun h' => absurd h' (not_le.mpr hg.1), fun h' => absurd h' (not_le.mpr hx.1)⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem preimage_Iic_right (h : ModifiedWithin f a b g) : g ⁻¹' Iic b = f ⁻¹' Iic b := by
  ext x
  by_cases hx : f x ∈ Ioo a b
  · have hg := h.mapsTo hx
    simp only [mem_preimage, mem_Iic]
    exact ⟨fun _ => hx.2.le, fun _ => hg.2.le⟩
  · simp only [mem_preimage, h.eqOn hx]

theorem trans {k : M → ℝ} (h₁ : ModifiedWithin f a b g) (h₂ : ModifiedWithin g a b k) :
    ModifiedWithin f a b k := by
  refine ⟨fun x hx => ?_, fun x hx => h₂.mapsTo (h₁.mapsTo hx)⟩
  have hx' : x ∈ (g ⁻¹' Ioo a b)ᶜ := by
    rw [h₁.preimage_Ioo]
    exact hx
  exact (h₂.eqOn hx').trans (h₁.eqOn hx)

end ModifiedWithin

theorem isHomotopyEquivInclusion_refl {X : Type*} [TopologicalSpace X] (A : Set X) :
    isHomotopyEquivInclusion A A :=
  ⟨ContinuousMap.HomotopyEquiv.refl A, fun _ => rfl⟩

theorem isHomotopyEquivInclusion.subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : isHomotopyEquivInclusion A B) : A ⊆ B := by
  obtain ⟨e, he⟩ := h
  intro x hx
  have hmem : ((e ⟨x, hx⟩ : B) : X) ∈ B := (e ⟨x, hx⟩).2
  rwa [he ⟨x, hx⟩] at hmem

end

end DifferentialGeometry.Topology
