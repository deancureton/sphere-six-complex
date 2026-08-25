module

public import SphereSixComplex.Topology.IntegralPoincareUCT
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Truncated integral-homology Euler characteristics

This file packages the finite-generation and dimension hypotheses used by the integral-homology
Euler characteristics through degrees six and seven.  The definitions are independent of the
paper-specific Section 7 geometry and of Mayer--Vietoris exactness.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

/-- Finiteness and dimension support sufficient for the six-dimensional integral-homology Euler
characteristic. -/
public structure IntegralHomologyFiniteSix
    (X : Type) [TopologicalSpace X] : Prop where
  /-- Every integral homology group is finitely generated. -/
  finiteHomology : ∀ k, Module.Finite ℤ (IntegralSingularHomology k X)
  /-- Homology vanishes above degree six. -/
  homologyAboveDimension : ∀ k, 6 < k → Subsingleton (IntegralSingularHomology k X)

namespace IntegralHomologyFiniteSix

/-- Homological finiteness and the dimension bound transport through a homeomorphism. -/
public theorem homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IntegralHomologyFiniteSix X) (e : X ≃ₜ Y) : IntegralHomologyFiniteSix Y where
  finiteHomology k := by
    let _ : Module.Finite ℤ (IntegralSingularHomology k X) := hX.finiteHomology k
    exact Module.Finite.equiv (integralSingularHomologyEquiv k e).toIntLinearEquiv
  homologyAboveDimension k hk := by
    let h := hX.homologyAboveDimension k hk
    let eH := integralSingularHomologyEquiv k e
    exact ⟨fun x y ↦ eH.symm.injective (@Subsingleton.elim _ h _ _)⟩

end IntegralHomologyFiniteSix

/-- Finiteness and dimension support through degree seven. -/
public structure IntegralHomologyFiniteSeven
    (X : Type) [TopologicalSpace X] : Prop where
  /-- Every integral homology group is finitely generated. -/
  finiteHomology : ∀ k, Module.Finite ℤ (IntegralSingularHomology k X)
  /-- Homology vanishes above degree seven. -/
  homologyAboveDimension : ∀ k, 7 < k → Subsingleton (IntegralSingularHomology k X)

namespace IntegralHomologyFiniteSeven

/-- A six-dimensional finiteness package is also a seven-dimensional one. -/
public theorem ofFiniteSix {X : Type} [TopologicalSpace X]
    (hX : IntegralHomologyFiniteSix X) : IntegralHomologyFiniteSeven X where
  finiteHomology := hX.finiteHomology
  homologyAboveDimension k hk := hX.homologyAboveDimension k (by omega)

/-- Seven-dimensional homological finiteness transports through a homeomorphism. -/
public theorem homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IntegralHomologyFiniteSeven X) (e : X ≃ₜ Y) : IntegralHomologyFiniteSeven Y where
  finiteHomology k := by
    let _ : Module.Finite ℤ (IntegralSingularHomology k X) := hX.finiteHomology k
    exact Module.Finite.equiv (integralSingularHomologyEquiv k e).toIntLinearEquiv
  homologyAboveDimension k hk := by
    let h := hX.homologyAboveDimension k hk
    let eH := integralSingularHomologyEquiv k e
    exact ⟨fun x y ↦ eH.symm.injective (@Subsingleton.elim _ h _ _)⟩

end IntegralHomologyFiniteSeven

/-- The degree-seven truncated integral-homology Euler characteristic. -/
public noncomputable def integralHomologyEulerCharacteristicSeven
    (X : Type) [TopologicalSpace X] : ℤ :=
  integralHomologyEulerCharacteristicSix X -
    Module.finrank ℤ (IntegralSingularHomology 7 X)

/-- The six-dimensional integral-homology Euler characteristic is invariant under homeomorphism. -/
public theorem integralHomologyEulerCharacteristicSix_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    integralHomologyEulerCharacteristicSix X =
      integralHomologyEulerCharacteristicSix Y := by
  unfold integralHomologyEulerCharacteristicSix
  rw [(integralSingularHomologyEquiv 0 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 1 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 2 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 3 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 4 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 5 e).toIntLinearEquiv.finrank_eq,
    (integralSingularHomologyEquiv 6 e).toIntLinearEquiv.finrank_eq]

/-- The degree-seven truncated Euler characteristic is invariant under homeomorphism. -/
public theorem integralHomologyEulerCharacteristicSeven_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    integralHomologyEulerCharacteristicSeven X =
      integralHomologyEulerCharacteristicSeven Y := by
  unfold integralHomologyEulerCharacteristicSeven
  rw [integralHomologyEulerCharacteristicSix_homeomorph e,
    (integralSingularHomologyEquiv 7 e).toIntLinearEquiv.finrank_eq]

/-- Vanishing in degree seven identifies the two truncated Euler characteristics. -/
public theorem integralHomologyEulerCharacteristicSeven_eq_six_of_finiteSix
    {X : Type} [TopologicalSpace X] (hX : IntegralHomologyFiniteSix X) :
    integralHomologyEulerCharacteristicSeven X =
      integralHomologyEulerCharacteristicSix X := by
  let _ := hX.homologyAboveDimension 7 (by omega)
  unfold integralHomologyEulerCharacteristicSeven
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, sub_zero]

end SphereSixComplex
