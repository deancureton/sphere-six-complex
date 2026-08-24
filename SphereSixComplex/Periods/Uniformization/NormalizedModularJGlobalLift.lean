module

public import SphereSixComplex.Periods.Uniformization.LocalModularJSolutions
import all SphereSixComplex.Periods.Uniformization.LocalModularJSolutions

@[expose] public section

/-!
# Global normalized modular-J lift

The pointwise local solutions and punctured regular comparison theorem combine with Tau Ceti's
relation-preserving monodromy theorem on the simply connected upper half-plane.  This file
packages the resulting global holomorphic lift, before identifying its two explicit deck
transformations.
-/

noncomputable section

namespace SphereSixComplex.Periods.NormalizedModularJGlobalLift

open Complex Filter Set Topology UpperHalfPlane
open scoped Manifold
open TauCeti
open SphereSixComplex.TriangleGroup
open LocalModularJSolutions
open PuncturedRegularComparison

/-- A chosen local solution at any source point analytically continues to a global solution of
the normalized modular-coordinate equation on the upper half-plane. -/
theorem exists_global_lift_extending_local
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate)
    (z₀ : UpperHalfPlane) (f₀ : ℂ → ℂ)
    (hf₀ : AnalyticAt ℂ f₀ (z₀ : ℂ))
    (hP₀ : IsUpperHalfPlaneSolutionGerm normalizedModularJCoordinate
      (C.coordinate ∘ UpperHalfPlane.ofComplex) (z₀ : ℂ) f₀) :
    ∃ τ : UpperHalfPlane → UpperHalfPlane,
      MDiff τ ∧
        (∀ z, normalizedModularJCoordinate (τ z) = C.coordinate z) ∧
        (fun w : ℂ ↦ (τ (UpperHalfPlane.ofComplex w) : ℂ)) =ᶠ[nhds (z₀ : ℂ)] f₀ := by
  have H := continuesInsideWith_of_exactSource_of_local_solutions J C z₀.im_pos hf₀ hP₀
    (exists_localSolution J C)
  exact H.exists_mdifferentiable_upperHalfPlane_lift

/-- Every pair of exact source and target quotient coordinates admits a global holomorphic lift
through the normalized modular coordinate. -/
theorem exists_global_lift
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) :
    ∃ τ : UpperHalfPlane → UpperHalfPlane,
      MDiff τ ∧ ∀ z, normalizedModularJCoordinate (τ z) = C.coordinate z := by
  obtain ⟨f₀, hf₀, hP₀⟩ :=
    exists_localSolution J C (fuchsianOneFixedPoint : ℂ) fuchsianOneFixedPoint.im_pos
  obtain ⟨τ, hτ, hEq, -⟩ :=
    exists_global_lift_extending_local J C fuchsianOneFixedPoint f₀ hf₀ hP₀
  exact ⟨τ, hτ, hEq⟩

/-- The same lift satisfies the unscaled modular-J equation used by
`NormalizedFuchsianModularJLift`. -/
theorem exists_global_normalizedJ_lift
    (J : ExactNormalizedModularJUniformization)
    (C : ExactFuchsianOrbifoldCoordinate) :
    ∃ τ : UpperHalfPlane → UpperHalfPlane,
      MDiff τ ∧ ∀ z, normalizedJ (τ z) = 1728 * C.coordinate z := by
  obtain ⟨τ, hτ, hEq⟩ := exists_global_lift J C
  refine ⟨τ, hτ, fun z ↦ ?_⟩
  have h := hEq z
  rw [normalizedModularJCoordinate] at h
  linear_combination 1728 * h


end SphereSixComplex.Periods.NormalizedModularJGlobalLift
