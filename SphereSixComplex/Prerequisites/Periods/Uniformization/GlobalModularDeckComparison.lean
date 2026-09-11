module

public import SphereSixComplex.Prerequisites.Periods.Uniformization.NormalizedModularJGlobalLift
import all SphereSixComplex.Prerequisites.Periods.Uniformization.NormalizedModularJGlobalLift

@[expose] public section

/-!
# Constant deck comparison for global modular lifts

Two global holomorphic solutions of the same exact normalized modular equation differ by one
constant modular deck transformation.  The proof compares them on a small tangent ball of
ordinary values and then uses the identity theorem on the upper half-plane.
-/

noncomputable section

namespace SphereSixComplex.Periods.GlobalModularDeckComparison

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped Manifold
open SphereSixComplex.TriangleGroup
open TauCeti
open SolutionGermDeckTransitivity
open PuncturedRegularComparison

/-- The ambient-complex representative of a holomorphic upper-half-plane map is analytic on the
upper-half-plane open set. -/
theorem coe_comp_ofComplex_analyticOnNhd {τ : UpperHalfPlane → UpperHalfPlane}
    (hτ : MDiff τ) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ (τ (UpperHalfPlane.ofComplex w) : ℂ))
      UpperHalfPlane.upperHalfPlaneSet := by
  intro w hw
  have hcomplex : MDiff (fun z : UpperHalfPlane ↦ (τ z : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp hτ
  exact TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex hcomplex hw



end SphereSixComplex.Periods.GlobalModularDeckComparison
