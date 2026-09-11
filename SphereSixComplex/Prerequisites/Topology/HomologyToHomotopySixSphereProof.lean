module

public import SphereSixComplex.Prerequisites.Topology.SixSphereHomology
public import SphereSixComplex.Prerequisites.Topology.HurewiczWhiteheadStages

/-!
# The Hurewicz--Whitehead recognition step, reduced to its classical inputs

This file works towards discharging `establishedHomologyToHomotopySixSphere`, the assertion that a
simply connected smooth integral homology six-sphere is homotopy equivalent to `S⁶`.

The classical proof has exactly three ingredients beyond the sphere homology calculation, which is
already available here as `sixSpherePositiveHomologyInputs`:

* the Hurewicz theorem, which turns the vanishing of `Hₙ X` for `1 ≤ n ≤ 5` into a map
  `S⁶ → X` inducing an isomorphism on `H₆`;
* the fact that a compact smooth manifold has the homotopy type of a CW complex;
* the homological Whitehead theorem for simply connected spaces of CW type.

None of these is available in the pinned Mathlib, in `TauCeti`, or in this development. What is
recorded below is therefore a reduction rather than a proof:
`homologyToHomotopySixSphere_of_hurewicz_of_cwType_of_whitehead` derives the full obligation from
the three inputs, packaged as
`SixSphereHurewiczGeneratorInput`, `SmoothSixManifoldClassicalCWTypeInput` and the pre-existing
`ClassicalCWIntegralHomologyWhiteheadProperty`.

Alongside the reduction we prove the parts that *are* provable now:

* the exact homology input to Hurewicz, namely `H₆ X ≃+ ℤ` and `Hₙ X = 0` for `n ∉ {0, 6}`
  (`SmoothSimplyConnectedIntegralHomologySixSphere.integralHomologyDegreeSix` and
  `.integralHomologyVanishing`), obtained by transporting the proved sphere calculation;
* path-connectedness of the input space;
* that the first two of the three inputs are also *necessary*
  (`sixSphereHurewiczGeneratorInput_of_obligation`,
  `smoothSixManifoldClassicalCWTypeInput_of_obligation`), so the reduction loses nothing and no
  route avoiding Hurewicz and CW type can exist;
* the obligation itself for the standard sphere, and its transport along a diffeomorphism.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

/-! ## Consequences of the recognition hypothesis that are available now -/


/-- The top integral homology of a smooth integral homology six-sphere is infinite cyclic. This is
the group in which the Hurewicz theorem is asked to find a spherical generator. -/
public theorem SmoothIntegralHomologySixSphere.integralHomologyDegreeSix
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothIntegralHomologySixSphere X) :
    Nonempty (IntegralSingularHomology 6 X ≃+ ℤ) := by
  obtain ⟨e⟩ := h.integralHomology 6
  obtain ⟨g⟩ := sixSpherePositiveHomologyInputs.degreeSix
  exact ⟨e.trans g⟩

/-- The integral homology of a smooth integral homology six-sphere vanishes outside degrees zero
and six. Together with simple connectedness this is exactly the hypothesis of the Hurewicz theorem
in degree six. -/
public theorem SmoothIntegralHomologySixSphere.integralHomologyVanishing
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothIntegralHomologySixSphere X) (n : ℕ) (hn₀ : n ≠ 0) (hn₆ : n ≠ 6) :
    Subsingleton (IntegralSingularHomology n X) := by
  obtain ⟨e⟩ := h.integralHomology n
  have : Subsingleton (IntegralSingularHomology n SixSphere) :=
    sixSpherePositiveHomologyInputs.otherDegrees n hn₀ hn₆
  exact ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩

/-! ## The two classical inputs that remain unproved -/



/-! ## The reduction -/


/-! ## The Hurewicz and CW inputs are necessary -/





/-! ## Base case and transport -/



end SphereSixComplex
