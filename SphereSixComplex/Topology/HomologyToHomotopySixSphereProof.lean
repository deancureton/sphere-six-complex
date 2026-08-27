module

public import SphereSixComplex.Topology.EstablishedSphereHomology
public import SphereSixComplex.Topology.HurewiczWhiteheadStages
public import SphereSixComplex.Topology.SmoothRecognition

/-!
# The Hurewicz--Whitehead recognition step, reduced to its classical inputs

This file works towards discharging `establishedHomologyToHomotopySixSphere`, the assertion that a
simply connected smooth integral homology six-sphere is homotopy equivalent to `S⁶`.

The classical proof has exactly three ingredients beyond the sphere homology calculation, which is
already available here as `establishedSixSpherePositiveHomologyInputs`:

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

/-- A simply connected smooth integral homology six-sphere is path connected. -/
public theorem SmoothSimplyConnectedIntegralHomologySixSphere.pathConnectedSpace
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothSimplyConnectedIntegralHomologySixSphere X) : PathConnectedSpace X := by
  let _ : SimplyConnectedSpace X := h.simplyConnected
  infer_instance

/-- The top integral homology of a smooth integral homology six-sphere is infinite cyclic. This is
the group in which the Hurewicz theorem is asked to find a spherical generator. -/
public theorem SmoothIntegralHomologySixSphere.integralHomologyDegreeSix
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothIntegralHomologySixSphere X) :
    Nonempty (IntegralSingularHomology 6 X ≃+ ℤ) := by
  obtain ⟨e⟩ := h.integralHomology 6
  obtain ⟨g⟩ := establishedSixSpherePositiveHomologyInputs.degreeSix
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
    establishedSixSpherePositiveHomologyInputs.otherDegrees n hn₀ hn₆
  exact ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩

/-! ## The two classical inputs that remain unproved -/

/-- The Hurewicz input, in the exact form consumed by the recognition argument: from a simply
connected smooth integral homology six-sphere, a map `S⁶ → X` which is an isomorphism on `H₆`.

Classically this is the Hurewicz theorem applied in degree six to a space which is simply
connected with `Hₙ = 0` for `1 ≤ n ≤ 5` (see
`SmoothIntegralHomologySixSphere.integralHomologyVanishing`): the Hurewicz homomorphism
`π₆ X → H₆ X` is then an isomorphism, and a preimage of a generator of `H₆ X ≃+ ℤ` is the required
map. Mathlib has no Hurewicz homomorphism. -/
public def SixSphereHurewiczGeneratorInput (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop :=
  SmoothSimplyConnectedIntegralHomologySixSphere X → HasTopDimensionalSphericalGenerator X

/-- The CW-type input: a compact smooth six-manifold has the homotopy type of a classical CW
complex. Classically this follows from the existence of a Morse function together with handle
attachment, or from smooth triangulability. Neither is available here: `TauCeti`'s Morse theory
(`TauCeti.Analysis.Calculus.Morse`) stops at nondegenerate critical points and gradient flow. -/
public def SmoothSixManifoldClassicalCWTypeInput (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop :=
  SmoothSimplyConnectedIntegralHomologySixSphere X → HasClassicalCWType X

/-! ## The reduction -/

/-- **The reduction.** The Hurewicz input, the CW-type input and the homological Whitehead theorem
for spaces of classical CW type together give the recognition obligation
`HomologyToHomotopySixSphereObligation X`, that is, the content of
`establishedHomologyToHomotopySixSphere`.

The sphere homology calculation that the intermediate detection step needs is supplied by the
proved `establishedSixSpherePositiveHomologyInputs`, and path connectedness by
`SmoothSimplyConnectedIntegralHomologySixSphere.pathConnectedSpace`, so no further input is
hidden in the statement. -/
public theorem homologyToHomotopySixSphere_of_hurewicz_of_cwType_of_whitehead
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (hHurewicz : SixSphereHurewiczGeneratorInput X)
    (hCWType : SmoothSixManifoldClassicalCWTypeInput X)
    (hWhitehead : ClassicalCWIntegralHomologyWhiteheadProperty SixSphere X) :
    HomologyToHomotopySixSphereObligation X := by
  intro hX
  let _ : PathConnectedSpace X := hX.pathConnectedSpace
  exact homotopyEquivSixSphere_of_sphericalGenerator_of_classicalCWWhitehead
    establishedSixSpherePositiveHomologyInputs hX.integralHomology (hHurewicz hX) (hCWType hX)
    hWhitehead

/-! ## The Hurewicz and CW inputs are necessary -/

/-- A space homotopy equivalent to `S⁶` carries a top-dimensional spherical generator. -/
public theorem hasTopDimensionalSphericalGenerator_of_homotopyEquivSixSphere
    {X : Type} [TopologicalSpace X] (e : X ≃ₕ SixSphere) :
    HasTopDimensionalSphericalGenerator X :=
  sixSphere_hasTopDimensionalSphericalGenerator.postcompHomotopyEquiv e.symm

/-- A space homotopy equivalent to `S⁶` has classical CW type, via the explicit finite two-cell
model of the standard sphere. -/
public theorem hasClassicalCWType_of_homotopyEquivSixSphere
    {X : Type} [TopologicalSpace X] (e : X ≃ₕ SixSphere) : HasClassicalCWType X :=
  hasClassicalCWType_precomp_homotopyEquiv e sixSphere_hasClassicalCWType

/-- The Hurewicz input is implied by the recognition obligation, hence is genuinely necessary: no
proof of `HomologyToHomotopySixSphereObligation X` can avoid producing a map `S⁶ → X` which is an
isomorphism on `H₆`. -/
public theorem sixSphereHurewiczGeneratorInput_of_obligation
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : HomologyToHomotopySixSphereObligation X) : SixSphereHurewiczGeneratorInput X := by
  intro hX
  obtain ⟨e⟩ := h hX
  exact hasTopDimensionalSphericalGenerator_of_homotopyEquivSixSphere e

/-- The CW-type input is likewise implied by the recognition obligation. -/
public theorem smoothSixManifoldClassicalCWTypeInput_of_obligation
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : HomologyToHomotopySixSphereObligation X) :
    SmoothSixManifoldClassicalCWTypeInput X := by
  intro hX
  obtain ⟨e⟩ := h hX
  exact hasClassicalCWType_of_homotopyEquivSixSphere e

/-! ## Base case and transport -/

/-- The recognition obligation holds for the standard six-sphere. -/
public theorem sixSphere_homologyToHomotopySixSphereObligation :
    HomologyToHomotopySixSphereObligation SixSphere :=
  fun _ ↦ ⟨ContinuousMap.HomotopyEquiv.refl SixSphere⟩

/-- The recognition obligation transports backwards along a diffeomorphism: if it holds for `Y`
and `X` is diffeomorphic to `Y`, it holds for `X`. -/
public theorem homologyToHomotopySixSphereObligation_of_diffeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace RealModel X] [ChartedSpace RealModel Y]
    (hY : IsManifold 𝓘(ℝ, RealModel) ∞ Y)
    (d : Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X Y ∞)
    (h : HomologyToHomotopySixSphereObligation Y) :
    HomologyToHomotopySixSphereObligation X := by
  intro hX
  obtain ⟨e⟩ := h (hX.diffeomorph hY d)
  exact ⟨d.toHomeomorph.toHomotopyEquiv.trans e⟩

end SphereSixComplex
