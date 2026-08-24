module

public import SphereSixComplex.Geometry.CuspPeriodExpansion
import all SphereSixComplex.Periods.FuchsianUniformizationBridge

/-!
# Normalizing the Fuchsian cusp coordinate

This file isolates the general parabolic-cusp inverse theorem needed to turn the assembled
Fuchsian modular parameter into the normalized coordinate used by the cusp expansion. The exact
source and target cusp records identify the correct cusps, but their present APIs do not provide
the completed cusp map or its nonzero derivative at the added point.
-/

@[expose] public section

noncomputable section

open scoped Manifold

namespace SphereSixComplex.Periods.FuchsianCuspNormalization

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup

/-- The complex half-plane above a real height. -/
public def upperHalfPlaneAbove (height : ℝ) : Set ℂ :=
  {s | height < s.im}

/-- Translation of the upper half-plane to the left by a real width. -/
public noncomputable def upperHalfPlaneRealTranslate
    (width : ℝ) (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(z : ℂ) - width, by simpa using z.im_pos⟩

@[simp]
public theorem coe_upperHalfPlaneRealTranslate (width : ℝ) (z : UpperHalfPlane) :
    ((upperHalfPlaneRealTranslate width z : UpperHalfPlane) : ℂ) = (z : ℂ) - width :=
  rfl

/-- A coherent local inverse at the parabolic cusp of a translation-equivariant holomorphic map.
The inverse can be required to land above any prescribed source height. -/
public structure ParabolicCuspLocalInverse
    (sourceWidth targetWidth sourceHeight : ℝ)
    (tau : UpperHalfPlane → UpperHalfPlane) where
  /-- Height above which the inverse is defined on the target cusp. -/
  targetHeight : ℝ
  /-- A chosen lift of the target cusp coordinate. -/
  lift : ℂ → UpperHalfPlane
  /-- The lift is holomorphic on its target half-plane. -/
  lift_holomorphic : MDiff[upperHalfPlaneAbove targetHeight] lift
  /-- The lift is a right inverse to the parabolic map. -/
  lift_tau : ∀ s ∈ upperHalfPlaneAbove targetHeight,
    ((tau (lift s) : UpperHalfPlane) : ℂ) = s
  /-- The lift lands above the requested source height. -/
  lift_source_height : ∀ s ∈ upperHalfPlaneAbove targetHeight,
    sourceHeight ≤ (lift s).im
  /-- The lift intertwines the two parabolic translations. -/
  lift_shift : ∀ s ∈ upperHalfPlaneAbove targetHeight,
    lift (s - targetWidth) = upperHalfPlaneRealTranslate sourceWidth (lift s)

namespace Established

/-- Classical degree-one parabolic-cusp inverse theorem.

After passing to exponential coordinates, the equivariance makes the target cusp parameter a
holomorphic map of punctured discs. Its bounded extension has a simple zero because one source
translation maps to one target translation. The holomorphic inverse theorem at zero, followed by
a logarithmic lift, gives the stated coherent inverse. This result is independent of modular
forms, period functions, and the six-sphere construction. -/
public axiom parabolicCuspLocalInverse
    (sourceWidth targetWidth sourceHeight : ℝ)
    (sourceWidth_pos : 0 < sourceWidth) (targetWidth_pos : 0 < targetWidth)
    (tau : UpperHalfPlane → UpperHalfPlane) (tau_holomorphic : MDiff tau)
    (tau_translate : ∀ z,
      tau (upperHalfPlaneRealTranslate sourceWidth z) =
        upperHalfPlaneRealTranslate targetWidth (tau z)) :
    Nonempty (ParabolicCuspLocalInverse sourceWidth targetWidth sourceHeight tau)

end Established

/-- Translation by the explicit source cusp width is the Fuchsian parabolic action. -/
public theorem upperHalfPlaneRealTranslate_sourceCuspWidth (z : UpperHalfPlane) :
    upperHalfPlaneRealTranslate sourceCuspWidth z = fuchsianSourceAction g₀ • z := by
  apply UpperHalfPlane.coe_injective
  change (z : ℂ) - sourceCuspWidth =
    (((fuchsianSourceAction g₀) z : UpperHalfPlane) : ℂ)
  rw [sourceCusp_translation]

/-- The established modular parameter intertwines the explicit source translation with the
unit target translation. -/
public theorem establishedModularParameter_tau_translate
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    E.modularParameter.tau (upperHalfPlaneRealTranslate sourceCuspWidth z) =
      upperHalfPlaneRealTranslate 1 (E.modularParameter.tau z) := by
  apply UpperHalfPlane.coe_injective
  rw [upperHalfPlaneRealTranslate_sourceCuspWidth, coe_upperHalfPlaneRealTranslate]
  have h := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.equivariant g₀ z)
  exact h.trans (rhoTauReal_g₀_smul (E.modularParameter.tau z))

/-- The general parabolic theorem supplies a cusp inverse for the modular parameter retained by
`EstablishedFuchsianModularParameter`. No additional source or target cusp axiom is required. -/
public theorem exists_establishedModularParameter_cuspLocalInverse
    (E : EstablishedFuchsianModularParameter) :
    Nonempty (ParabolicCuspLocalInverse sourceCuspWidth 1 1 E.modularParameter.tau) :=
  Established.parabolicCuspLocalInverse sourceCuspWidth 1 1 sourceCuspWidth_pos zero_lt_one
    E.modularParameter.tau E.modularParameter.tau_holomorphic
      (establishedModularParameter_tau_translate E)

/-- The selected assembled period family has the same exact parabolic translation law, regardless
of how its final nondegeneracy shift was selected. -/
public theorem assembledPeriodFunctions_tau_translate
    (E : EstablishedFuchsianModularParameter) (D : FuchsianPeriodLocalData E)
    (z : UpperHalfPlane) :
    (assembledFuchsianPeriodFunctions E D).tau
        (upperHalfPlaneRealTranslate sourceCuspWidth z) =
      upperHalfPlaneRealTranslate 1 ((assembledFuchsianPeriodFunctions E D).tau z) := by
  let F := assembledFuchsianPeriodFunctions E D
  apply UpperHalfPlane.coe_injective
  rw [upperHalfPlaneRealTranslate_sourceCuspWidth, coe_upperHalfPlaneRealTranslate]
  exact F.tau_transform_cusp z

/-- The general parabolic inverse theorem constructs the normalized cusp coordinate required by
the Fuchsian period expansion. -/
public theorem exists_normalizedFuchsianCuspCoordinate
    (E : EstablishedFuchsianModularParameter) (D : FuchsianPeriodLocalData E) :
    Nonempty (NormalizedFuchsianCuspCoordinate E D) := by
  let F := assembledFuchsianPeriodFunctions E D
  obtain ⟨L⟩ := Established.parabolicCuspLocalInverse sourceCuspWidth 1 1
    sourceCuspWidth_pos zero_lt_one F.tau F.tau_holomorphic
      (assembledPeriodFunctions_tau_translate E D)
  refine ⟨{
    height := L.targetHeight
    lift := L.lift
    lift_holomorphic := ?_
    lift_tau := L.lift_tau
    lift_mem_cusp := ?_
    lift_shift := ?_
  }⟩
  · simpa only [upperHalfPlaneAbove, cuspHalfPlane] using L.lift_holomorphic
  · intro s hs
    exact L.lift_source_height s hs
  · intro s hs
    have h := L.lift_shift s (by
      simpa only [upperHalfPlaneAbove, cuspHalfPlane] using hs)
    change L.lift (s - 1) = fuchsianSourceAction g₀ • L.lift s
    rw [← upperHalfPlaneRealTranslate_sourceCuspWidth]
    simpa using h

end SphereSixComplex.Periods.FuchsianCuspNormalization
