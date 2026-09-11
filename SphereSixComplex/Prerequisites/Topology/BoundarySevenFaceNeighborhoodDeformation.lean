module

public import SphereSixComplex.Prerequisites.Topology.BoundarySevenRealizationInjective
public import SphereSixComplex.Prerequisites.Topology.BoundarySevenFaceNeighborhoodComparison

/-!
# Deformation of a boundary-face neighbourhood onto its face

For a fixed barycentric coordinate `i`, the open subset `w i < 1 / 8` of the boundary of the
standard seven-simplex deformation retracts onto the face `w i = 0`.  The retraction sets the
`i`-th coordinate to zero and divides all other coordinates by `1 - w i`.

This file develops the affine formula independently of the total-complex argument.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap Set Simplicial

namespace SphereSixComplex















/-! ## The face inclusion is a homotopy equivalence -/







/-! ## Transport back to the geometric realization -/

/-- The canonical barycentric homeomorphism, now available unconditionally. -/
public noncomputable def boundarySevenRealizationHomeomorphStandardBoundary :
    (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ≃ₜ StandardSimplexBoundary 7 :=
  boundarySevenRealizationHomeomorphStandardBoundary_of_injective
    boundarySevenRealizationToBoundary_injective

@[simp]
public theorem boundarySevenRealizationHomeomorphStandardBoundary_apply_val
    (x : SSet.toTop.obj (∂Δ[7] : SSet.{0})) :
    (boundarySevenRealizationHomeomorphStandardBoundary x :
        stdSimplex ℝ (Fin 8)) = boundarySevenComparisonToStdSimplex x :=
  rfl








end SphereSixComplex
