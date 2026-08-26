module

public import SphereSixComplex.Periods.EstablishedOrbifoldAffineTorsorDescent

/-!
# Established analytic descent for affine-line torsors

This module is the classical several-complex-variables boundary for the two affine quotient
charts.  It is independent of the period formulas and of the six-sphere construction.
-/

namespace SphereSixComplex.Periods

/-- The two homogeneous frames used by the construction are the acyclic line bundles
`O(-1)` and `O` on the projective line. -/
@[expose] public def OrbifoldAffineLineTorsorDescentProblem.HasAcyclicProjectiveLineFrame
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop :=
  (P.frameOrderOne = 2 ∧ P.frameOrderTwo = 1 ∧
      P.frameTransition = fun q ↦ q⁻¹) ∨
    (P.frameOrderOne = 0 ∧ P.frameOrderTwo = 0 ∧
      P.frameTransition = fun _ ↦ 1)

/-- Cartan--B/Cousin descent for a holomorphic affine-line torsor under `O(-1)` or `O` over an
exact orbifold projective line.

The problem structure supplies the exact orbifold quotient, holomorphic affine transport and
finite stabilizer consistency, genuine homogeneous frames at the elliptic points and completed
cusp, and explicit local elliptic and cusp primitives.  The conclusion consists precisely of
holomorphic affine sections over the two Stein quotient charts and holomorphic descent of their
homogeneous overlap mismatch through the quotient coordinate.  Besides Cartan--B, this standard
package includes finite-orbifold descent, finite-jet interpolation at the two branch points, and
the removable-singularity estimate at the completed cusp. 
Reference: Cartan's Theorem B for Stein spaces (vanishing of coherent cohomology), see [GrRe],
together with descent along a finite orbifold quotient and the removable-singularity theorem at
the completed cusp. -/
public axiom establishedOrbifoldAffineLineTorsorAnalyticDescent
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hP : P.HasAcyclicProjectiveLineFrame) :
    Nonempty P.AnalyticDescentData

end SphereSixComplex.Periods
