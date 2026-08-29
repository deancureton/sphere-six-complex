module

public import SphereSixComplex.Periods.OrbifoldAffineTorsorCuspBoundedCousinCorrection

/-!
# Established analytic descent for affine-line torsors

This module is the classical several-complex-variables boundary for the two affine quotient
charts.  It is independent of the period formulas and of the six-sphere construction.

The retained input is now the single classical existence statement
`OrbifoldAffineLineTorsorDescentProblem.HasCuspBoundedEquivariantSection`; the two-chart Cech
package `AnalyticDescentData` is derived from it in
`EstablishedOrbifoldAffineTorsorAnalyticDescentProof`.
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

/-- Cartan--B for a holomorphic affine-line torsor under `O(-1)` or `O` over the compactified
exact `(3, 4, ∞)` orbifold: the torsor has a global holomorphic section.

Precisely, the conclusion asserts a single holomorphic function on the upper half-plane,
equivariant for both finite generators of the deck group, whose discrepancy from the supplied
regular cusp primitive is bounded on the distinguished horodisc.  That is the classical statement
that a holomorphic affine torsor under an acyclic line bundle on a compact Riemann surface
splits; no chart, cover or Cech datum occurs in it.

## Why this is the statement that has to be assumed

* `Delta` is `Monoid.Coprod CyclicThree CyclicFour`, a genuine free product, so the order-three
  and order-four relations recorded in the problem are *all* the relations the affine cocycle
  must satisfy; the multiplier system is a nowhere-zero holomorphic automorphy factor
  (`linearOne_cycle`, `linearTwo_cycle`, `linearOne_ne_zero`, `linearTwo_ne_zero`) and is trivial
  on the parabolic generator (`linearOne_mul_linearTwo_cusp`).  Nothing is missing from the
  hypotheses on the group side.
* For a free product `Delta = A * B` acting on a module `M` over a `ℚ`-vector space, Mayer--
  Vietoris gives `0 → M^Delta → M^A ⊕ M^B → M → H¹(Delta, M) → H¹(A, M) ⊕ H¹(B, M) → 0`, and
  `H¹(A, M) = H¹(B, M) = 0` by averaging over the finite factors.  So for `M` the holomorphic
  functions on the upper half-plane twisted by the multiplier system, the obstruction is exactly
  `M / (M^A + M^B)`, an additive Cousin-I problem on the Stein orbifold chart `ℂ = ℍ/Delta`, and
  the residual cusp normalization is a Mittag-Leffler principal-part extraction.  Both vanish
  because `H¹(ℙ¹, O(-1)) = H¹(ℙ¹, O) = 0`; that is what `HasAcyclicProjectiveLineFrame` records,
  and the conclusion is false without it, since `H¹(ℙ¹, O(-k)) ≠ 0` for `k ≥ 2`.
* The two halves cannot be separated with what is available.  `EstablishedProjectiveLineCohomology`
  proves the two-chart Laurent splitting on `ℙ¹`, so the *gluing* of two chart sections is a
  theorem here; what is missing is the *production* of the affine-chart section, and the cusp
  principal-part extraction needs Laurent's theorem on an annulus, which neither Mathlib nor that
  module supplies (its Laurent development is for `ℂ ∖ {0}`, not for a punctured disc).

Besides Cartan--B, this standard package includes finite-orbifold descent, finite-jet
interpolation at the two branch points, and the removable-singularity estimate at the completed
cusp. -/
public axiom establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hP : P.HasAcyclicProjectiveLineFrame) :
    Nonempty P.CuspBoundedEllipticOneCorrection

public theorem establishedOrbifoldAffineLineTorsorCuspBoundedSection
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hP : P.HasAcyclicProjectiveLineFrame) :
    P.HasCuspBoundedEquivariantSection := by
  obtain ⟨C⟩ := establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection P hP
  exact P.hasCuspBoundedEquivariantSection_of_correction C

/-- Cartan--B/Cousin descent for a holomorphic affine-line torsor under `O(-1)` or `O` over an
exact orbifold projective line.

The problem structure supplies the exact orbifold quotient, holomorphic affine transport and
finite stabilizer consistency, genuine homogeneous frames at the elliptic points and completed
cusp, and explicit local elliptic and cusp primitives.  The conclusion consists precisely of
holomorphic affine sections over the two Stein quotient charts and holomorphic descent of their
homogeneous overlap mismatch through the quotient coordinate.  This is now a theorem: one global
equivariant section serves on both charts, so the overlap mismatch vanishes and descends with the
zero coefficient. -/
public theorem establishedOrbifoldAffineLineTorsorAnalyticDescent
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hP : P.HasAcyclicProjectiveLineFrame) :
    Nonempty P.AnalyticDescentData :=
  nonempty_analyticDescentData_of_hasCuspBoundedEquivariantSection P
    (establishedOrbifoldAffineLineTorsorCuspBoundedSection P hP)

end SphereSixComplex.Periods
