# Classical trust-boundary review

The retained boundary consists of smooth six-sphere recognition, together with Lean's
`propext`, `Classical.choice`, and `Quot.sound`. The classical-source review was made on
2026-09-09. Cellular comparison, collaring, Poincaré duality and the required UCT cases now have
checked proofs. An explicit geometric retraction replaces relative triangulation and
relative Whitehead, as described below. This document records the remaining assumptions and their
source correspondence; it does not formally prove those assumptions.

Repository-relative links point to the exact Lean contracts and supporting definitions.

## Declarations and source correspondence

All names have prefix `SphereSixComplex.` unless another namespace is shown.

| Declaration and source | Exact-contract checks | Classical reference |
| --- | --- | --- |
| `SmoothSixSphere.poincare`, [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean) | [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean), requires a compact smooth real six-manifold homotopy equivalent to the standard six-sphere. [SmoothRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/SmoothRecognition.lean), requests an actual diffeomorphism for the specified smooth atlas. | [Kervaire–Milnor, Groups of homotopy spheres I](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/kervmiln.pdf), computation of the group of homotopy six-spheres, together with smooth h-cobordism. This is dimension-six smooth classification, not an arbitrary-dimensional smooth Poincare assertion. |

## Proved cellular comparison

[Homology.lean](SphereSixComplex/Prerequisites/Topology/CWComplex/Homology.lean)
now constructs the cellular chain model from Tau Ceti's
`cellularSingularHomologyIso`. It proves the cell basis using coproducts of abelian
groups and identifies homology with the project's actual singular chains.
The theorem requires a Hausdorff finite-dimensional CW complex. Every consumer
supplies this hypothesis through an existing finite CW model, including the sphere
model. The constructed manifold’s homology bounds are now proved geometrically. The former, broader cellular comparison
axiom and its unused interfaces have been deleted.

The constructor and its sphere and finite-model consumers were checked with
`#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Proved collaring

[Existence.lean](SphereSixComplex/Prerequisites/Topology/Collar/Existence.lean)
now proves collar existence for compact locally collared subsets of Hausdorff
spaces using Tau Ceti's compact Brown theorem. Local collars explicitly meet the
whole boundary only on their zero slices.

[CompactCore.lean](SphereSixComplex/Toric/Positive/CompactCore.lean) proves that
the quotient core is compact by expressing it as the continuous image of six
squares. This gives an actual quotient collar. The upstairs contractibility proof
lifts the resulting deformation through the existing covering map; it no longer
assumes a collar for the noncompact upstairs boundary. The compact Brown adapter,
core compactness, quotient collar and upstairs contractibility each have only
Lean's three standard axioms.

## Proved Poincaré duality

[PoincareDuality.lean](SphereSixComplex/Prerequisites/Topology/Manifold/PoincareDuality.lean)
proves `H^k(X; ℤ) ≃+ H_m(X; ℤ)` for compact simply connected real C¹ manifolds with
`k + m = finrank ℝ E`. It combines the proved compact-support comparison and cap-product
duality theorem from DifferentialGeometry with
[ModuleComparison.lean](SphereSixComplex/Prerequisites/Topology/SingularHomology/ModuleComparison.lean),
which identifies the actual chain and cochain complexes across coefficient categories.
The resulting theorem has only Lean's three standard axioms.

Every consumer supplies simple connectedness from the independent fundamental-group proof.
[Assembly.lean](SphereSixComplex/Homology/Assembly.lean) establishes it before invoking the
homology-sphere argument. The redundant orientation adapter was removed; manifold homology
is now indexed directly by the real dimension of the model space. Final theorem statements
are unchanged.

The [selected dependency](vendor/DifferentialGeometry/README.md) preserves the pinned source,
licenses and original hashes. Its module-system port has an exact recorded patch. Dependency
proofs are checked by Lean and are not additional permitted axioms.

## Proved universal-coefficient comparisons

[UniversalCoefficients.lean](SphereSixComplex/Prerequisites/Algebra/Homology/UniversalCoefficients.lean)
proves that the Kronecker map is an equivalence for a complex of projective objects
whose lower homology objects are projective, with arbitrary coefficients in a linear
abelian category. The proof splits the successive cycle and boundary sequences.

The [singular adapter](SphereSixComplex/Prerequisites/Topology/SingularHomology/UniversalCoefficients.lean)
uses the actual singular-simplex basis and the explicit chain/cochain comparisons to
identify integral cohomology with the dual of integral homology when all lower groups
are free. Degree zero has no freeness hypothesis. The manifold argument uses only
degrees zero through three, with `H₀ ≃ ℤ`, `H₁ = 0` and `H₂ = 0` supplied independently.
The broader assumed splitting involving `Ext` is no longer used and has been deleted.
The new algebraic theorem and singular adapter use only Lean's three standard axioms.

## Explicit positive quotient retraction

[CompactSublevels.lean](SphereSixComplex/Toric/Positive/CompactSublevels.lean) proves
compactness of positive height sublevels using the continuous modulus projection
from the actual cusp filling. Consequently every neighborhood of the compact boundary
contains a sufficiently small height band.

[HeightRetraction.lean](SphereSixComplex/Toric/Positive/HeightRetraction.lean) first
pushes the space a small positive distance into its interior using the collar.
The interior's torus-times-interval coordinates then compress height to a fixed small
positive value. Boundary trajectories stay within the small height band throughout,
and the endpoint lies in the collar. Projection along the collar yields a homotopy
inverse of the boundary inclusion.

[Cofibration.lean](SphereSixComplex/Prerequisites/Topology/Collar/Cofibration.lean)
proves homotopy extension for compact collared subsets of Hausdorff spaces using an
explicit cylinder retraction. Combined with Tau Ceti's deformation-retract theorem,
this gives [the actual strong deformation retraction](SphereSixComplex/Toric/Positive/QuotientRetraction.lean).
It lifts equivariantly through the existing quotient covering and supplies phase spreading.

This bypasses both `CWPair.whitehead` and `ManifoldWithCorners.relativeCWComplex`;
it does not formalize those general theorems. Their axiom declarations and the unused
quadrant/CW proof route have been deleted. All new geometric ingredients use only
the three standard Lean axioms.

## Geometric homology finiteness and dimension bound

[Homology/Euler/Finiteness.lean](SphereSixComplex/Homology/Euler/Finiteness.lean)
proves finite generation and vanishing above degree six from the actual four-piece
open cover. Each collar is a mapping torus of a four-torus and has zero sixth
homology. The Mayer–Vietoris sequence then gives zero seventh homology at every
attachment; its existing finiteness theorem supplies the remaining degrees.

The Poincare/UCT package now records only proved duality pairings. The paper's
homology calculation supplies finiteness and dimensional vanishing from this cover,
so it no longer invokes smooth triangulation. The finite-CW axiom remains only in
sphere recognition, where it supplies CW homotopy type.

## Scope and limits

The classical-source review above is retained from the September review. The
correspondences use the standard classical results and inspection of the Lean
contracts. This is not a formal proof of the remaining assumptions.

Smooth Poincare's manifold hypotheses and diffeomorphism conclusion are expanded directly. See
[ChallengeAxioms.lean](ChallengeAxioms.lean) for Lean-generated exact signatures.

## Verified dependency boundary

The final theorem's compiled dependency closure contains Lean's three standard
axioms and `SmoothSixSphere.poincare`. The construction closure
contains only the three standard Lean axioms. The exact
allowlists are checked independently against those closures and Comparator's
configuration. No construction-specific axiom remains.

The weaker endpoint `mathoverflow_1973` asks only for a complex atlas compatible with the
standard topology. Its proof transports the constructed atlas along the sphere homeomorphism
and uses only the three standard Lean axioms. The stronger endpoint also requires compatibility
with the standard smooth structure and retains `SmoothSixSphere.poincare`.
The audit checks the weaker endpoint separately to prevent reintroducing that dependency.

The full project build, exact axiom audit and Comparator pass on this boundary.
Comparator accepts the exported solution with Lean's default kernel. The local
macOS run uses fake-landrun, so Linux sandbox isolation was not tested here.

## Homology-sphere recognition by h-cobordism

[HomologyRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/HomologyRecognition.lean)
proves that a compact simply connected smooth manifold of dimension at least six with
integral homology vanishing outside degrees zero and its dimension is homeomorphic to
the standard sphere. A global fundamental class generates local top homology, so the
punctured manifold is acyclic. Removing two chart disks gives the simply connected,
relatively acyclic cobordism used by the imported h-cobordism proof. The twisted-sphere
assembly then gives a homeomorphism.

This bypasses the former higher Hurewicz, homological Whitehead and finite CW model
assumptions; it does not prove those general theorems. Their declarations and unused
recognition route are deleted. The selected DifferentialGeometry dependency supplies
checked h-cobordism and twisted-sphere proofs, with original hashes and the exact port
patch recorded under `vendor/DifferentialGeometry`.

The final smooth classification assumption is still necessary for the current proof:
Alexander's radial extension is continuous, but need not be smooth at the center.
The available homeomorphism does not establish a diffeomorphism for the given atlas.
