# Classical trust-boundary review

The retained boundary consists of seven general classical results, together with Lean's
`propext`, `Classical.choice`, and `Quot.sound`. The classical-source review was made on
2026-09-09. Cellular comparison, collaring and Poincaré duality have since been replaced by
checked proofs, described below. This document records the remaining assumptions and their
source correspondence; it does not formally prove those assumptions.

Repository-relative links point to the exact Lean contracts and supporting definitions.

## Declarations and source correspondence

All names have prefix `SphereSixComplex.` unless another namespace is shown.

| Declaration and source | Exact-contract checks | Classical reference |
| --- | --- | --- |
| `Hurewicz.exists_map`, [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean) | [Higher.lean](SphereSixComplex/Prerequisites/Topology/Hurewicz/Higher.lean) uses actual cubical homotopy groups and postcomposition maps, a natural homomorphism, degree at least two, path connectedness, and triviality of every lower positive homotopy group. Existence of a natural isomorphism in the Hurewicz range is weaker than specifying the canonically normalized Hurewicz map. | [Hatcher, Chapter 4, Theorem 4.32](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). |
| `CWType.homological_whitehead`, [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean) | Both spaces are simply connected and have actual CW homotopy models. The same given continuous map induces isomorphisms in every integral singular homology degree, and the conclusion makes that map a homotopy equivalence. | [Hatcher, Chapter 4, Corollary 4.33](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). |
| `SmoothSixSphere.poincare`, [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean) | [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean), requires a compact smooth real six-manifold homotopy equivalent to the standard six-sphere. [SmoothRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/SmoothRecognition.lean), requests an actual diffeomorphism for the specified smooth atlas. | [Kervaire–Milnor, Groups of homotopy spheres I](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/kervmiln.pdf), computation of the group of homotopy six-spheres, together with smooth h-cobordism. This is dimension-six smooth classification, not an arbitrary-dimensional smooth Poincare assertion. |
| `IntegralCohomology.universal_coefficients`, [UniversalCoefficients.lean](SphereSixComplex/Prerequisites/Topology/SingularHomology/UniversalCoefficients.lean) | [Cohomology.lean](SphereSixComplex/Prerequisites/Topology/SingularHomology/Cohomology.lean) defines the actual dual singular-chain complex. The obstruction is derived `Ext¹` in integer modules. Positive-degree splitting is noncanonical; no natural splitting is assumed. | [Hatcher, Chapter 3, Section 3.1, universal coefficient theorem](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf). |
| `SmoothManifold.finiteCWModel`, [Triangulation.lean](SphereSixComplex/Prerequisites/Topology/Manifold/Triangulation.lean) | Compact, Hausdorff, second-countable, finite-dimensional boundaryless C1 manifold. Only a finite CW homotopy model with dimension bounded by the actual real model dimension is requested. | [Whitehead, On C1-complexes](https://www.sciencedirect.com/science/chapter/edited-volume/pii/B978008009870850021X), Annals of Mathematics 41 (1940), 809–824. |
| `CWPair.whitehead`, [StrongDeformationRetraction.lean](SphereSixComplex/Prerequisites/Topology/Homotopy/StrongDeformationRetraction.lean) | Actual relative CW inclusion; path connectedness of both spaces; actual induced bijections on the fundamental group and every higher homotopy group. [SubspaceInclusion.lean](SphereSixComplex/Prerequisites/Topology/Homotopy/SubspaceInclusion.lean), defines the conclusion as an ordinary homotopy equivalence whose inverse map is the inclusion. No covering-space or toric conclusion is assumed. | [Hatcher, Chapter 4, Theorem 4.5 and the relative CW compression argument](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). |
| `ManifoldWithCorners.relativeCWComplex`, [CornersCWComplex.lean](SphereSixComplex/Prerequisites/Topology/Manifold/CornersCWComplex.lean) | Hausdorff, second-countable C1 manifold on a finite-dimensional real quadrant. Only a CW decomposition relative to the full manifold boundary is asserted, not compatibility with an arbitrary subset or prescribed stratification. Second countability and local Euclidean-quadrant structure give the needed paracompactness. | [Murayama–Shiota, Triangulation of the map of a G-manifold to its orbit space, Nagoya Math. J. 212 (2013), pp. 159–160](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B650C32D644185E786B3DB76ABF44740/S0027763000022418a.pdf/triangulation_of_the_map_of_a_gmanifold_to_its_orbit_space.pdf). These pages explicitly allow k=1 and corners and state the Cairns–Whitehead triangulation theorem, citing Munkres. The PL manifold boundary is a subcomplex, giving the stated relative CW consequence. |

## Proved cellular comparison

[Homology.lean](SphereSixComplex/Prerequisites/Topology/CWComplex/Homology.lean)
now constructs the cellular chain model from Tau Ceti's
`cellularSingularHomologyIso`. It proves the cell basis using coproducts of abelian
groups and identifies homology with the project's actual singular chains.
The theorem requires a Hausdorff finite-dimensional CW complex. Every consumer
supplies this hypothesis through an existing finite CW model, including the sphere
model and compact smooth manifold models. The former, broader cellular comparison
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

## Scope and limits

The classical-source review above is retained from the September review. The corners contract was checked against the cited primary-source PDF; the other
correspondences use the standard classical results and inspection of the Lean
contracts. This is not a formal proof of the remaining assumptions.

`IntegralCohomology.universal_coefficients` displays both degree cases and Mathlib's
`Abelian.Ext` in its statement. Hurewicz's range and smooth Poincare's manifold
hypotheses and diffeomorphism conclusion are also expanded directly. See
[ChallengeAxioms.lean](ChallengeAxioms.lean) for Lean-generated exact signatures.

## Verified dependency boundary

The final theorem's compiled dependency closure contains Lean's three standard
axioms and the seven classical declarations listed above. The construction closure
contains four classical declarations and the same three standard axioms. The exact
allowlists are checked independently against those closures and Comparator's
configuration. No construction-specific axiom remains.

The full project build, exact axiom audit and Comparator pass on this boundary.
Comparator accepts the exported solution with Lean's default kernel. The local
macOS run uses fake-landrun, so Linux sandbox isolation was not tested here.
