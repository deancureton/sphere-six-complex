# Classical trust-boundary review

Classical contracts reviewed 2026-09-09; the cellular assumption was subsequently discharged. This is a mathematical review of the exact Lean statements and their supporting definitions, not a formal proof of the retained boundary. The nine retained declarations below describe general classical results; no substantive specialization, missing hypothesis, or contradictory encoding was found. Lean's `propext`, `Classical.choice`, and `Quot.sound` are separate logical dependencies. Comparator and full-build acceptance are separate checks performed by the main agent.

Repository-relative links below are intended for a document placed at the repository root. Line references are descriptive and reflect the reviewed checkout.

## Declarations and source correspondence

All names have prefix `SphereSixComplex.` unless another namespace is shown.

| Declaration and source | Exact-contract checks | Classical reference |
| --- | --- | --- |
| `Hurewicz.exists_map`, [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean), line 31 | [Higher.lean](SphereSixComplex/Prerequisites/Topology/Hurewicz/Higher.lean) uses actual cubical homotopy groups and postcomposition maps, a natural homomorphism, degree at least two, path connectedness, and triviality of every lower positive homotopy group. Existence of a natural isomorphism in the Hurewicz range is weaker than specifying the canonically normalized Hurewicz map. | [Hatcher, Chapter 4, Theorem 4.32](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). |
| `CWType.homological_whitehead`, [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean), line 57 | Both spaces are simply connected and have actual CW homotopy models. The same given continuous map induces isomorphisms in every integral singular homology degree, and the conclusion makes that map a homotopy equivalence. | [Hatcher, Chapter 4, Corollary 4.33](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). |
| `SmoothSixSphere.poincare`, [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean), line 67 | [ClassicalRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/ClassicalRecognition.lean), line 67, requires a compact smooth real six-manifold homotopy equivalent to the standard six-sphere. [SmoothRecognition.lean](SphereSixComplex/Prerequisites/Topology/Sphere/SmoothRecognition.lean), line 73, requests an actual diffeomorphism for the specified smooth atlas. | [Kervaire–Milnor, Groups of homotopy spheres I](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/kervmiln.pdf), computation of the group of homotopy six-spheres, together with smooth h-cobordism. This is dimension-six smooth classification, not an arbitrary-dimensional smooth Poincare assertion. |
| `PoincareDuality.nonempty_addEquiv`, [PoincareDuality.lean](SphereSixComplex/Prerequisites/Topology/Manifold/PoincareDuality.lean), line 28 | Compact boundaryless finite-dimensional C1 manifold, Hausdorff and second countable. [Orientation.lean](SphereSixComplex/Prerequisites/Topology/Manifold/Orientation.lean) includes exact dimension equality and preservation of orientation by transition derivatives. Only complementary-degree additive equivalences are asserted. Connectedness is unnecessary. | [Hatcher, Chapter 3, Theorem 3.30](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf). |
| `IntegralCohomology.universal_coefficients`, [UniversalCoefficients.lean](SphereSixComplex/Prerequisites/Topology/SingularHomology/UniversalCoefficients.lean), line 30 | [Cohomology.lean](SphereSixComplex/Prerequisites/Topology/SingularHomology/Cohomology.lean) defines the actual dual singular-chain complex. The obstruction is derived `Ext¹` in integer modules. Positive-degree splitting is noncanonical; no natural splitting is assumed. | [Hatcher, Chapter 3, Section 3.1, universal coefficient theorem](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf). |
| `SmoothManifold.finiteCWModel`, [Triangulation.lean](SphereSixComplex/Prerequisites/Topology/Manifold/Triangulation.lean), line 40 | Compact, Hausdorff, second-countable, finite-dimensional boundaryless C1 manifold. Only a finite CW homotopy model with dimension bounded by the actual real model dimension is requested. | [Whitehead, On C1-complexes](https://www.sciencedirect.com/science/chapter/edited-volume/pii/B978008009870850021X), Annals of Mathematics 41 (1940), 809–824. |
| `CWPair.whitehead`, [StrongDeformationRetraction.lean](SphereSixComplex/Prerequisites/Topology/Homotopy/StrongDeformationRetraction.lean), line 238 | Actual relative CW inclusion; path connectedness of both spaces; actual induced bijections on the fundamental group and every higher homotopy group. [SubspaceInclusion.lean](SphereSixComplex/Prerequisites/Topology/Homotopy/SubspaceInclusion.lean), line 33, defines the conclusion as an ordinary homotopy equivalence whose inverse map is the inclusion. No covering-space or toric conclusion is assumed. | [Hatcher, Chapter 4, Theorem 4.5 and the relative CW compression argument](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). |
| `LocallyCollared.nonempty_collar`, [Existence.lean](SphereSixComplex/Prerequisites/Topology/Collar/Existence.lean), line 26 | Metrizable ambient space and a relative open cover by subsets admitting collars. [OpenPush.lean](SphereSixComplex/Prerequisites/Topology/Collar/OpenPush.lean), line 18, requires a homeomorphism from `B × [0,1)` onto an open neighborhood, fixing zero. No closedness hypothesis is missing. | [Brown, Locally Flat Imbeddings of Topological Manifolds](https://www.maths.gla.ac.uk/~mpowell/Brown%20collars.pdf), Annals 75 (1962), Section II p. 332 for definitions and Theorem 1 p. 337. These pages were checked directly. |
| `ManifoldWithCorners.relativeCWComplex`, [CornersCWComplex.lean](SphereSixComplex/Prerequisites/Topology/Manifold/CornersCWComplex.lean), line 35 | Hausdorff, second-countable C1 manifold on a finite-dimensional real quadrant. Only a CW decomposition relative to the full manifold boundary is asserted, not compatibility with an arbitrary subset or prescribed stratification. Second countability and local Euclidean-quadrant structure give the needed paracompactness. | [Murayama–Shiota, Triangulation of the map of a G-manifold to its orbit space, Nagoya Math. J. 212 (2013), pp. 159–160](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B650C32D644185E786B3DB76ABF44740/S0027763000022418a.pdf/triangulation_of_the_map_of_a_gmanifold_to_its_orbit_space.pdf). These pages explicitly allow k=1 and corners and state the Cairns–Whitehead triangulation theorem, citing Munkres. The PL manifold boundary is a subcomplex, giving the stated relative CW consequence. |

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

## Scope and limits

The classical-source review above is retained from the September review. The Brown
and corners contracts were checked against the cited primary-source PDFs; the other
correspondences use the standard classical results and inspection of the Lean
contracts. This is not a formal proof of the remaining assumptions.

`IntegralCohomology.universal_coefficients` displays both degree cases and Mathlib's
`Abelian.Ext` in its statement. Hurewicz's range and smooth Poincare's manifold
hypotheses and diffeomorphism conclusion are also expanded directly. See
[ChallengeAxioms.lean](ChallengeAxioms.lean) for Lean-generated exact signatures.

## Verified dependency boundary

The final theorem's compiled dependency closure contains Lean's three standard
axioms and the nine classical declarations listed above. The construction closure
contains six classical declarations and the same three standard axioms. The exact
allowlists are checked independently against those closures and Comparator's
configuration. No construction-specific axiom remains.

The full project build, exact axiom audit and Comparator pass on this boundary.
Comparator accepts the exported solution with Lean's default kernel. The local
macOS run uses fake-landrun, so Linux sandbox isolation was not tested here.
