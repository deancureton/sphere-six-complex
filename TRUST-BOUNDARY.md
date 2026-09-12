# Classical trust-boundary review

Reviewed 2026-09-09. This is a mathematical review of the exact Lean statements and their supporting definitions, not a formal proof of the retained boundary. All ten declarations below describe general classical results; no substantive specialization, missing hypothesis, or contradictory encoding was found. Lean's `propext`, `Classical.choice`, and `Quot.sound` are separate logical dependencies. Comparator and full-build acceptance are separate checks performed by the main agent.

Repository-relative links below are intended for a document placed at the repository root. Line references are descriptive and reflect the reviewed checkout.

## Declarations and source correspondence

All names have prefix `SphereSixComplex.` unless another namespace is shown.

| Declaration and source | Exact-contract checks | Classical reference |
| --- | --- | --- |
| `Hurewicz.exists_map`, [HomologySphereRecognition.lean](SphereSixComplex/Prerequisites/Topology/HomologySphereRecognition.lean), line 30 | [HigherHurewicz.lean](SphereSixComplex/Prerequisites/Topology/HigherHurewicz.lean) uses actual cubical homotopy groups and postcomposition maps, a natural homomorphism, degree at least two, path connectedness, and triviality of every lower positive homotopy group. Existence of a natural isomorphism in the Hurewicz range is weaker than specifying the canonically normalized Hurewicz map. | [Hatcher, Chapter 4, Theorem 4.32](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). |
| `CWType.homological_whitehead`, [HomologySphereRecognition.lean](SphereSixComplex/Prerequisites/Topology/HomologySphereRecognition.lean), line 51 | Both spaces are simply connected and have actual CW homotopy models. The same given continuous map induces isomorphisms in every integral singular homology degree, and the conclusion makes that map a homotopy equivalence. | [Hatcher, Chapter 4, Corollary 4.33](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). |
| `SmoothSixSphere.poincare`, [HomologySphereRecognition.lean](SphereSixComplex/Prerequisites/Topology/HomologySphereRecognition.lean), line 61 | [SmoothSixSphereClassification.lean](SphereSixComplex/Prerequisites/Topology/SmoothSixSphereClassification.lean), line 39, requires a compact smooth real six-manifold homotopy equivalent to the standard six-sphere. [SmoothRecognition.lean](SphereSixComplex/Prerequisites/Topology/SmoothRecognition.lean), line 81, requests an actual diffeomorphism for the specified smooth atlas. | [Kervaire–Milnor, Groups of homotopy spheres I](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/kervmiln.pdf), computation of the group of homotopy six-spheres, together with smooth h-cobordism. This is dimension-six smooth classification, not an arbitrary-dimensional smooth Poincare assertion. |
| `PoincareDuality.nonempty_addEquiv`, [IntegralPoincareDuality.lean](SphereSixComplex/Prerequisites/Topology/IntegralPoincareDuality.lean), line 28 | Compact boundaryless finite-dimensional C1 manifold, Hausdorff and second countable. [SmoothAtlasOrientation.lean](SphereSixComplex/Prerequisites/Topology/SmoothAtlasOrientation.lean) includes exact dimension equality and preservation of orientation by transition derivatives. Only complementary-degree additive equivalences are asserted. Connectedness is unnecessary. | [Hatcher, Chapter 3, Theorem 3.30](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf). |
| `IntegralCohomology.universal_coefficients`, [IntegralUniversalCoefficients.lean](SphereSixComplex/Prerequisites/Topology/IntegralUniversalCoefficients.lean), line 44 | [IntegralSingularCohomology.lean](SphereSixComplex/Prerequisites/Topology/IntegralSingularCohomology.lean) defines the actual dual singular-chain complex. The obstruction is derived `Ext¹` in integer modules. Positive-degree splitting is noncanonical; no natural splitting is assumed. | [Hatcher, Chapter 3, Section 3.1, universal coefficient theorem](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf). |
| `SmoothManifold.finiteCWModel`, [SmoothTriangulation.lean](SphereSixComplex/Prerequisites/Topology/SmoothTriangulation.lean), line 40 | Compact, Hausdorff, second-countable, finite-dimensional boundaryless C1 manifold. Only a finite CW homotopy model with dimension bounded by the actual real model dimension is requested. | [Whitehead, On C1-complexes](https://www.sciencedirect.com/science/chapter/edited-volume/pii/B978008009870850021X), Annals of Mathematics 41 (1940), 809–824. |
| `CellularHomology.integralComparison`, [CellularHomology.lean](SphereSixComplex/Prerequisites/Topology/CellularHomology.lean), line 551 | General cellular/singular comparison on actual relative skeletal homology, with characteristic-map bases and naturality. Detailed field review below. | [Hatcher, Chapter 2, Section 2.2, pp. 138–140, Theorem 2.35 and its skeletal proof](https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf). |
| `CWPair.whitehead`, [StrongDeformationRetraction.lean](SphereSixComplex/Prerequisites/Topology/StrongDeformationRetraction.lean), line 284 | Actual relative CW inclusion; path connectedness of both spaces; actual induced bijections on the fundamental group and every higher homotopy group. [EstablishedStrongDeformationRetractsDefs.lean](SphereSixComplex/Prerequisites/Topology/EstablishedStrongDeformationRetractsDefs.lean), line 33, defines the conclusion as an ordinary homotopy equivalence whose inverse map is the inclusion. No covering-space or toric conclusion is assumed. | [Hatcher, Chapter 4, Theorem 4.5 and the relative CW compression argument](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). |
| `LocallyCollared.nonempty_collar`, [Collaring.lean](SphereSixComplex/Prerequisites/Topology/Collaring.lean), line 26 | Metrizable ambient space and a relative open cover by subsets admitting collars. [OpenCollarPush.lean](SphereSixComplex/Prerequisites/Topology/OpenCollarPush.lean), line 17, requires a homeomorphism from `B × [0,1)` onto an open neighborhood, fixing zero. No closedness hypothesis is missing. | [Brown, Locally Flat Imbeddings of Topological Manifolds](https://www.maths.gla.ac.uk/~mpowell/Brown%20collars.pdf), Annals 75 (1962), Section II p. 332 for definitions and Theorem 1 p. 337. These pages were checked directly. |
| `ManifoldWithCorners.relativeCWComplex`, [ManifoldWithCornersCWComplex.lean](SphereSixComplex/Prerequisites/Topology/ManifoldWithCornersCWComplex.lean), line 35 | Hausdorff, second-countable C1 manifold on a finite-dimensional real quadrant. Only a CW decomposition relative to the full manifold boundary is asserted, not compatibility with an arbitrary subset or prescribed stratification. Second countability and local Euclidean-quadrant structure give the needed paracompactness. | [Murayama–Shiota, Triangulation of the map of a G-manifold to its orbit space, Nagoya Math. J. 212 (2013), pp. 159–160](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B650C32D644185E786B3DB76ABF44740/S0027763000022418a.pdf/triangulation_of_the_map_of_a_gmanifold_to_its_orbit_space.pdf). These pages explicitly allow k=1 and corners and state the Cairns–Whitehead triangulation theorem, citing Munkres. The PL manifold boundary is a subcomplex, giving the stated relative CW consequence. |

## Cellular foundation: field-by-field review

The trusted structure is in [CellularHomology.lean](SphereSixComplex/Prerequisites/Topology/CellularHomology.lean), lines 439–489. It is the largest human audit surface among the retained boundaries.

- `diskOrientation`: chooses an additive isomorphism from the actual relative homology of the characteristic disk and its boundary to the integers in the disk dimension. The sup-norm coordinate disk is topologically an ordinary disk, including dimension zero with empty boundary.
- `cellBasis`: identifies finitely supported integer cell coefficients with actual relative singular homology of consecutive skeleta.
- `cellBasis_single`: requires each basis generator to be the image of the chosen disk generator under the actual characteristic pair map. It does not leave the attaching data arbitrary.
- `homologyEquiv`: compares homology of the actual skeletal chain complex with integral singular homology. The skeletal differential and its square-zero identity are constructed and proved outside the axiom.
- `homologyEquiv_skeletal`: fixes this comparison on absolute skeletal cycles by the actual skeleton-to-space inclusion. This is the normalization in the standard skeletal proof of Hatcher's Theorem 2.35, pp. 139–140.
- `cellularChainMap`: provides a chain map for an actual continuous cellular map.
- `cellularChainMap_f`: forces its degreewise components to equal the induced relative singular homology maps.
- `homologyEquiv_natural`: requires comparison to commute with those maps and actual singular homology maps.

The orientation choices are consistent with this contract: a common disk generator in each dimension is transported by characteristic maps. Arbitrary cellular maps need not preserve generators; their degrees encode orientation changes. No unsupported compatibility between orientations in different dimensions, prescribed cusp coefficients, or specialized specialization matrix is asserted.

## Scope and limits

The Brown and corners statements were checked against the primary-source PDFs, including definitions and the precise locations above. The cellular skeletal comparison proof was also inspected directly. The other source correspondences use the standard classical results listed in the repository catalog together with inspection of the Lean contracts and their mathematical definitions; this review is not a fresh reconstruction of every classical proof.

No change to the ten mathematical assumptions is recommended. Documentation should keep the cellular fields explicit rather than relying on the short theorem label. This review does not approve any transitional paper-specific axiom still present in an old allowlist; eliminating such a declaration and checking the final dependency closure remain separate integration gates.

## Verified dependency boundary

The module-separation checkpoint passed the full build (10,262 jobs), import and layer checks (1,233 modules), and placeholder gate (only the two Comparator challenge declarations). The strict compiled-environment audit finds exactly Lean's three logical axioms plus the ten classical declarations above for the final theorem. The implemented construction uses the three logical axioms and seven of the classical declarations. Comparator accepted the solution with Lean's default kernel against this exact permitted list. No specialized axiom remains in the formalization.


## September 12 interface cleanup

`IntegralCohomology.universal_coefficients` now displays both degree cases and Mathlib's
`Abelian.Ext` in its statement. A Lean check established equivalence between the former record's
inhabitation and the new universally quantified conjunction using classical choice. Hurewicz's
isomorphism range and smooth Poincaré's manifold hypotheses and diffeomorphism conclusion are
expanded directly; these two expansions are definitionally equal to their former contracts.
The ten mathematical assumptions are unchanged. The cellular comparison remains a dependent
bundle for the synchronized choices detailed above.
