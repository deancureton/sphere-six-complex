# Axiom-elimination plan

## Objective

The current target for the final Comparator report is Lean's three standard logical axioms and a
small set of general classical blackboxes:

\[
\{\mathsf{propext},\ \mathsf{Quot.sound},\ \mathsf{Classical.choice}\}
\cup \{\mathrm{Hurewicz},\ \mathrm{HomologicalWhitehead},
\mathrm{SmoothPoincare}_6,\ \mathrm{CellularHomology},\ \mathrm{PoincareDuality},
\mathrm{CohomologicalUCT},\ \mathrm{SmoothTriangulation},\ \mathrm{BrownCollaring},
\mathrm{RelativeTriangulation},\ \mathrm{RelativeWhitehead}\}.
\]

The displayed size is not a quota. This boundary may shrink, or one entry may be replaced by a more natural
literature theorem, as the formalization develops.  It may grow only when the additional entry is
a standard theorem in its usual generality, is independently auditable without understanding this
paper, and replaces a genuinely infeasible foundational development.  A specialized corollary,
even when mathematically true, is never an admissible blackbox.

The phase-geometry axiom has been replaced in source by a proved constructed-model package.
Its classical dependencies add Brown collaring and activate the existing relative triangulation
and relative Whitehead theorems. The computed final closure is ten classical inputs and one
transitional dependency. The finite-fibre specialization declaration remains a proof obligation;
its current marking must be corrected to agree with the proved deck coordinates.
The analytic correction is proved, the cellular input has been strengthened in place, the former combined manifold-homology package
is now derived from general Poincare duality, UCT, and smooth triangulation, and the analytic
correction is derived from the proved Cauchy–Green/Cousin theorem. Adding files,
structures, or reductions does not count as progress unless it closes a named milestone below or
rules out a proposed route and updates this plan.

The retained `classicalHigherHurewiczTheory` is the general classical theorem: it asserts the
existence of a natural higher Hurewicz homomorphism for arbitrary spaces and degrees and its
usual isomorphism property under the standard connectivity hypothesis. Sphere realization is now
a theorem derived solely from naturality and the cube-boundary quotient comparison, rather than
a separate field in the trusted structure. The application-shaped
`generalHigherHurewiczClassSurjectivity` is now a theorem derived from that one blackbox and is not
permitted by Comparator. Cubical loops now descend uniquely through the cube-boundary quotient,
and that quotient is proved homeomorphic to Mathlib's Euclidean sphere model in every positive
dimension, using only Lean's standard three axioms. The manifold-CW boundary has also been
repaired: the retained theorem includes both ordinary CW type and compact-implies-finite-CW,
and, on the compact manifolds in the final proof, it is now derived from the stronger
dimension-controlled smooth triangulation theorem. The redundant CW-type axiom has been removed.
The former combined
`establishedCompactSmoothOrientedManifoldHomologyTheory` is now a Lean definition derived from
general integral Poincare duality, the cohomological universal coefficient theorem, and the
dimension-controlled smooth triangulation theorem. Its finite-generation and dimension-vanishing
fields are proved from triangulation and the general cellular-homology foundation.

The deletion test is intentionally mechanical. A project axiom is gone exactly when its name is
absent from `comparator.json`, Comparator accepts the challenge, and the printed axiom closure of
the headline theorem contains only `propext`, `Quot.sound`, `Classical.choice`, and the explicitly
listed literature-level blackboxes in this section. A theorem-shaped wrapper elsewhere in the
repository does not count as removal if its proof still reaches an unlisted axiom.

The paper-specific statements do not follow from Hurewicz or smooth Poincare. They must be proved
from the explicit construction and Mathlib. The four recognition blackboxes enter only at the
final recognition stage. Cellular homology and Poincare duality/UCT enter while proving that the
constructed complex threefold has the integral homology of \(S^6\).

## Candidate final blackboxes

The classical boundary now has ten entries. The analytic track now has an axiom-free arbitrary-cover
Cousin theorem, so Cartan B is no longer a proposed boundary entry. The trusted statements
must not mention this paper, the constructed threefold, or the number six except where dimension
six is intrinsic.

1. **Higher Hurewicz theorem.** Retain the ordinary general theorem as the existence of a natural
   Hurewicz homomorphism \(\pi_n(X,x)\to H_n(X;\mathbb Z)\), its realization by sphere maps, and
   its isomorphism property for an \((n-1)\)-connected space, for arbitrary \(n\ge 2\). Mathlib's
   cubical generalized loops are independently proved equivalent to based maps from its Euclidean
   sphere model, so the boundary does not hide an S⁶-specific representation principle. Derive
   lower homotopy vanishing by strong
   induction from the present lower-homology hypotheses, and then derive
   `establishedHigherHurewiczSixGenerator` at \(n=6\). The former class-surjectivity specialization
   is now a theorem and is not permitted by Comparator.

2. **Compact smooth manifolds have finite dimension-controlled CW models.** This is not a separate
   blackbox: `establishedCompactSmoothSixManifoldClassicalCWType` is derived by forgetting the
   finiteness and dimension data in the smooth-triangulation blackbox below. The former weaker
   `finiteDimensionalSmoothManifoldClassicalCWModel` axiom has been deleted.

3. **Homological Whitehead theorem.** Assume the general theorem that an integral-homology
   equivalence between simply connected spaces of CW type is a homotopy equivalence, with the given
   map as its forward map. Derive
   `establishedSimplyConnectedClassicalCWIntegralHomologyWhitehead` as a packaging theorem.

4. **Smooth Poincare in dimension six.** Retain the statement that every compact smooth
   six-manifold homotopy equivalent to \(S^6\) is diffeomorphic to the standard smooth sphere. This
   is the necessarily dimension-specific input combining generalized Poincare, smooth
   \(h\)-cobordism, and \(\Theta_6=0\).

5. **Integral cellular homology.** Retain the source-independent cellular-homology theorem
   `integralCWCellularHomologyFoundation` in its
   natural skeletal-relative form: \(C_n^{\mathrm{cell}}(X)=H_n(X^n,X^{n-1};\mathbb Z)\), with
   differential induced by the relative connecting map and projection. Characteristic maps fix
   the oriented cell basis, boundary coefficients are the corresponding attaching-map degrees,
   cellular maps induce a functorial chain map, and the resulting homology is naturally isomorphic
   to integral singular homology. The comparison agrees with skeleton inclusion on absolute
   skeletal homology, via the proved relative cycle map, exactly as in the proof of Hatcher's
   Theorem 2.35. Naturality alone would permit negating every comparison. This normalization
   does not require a noncanonical strict chain map from
   cellular chains to singular chains. Derive the present objectwise
   `integralCWCellularHomologyModel` from this theorem. Its attaching-degree formula uses the
   actual characteristic attaching-sphere map and contains no application-specific incidence
   values or specialization matrices. Disk orientations in dimensions zero, one, and two are
   normalized by proved point, interval, and counterclockwise square-boundary calculations.

6. **Smooth triangulation with dimension.** Retain the classical theorem that every compact,
   second-countable Hausdorff finite-dimensional boundaryless real `C¹` manifold has the homotopy
   type of a finite CW complex of dimension at most its manifold dimension. This is stated for
   arbitrary model spaces and manifolds. Finite generation and homology vanishing above the
   dimension are derived from blackbox 5.

7. **Integral Poincare duality and UCT.** Integral singular cohomology and its cochain complex are
   defined in Lean. Retain group-level integral Poincare duality for arbitrary closed oriented
   manifolds and the ordinary cohomological UCT for arbitrary spaces as separate theorems in their
   standard generality. Since cap products are not yet formalized, the duality boundary honestly
   asserts only the usual degreewise additive equivalences and makes no fake claim that an
   unconstrained map is the cap product. The noncanonical UCT splitting is wrapped in `Nonempty`.
   The old `establishedCompactSmoothOrientedManifoldHomologyTheory` package is derived and is not
   permitted by Comparator.

The current recognition signatures are `classicalHigherHurewiczTheory`,
`simplyConnectedHomologicalWhitehead`, and `establishedSmoothPoincareSixStandardModel`.
The Hurewicz interface asserts existence of a natural homomorphism satisfying the classical
properties; it does not uniquely characterize a canonical choice or its sign. Smooth CW type is
already derived from dimension-controlled triangulation. A candidate is rejected if it is merely
a custom conclusion needed by this project rather than a literature-level theorem.

8. **Brown collaring.** Retain Brown’s general theorem that a locally collared subset of a
   metrizable space has an open collar. The statement has no dimension or manifold hypothesis.
   The actual local collars are proved from the positive quadrant charts and an explicit
   orthant-to-half-space homeomorphism. The homotopy equivalence with the boundary complement
   is proved in Lean using a Urysohn cutoff; it is not part of this blackbox.

9. **Relative C¹ triangulation with corners.** Retain the general relative CW consequence of
   Cairns–Whitehead triangulation for arbitrary second-countable Hausdorff C¹ manifolds with
   corners in any finite dimension. The base is the full manifold boundary. The actual
   quadrant atlas, smooth deck action, descended quotient atlas, and boundary identification
   are all proved before applying this theorem. This activates a previously dormant classical
   boundary, rather than adding a toric-specific assumption.

10. **Relative Whitehead theorem.** Retain the general theorem that a path-connected relative
    CW inclusion inducing bijections on the fundamental group and all higher homotopy groups
    is a homotopy equivalence. This previously dormant theorem supplies the quotient inclusion
    step after the regular cover and its full core preimage have both been proved contractible.
    The covering comparison, homotopy extension, and equivariant strong retraction are proved.

### Human review of the classical boundary

The source theorem and the Lean hypotheses must be checked together. A familiar name alone does
not validate an opaque structure. The generated catalog in `ChallengeAxioms.lean` gives the
constant types; reviewers must also inspect the definitions those types mention.

| Input | Source and signature checks |
|---|---|
| Higher Hurewicz | [Hatcher, Chapter 4, Theorem 4.32 and the Hurewicz homomorphism](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). Arbitrary spaces, degree at least two, path connectedness, and all lower positive homotopy groups trivial. Cubical loops and Euclidean spheres are linked by proved maps. |
| Homological Whitehead | [Hatcher, Chapter 4, Corollary 4.33](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). Both spaces must be simply connected and have CW type. The actual given homology-equivalence map must be a homotopy equivalence. |
| Smooth Poincare in dimension six | [Kervaire--Milnor, Groups of homotopy spheres I](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/kervmiln.pdf), together with smooth h-cobordism. The input is a compact smooth homotopy six-sphere, and the conclusion concerns its given smooth atlas. This is a combination of classical results, not smooth Poincare in arbitrary dimension. |
| Cellular homology | [Hatcher, Chapter 2, Theorem 2.35 and its skeletal construction](https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf). The groups and maps are actual relative singular homology of consecutive skeleta, with characteristic-map cell bases and comparison normalized on absolute skeletal cycles. The characteristic pair maps, `d² = 0`, and attaching-degree identity are now proved directly from Mathlib and removed from the trusted structure. |
| Smooth triangulation | [Whitehead, On C1-complexes](https://www.sciencedirect.com/science/chapter/edited-volume/pii/B978008009870850021X). The Lean statement keeps compactness, Hausdorffness, second countability, finite dimension, and absence of boundary. It requests only a finite CW homotopy model with the dimension bound. |
| Poincare duality | [Hatcher, Chapter 3, Theorem 3.30](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf). Closed oriented manifolds, integral coefficients, and complementary degrees. `SmoothAtlasOrientation` includes the dimension equality and orientation-preserving transition derivatives. Only additive equivalences are asserted. |
| Cohomological UCT | [Hatcher, Chapter 3, Section 3.1](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf). The cohomology is that of the integral singular cochain complex and the obstruction is actual derived `Ext¹` over the integers. The positive-degree splitting is noncanonical. |
| Brown collaring | [Brown, Locally Flat Imbeddings of Topological Manifolds, Theorem 1, p. 337](https://www.maths.gla.ac.uk/~mpowell/Brown%20collars.pdf). Section II defines precisely an open collar by `B × [0,1)` fixing zero. `LocallyCollared` requires a relative open cover by subsets with these collars. Only metrizability is assumed. |
| Relative Whitehead | [Hatcher, Chapter 4, Theorem 4.5 and the relative CW compression argument](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). The statement requires a relative CW inclusion, path connectedness on both sides, and actual induced bijections on π₁ and every higher homotopy group. It contains no toric or covering-space conclusion. |
| Relative C¹ triangulation with corners | [Murayama–Shiota, Nagoya Math. J. 212 (2013), pp. 159–160](https://doi.org/10.1215/00277630-2366201) explicitly states the classical Cairns–Whitehead theorem for `C^k` manifolds with corners, including `k = 1`, and cites Munkres. A PL triangulation has its full boundary as a subcomplex; the Lean axiom retains only the resulting relative CW structure. |


This audit does not approve the four remaining transitional axioms. The former analytic declaration is
now proved using only Lean's standard logical axioms and has been removed from both allowlists.

No additional blackbox may be added silently. A candidate is permitted only when it is a standard,
source-independent literature theorem in its natural generality and its exact Lean signature is
auditable without understanding this construction.

## Global proof architecture

The paper's first-page argument becomes the following Lean pipeline:

\[
\begin{aligned}
&\text{period functions and affine descent}\\
&\quad\Longrightarrow \text{complex torus family over the }(3,4,\infty)\text{ orbifold},\\
&\text{elliptic logarithmic transforms plus the }A_2\text{ toric cusp filling}\\
&\quad\Longrightarrow \text{compact complex threefold }X,\\
&\text{explicit cover, van Kampen, Wang and Mayer--Vietoris calculations}\\
&\quad\Longrightarrow \pi_1(X)=0,\quad H_*(X;\mathbb Z)\cong H_*(S^6;\mathbb Z),\\
&\text{Hurewicz + CW type + homological Whitehead}\\
&\quad\Longrightarrow X\simeq S^6,\\
&\text{smooth Poincare in dimension six}\\
&\quad\Longrightarrow X\cong_{\mathrm{diff}} S^6,\\
&\text{pull back the complex atlas along the diffeomorphism}\\
&\quad\Longrightarrow S^6\text{ admits a complex structure.}
\end{aligned}
\]

There are five largely independent implementation tracks:

- **C: classical interfaces** - generalize the three recognition wrappers without changing their
  mathematical content;
- **CF: cellular foundation** - replace the arbitrary objectwise model by the standard
  characteristic-map-normalized, functorial skeletal-relative theory;
- **T: toric cusp** - the nonnegative \(A_2\) toric locus, honeycomb, CW atlas and incidence;
- **S: Section 7 topology** - finite specialization, marked bands, cusp coordinates and relators;
- **A: analytic descent** - the affine-line torsor correction at the orbifold cusp.

The recognition and analytic tracks are complete and should remain stable while T and S remove
the four remaining transitional axioms.

## Dependency work items

For every row marked **eliminate**, success means that the named declaration is a theorem (or all
consumers are redirected to an equivalent theorem), its name is absent from both axiom allowlists,
and Comparator passes.

| # | Current declaration | Disposition | Derivation plan |
|---|---|---|---|
| 1 | `establishedHigherHurewiczSixGenerator` | proved from blackbox 1 | Instantiate the general natural higher Hurewicz theorem. Use simply connectedness at degree one and strong induction with its isomorphism property to turn lower integral-homology vanishing into lower homotopy vanishing. Sphere realization supplies a representative of the chosen degree-six generator, and the proved \(H_6(S^6)\cong\mathbb Z\) calculation makes its homology map an isomorphism. The application-shaped `generalHigherHurewiczClassSurjectivity` is proved in Lean and is not permitted by Comparator. |
| 2 | `establishedCompactSmoothSixManifoldClassicalCWType` | proved from smooth triangulation | The exact public accessor is derived by forgetting the finiteness and dimension data in `compactCOneManifoldFiniteCWModelAtDimension`. The redundant `finiteDimensionalSmoothManifoldClassicalCWModel` declaration has been deleted and is not permitted by Comparator. |
| 3 | `establishedSimplyConnectedClassicalCWIntegralHomologyWhitehead` | proved from blackbox 3 | Package `simplyConnectedHomologicalWhitehead`, stated elementwise for arbitrary simply-connected spaces of classical CW type, into the existing property interface. |
| 4 | `establishedSmoothPoincareSixStandardModel` | retain as blackbox 4 | Its current quantified statement is already the general dimension-six smooth-Poincare theorem: every compact smooth six-manifold homotopy equivalent to the standard sphere is diffeomorphic to it. It does not mention the constructed threefold. |
| 5 | `establishedCompactSmoothOrientedManifoldHomologyTheory` | proved from blackboxes 5--7 | Integral singular cohomology and its cochain complex are defined in Lean. General group-level Poincare duality and general cohomological UCT give the complementary-homology equivalences; the dimension-controlled smooth triangulation theorem plus cellular homology give finite generation and vanishing above the manifold dimension. The combined reduced package is now a definition and is not permitted by Comparator. |
| 6 | `EstablishedCellularHomology.integralCWCellularHomologyModel` | proved from blackbox 5 | The old objectwise accessor is now a definition derived from `integralCWCellularHomologyFoundation`, whose basis is carried by the characteristic maps and whose singular-homology comparison is natural for cellular maps. |
| 7 | `Periods.establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection` | proved, no analytic blackbox | Whole-group affine transport, regular and elliptic local sections, the precisely invariant cusp section, and an explicit `Option ℂ` quotient cover are constructed. Distinct overlaps avoid the branch values, so their normalized differences descend to analytic scalar cocycles. The proved arbitrary-cover Cousin theorem supplies an `O(-1)`-normalized splitting; corrected local sections glue to a global equivariant holomorphic section. The resulting infinity germ and parabolic invariance give the bound on the whole closed cusp. The assembled theorem and original accessor use only the three standard Lean axioms. |
| 8 | `establishedStandardA2ToricCentralOrbitCellAtlas` | **proved (T)** | Explicit characteristic maps in dimensions zero through four satisfy continuity, inverse continuity, disjointness, boundary attachments, and full coverage. The resulting atlas is transported from `constructedModel` to every allowed toric model by the canonical central-orbit homeomorphism. Its axiom audit contains only Lean’s standard three axioms. |
| 9 | `establishedStandardA2ToricCentralFiberHigherIncidenceResidual` | **proved** | All eight three-cell and both four-cell entries follow from actual phase sweeps, relative prism generators, and absolute attaching-map vanishing. All cellular entries are transported through both actual atlas homeomorphisms. No incidence axiom remains. |
| 10 | `establishedFiniteFiberDegreeTwoSpecializationMatrix` | eliminate (T+CF) | Degree one is proved in canonical deck coordinates. Degree two remains assumed: prove the actual coordinate tori give an integral homology basis, using phase-cell charts and the natural cellular-to-singular comparison, then choose coherent target coordinates. The old two-degree residual is now a theorem. |
| 11 | `EstablishedSectionSevenAffineRegularLiftTopology.markedBandHomotopies` | **proved** | The named strip is normalized by the common peripheral marking. The normalized meridians have exact `g₁`/`g₂` deck labels; strengthened chosen marking radii and connected-sheet trapping prove identity-collar Cayley bounds throughout both strips. These bounds and midpoint-pinned real-period gauges prove both band homotopies. The former arbitrary-radius identity-sheet claim is not used. |
| 12 | `EstablishedSectionSevenCuspTopology.establishedCuspPulledBackMarkedInvariantBasisData` | **deleted; corrected boundary proved** | The actual boundary homomorphism equals raw coordinate four. The raw-four normalized elliptic splitting and corrected signed cusp basis now feed the production homology assembly directly. The rejected raw-five-boundary package and its unconditional wrappers are removed from production; conditional diagnostics remain. |
| 13 | `EstablishedSectionSevenCuspTopology.establishedActualCuspFiberEllipticMarkedCoordinateResidual` | **proved** | Both fields are now proved. The full-iterate relation uses the actual cusp Wang generator comparison. The raw-five fibre coefficient follows by applying the global fourth-circle sweep to that relation, identifying both oriented endpoint tori, and cancelling twelve. The remaining dependencies are the separate toric incidence and specialization inputs. |
| 14 | `StandardInfiniteA2ToricModel.Established.normalizedPolarHoneycombPhaseGeometry` | proved | The corrected global honeycomb homeomorphism is proved from compatible finite quotient charts and a locally finite closed hexagonal cover. Its construction uses only standard Lean axioms and replaces the `honeycombCells` input. The positive-deck quotient relative CW structure is now proved from the general C¹ manifold-with-corners relative triangulation theorem, using an explicit C¹ quadrant atlas, zero-height boundary identification, and smooth deck action. The full positive locus is contractible by the explicit interior homeomorphism and Brown collaring applied to proved local collars. The open-collar homotopy equivalence is proved using a Urysohn cutoff. Relative Whitehead and proved covering/HEP machinery supply the equivariant retraction; invariant modulus and stabilizer theorems complete phase spreading. Generic consumers now state a `HasCuspPhaseSpreading W` hypothesis; the constructed model has a proved instance, and the universal phase axiom and its wrappers are deleted. |
| 15 | `PaperAnalyticData.establishedActualEllipticRelatorNormalClosureResidual` | **proved (S)** | Both orders use the entering sheet of the existing comparison homotopy's own lifted trace. Literal straight-fibre loops are identified with their labelled regular-family periods; transport along that same trace proves the corrected period identities and both normal-closure statements. The resulting theorem uses only standard Lean axioms. |


### Confirmed cusp marking mismatch

`CuspFourthSweepCentralImage.actualCuspFourthSweep_pulledBack_boundary` proves actual
fourth-period sweep vanishing with only `propext`, `Classical.choice`, and `Quot.sound`.
`actualCuspRawFive_pulledBack_boundary_zero` transports this to the raw basis using the Wang
sequence, and `not_cuspPulledBackMarkedInvariantBasisData` rejects row 12. Those raw-basis
statements additionally use `integralCWCellularHomologyFoundation` and the remaining toric
incidence and polar-honeycomb inputs. Existence of the radial completion input additionally
uses `markedBandHomotopies`. No contradiction was used to prove the headline or remove an axiom.

This agrees with the actual paper, printed page 60, Theorem 7.22: the third-period sweep maps
to a generator of the band kernel; the fourth-period sweep has zero boundary and supplies the
remaining fibre coordinate. The former formalization swapped their roles. Earlier unit-index-five
routes below are superseded and must not be revived. Comparator currently checks only the declared
assumptions; its success does not certify their consistency.

The required correction preserves the headline theorem and the toric specialization projection,
but exchanges the first two Section 7 cusp coordinates and proves the corresponding geometric
statements. Raw Wang-coordinate equality alone suffices for boundary comparison; it does not
suffice for the fibre-unit calculation, because the difference may be a fibre class.

### Cusp route audit

`PaperSectionSevenCuspFullFibreNaturalityObstruction` refutes the previously proposed stronger
full-fibre naturality comparison by exactness and the two-side matrix. This does not refute the
scalar row-12 assumption. `PaperCuspFourthPeriodInvariance` proves that every monodromy element
fixes the fourth basis vector, while the inverse order-three difference of the third basis vector
is the required kernel generator. This suggests checking a possible index-four/index-five mismatch
geometrically before pursuing a unit coefficient for the latter.

`NormalizedCircleProductCross` now constructs a canonical additive circle cross product in every
degree using Wang exactness and fibre projection. Homological circle sweeps respect loop
concatenation and homotopy, and geometric positive circle crosses are additive for additive targets.
These results use only standard Lean axioms. The generic fixed-circle Wang calculation has now been generalized from additive targets to
arbitrary spaces, with the old public signature retained. Canonical circle-cross naturality and
explicit path-circle descent are proved. The next check is the globally invariant fourth-circle
sweep of the already proved peripheral pair-of-pants homotopy. The scalar residual has not yet been
refuted or eliminated.

## Correct toric route

The old proposed homeomorphism

\[
\texttt{constructedLocalPositivePart }r\ \simeq
\mathbb R^2\times[0,r)
\]

was pinned off the central fibre to a rescaled logarithmic coordinate. It cannot exist with that
pinning: the formal theorem `constructedA2ProperMomentCoordinate_isEmpty` exhibits two distinct
central points approached by positive-height sequences whose pinned coordinates both converge to
\((0,0,0)\). No future proof may use `ConstructedA2ProperMomentCoordinate` as an existence target.

The replacement is the standard nonnegative toric model.

1. Use the affine nonnegative orthant charts and monomial transition maps on their genuine overlap
   domains. A negative exponent is permitted only where its coordinate is nonzero.
2. Identify the glued nonnegative toric locus with the polyhedral realization of the cone over the
   locally finite \(A_2\) fan. Its zero-height boundary is the planar honeycomb rather than a point.
3. Contract that polyhedral realization by an explicit PL homotopy. This proves positive-part
   contractibility without extending the false logarithmic coordinate.
4. Prove the normalized deck transformations are \(C^1\) in these local charts. Descend the atlas
   through the already-proved properly discontinuous action and apply relative triangulation, or
   give explicit locally finite relative cells.
5. Replace the current planar-tile convention before attempting the finite quotient.  The theorem
   `not_constructedA2HoneycombLaurentFiniteIdentity` gives an explicit neighboring-cell
   counterexample, so that proposition must not be assumed or targeted.  Reparametrize each square
   sector by the affine chart convention used by `constructedA2CellChart`; then prove the corrected
   same-fibres statement by a finite classification of chart-pair and lattice-neighbor orbits.
6. Assemble `ConstructedPolarHoneycombResidualData`; use the existing invariant-modulus theorem to
   obtain the phase-geometric core.

The central CW atlas and its incidence table should be constructed from the same toric charts so
that rows 8, 9, 10, and 14 share one oriented coordinate system.

## Classical infrastructure boundary

Rows 5 and 6 use cellular homology together with general Poincare duality and UCT. Row 5's current
combined consequence package is temporary and must be derived from those literature-level
theorems. Row 6 is derived from the characteristic-map-compatible, natural cellular comparison
theorem, so the cellular foundation remains one blackbox. It supplies only
the general basis, attaching-degree boundary, and naturality principles; every numerical
incidence and specialization value remains a consequence of the explicit toric construction.

Row 7 is being proved using Cauchy–Green inversion and normalized arbitrary-cover Cousin
splitting. Both are now Lean theorems using only the standard logical axioms; no Cartan B
blackbox is needed for this route.

## Execution order

Work may proceed in parallel, but the preferred merge order is:

1. **CF0 (complete):** the objectwise cellular-homology accessor is derived from the general
   characteristic-map-compatible natural theorem;
2. **S1:** row 10, the finite specialization matrix;
3. **S2 (complete):** row 11, the two marked-band Cayley/gauge calculations;
4. **S3:** refactor the final Mayer--Vietoris endpoint to degree-one bijectivity and degree-two
   surjectivity, then prove the corrected raw-four suspension boundary is a unit;
5. **S4:** prove row 13's meridian and index-four coefficients are units; the literal meridian's
   Wang sign is already computed;
6. **S5:** row 15, the two connector endpoint evaluations;
7. **T1:** correct the honeycomb tile/chart convention, then prove the corrected finite quotient
   and direct nonnegative toric atlas;
8. **T2:** row 14 is proved; the constructed instance passes the full build and dependency audit;
9. **T3:** row 8, the complete central-orbit CW atlas;
10. **T4:** row 9, the oriented cellular incidence table;
11. **A1 (complete):** the finite-orbifold torsor section, normalized Cousin splitting, and cusp
    bounds are proved; row 7 is no longer an axiom;
12. replace rows 1--3 by corollaries of the three general recognition blackboxes and run final
    recognition.

Rows 10--15 have narrow endpoint propositions already isolated in the repository and therefore
come first. Rows 7--9 are larger construction projects and should be split only along the
milestones stated here, not by inventing new residual structures.

## Progress accounting and acceptance

The progress number is the number of paper-specific transitional declarations removed:

\[
\mathrm{progress}=\frac{9-N_{\mathrm{transitional}}}{9}.
\]

A reduction lemma, conditional constructor, or newly named residual earns no percentage by itself.
It may be reported as a milestone, but an axiom is green only after all of the following hold:

1. the old declaration is a theorem of the same type, or no final-cone consumer uses it;
2. its fully qualified name is removed from `scripts/allowed-axioms.txt` and
   `scripts/allowed-construction-axioms.txt`;
3. the generated human-review catalog is regenerated;
4. the source scan finds no unauthorized `sorry`, `axiom`, `admit`, `set_option`, or
   `native_decide`;
5. the relevant narrow theorem and the headline theorem pass axiom inspection;
6. a full build succeeds against the pinned dependencies (fetch their cache only when artifacts are missing);
7. import reachability, placeholder, axiom-catalog, and Comparator checks pass;
8. Comparator reports only the three logical axioms and the approved general classical boundary.

The allowlist is changed only when a dependency is actually removed from the final theorem. It is
never changed to rename a paper-specific assumption or to replace it with an equivalent residual.

## Iteration protocol

### External reference audit

The parallel development [plby/HopfProblem, `Solution.lean` at
`9ac8a456b526527837d7082ff775213ca8bc9809`](https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean)
is used for ideas and small targeted comparisons, not as a replacement library. In particular:

- `RefinedWang.markedConnecting_quarterColumns` computes the signed Mayer--Vietoris boundary
  from quarter slices. This repository already has the corresponding signed Wang algebra; the
  geometric homotopy and markings remain the work to do.
- Its affine-torsor construction uses a cover by many small patches, with elliptic centers kept
  out of distinct overlaps, then a compactly supported Cauchy--Green correction. Focused ports of scalar Cauchy--Green
  inversion and normalized arbitrary-cover Cousin splitting now prove that analytic step from
  mathlib. Each port records the exact source and Apache-2.0 provenance; no parallel topology
  development has been imported.
- The toric continuous-inverse argument uses compactness and fibre saturation. Here the full
  geometric singleton-stratum product is now proved using the actual quotient and phase action.

The pinned Tau Ceti revision is `c15c6f90c283c3ecce9e01ddda0e7912e2a1fb87`. Searches of that
revision and upstream `22ca3462eba18c466d1a37ee8c6e8d3fe1477dde`, and of the
[Palomar registry](https://data.palomar-registry.org/recent.json), found no direct replacement for
the current singular Wang/Mayer--Vietoris or Cousin obligations. No dependency pin has changed.

### Recording a work item

Each work session should select one row and record:

- the exact current endpoint theorem;
- the next unconditional theorem to prove;
- whether that theorem directly closes the row or which listed milestone remains;
- any counterexample discovered to the proposed route;
- the resulting change, if any, in the transitional count.

If a route is false, first prove or document the counterexample, update this plan, and remove the
dead route from active work. The global dependency table—not file count—is the source of truth.

### Geometric attachment and marking checkpoint

At checkpoint `6153629`, the transitional count remained eight. The following unconditional milestones use only the three
standard Lean axioms; they do not yet eliminate their corresponding residuals.

- **Toric:** `ConstructedA2BoundaryPhaseCancellation` and `ConstructedA2BoundaryDeckAttachment`
  prove the phase-corrected positive two-ball's entire boundary lands in the existing real
  one-skeleton in the actual orbit quotient. `ConstructedA2CorrectedPositiveTwoCell` proves
  closed-ball continuity and a genuine embedding of its open interior. Complete the partial
  equivalence and inverse continuity, then construct the three- and four-dimensional cells.
- **Model independence:** `StandardA2ModelEquivalence` constructs a canonical homeomorphism between
  arbitrary models, preserving charts, height, central components, torus action, and fan shear.
  `ActualCuspCentralModelEquivalence.centralOrbitModelHomeomorph` descends it to the actual central
  cusp quotients, including witnesses with different radii. Transport the eventual canonical
  cell atlas along this homeomorphism to prove the general atlas interface.
- **Cusp:** `GlobalInvariantPeriodCircle` constructs the global fourth-period circle action over
  the twice-punctured base. `CentralInvariantCircleBoundary` proves its normalized circle-cross
  classes have zero actual elliptic Mayer--Vietoris boundary, and extends this to product classes
  with zero fibre projection. The raw `Fin 6` index-five class (the sixth basis vector) has Wang
  coordinate fourth period; index four has third period. Match the actual index-five cusp
  representative modulo fibre classes before asserting any contradiction with the scalar residual.
  The file-checked local draft `/private/tmp/CuspFourthCircle.lean` constructs the fixed actual
  fourth-period circle and proves its sweep has the required Wang coordinate; it is not imported.
- **Elliptic:** `PaperEllipticBoundaryBaseMarking` proves both physical meridians' first-power
  markings unconditionally. The local translation projects to a constant base loop; the filling
  relation identifies the powered meridian, and unique roots in the free fundamental group
  recover the first power. Next lift the same base path to identify its endpoint deck and
  period transport simultaneously, then compare the whole relator.
- **Classical boundary:** cellular-chain-map identity and composition are now derived theorems,
  removed as fields from `IntegralCWCellularHomologyFoundation`. Their proofs use functoriality
  of relative singular chains and homology; no additional classical assumption is introduced.

Temporary paths are local continuation notes, not trusted or imported project content.

## Explicit atlas checkpoint

The orbit cell atlas is now proved, reducing the transitional count from eight to seven.
The cusp refutation remains unresolved; the refreshed Comparator allowlist records dependencies,
not acceptance of the rejected cusp package. The actual elliptic comparison trace now determines
its own entering sheet and conjugation equation in `PaperEllipticSynchronizedEnteringSheet`.

## Synchronized relator and honeycomb checkpoint

The actual elliptic relator axiom is replaced by a theorem, reducing the transitional count from
seven to six. The rejected cusp marking still prevents acceptance of the remaining trust boundary.
The global honeycomb is now constructed, removing that field from the coordinate residue.

The cellular foundation's arbitrary disk orientations cannot imply a fixed nonzero signed
incidence coefficient: `CellularOrientationAudit` proves this by reversing one dimension.
Canonical degree-zero and degree-one orientations are now derived from point augmentation and
the explicit interval relative singular chain. The public cellular model uses this normalized
foundation; no new classical axiom or field was introduced. Characteristic-map naturality
transports coefficients across atlas homeomorphisms, and all nine phase-two-cell boundary
coefficients vanish because their attaching maps factor through embedded intervals. All six edge
coefficients are proved from the canonical interval boundary; the coordinate-table
conversion is also proved in `ToricCellularCoordinateIncidence`.

## Positive quadrant and collar checkpoint

The constructed positive locus now has a proved C¹ quadrant atlas. Its manifold boundary is
exactly the zero-height locus, and the positive deck action is C¹. The existing general
`establishedSecondCountableCOneManifoldWithCornersRelativeCW` theorem therefore supplies the
quotient relative CW structure. `constructedPolarHoneycombResidualData_of_contractible`
assembles the polar-honeycomb residual from contractibility alone. This does not yet replace
row 14 in the headline dependency closure.

`OrthantHalfSpace` identifies the three-dimensional orthant and its coordinate boundary with
a half-space and its boundary. `ClosedCollarPush` proves that an explicit closed topological
collar gives a homotopy equivalence with the boundary complement, and hence transfers
contractibility from that complement. Both use only the three standard Lean axioms. No
collar existence axiom has been added; supplying a collar and proving the actual interior
contractible remain necessary for this route.

The third-period cusp sweep now realizes raw class 4 and its actual Mayer–Vietoris boundary.
The fourth-period circle and sweep reuse the same general construction. Generic circle
whiskering and free two-side homotopies support the remaining two-meridian calculation.
For each elliptic strip, one entering deck is proved to work over the entire strip, and the
full real-period frame changes by its actual lattice action. Comparing the two strips in one
shared marking remains open. The six transitional headline assumptions, including the
formally rejected raw cusp boundary marking, remain unresolved at this checkpoint.

## Constructed phase-spreading completion

`constructedLocalPositivePart_contractible` uses only Brown collaring and the standard Lean
axioms. `constructedHasCuspPhaseSpreading` additionally uses the two general classical results
for relative triangulation with corners and relative Whitehead. A direct `#print axioms` probe
confirms exactly these three project inputs. No specialized phase-geometry assumption survives
in this constructed instance. The full build, import and placeholder checks, axiom catalog,
closure audit, and Comparator default-kernel gate all pass. The headline closure contains
the standard three Lean axioms, ten classical inputs, and five transitional assumptions.

The normalized strip midpoint is now constructed using the actual marked cusp whisker and
its same cusp conjugator correction. Both total-cover meridian labels are proved to be the
named generators. Their transfer to the regular-base cover and the full-fibre band marking
comparison remain to be completed; no cusp-marking axiom is removed by this partial work.

The normalized zero/one midpoint labels and the third-sweep homology realization each have
direct kernel axiom audits containing only the three standard Lean axioms.


## Cellular comparison and marked-path normalization

The former cellular comparison interface fixed naturality but not its absolute sign: simultaneous
negation of every comparison preserves naturality. `homologyEquiv_skeletal` now states the
canonical compatibility from Hatcher, Theorem 2.35, p. 140. Its input map
`integralCWSkeletalHomologyToCellular` is proved from relative projection and exactness; no
application-specific equation is added to the classical theorem.

`CellularPathComparison` identifies an oriented characteristic edge with its relative singular
path class. Two such paths with the same endpoints give precisely the coefficient vector
`e - f`. `CellularSkeletalComparison` carries computed skeletal cycles to actual singular
homology with the corrected comparison.

The formerly arbitrary dimension-two disk orientation is now normalized in Lean by the relative
boundary isomorphism of a contractible disk and the winding coordinate on its square boundary.
`CellularSquareBoundary` gives the explicit radial homeomorphism to the complex unit circle.
The resulting positive boundary loop generates all first homology, and its image vanishing in
the one-skeleton implies every corresponding two-cell attaching coefficient is zero. Higher
disk orientations remain arbitrary; the remaining degree-three/four incidence targets are zero
and do not depend on their signs.


The positive cell's twelve half-sides now have their exact three edge labels. Its six-side
boundary loop is proved zero in first homology of the actual one-skeleton. The source-side
identification with a generating boundary loop is still required before declaring its attaching
coefficients proved; vanishing only in ambient homology would not have sufficed.

The normalized meridians now have exact `g₁`/`g₂` labels in the regular-base cover and use the
same corrected cusp whisker. Chosen internal marking radii satisfy stronger Cayley bounds while
preserving every previous radius specification. The connected-sheet trapping theorem is proved;
its application to the normalized radial paths and the production band replacement remain.
The third sweep is moved by a proved homotopy to the exact chosen cusp base, with a closed period
loop and exact torus realization. The common-endpoint cusp/meridian path comparison still needs
a homotopy before the primitive Mayer–Vietoris boundary calculation can be completed.

Direct kernel probes verify that the square orientation, its generating loop, the attaching-degree
zero criterion, and the characteristic edge-difference calculation use only Lean's standard
three axioms (the general cellular foundation is an explicit parameter in the latter criteria).
No transitional axiom is removed by this checkpoint.

Checkpoint gates passed: full build (10,077 jobs), import reachability (1,048 modules),
placeholder scan (only the two intentional challenge placeholders), exact axiom catalog and
closure audits, and Comparator with Lean's default kernel. The headline closure remains
18 constants and the construction closure 15. On macOS, Comparator's fake-landrun wrapper
checks functionality, not Linux sandbox isolation.


## Normalized band homotopies and cusp fibre transport

`markedBandHomotopies` is now a theorem. The named strip lift uses the common peripheral
normalization, with exact meridian labels and stronger chosen-radius specifications. Connected-sheet
trapping establishes the actual normalized radial Cayley bounds throughout each strip; the
midpoint-pinned real-period endpoint formulas supply the two finite-cover band homotopies.

The old named-strip crossing equality was not preserved: it does not follow for the corrected
marking. Optional full-fibre band-coordinate diagrams now state crossing agreement as an explicit
hypothesis. Production does not use that hypothesis. `PaperRegularFiberTransport` constructs the
continuous fixed-period torus family over the regular base and proves that any two fibre slices
are homotopic. `PaperCuspFiberTransportCompatibility` identifies both actual cusp and canonical
band slices in this family. Their homotopy after inclusion into the elliptic interior restores
`canonicalCuspFiberBandTopologicalCompatibility` unconditionally.

The actual cusp and normalized meridian paths are now homotopic upstairs, not merely equal in
endpoint or in fundamental-group class downstairs. The chosen third-period sweep is homotopic
to the two normalized meridian cylinders, whose actual Mayer--Vietoris boundary is the difference
of their overlap period circles. The marked overlap coordinate and Wang-generator orientation
remain to be identified before removing the rejected raw-four/raw-five cusp package.

`CellularLoopComparison` and `ConstructedA2CellularEdgeLoops` identify each actual characteristic
edge-return loop with the exact relative cellular vector `e - f`. The cellular specialization
matrix still requires comparison with the marked period loops and tori.

For the positive two-cell, the source hexagon boundary now has a radial homeomorphism from
the characteristic square boundary. The six sides are grouped into four paths, each with the
same endpoints as a circle quarter-arc and contained in the same convex open half-plane.
The generic convex homotopy is proved; assembling the four comparisons and matching the full
positive generator is still required before concluding that the attaching coefficients vanish.

The closure refresh removes exactly `markedBandHomotopies`, with no additions: 17 headline
constants (three Lean, ten classical, four transitional) and 14 construction constants.
Direct compiled audits of the marked band theorem, regular fibre transport, unconditional cusp
fibre compatibility, normalized cylinder boundary, actual sweep homotopy, and edge-loop cellular
comparison all report only the three standard Lean axioms.

Checkpoint gates passed: full build (10,090 jobs), import reachability (1,061 modules),
placeholder scan (only the two intentional challenge placeholders), exact axiom catalog and
closure audits, and Comparator with Lean's default kernel on the reduced 17-constant allowlist.
Comparator uses the macOS functional wrapper here, not Linux Landrun isolation.


## Positive two-cell and corrected cusp boundary checkpoint

The actual six-side hexagon traversal is now identified with the canonical positive square-boundary
homology generator. Its attaching image is null-homologous in the actual one-skeleton. Thus all
three positive two-cell coefficients vanish, completing all twelve entries of the degree-two
cellular differential. These new incidence proofs use only Lean's three standard axioms.

Canonical skeletal comparison now computes the chosen singular H1 and H2 coordinates of cellular
cycles. In particular, the actual edge loops have their signed standard coordinates. Identifying
the marked period loops and tori with these cycles remains necessary for specialization.

The normalized third-period sweep now has primitive Mayer–Vietoris boundary. Its normalized raw4
class has marked scalar one; raw5 has boundary zero. This proves the corrected boundary values
without using the rejected boundary or elliptic-coordinate assumptions. The production boundary
interface still needs a coordinated correction before its axiom can be deleted.

For the fourth-period sweep, the fiber correction is exactly `12 * raw[1] + 2 * raw[2]`.
Parity alone cannot prove surjectivity of the full gluing map: adjusting the elliptic coordinate
can alter the cusp-filling component. Exact control of specialization and the normalized fiber
coefficient is still required. No transitional axiom is removed at this checkpoint; four remain.

## Corrected production assembly and fourth sweep normalization

The complete pulled-back cusp boundary map is now proved to be raw coordinate four. It supplies
an explicit normalized splitting with raw-four coordinates `[0,1]`. The corrected signed basis
`[x5,x4,-x0,-x1,-x2,x3]` preserves the cusp-filling coordinates and gives the required final
Mayer–Vietoris matrices. The production endpoint uses this assembly, and the rejected boundary
axiom and its unconditional completion wrappers are deleted.

The surviving cusp residual was corrected explicitly: it requires the meridian full-iterate
relation and raw-five fibre coefficient one in this proved splitting. It is still an unresolved
paper-specific input. It no longer silently selects a splitting through the false boundary axiom.
All other elliptic coordinates follow from proved fibre values and the corrected boundary map.

The actual fourth-period sweep factors through a circle action on the simply connected local
toric carrier. Its degree-two specialization vanishes. Together with Wang coordinates and the
specialization projection, this proves equality with normalized raw five. No parity argument or
ex-falso step is used. The elliptic unit coefficient remains to be computed.

Actual higher-cell opposite phase faces are identified, and the compact phase action descends to
the central quotient. The relative-homology cancellation bridge needed for higher attaching
coefficients is still missing; no higher incidence vanishing is claimed from face identities alone.

## Higher-incidence reduction and cylinder prisms

The former twenty-four-entry independent-incidence assumption is now a theorem derived from the
proved edge/two-cell calculations and a ten-entry higher-incidence residual. Characteristic-map
naturality transports the low-dimensional coefficients through both actual atlas homeomorphisms.
This removes fourteen previously assumed independent scalar entries; the number of transitional
axiom declarations remains three.

A closed singular homotopy now gives an explicit prism taking boundaries to boundaries, and the
actual compact circle action identifies its characteristic cylinders with the three/four-cell
maps. A general short-exact-chain theorem proves that contracting prisms surject onto homology.
The cylinder contracts continuously to its bottom while preserving bottom plus sides, with exact
compatibility on that subspace. Descending these homotopies to relative chains and the top-face
excision comparison remain necessary before claiming higher attaching coefficients vanish.

Fourth-period translations are now jointly continuous on both actual elliptic filling quotients
and reduced fibres. The principal gauges and their inverses commute with these translations,
and the real-period product charts identify them with literal fourth-coordinate translation.
The regular-family translation is equivariant under the full deck group. Global quotient descent
and compatibility across elliptic collars still precede a proof of the fibre-unit coefficient.

The actual finite elliptic relators are now killed inside the elliptic interior. Their abelian
images imply the twelfth-power relation between the inverse cusp-bridge meridian and the first
fibre translation. Gamma-coinvariant algebra proves this for every abelian target. Identifying
these actual bridge loops with the mapping-torus homology generators via first-Hurewicz
naturality remains necessary to discharge the full-iterate field; the meridian sign and Wang
normalization themselves are already proved.

## Relative chains and concrete elliptic homology

Chain homotopies now descend through arbitrary short exact sequences when their components
preserve the subcomplex. The canonical relative-chain sequence for a triple is proved, including
its concrete cylinder instance and top-face chain map. Applying descent to the actual cylinder
prism still requires its compatibility with the subspace inclusion. Top-face excision remains
open; a concrete route uses the cylinder-boundary open cover `t > 0`, `t < 1`, followed by the
upper-cylinder retraction. These algebraic results alone do not establish higher incidence zero.

First-Hurewicz naturality and invariance under basepoint transport now turn the elliptic-interior
relator calculation into a relation in actual singular homology: twelve times the negative
cusp-bridge meridian equals the first bridge translation after inclusion. Comparing those two
classes with the chosen mapping-torus raw-two and raw-zero generators remains necessary to
remove the production full-iterate assumption.

Fourth-period circle translation now descends to the central-family quotient and is transported
to both actual varying elliptic fillings, with checked representative formulas. The collar
compatibility squares and gluing across the three open images remain necessary before using
this translation to compute the fibre-unit coefficient. This checkpoint removes no additional
axiom; the ten classical and three transitional project inputs remain unchanged.


## Full-iterate relation and relative cylinder contraction

The actual cusp meridian and first translation are now identified with the chosen Wang classes
through the radial maps. Applying the normalized elliptic coordinate to their proved homology
relation and cancelling twelve proves the production full-iterate relation. That field has been
removed from `ActualCuspFiberEllipticMarkedCoordinateResidual`; only the raw-five fibre coefficient
remains. Three transitional axiom declarations remain, but this cusp axiom has strictly less content.
The new full-iterate proof still depends on the toric higher-incidence and specialization inputs;
it does not depend on the cusp residual it replaces.

The fourth-period translations now satisfy both actual collar compatibility squares and glue to
a continuous map on the elliptic interior, with exact central and filling restriction formulas.
Computing the induced sweep map on homology is still required to discharge the last cusp coefficient.

Prism naturality is proved from Mathlib's alternating simplicial homotopy construction through
the singular functor. Compatible pair homotopies now descend to the actual relative chain maps.
The cylinder's bottom contraction therefore gives a contraction of its relative chains, with an
explicit projection identity and surjective prism classes. The upper cylinder and its top face
are homotopy equivalent on relative chains through the actual inclusion and projection maps.

Relative excision now follows from an open-refinement small-chain comparison and the actual
simplicial-subcomplex pushout, with singular subset intersections identified. This gives a
quasi-isomorphism for the upper-cylinder inclusion. Identifying that constructed map with the
canonical pair-induced map, and transporting the intersection subtype to compose the top-face
equivalence, remain necessary before applying the prism to the higher cellular coefficients.


## Cusp residual eliminated and top-face excision

The global fourth-circle sweep sends the positive cusp meridian to negative included raw five,
and sends the first fibre translation to fibre coordinate minus twelve. The factor-swap sign is
proved through the determinant of the standard two-torus transposition. Applying the sweep to
the actual full-iterate relation and cancelling twelve proves the raw-five coefficient is one,
for every normalized splitting. The former cusp residual axiom is now a theorem. Its proof uses
the remaining toric incidence and specialization assumptions, but no cusp residual.

The actual top-face relative chain map is now proved to induce homology isomorphisms in every
degree. The proof identifies the constructed excision map with the canonical inclusion and
composes the explicit upper-cylinder retraction and subtype isomorphisms. The characteristic
cylinder is homeomorphic to the next coordinate ball by the literal appended-coordinate map;
its entire boundary maps exactly to the coordinate sphere.

The closed prism now induces a natural degree-raising homology map and satisfies the signed
relative connecting-map formula on cycle representatives. The actual compact phase action
preserves the boundary two-skeleton, sends the one-skeleton into it, and fixes zero cells.
Applying these results to the actual higher characteristic maps remains the next incidence step;
no higher coefficient vanishing follows merely from having these general interfaces.

## Higher-cell prism generators and literal specialization markings

Every higher-ball relative homology class is now represented by a lower-ball cycle followed
by the actual top-face contraction prism and characteristic cylinder homeomorphism. This is a
surjectivity statement, so it does not require choosing an orientation sign. The actual phase
sweeps restrict from the one-skeleton to the two-skeleton and from the two-skeleton to the
three-skeleton. Sweeping the hexagon gives zero in absolute homology. Comparing the higher
characteristic maps with these relative prism representatives remains necessary to remove row 9.

The three literal cellular edge paths now have continuous lifts to the local carrier, with
checked deck endpoints `0`, `(0,-1)`, and `(1,0)` and exact quotient projection formulas.
Their endpoint differences suggest a basis mismatch with the identity asserted in row 10;
the Hurewicz comparison is still required before changing production coordinates. The four
source degree-two generators are proved to be the marked coordinate tori `(01,03,12,02)`,
including their actual filling-point formulas. Their target cellular coordinates remain open.
These results do not verify the assumed specialization matrix. Two transitional axioms remain.


## Higher incidence eliminated; specialization marking correction required

The actual three-cell and four-cell characteristic maps are identified with closed phase sweeps
through the characteristic cylinder homeomorphisms. Relative prism naturality and surjective
prism representatives convert the positive attaching-circle homology vanishing into vanishing
of both three-cell attaching maps, then the four-cell attaching map. Their canonical cellular
coefficients are zero. The production higher-incidence residual is now a theorem, transported
through the existing model and central-fibre homeomorphisms. The final closure has fourteen
constants: Lean's three standard axioms, ten classical inputs, and one transitional axiom.

The specialization audit proves that the actual first two period classes in the constructed
filling are `-graph₀` and `graph₀ - graph₁`, where `graphⱼ` is edge `j` followed by reversed edge 2.
Thus the identity asserted in the current cellular marking is not correct. A canonical deck
homology equivalence and literal source period-circle comparison now supply the appropriate
period coordinates without that assumption. Switching the production coordinate interface and
updating its cellular comparisons remain necessary. No contradiction from the old assumption
is used to prove a geometric statement or the headline theorem.

The degree-two source coordinate tori and actual filling phase actions are also compared: the
fourth-period sweep of the first-period circle is the negative mixed torus class. The central
chart weights are proved explicitly. The remaining geometric step is primitivity of the swept
phase-edge classes and the positive torus class, followed by a coherent degree-two basis choice.
Comparator acceptance at this checkpoint still permits the transitional specialization axiom;
it does not establish the requested final trust boundary.

The next degree-one integration should preserve the old filling cellular equivalence under an
explicit name and use `actualCuspDeckHomologyOneEquiv` for production period coordinates.
The cellular comparisons in `StandardA2ToricCentralFiberExplicitCW`,
`CuspFiniteFiberSpecializationMatrixProof`, and `CuspFiniteFiberSpecializationExactResidual`
should use the explicit coordinate change induced by the two equivalences. This does not
require asserting a numerical transport matrix for arbitrary selected models. To consume
`cuspFiniteFiberGenerator_deckCoordinates` in the residual owner, extract the pre-axiom
specialization definitions from `PaperCuspGeometricSpecialization` into a lower module and
retarget `CuspFiniteFiberSpecializationGeometricReduction` to it, breaking the import cycle.


## Degree-one specialization proved in deck coordinates

Production degree-one coordinates now use `actualCuspDeckHomologyOneEquiv`. The old
cellular equivalence is retained as `actualLocalCuspFillingCellularHomologyOneEquiv`, and
`actualCuspDeckCellularHomologyOneEquiv` records the explicit change of coordinates.
The cellular naturality comparisons use this readout. No numerical transport matrix is
asserted for arbitrary selected cusp models.

The pre-axiom specialization types are extracted into `PaperCuspGeometricSpecializationTypes`,
allowing the owner to use the proved literal period loops without an import cycle.
`establishedFiniteFiberGeneratorSpecializationMatrix` is now a theorem: its degree-one
component follows from `cuspFiniteFiberGenerator_deckCoordinates`, and only its degree-two
component uses the new residual `establishedFiniteFiberDegreeTwoSpecializationMatrix`.
This narrows the remaining assumption; it does not eliminate the last transitional axiom.

Further degree-two infrastructure proves an angular cut chart for the circle, relative-chain
comparison for cellular recharts with unchanged cell images, and an integral retraction of
each characteristic generator. The actual fourth-phase sweep of edge zero is injective on
the circle times the open edge and, after deleting the identity phase, has exactly the image
of the original phase-zero open cell. Completing the replacement charts and identifying
the swept homology classes as an integral basis remain open.

Checkpoint verification: full `lake build` passed (10,174 jobs), all 1,145 library modules are
reachable, and the placeholder gate found only the two declared challenge placeholders.
The refreshed exact closures contain fourteen final-theorem and eleven construction axioms,
with only the degree-two specialization residual transitional. Comparator accepted the solution
using Lean's default kernel. The standalone degree-one theorem uses only Lean's three axioms
and the retained Brown collaring, relative triangulation, and relative Whitehead inputs.


## Phase-sweep charts and the positive projection

The three mixed source coordinate tori are now proved to be signed compact-phase sweeps of
the actual first two period circles. Combining this with the established cellular loop markings
gives their exact expressions in phase sweeps of the two graph loops.

A continuous map from the actual filling to the positive deck quotient is constructed by
straightening the actual action and descending the modulus map. It is invariant under compact
phase on the central fibre. Consequently all three actual mixed source torus classes map to
zero in its second homology. No homology conclusion here is inferred merely from endpoint
labels or from first homology.

The phase-sweep charts replace the three old phase-cell charts with exactly the same open and
closed images and compatible boundary maps. The actual cylinder suspension is an integral
homology isomorphism, and its value on the oriented interval generator is proved to equal
the square generator or its negative. This sign is derived from an automorphism of the
integers, not assumed. The degree-one singular prism is also expanded into its two simplices.

The positive deck quotient is proved homotopy equivalent to its interior, with inverse the
actual inclusion. Local half-space charts descend through its covering, and Brown collaring
is applied on the quotient; no equivariance is assumed for a collar upstairs.

The remaining tasks include identifying the universal circle prism with the explicit torus
fundamental cycle, using the replacement charts to prove the mixed columns form an integral
basis of the kernel, and computing the positive column using logarithmic interior coordinates.
The degree-two specialization axiom is unchanged and remains outside the proposed final
trust boundary.

Checkpoint gates passed: full build (10,187 jobs), all 1,158 library modules reachable, only
the two declared challenge placeholders, unchanged exact final/construction axiom closures
(14/11), and Comparator acceptance with Lean's default kernel. New atlas, mixed-sweep,
and suspension-orientation results use only Lean's three standard axioms. The positive
projection vanishing uses the retained Brown and relative triangulation inputs; the quotient
interior homotopy equivalence uses Brown collaring.


## Integral prism comparisons and positive torus coordinates

The universal circle prism is identified with the explicit two-triangle torus fundamental
cycle up to one uniform integral sign. The full-boundary cylinder prism, its time reflection,
and its map into a relative homotopy now have proved naturality and orientation comparisons.
These are chain-level comparisons of the actual maps.

The replacement phase atlas has zero differentials into and out of degree two. An identity
cellular chain isomorphism transports this fact from the original atlas. Its singular second
homology is therefore identified with the four relative cell generators, compatibly with
inclusion of the two-skeleton and projection to relative homology. The compact phase action
preserves the required pair of skeleta, and the edge characteristic generators have their
normalized relative basis readouts. The central orbit inclusion into the filling is also
identified with a homology equivalence in every degree.

Logarithmic coordinates give an explicit homeomorphism from the positive quotient interior
to the standard two-torus times an open interval. Under this homeomorphism, the actual first
source torus projects to the identity torus at a fixed height. This is a pointwise formula for
the actual map; it does not infer a second-homology degree from first-homology information.

Still required: finish the relative swept-edge evaluations, combine them into the three mixed
columns, and use the positive torus degree to choose a coherent integral basis for the filling.
The production degree-two specialization assumption remains unchanged. None of these new
comparisons makes it part of the proposed final trust boundary.

Checkpoint gates passed: full build (10,204 jobs), all 1,175 library modules reachable,
only the two declared challenge placeholders, unchanged exact final/construction axiom
closures (14/11), and Comparator acceptance with Lean's default kernel.


## Integral fibre specialization isomorphism

The actual degree-two map from fibre coinvariants to the cusp filling is now proved bijective
in `cuspFiberSpecializationTwoBijective`, without the transitional specialization axiom.
The three mixed torus columns are evaluated in the phase-sweep cellular coordinates. Their
signed integral matrix is unimodular on the three graph coordinates. The positive projection
kills these columns and takes the first torus generator to one, so that generator completes
them to an integral basis. The proof compares the actual torus maps and homology classes.

This proves an isomorphism, not the old assertion that the map is the identity in the previously
chosen cellular coordinates. Production integration must change the target filling basis and
normalize the degree-two Wang section using the proved fibre inverse. The canonical source
fibre coordinates must be preserved: the elliptic attachment calculation uses those markings.
The local basis package now accepts a filling basis explicitly, retaining its old default.

The circle exponential is separated from the fourth-sweep module so the isomorphism proof can
be imported by the specialization owner without an import cycle. A general fourth-sweep
normalization theorem is also proved from a filling projection equation, ready for the corrected
coordinates. The last transitional axiom is still present in the production theorem and is not
part of the proposed final trust boundary.

Checkpoint gates passed: full build (10,219 jobs), all 1,190 library modules reachable,
only the two declared challenge placeholders, unchanged exact final/construction axiom
closures (14/11), and Comparator acceptance with Lean's default kernel. The isomorphism itself
uses only Lean's three axioms, cellular homology, Brown collaring, triangulation with corners,
and relative Whitehead.
