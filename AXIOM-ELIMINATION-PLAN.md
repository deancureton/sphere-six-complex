# Axiom-elimination plan

## Objective

The current target for the final Comparator report is Lean's three standard logical axioms and a
small set of general classical blackboxes:

\[
\{\mathsf{propext},\ \mathsf{Quot.sound},\ \mathsf{Classical.choice}\}
\cup \{\mathrm{Hurewicz},\ \mathrm{HomologicalWhitehead},
\mathrm{SmoothPoincare}_6,\ \mathrm{CellularHomology},\ \mathrm{PoincareDuality},
\mathrm{CohomologicalUCT},\ \mathrm{SmoothTriangulation}\}.
\]

The displayed size is not a quota. This boundary may shrink, or one entry may be replaced by a more natural
literature theorem, as the formalization develops.  It may grow only when the additional entry is
a standard theorem in its usual generality, is independently auditable without understanding this
paper, and replaces a genuinely infeasible foundational development.  A specialized corollary,
even when mathematically true, is never an admissible blackbox.

The present final theorem uses fifteen project axioms: seven retained classical inputs and eight
transitional dependencies. The task is to replace the eight transitional declarations by theorems.
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

The current boundary has seven entries. The analytic track now has an axiom-free arbitrary-cover
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
   to integral singular homology. This does not require a noncanonical strict chain map from
   cellular chains to singular chains. Derive the present objectwise
   `integralCWCellularHomologyModel` from this theorem. Its attaching-degree formula uses the
   actual characteristic attaching-sphere map and contains no application-specific incidence
   values or specialization matrices.

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

### Human review of the classical boundary

The source theorem and the Lean hypotheses must be checked together. A familiar name alone does
not validate an opaque structure. The generated catalog in `ChallengeAxioms.lean` gives the
constant types; reviewers must also inspect the definitions those types mention.

| Input | Source and signature checks |
|---|---|
| Higher Hurewicz | [Hatcher, Chapter 4, Theorem 4.32 and the Hurewicz homomorphism](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). Arbitrary spaces, degree at least two, path connectedness, and all lower positive homotopy groups trivial. Cubical loops and Euclidean spheres are linked by proved maps. |
| Homological Whitehead | [Hatcher, Chapter 4, Corollary 4.33](https://pi.math.cornell.edu/~hatcher/AT/ATch4.pdf). Both spaces must be simply connected and have CW type. The actual given homology-equivalence map must be a homotopy equivalence. |
| Smooth Poincare in dimension six | [Kervaire--Milnor, Groups of homotopy spheres I](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/kervmiln.pdf), together with smooth h-cobordism. The input is a compact smooth homotopy six-sphere, and the conclusion concerns its given smooth atlas. This is a combination of classical results, not smooth Poincare in arbitrary dimension. |
| Cellular homology | [Hatcher, Chapter 2, Theorem 2.35 and its skeletal construction](https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf). The groups and maps are actual relative singular homology of consecutive skeleta, with characteristic-map cell bases and natural comparison. The characteristic pair maps, `d² = 0`, and attaching-degree identity are now proved directly from Mathlib and removed from the trusted structure. |
| Smooth triangulation | [Whitehead, On C1-complexes](https://www.sciencedirect.com/science/chapter/edited-volume/pii/B978008009870850021X). The Lean statement keeps compactness, Hausdorffness, second countability, finite dimension, and absence of boundary. It requests only a finite CW homotopy model with the dimension bound. |
| Poincare duality | [Hatcher, Chapter 3, Theorem 3.30](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf). Closed oriented manifolds, integral coefficients, and complementary degrees. `SmoothAtlasOrientation` includes the dimension equality and orientation-preserving transition derivatives. Only additive equivalences are asserted. |
| Cohomological UCT | [Hatcher, Chapter 3, Section 3.1](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf). The cohomology is that of the integral singular cochain complex and the obstruction is actual derived `Ext¹` over the integers. The positive-degree splitting is noncanonical. |

This audit does not approve the eight transitional axioms. The former analytic declaration is
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
the eight transitional axioms.

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
| 8 | `establishedStandardA2ToricCentralOrbitCellAtlas` | eliminate (T) | Two cyclic phase-face maps are genuine quotient-level injective `PartialEquiv` characteristic maps. The old planar-tile parametrization is disproved by an explicit counterexample. For the corrected embedding `C(v)=((2/3)v₀+(4/3)v₁, -(2/3)v₀+(2/3)v₁)`, same-cell, all positive and negative neighbor cases, the global Laurent iff, and the finite same-fibres equivalence are now proved. The corrected square-to-hexagon homeomorphism and four explicit 2-cells account for all dimensions through two. The two 3-cells and one 4-cell require a genuine effective-phase trivialization of the singleton-support stratum, schematically `ball(0,1) × (Fin 2 → Circle) ≃ₜ singletonSupportStratum W`, with forward map given by the corrected positive representative acted on by a two-dimensional phase section. The phase API now has explicit chart homeomorphisms, exact stabilizer/fibre classification across all six zero-ray charts, a global effective-phase section `(k₀,k₁,1)`, and joint injectivity of positive representative and effective phase in the actual orbit quotient. A proper-map argument now proves continuity of the inverse, and deck normalization proves surjectivity onto the full geometric singleton-support stratum. Thus the actual stratum product homeomorphism is established. The positive singleton factor is now identified with the open 2-ball, giving the actual ball-times-phase homeomorphism. Every actual representative with support cardinality at least two now lies in the existing one-skeleton or one of the three open phase two-cells. The 3/4-dimensional characteristic maps and their remaining boundary checks remain. Separately, the public atlas theorem is generic in an arbitrary toric `Model`, while the explicit cells are specialized to `constructedModel`; either transport the atlas along a proved model equivalence or specialize the theorem honestly. |
| 9 | `establishedStandardA2ToricCentralFiberIndependentIncidenceResidual` | eliminate (T+CF) | The strengthened foundation now reduces each coefficient to the homological degree of the actual characteristic attaching map. Row 8 must first identify the atlas `cellMap` fields with the explicit toric maps. Then compute the 24 independent degrees (beginning with the oriented interval boundary for edge 0) and derive the remaining four entries from \(d^2=0\). |
| 10 | `establishedFiniteFiberGeneratorSpecializationMatrix` | eliminate (S+T+CF) | The natural cellular-to-singular comparison is now available. Prove the relevant inclusions are cellular and compute their images in the characteristic-cell basis; this simultaneously fixes the degree-one normalized coordinates and the four degree-two entries. |
| 11 | `EstablishedSectionSevenAffineRegularLiftTopology.markedBandHomotopies` | eliminate (S) | The former attempt to deduce the identity-sheet Cayley bounds from `starSeparation` is false: valid separation radii can be shrunk below both positive pinned norms. The entering-sheet group calculation is now proved: each order-three or order-four entering sheet is an elliptic-stabilizer multiple of the inverse common peripheral conjugator. The remaining point-set work is to identify the extracted local Cayley meridian with the corresponding geometric central meridian and to prove that translation by this common conjugator transports both finite-cover markings. The existing clopen-sheet and endpoint-gauge theorems then give the band homotopies. No identity-sheet bound is a valid target. |
| 12 | `EstablishedSectionSevenCuspTopology.establishedCuspPulledBackMarkedInvariantBasisData` | eliminate (S) | The final Mayer--Vietoris endpoint now accepts the full marked matrix family with arbitrary index-four coefficient `a` and orientation-independent unit index-five coefficient `b`, expressed by `b*b=1`; an explicit integral inverse is proved. Thus the current exact values `a=0,b=1` are unnecessary. The adaptive index-five boundary has been identified with an explicit band carrier, and a one-class split implies `b*b=1`. The inverse radial equivalence has a fixed radius, so cylinder height is independent of the fibre. Two scalar crossing times therefore give continuous full-fibre low and high slices in the adaptive overlap; no continuous-choice theorem is needed. What remains is to identify the signed slice difference with the Mayer--Vietoris boundary and compute its marked elliptic-band image. |
| 13 | `EstablishedSectionSevenCuspTopology.establishedActualCuspFiberEllipticMarkedCoordinateResidual` | eliminate (S) | Degree one needs only a unit meridian coefficient and degree two only `IsUnit a`. The full raw `[12,0,1]` source coordinate is proved. The global base phase `-4·phase(z)+3·phase(z-1)` corrects `12γ`; the radial homotopy is deck-invariant and has been descended through the additive cusp quotient, giving the corrected central mapping-torus character the same `[12,0,1]` coordinate. Extend that character over both elliptic filling pieces and identify the induced global winding, then prove the index-four side lift is primitive up to sign. |
| 14 | `StandardInfiniteA2ToricModel.Established.normalizedPolarHoneycombPhaseGeometry` | eliminate (T) | Replace the impossible pinned logarithmic coordinate with the nonnegative toric/PL model below. The explicit modulus now proves that contractibility of the full local carrier implies contractibility of the positive locus; construct that global contraction, the honeycomb homeomorphism, and a relative CW structure on the positive-deck quotient. Existing invariant-modulus and stabilizer theorems then supply the complete phase-geometric core. |
| 15 | `PaperAnalyticData.establishedActualEllipticRelatorNormalClosureResidual` | eliminate (S) | Connector-invariance reduces this to trace-compatible free homotopies from the projected regular filling loops to the expected affine relators. Axiom-clean local-degree arguments identify the order-three and order-four raw base loops with the inverse marked meridians cubed and fourth-powered. Both actual regular loops are identified pointwise in punctured real-period product coordinates and split endpoint-relatively into fibre-then-base paths. The order-three fibre factor is now explicitly swept from its local principal-gauge period to the corrected global cusp period, and the order-three base factor already reaches the zero-section triple. Their individual free-loop traces are not yet the same: the fibre sweep currently uses a path-connectedness witness while the base sweep uses the cubic zero-section trace and marked cusp whisker. Rebuild them over one common trace, or construct the whole-relator homotopy directly; unrelated conjugators are insufficient. For order four the remaining synchronization is still the single class-level transported-period identity. |

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
3. **S2:** row 11, the two marked-band Cayley/gauge calculations;
4. **S3:** refactor the final Mayer--Vietoris endpoint to degree-one bijectivity and degree-two
   surjectivity, then prove row 12's second suspension coefficient is a unit;
5. **S4:** prove row 13's meridian and index-four coefficients are units; the literal meridian's
   Wang sign is already computed;
6. **S5:** row 15, the two connector endpoint evaluations;
7. **T1:** correct the honeycomb tile/chart convention, then prove the corrected finite quotient
   and direct nonnegative toric atlas;
8. **T2:** row 14, positive contractibility and quotient relative CW;
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
8. Comparator reports only the three logical axioms and the seven approved general blackboxes.

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
- the resulting change, if any, in the eight-item transitional count.

If a route is false, first prove or document the counterexample, update this plan, and remove the
dead route from active work. The global dependency table—not file count—is the source of truth.

### Resume after the analytic-removal checkpoint

- **Toric:** `ConstructedA2PhaseBallBoundary` proves all effective phases on the closed base-ball
  boundary land in the existing two-skeleton. `ConstructedA2HexagonBoundaryPhaseGauge` constructs
  the continuous six-edge character gauge. The next step is its actual carrier compatibility
  with the existing real edges, then the remaining characteristic maps. Local draft
  `/private/tmp/s6-boundary-gauge.lean` has checked square-edge character constraints; its final
  phase-cancellation and axis-fixing additions are unverified.
- **Cusp:** the generic circle-cross and Wang naturality machinery is integrated. Local draft
  `/private/tmp/GlobalInvariantPeriodCircle.lean` constructs the invariant fourth-circle orbit
  through both quotients; its final base-coordinate lemmas are unverified. Match the actual cusp
  index-five representative modulo fibre classes and sweep the peripheral homotopy before making
  any claim that the scalar residual is false.
- **Elliptic:** recover first-power markings in the twice-punctured base's free fundamental group,
  where powers are injective, before projecting to the triangle group. The remaining geometric
  lemma identifies the local full filling base loop with the third/fourth power of its physical
  meridian with the same entering-sheet basepoint. Existing synchronized powered homotopies are
  in `PaperActualEllipticOrderThreeBaseFactorHomotopyProof` and
  `PaperActualEllipticOrderFourBaseFreeHomotopyProof`. This route is an audit finding, not a proof.

The temporary paths are local continuation notes, not trusted or imported project content.
