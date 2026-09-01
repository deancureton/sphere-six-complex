# Axiom-elimination plan

## Objective

The current target for the final Comparator report is Lean's three standard logical axioms and a
small set of general classical blackboxes:

\[
\{\mathsf{propext},\ \mathsf{Quot.sound},\ \mathsf{Classical.choice}\}
\cup \{\mathrm{Hurewicz},\ \mathrm{HomologicalWhitehead},
\mathrm{SmoothPoincare}_6,\ \mathrm{CellularHomology},\ \mathrm{PoincareDuality},
\mathrm{CohomologicalUCT},\ \mathrm{SmoothTriangulation},
\mathrm{CartanB}\}.
\]

The displayed size is not a quota. This boundary may shrink, or one entry may be replaced by a more natural
literature theorem, as the formalization develops.  It may grow only when the additional entry is
a standard theorem in its usual generality, is independently auditable without understanding this
paper, and replaces a genuinely infeasible foundational development.  A specialized corollary,
even when mathematically true, is never an admissible blackbox.

The present final theorem uses sixteen project axioms: seven retained classical inputs and nine
transitional dependencies. The task is to replace the nine transitional declarations by theorems.
The cellular input has been strengthened in place, the former combined manifold-homology package
is now derived from general Poincare duality, UCT, and smooth triangulation, and the analytic
correction may introduce Cartan Theorem B only in its natural generality. Adding files,
structures, or reductions does not count as progress unless it closes a named milestone below or
rules out a proposed route and updates this plan.

The retained `classicalHigherHurewiczTheory` is the general classical theorem: it asserts the
existence of the natural higher Hurewicz homomorphism for arbitrary spaces and degrees and its
usual isomorphism property under the standard connectivity hypothesis. The application-shaped
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

The current boundary has seven entries. Cartan B may become an eighth only if the analytic track
genuinely needs it. The trusted statements
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

8. **Cartan Theorem B.** Retain the standard theorem that the positive-degree sheaf cohomology of
   every coherent analytic sheaf on a Stein complex space vanishes. The blackbox must be stated for
   arbitrary Stein complex spaces and coherent analytic sheaves; it must not mention affine
   torsors, orbifold triangle groups, cusp corrections, or this paper. The finite-orbifold
   affine-torsor corollary and every descent, extension, and boundedness statement needed here must
   be derived in the repository.

The final first three Lean signatures are intended to be `generalHigherHurewiczIsomorphism` for a
concretely defined canonical map, `finiteDimensionalSmoothManifoldClassicalCWModel`, and
`simplyConnectedHomologicalWhitehead`. The old application interfaces must be proved corollaries.
A candidate is rejected if it is merely a custom conclusion needed by this project rather than the
usual literature-level theorem.

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

The recognition track is already assembled and should remain stable while CF, T, S, and A remove
the nine transitional axioms.

## The fifteen current dependencies

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
| 7 | `Periods.establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection` | eliminate (A) | Derive finite-orbifold affine-torsor triviality from general Cartan B using exactness of finite-group invariants over \(\mathbb C\). Construct the two compactified quotient orbifold charts, descend the affine actions to genuine torsors, prove extension across elliptic points and the cusp, descend the overlap coefficient, and establish the cusp bound. The existing projective-line Cech splitting then produces the correction. None of those project-specific bridges belongs in blackbox 7. |
| 8 | `establishedStandardA2ToricCentralOrbitCellAtlas` | eliminate (T) | Two cyclic phase-face maps are genuine quotient-level injective `PartialEquiv` characteristic maps. The old planar-tile parametrization is disproved by an explicit counterexample. For the corrected embedding `C(v)=((2/3)v₀+(4/3)v₁, -(2/3)v₀+(2/3)v₁)`, same-cell, all positive and negative neighbor cases, the global Laurent iff, and the finite same-fibres equivalence are now proved. The corrected square-to-hexagon homeomorphism and positive central-fibre 2-cell satisfy the ball, sphere, continuity, inverse-continuity, closed-cell-image, and actual-open-orbit-injectivity requirements. The naive phase-zero quotient characteristic is not an atlas cell: the three translated boundary sides acquire the surviving compact phase `frozenCompactPhase N λ` and therefore need not land in the positive one-skeleton. Additivity and all six lattice-shear cancellation formulas are proved, as is a continuous flat cocycle extension across the hexagon, but that flat extension still varies in the surviving side character and is not the final cell. Construct sidewise phases modulo each edge stabilizer, glue them at the vanishing-coordinate vertices, extend the resulting boundary correction across the hexagon, and prove that corrected quotient boundary lands in the existing three one-cells. |
| 9 | `establishedStandardA2ToricCentralFiberIndependentIncidenceResidual` | eliminate (T+CF) | The strengthened foundation now reduces each coefficient to the homological degree of the actual characteristic attaching map. Row 8 must first identify the atlas `cellMap` fields with the explicit toric maps. Then compute the 24 independent degrees (beginning with the oriented interval boundary for edge 0) and derive the remaining four entries from \(d^2=0\). |
| 10 | `establishedFiniteFiberGeneratorSpecializationMatrix` | eliminate (S+T+CF) | The natural cellular-to-singular comparison is now available. Prove the relevant inclusions are cellular and compute their images in the characteristic-cell basis; this simultaneously fixes the degree-one normalized coordinates and the four degree-two entries. |
| 11 | `EstablishedSectionSevenAffineRegularLiftTopology.markedBandHomotopies` | eliminate (S) | The former attempt to deduce the identity-sheet Cayley bounds from `starSeparation` is false: valid separation radii can be shrunk below both positive pinned norms. Use the entering sheets already supplied at the pinned crossing and identify their two deck cosets with the common peripheral conjugator from `geometricCentralCuspConjugatorExponent`, modulo the respective elliptic stabilizers. Conjugate the two finite-cover markings by that common deck action; the existing clopen-sheet and endpoint-gauge theorems then give the band homotopies. No identity-sheet bound is a valid target. |
| 12 | `EstablishedSectionSevenCuspTopology.establishedCuspPulledBackMarkedInvariantBasisData` | eliminate (S) | The final Mayer--Vietoris endpoint now accepts the full marked matrix family with arbitrary index-four coefficient `a` and orientation-independent unit index-five coefficient `b`, expressed by `b*b=1`; an explicit integral inverse is proved. Thus the current exact values `a=0,b=1` are unnecessary. `ActualCuspAdaptiveBoundaryCarrierCompatibility` is equivalent to two stronger full-fibre comparisons, so prove only the second suspension coefficient is a unit from the two-leg cusp geometry. |
| 13 | `EstablishedSectionSevenCuspTopology.establishedActualCuspFiberEllipticMarkedCoordinateResidual` | eliminate (S) | Degree one needs only a unit meridian coefficient and degree two only `IsUnit a`. The full raw `[12,0,1]` source coordinate is proved. The global base phase `-4·phase(z)+3·phase(z-1)` corrects `12γ`; the radial homotopy is deck-invariant and has been descended through the additive cusp quotient, giving the corrected central mapping-torus character the same `[12,0,1]` coordinate. Extend that character over both elliptic filling pieces and identify the induced global winding, then prove the index-four side lift is primitive up to sign. |
| 14 | `StandardInfiniteA2ToricModel.Established.normalizedPolarHoneycombPhaseGeometry` | eliminate (T) | Replace the impossible pinned logarithmic coordinate with the nonnegative toric/PL model below. The explicit modulus now proves that contractibility of the full local carrier implies contractibility of the positive locus; construct that global contraction, the honeycomb homeomorphism, and a relative CW structure on the positive-deck quotient. Existing invariant-modulus and stabilizer theorems then supply the complete phase-geometric core. |
| 15 | `PaperAnalyticData.establishedActualEllipticRelatorNormalClosureResidual` | eliminate (S) | Connector-invariance reduces this to trace-compatible free homotopies from the projected regular filling loops to the expected affine relators. Axiom-clean local-degree arguments identify the order-three and order-four raw base loops with the inverse marked meridians cubed and fourth-powered. Both actual regular loops are identified pointwise in punctured real-period product coordinates and split endpoint-relatively into fibre-then-base paths. The order-three and order-four base factors each have an explicit traced free homotopy to the affine-based zero-section triple or quadruple, and both fibre factors have traced straightening homotopies to their local principal-gauge periods. For order four the entire synchronization is reduced to one class-level transported-period identity. Remaining work is to identify each local straight period with its corrected global marked period; horizontal composition then gives the complete relator homotopies. |

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

Blackbox 7 is ordinary Cartan Theorem B, not its affine-torsor specialization. Proving the
finite-orbifold torsor corollary and connecting it to the paper's explicit charts is part of row 7.

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
11. **A1:** derive the finite-orbifold torsor theorem from Cartan B and prove row 7's explicit
    descent and cusp bridges;
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
6. `lake exe cache get` precedes a successful full build;
7. import reachability, placeholder, axiom-catalog, and Comparator checks pass;
8. Comparator reports only the three logical axioms and the seven approved general blackboxes.

The allowlist is changed only when a dependency is actually removed from the final theorem. It is
never changed to rename a paper-specific assumption or to replace it with an equivalent residual.

## Iteration protocol

Each work session should select one row and record:

- the exact current endpoint theorem;
- the next unconditional theorem to prove;
- whether that theorem directly closes the row or which listed milestone remains;
- any counterexample discovered to the proposed route;
- the resulting change, if any, in the nine-item transitional count.

If a route is false, first prove or document the counterexample, update this plan, and remove the
dead route from active work. The global dependency table—not file count—is the source of truth.
