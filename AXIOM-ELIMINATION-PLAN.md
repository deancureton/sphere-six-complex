# Axiom-elimination plan

## Objective

The final Comparator report must contain exactly Lean's three standard logical axioms and four
general classical blackboxes:

\[
\{\mathsf{propext},\ \mathsf{Quot.sound},\ \mathsf{Classical.choice}\}
\cup \{\mathrm{Hurewicz},\ \mathrm{CWType},\ \mathrm{HomologicalWhitehead},
\mathrm{SmoothPoincare}_6\}.
\]

The present final theorem uses fifteen project axioms: four intended recognition inputs and eleven
transitional dependencies. The task is to replace the eleven transitional declarations by
theorems. Adding files, structures, or reductions does not count as progress unless it closes a
named milestone below or rules out a proposed route and updates this plan.

The paper-specific statements do not follow from Hurewicz or smooth Poincare. They must be proved
from the explicit construction and Mathlib. The four blackboxes enter only at the final recognition
stage, after the constructed complex threefold has been proved simply connected and to have the
integral homology of \(S^6\).

## The four permitted blackboxes

The current four declarations are useful interfaces, but three should be replaced by corollaries of
more general statements. The trusted statements must not mention this paper, the constructed
threefold, or the number six except where dimension six is intrinsic.

1. **Higher Hurewicz theorem.** Define the general Hurewicz homomorphism
   \(\pi_n(X,x)\to H_n(X;\mathbb Z)\), and assume the standard theorem that it is an isomorphism
   for an \((n-1)\)-connected space, for arbitrary \(n\ge 2\). Derive
   `establishedHigherHurewiczSixGenerator` at \(n=6\).

2. **Smooth manifolds have CW type.** Assume, in dimension-independent form, that a Hausdorff,
   second-countable finite-dimensional smooth manifold has the homotopy type of a CW complex, and
   that the model may be finite for a compact manifold. Derive
   `establishedCompactSmoothSixManifoldClassicalCWType` by forgetting the dimension and finiteness
   data.

3. **Homological Whitehead theorem.** Assume the general theorem that an integral-homology
   equivalence between simply connected spaces of CW type is a homotopy equivalence, with the given
   map as its forward map. Derive
   `establishedSimplyConnectedClassicalCWIntegralHomologyWhitehead` as a packaging theorem.

4. **Smooth Poincare in dimension six.** Retain the statement that every compact smooth
   six-manifold homotopy equivalent to \(S^6\) is diffeomorphic to the standard smooth sphere. This
   is the necessarily dimension-specific input combining generalized Poincare, smooth
   \(h\)-cobordism, and \(\Theta_6=0\).

The first three exact Lean signatures will be finalized before the allowlist is changed. A candidate
is rejected if it is merely a custom conclusion needed by this project rather than the usual
literature-level theorem.

No additional blackbox may be added silently. If Poincare duality, cellular homology, or analytic
descent later proves disproportionate to formalize, this document must first be amended with the
exact general theorem proposed for promotion and the reason it is independently auditable.

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

There are four largely independent implementation tracks:

- **C: classical infrastructure** - cellular homology and integral Poincare duality/UCT;
- **T: toric cusp** - the nonnegative \(A_2\) toric locus, honeycomb, CW atlas and incidence;
- **S: Section 7 topology** - finite specialization, marked bands, cusp coordinates and relators;
- **A: analytic descent** - the affine-line torsor correction at the orbifold cusp.

The recognition track is already assembled and should remain stable while C, T, S, and A remove
the eleven transitional axioms.

## The fifteen current dependencies

For every row marked **eliminate**, success means that the named declaration is a theorem (or all
consumers are redirected to an equivalent theorem), its name is absent from both axiom allowlists,
and Comparator passes.

| # | Current declaration | Disposition | Derivation plan |
|---|---|---|---|
| 1 | `establishedHigherHurewiczSixGenerator` | derive from blackbox 1 | Specialize the general Hurewicz isomorphism at \(n=6\), choose a generator of \(H_6(X)\cong\mathbb Z\), and represent it by a map \(S^6\to X\). |
| 2 | `establishedCompactSmoothSixManifoldClassicalCWType` | derive from blackbox 2 | Apply the general smooth-manifold CW theorem to `RealModel`, then forget finiteness and the dimension bound. |
| 3 | `establishedSimplyConnectedClassicalCWIntegralHomologyWhitehead` | derive from blackbox 3 | Unpack the two `ClassicalCWModel`s, transport the homology equivalence to their CW carriers, apply homological Whitehead, and transport the homotopy equivalence back. |
| 4 | `establishedSmoothPoincareSixStandardModel` | retain as blackbox 4 | Keep its current application-level wrapper, but make it a direct corollary of the single audited smooth-Poincare declaration if the trusted signature is renamed. |
| 5 | `establishedCompactSmoothOrientedManifoldHomologyTheory` | eliminate (C) | Build general integral Poincare duality and UCT in the singular/cellular chain API. Use blackbox 2 for a finite \(d\)-dimensional CW model; derive finite generation and vanishing above \(d\) from cellular chains. Assemble `IntegralPoincareUCTData d X`. |
| 6 | `EstablishedCellularHomology.integralCWCellularHomologyModel` | eliminate (C) | Construct the skeletal cellular chain complex, identify \(H_n(X^n,X^{n-1})\) with the free abelian group on \(n\)-cells, obtain the differential from the filtration exact couple, and prove comparison with integral singular homology. Preserve the explicit `T2Space` hypothesis. |
| 7 | `Periods.establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection` | eliminate (A) | Complete the existing local Cech reduction. Construct sections on the two quotient charts; split the overlap Laurent series into positive and negative parts for \(O\) and \(O(-1)\); average over the finite orbifold stabilizers; impose the two finite jets; subtract the cusp principal part; prove boundedness and removable extension. |
| 8 | `establishedStandardA2ToricCentralOrbitCellAtlas` | eliminate (T) | Finish explicit characteristic maps with cell counts \((2,3,4,2,1)\). Prove continuity, inverse continuity on open cells, disjoint interiors, attaching containment and coverage. Incorporate the phase-correction matrix into the maps or remove it by a proved equivariant gauge; do not assume cyclic covariance. |
| 9 | `establishedStandardA2ToricCentralFiberIndependentIncidenceResidual` | eliminate (T+C) | First tie the cellular differential to oriented characteristic-map attaching degrees; the current arbitrary `cellBasis` is insufficient. Compute the 24 independent entries from the explicit attaching maps. Derive the remaining four entries from \(d^2=0\) using the existing algebra. |
| 10 | `establishedFiniteFiberGeneratorSpecializationMatrix` | eliminate (S+T) | Construct `MarkedFiberCellularCoinvariantNaturality` for the labelled \(A_2\) cellular specialization. The existing reductions then turn this chain-level square into the four degree-one and sixteen degree-two Kronecker-delta identities. |
| 11 | `EstablishedSectionSevenAffineRegularLiftTopology.markedBandHomotopies` | eliminate (S) | Use the existing reduction to two pinned endpoint gauge formulas, or further to the two strict Cayley-radius inequalities at the selected actual-cusp crossing. Unfold the named radial lifts, prove the pinned-coordinate formulas, evaluate the two norms, and reuse the assembled homotopies. |
| 12 | `EstablishedSectionSevenCuspTopology.establishedCuspPulledBackMarkedInvariantBasisData` | eliminate (S) | Build the canonical two-leg or swapped-refinement Mayer--Vietoris naturality square. Compute the cover-swap orientation sign and the fourth band coordinate. Existing theorems already prove four basis cases; this supplies exactly raw basis values \(4\mapsto0\) and \(5\mapsto1\). |
| 13 | `EstablishedSectionSevenCuspTopology.establishedActualCuspFiberEllipticMarkedCoordinateResidual` | eliminate (S) | Prove the two remaining geometric identities: the 12-fold meridian/full-iterate relation in \(H_1\), and equality of the positive index-four side lift with the fourth raw cusp class in \(H_2\). Existing Wang, prism, basis and coordinate algebra then assemble the residual. |
| 14 | `StandardInfiniteA2ToricModel.Established.normalizedPolarHoneycombPhaseGeometry` | eliminate (T) | Replace the impossible pinned logarithmic coordinate with the nonnegative toric/PL model below. Construct the honeycomb homeomorphism, contractibility of the positive locus, and a relative CW structure on the positive-deck quotient. Existing invariant-modulus and stabilizer theorems then supply the complete phase-geometric core. |
| 15 | `PaperAnalyticData.establishedActualEllipticRelatorNormalClosureResidual` | eliminate (S) | Evaluate the order-three and order-four product-connector lifts at the filling-relation endpoints using explicit cover/deck formulas and path-lift uniqueness. Existing common-gauge, connector-coherence and chart-identity theorems turn those two endpoint equalities into the required normal-closure memberships. |

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
5. Finish `ConstructedA2HoneycombFiniteQuotientResidual.sameFibres` by a finite classification of
   the six square charts and their lattice translates. The same-chart and six cyclic-adjacent
   Laurent identities are already proved; all remaining chart-pair orbits must be enumerated.
6. Assemble `ConstructedPolarHoneycombResidualData`; use the existing invariant-modulus theorem to
   obtain the phase-geometric core.

The central CW atlas and its incidence table should be constructed from the same toric charts so
that rows 8, 9, 10, and 14 share one oriented coordinate system.

## Classical infrastructure route

Rows 5 and 6 are intentionally not hidden inside the four blackboxes in the first version of this
plan.

For cellular homology, define the filtration \(X^{-1}\subset X^0\subset\cdots\), the relative
singular complexes, and the exact couple. Excision and the homology of \((D^n,S^{n-1})\) give

\[
H_k(X^n,X^{n-1};\mathbb Z)\cong
\begin{cases}
\mathbb Z[\text{\(n\)-cells}],&k=n,\\
0,&k\ne n.
\end{cases}
\]

The resulting differential must be normalized by the chosen orientations of characteristic maps.
That normalization is also the missing bridge for row 9.

For a closed oriented smooth \(d\)-manifold, use the finite CW model, define singular cochains and
the cap product, construct the fundamental class from compatible local orientation classes, and
prove cap-product duality. The algebraic UCT for a finite free cellular complex then yields the
pairing and torsion information required by `IntegralPoincareUCTData`; finite generation and
dimension vanishing come from the CW model rather than from a bundled assumption.

These are large work packages, but their statements and artifacts are general-purpose algebraic
topology, not paper-specific escape hatches.

## Execution order

Work may proceed in parallel, but the preferred merge order is:

1. **S1:** row 10, the finite specialization matrix;
2. **S2:** row 11, the two marked-band Cayley/gauge calculations;
3. **S3:** row 12, the pulled-back invariant basis naturality square;
4. **S4:** row 13, the two remaining cusp geometric identities;
5. **S5:** row 15, the two connector endpoint evaluations;
6. **T1:** finish the honeycomb finite quotient and direct nonnegative toric atlas;
7. **T2:** row 14, positive contractibility and quotient relative CW;
8. **T3:** row 8, the complete central-orbit CW atlas;
9. **C1/T4:** rows 6 and 9, oriented cellular homology and the incidence table;
10. **C2:** row 5, compact oriented manifold Poincare/UCT data;
11. **A1:** row 7, orbifold Cousin correction;
12. replace rows 1--3 by corollaries of the three general blackboxes and run final recognition.

Rows 10--15 have narrow endpoint propositions already isolated in the repository and therefore
come first. Rows 5--9 are larger library/construction projects and should be split only along the
milestones stated here, not by inventing new residual structures.

## Progress accounting and acceptance

The progress number is the number of transitional allowlisted declarations removed:

\[
\mathrm{progress}=\frac{11-N_{\mathrm{transitional}}}{11}.
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
8. Comparator reports only the three logical axioms and the four approved general blackboxes.

The allowlist is changed only when a dependency is actually removed from the final theorem. It is
never changed to rename a paper-specific assumption or to replace it with an equivalent residual.

## Iteration protocol

Each work session should select one row and record:

- the exact current endpoint theorem;
- the next unconditional theorem to prove;
- whether that theorem directly closes the row or which listed milestone remains;
- any counterexample discovered to the proposed route;
- the resulting change, if any, in the eleven-item transitional count.

If a route is false, first prove or document the counterexample, update this plan, and remove the
dead route from active work. The global dependency table—not file count—is the source of truth.
