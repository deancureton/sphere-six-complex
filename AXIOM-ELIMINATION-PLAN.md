# Axiom-elimination plan

## Objective

The final Comparator report must contain exactly Lean's three standard logical axioms and seven
general classical blackboxes:

\[
\{\mathsf{propext},\ \mathsf{Quot.sound},\ \mathsf{Classical.choice}\}
\cup \{\mathrm{Hurewicz},\ \mathrm{CWType},\ \mathrm{HomologicalWhitehead},
\mathrm{SmoothPoincare}_6,\ \mathrm{CellularHomology},\ \mathrm{PoincareDualityUCT},
\mathrm{CartanB}\}.
\]

The present final theorem uses fifteen project axioms: six accepted classical inputs and nine
transitional dependencies. The task is to replace the nine transitional declarations by theorems.
The cellular input will be strengthened in place, and the analytic correction may introduce the
seventh accepted input only as Cartan Theorem B in its natural generality. Adding files,
structures, or reductions does not count as progress unless it closes a named milestone below or
rules out a proposed route and updates this plan.

The paper-specific statements do not follow from Hurewicz or smooth Poincare. They must be proved
from the explicit construction and Mathlib. The four recognition blackboxes enter only at the
final recognition stage. Cellular homology and Poincare duality/UCT enter while proving that the
constructed complex threefold has the integral homology of \(S^6\).

## The seven permitted blackboxes

The first four declarations are useful interfaces, but three should be replaced by corollaries of
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

5. **Integral cellular homology.** Retain one source-independent cellular-homology theorem in its
   natural skeletal-relative form: \(C_n^{\mathrm{cell}}(X)=H_n(X^n,X^{n-1};\mathbb Z)\), with
   differential induced by the relative connecting map and projection. Characteristic maps fix
   the oriented cell basis, boundary coefficients are the corresponding attaching-map degrees,
   cellular maps induce a functorial chain map, and the resulting homology is naturally isomorphic
   to integral singular homology. This does not require a noncanonical strict chain map from
   cellular chains to singular chains. Derive the present objectwise
   `integralCWCellularHomologyModel` from this theorem. The strengthened theorem must contain no
   application-specific incidence values or specialization matrices and replaces blackbox 5
   rather than adding another retained blackbox.

6. **Integral Poincare duality and UCT.** Retain the dimension-generic compact smooth oriented
   manifold theorem `establishedCompactSmoothOrientedManifoldHomologyTheory`. Its conclusion is
   only the standard complementary-degree dualities, finite generation, and vanishing above the
   manifold dimension.

7. **Cartan Theorem B.** Retain the standard theorem that the positive-degree sheaf cohomology of
   every coherent analytic sheaf on a Stein complex space vanishes. The blackbox must be stated for
   arbitrary Stein complex spaces and coherent analytic sheaves; it must not mention affine
   torsors, orbifold triangle groups, cusp corrections, or this paper. The finite-orbifold
   affine-torsor corollary and every descent, extension, and boundedness statement needed here must
   be derived in the repository.

The first three exact Lean signatures are now `generalHigherHurewiczClassSurjectivity`,
`finiteDimensionalSmoothManifoldHasClassicalCWType`, and
`simplyConnectedHomologicalWhitehead`. The old six-dimensional interfaces are proved corollaries.
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
| 1 | `establishedHigherHurewiczSixGenerator` | proved from blackbox 1 | Apply the class-surjectivity form of homological higher Hurewicz to a generator of \(H_6(X)\). The proved \(H_6(S^6)\cong\mathbb Z\) calculation shows the resulting sphere map is an isomorphism on top homology. |
| 2 | `establishedCompactSmoothSixManifoldClassicalCWType` | proved from blackbox 2 | Apply `finiteDimensionalSmoothManifoldHasClassicalCWType` to `RealModel`; compactness is not required by the general theorem. |
| 3 | `establishedSimplyConnectedClassicalCWIntegralHomologyWhitehead` | proved from blackbox 3 | Package `simplyConnectedHomologicalWhitehead`, stated elementwise for arbitrary simply-connected spaces of classical CW type, into the existing property interface. |
| 4 | `establishedSmoothPoincareSixStandardModel` | retain as blackbox 4 | Keep its current application-level wrapper, but make it a direct corollary of the single audited smooth-Poincare declaration if the trusted signature is renamed. |
| 5 | `establishedCompactSmoothOrientedManifoldHomologyTheory` | retain as blackbox 6 | General compact-oriented-manifold Poincare duality/UCT, with no paper-specific conclusion. |
| 6 | `EstablishedCellularHomology.integralCWCellularHomologyModel` | replace by blackbox 5 corollary | The current objectwise model leaves `cellBasis` and `homologyEquiv` unconstrained. Replace its axiom by a theorem derived from the general characteristic-map-compatible, natural cellular comparison in blackbox 5. |
| 7 | `Periods.establishedOrbifoldAffineLineTorsorCuspBoundedCousinCorrection` | eliminate (A) | Derive finite-orbifold affine-torsor triviality from general Cartan B using exactness of finite-group invariants over \(\mathbb C\). Construct the two compactified quotient orbifold charts, descend the affine actions to genuine torsors, prove extension across elliptic points and the cusp, descend the overlap coefficient, and establish the cusp bound. The existing projective-line Cech splitting then produces the correction. None of those project-specific bridges belongs in blackbox 7. |
| 8 | `establishedStandardA2ToricCentralOrbitCellAtlas` | eliminate (T) | Two cyclic phase-face maps are now genuine quotient-level injective `PartialEquiv` characteristic maps with unit-ball source and closed-ball continuity. Construct the remaining labelled 2-cells and the other dimensions, then prove inverse continuity on open cells, disjoint interiors, attaching containment and coverage. Incorporate the phase-correction matrix into the maps or remove it by a proved equivariant gauge. |
| 9 | `establishedStandardA2ToricCentralFiberIndependentIncidenceResidual` | eliminate (T+CF) | Foundation gate: the current arbitrary `cellBasis` does not determine signed incidence coefficients; changing basis signs changes the requested table without changing the objectwise homology model. First derive that model from the characteristic-map-compatible cellular theorem in blackbox 5. Then compute the 24 independent attaching degrees from the explicit toric maps and derive the remaining four entries from \(d^2=0\). |
| 10 | `establishedFiniteFiberGeneratorSpecializationMatrix` | eliminate (S+T+CF) | Foundation gate: pointwise identification of the four coordinate tori does not determine their labelled cellular coordinates while `homologyEquiv` may be postcomposed with an arbitrary automorphism. After blackbox 5 supplies a natural cellular-to-singular comparison, prove the relevant inclusions are cellular and compute their images in the characteristic-cell basis. This simultaneously fixes the degree-one normalized coordinates and the four degree-two entries. |
| 11 | `EstablishedSectionSevenAffineRegularLiftTopology.markedBandHomotopies` | eliminate (S) | The former attempt to deduce the pinned Cayley bounds from `starSeparation` is false: valid separation radii can be shrunk below both positive pinned norms. Variable overlap radii can approach the elliptic branch values in quotient coordinates, but this does not determine the covering sheet. Prove that the pinned lifts converge to the standard fixed points, or conjugate the collar markings by the existing common cusp-conjugator exponent, then reuse the assembled endpoint homotopies. |
| 12 | `EstablishedSectionSevenCuspTopology.establishedCuspPulledBackMarkedInvariantBasisData` | eliminate (S) | The adaptive cover, Wang comparison, cover-swap sign, and boundary naturality are proved. The remaining `ActualCuspAdaptiveBoundaryCarrierCompatibility` is exactly the oriented Wang-boundary/cover-connecting square. Prove its chain relation inside the cusp intersection; inclusion into the elliptic interior is not injective and loses the relevant band class, so the existing radial homotopy cannot be cancelled. |
| 13 | `EstablishedSectionSevenCuspTopology.establishedActualCuspFiberEllipticMarkedCoordinateResidual` | eliminate (S) | The literal angular collar loop is identified with `actualCuspAngularCentralLoop`; the abstract deck/Hurewicz meridian is also identified with the literal punctured-cusp angular loop and its mapping-torus image. Finish degree one by computing the transported loop's base-circle winding as \(-1\), which fixes the Wang-section sign. In degree two, prove that the positive index-four side lift includes as raw cusp basis index 4. |
| 14 | `StandardInfiniteA2ToricModel.Established.normalizedPolarHoneycombPhaseGeometry` | eliminate (T) | Replace the impossible pinned logarithmic coordinate with the nonnegative toric/PL model below. The explicit modulus now proves that contractibility of the full local carrier implies contractibility of the positive locus; construct that global contraction, the honeycomb homeomorphism, and a relative CW structure on the positive-deck quotient. Existing invariant-modulus and stabilizer theorems then supply the complete phase-geometric core. |
| 15 | `PaperAnalyticData.establishedActualEllipticRelatorNormalClosureResidual` | eliminate (S) | Connector-invariance is now proved: free homotopies from the two projected regular filling loops to representatives of the expected affine relators directly imply both normal-closure memberships, using the moving-basepoint traces as connectors. Construct those two explicit global free homotopies; no identity involving the arbitrary van Kampen connectors remains. |

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

## Classical infrastructure boundary

Rows 5 and 6 occupy the two retained cellular/Poincare foundation slots. Row 5 already has the
required natural generality. Row 6's current objectwise signature is insufficient for rows 9 and
10 because it leaves both `cellBasis` and `homologyEquiv` unconstrained. Blackbox 5 must therefore
be strengthened or replaced by the standard characteristic-map-compatible, natural cellular
comparison theorem, with the current objectwise model derived as a corollary. This keeps the
cellular foundation to one blackbox. It supplies only the general basis, boundary, and naturality
principles; every numerical incidence and specialization value remains a consequence of the
explicit toric construction.

Blackbox 7 is ordinary Cartan Theorem B, not its affine-torsor specialization. Proving the
finite-orbifold torsor corollary and connecting it to the paper's explicit charts is part of row 7.

## Execution order

Work may proceed in parallel, but the preferred merge order is:

1. **CF0:** replace the objectwise cellular-homology foundation with the general
   characteristic-map-compatible natural theorem and derive the existing model;
2. **S1:** row 10, the finite specialization matrix;
3. **S2:** row 11, the two marked-band Cayley/gauge calculations;
4. **S3:** row 12, the pulled-back invariant basis naturality square;
5. **S4:** row 13, the two remaining cusp geometric identities;
6. **S5:** row 15, the two connector endpoint evaluations;
7. **T1:** finish the honeycomb finite quotient and direct nonnegative toric atlas;
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
