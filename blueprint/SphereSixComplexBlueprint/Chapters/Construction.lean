import Verso
import VersoBlueprint
import VersoManual
import SphereSixComplex.Construction
import SphereSixComplex.Geometry.AnalyticTorusFamily
import SphereSixComplex.Geometry.AtlasTransport
import SphereSixComplex.Geometry.ComplexTorus
import SphereSixComplex.Geometry.ComplexThreefoldGluing
import SphereSixComplex.Geometry.CuspCombinatorics
import SphereSixComplex.Geometry.CuspFilling
import SphereSixComplex.Geometry.EllipticComplexFilling
import SphereSixComplex.Geometry.EllipticFilling
import SphereSixComplex.Geometry.FamilyEquivariance
import SphereSixComplex.Geometry.Gluing
import SphereSixComplex.Geometry.GlobalTorusFamily
import SphereSixComplex.Geometry.PaperAssembly
import SphereSixComplex.Geometry.Quotient
import SphereSixComplex.Geometry.TorusFamily
import SphereSixComplex.LatticeData
import SphereSixComplex.Periods.Domain
import SphereSixComplex.Periods.CanonicalObstruction
import SphereSixComplex.Periods.Functions
import SphereSixComplex.Periods.Invariant
import SphereSixComplex.Periods.Matrix
import SphereSixComplex.Periods.Nondegeneracy
import SphereSixComplex.Periods.Transformations
import SphereSixComplex.Periods.TorsorAlgebra
import SphereSixComplex.Periods.ProjectiveLineTorsors
import SphereSixComplex.Periods.SchurCompactness
import SphereSixComplex.Topology.FundamentalGroup
import SphereSixComplex.Topology.FundamentalGroupComputation
import SphereSixComplex.Topology.HomologyComputation
import SphereSixComplex.Topology.HomologySphere
import SphereSixComplex.Topology.HurewiczWhitehead
import SphereSixComplex.Topology.MayerVietoris
import SphereSixComplex.Topology.SectionSevenChainModel
import SphereSixComplex.Topology.SmoothRecognition
import SphereSixComplex.Topology.SmoothRecognitionFoundations
import SphereSixComplex.Topology.SphereSimplyConnected
import SphereSixComplex.Topology.StandardSphere
import SphereSixComplex.Topology.TwistObstruction
import SphereSixComplex.TriangleGroup.ModularParameter
import SphereSixComplex.TriangleGroup.FuchsianAction
import SphereSixComplex.TriangleGroup.Representation

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Construction Spine" =>

This chapter follows the condensed Setup and Theorem on the first two PDF pages. Later sections of the
paper are consulted only when they are needed to prove one of these nodes.

:::group "construction_spine"
The minimal construction and recognition path.
:::

:::definition "lattice-monodromy-data" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.T₁, SphereSixComplex.LatticeData.T₂, SphereSixComplex.LatticeData.T₀, SphereSixComplex.LatticeData.A₁, SphereSixComplex.LatticeData.A₂, SphereSixComplex.LatticeData.M₀")
The rank-four lattice carries explicit local monodromies of orders three, four, and infinite order at
the cusp.
:::

:::theorem "monodromy-identities" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.T₁_det, SphereSixComplex.LatticeData.T₂_det, SphereSixComplex.LatticeData.T₁_pow_three, SphereSixComplex.LatticeData.T₂_pow_four, SphereSixComplex.LatticeData.N_sq, SphereSixComplex.LatticeData.A₁_mul_A₂_mul_M₀")
The displayed matrices are unimodular, the finite monodromies have exact orders three and four, and
the nilpotent part $`N = T_0-I` satisfies $`N^2=0`.
:::

:::proof "monodromy-identities"
Expand the four-by-four matrices and check every integral entry. The Lean proof is kernel checked and
does not use a native evaluator.
:::

:::theorem "triangle-representation" (parent := "construction_spine") (lean := "SphereSixComplex.TriangleGroup.rhoV, SphereSixComplex.TriangleGroup.rhoLambda, SphereSixComplex.TriangleGroup.rhoV_g₀, SphereSixComplex.TriangleGroup.rhoLambda_g₀")
The free product $`(\mathbb Z/3)*(\mathbb Z/4)` acts on the rank-four lattice and its dual with the
prescribed monodromies at the two elliptic points and the cusp.
:::

:::theorem "modular-parameter-action" (parent := "triangle-representation") (lean := "SphereSixComplex.TriangleGroup.rhoTau, SphereSixComplex.TriangleGroup.rhoTauReal_g1_smul, SphereSixComplex.TriangleGroup.rhoTauReal_g2_smul, SphereSixComplex.TriangleGroup.rhoTauReal_g0_smul")
The same triangle group acts on the upper half-plane by the displayed fractional-linear
transformations $`\tau \mapsto (\tau-1)/\tau`, $`\tau \mapsto -1/\tau`, and
$`\tau \mapsto \tau-1` at the cusp.
:::

:::proof "triangle-representation"
Descend the powers of $`T_1` and $`T_2` to the two cyclic factors, then use the coproduct universal
property. The cusp relation identifies the inverse product with $`T_0`.
:::

:::theorem "invariant-polarization" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.invariant_alternating_matrix_classification, SphereSixComplex.LatticeData.Q₀Matrix_T₁_invariant, SphereSixComplex.LatticeData.Q₀Matrix_T₂_invariant")
Every integral alternating form invariant under both finite monodromies is an integral multiple of
the displayed form $`Q_0`.
:::

:::theorem "dual-coinvariants" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.dualCoinvariantRelations_eq_ker_gamma, SphereSixComplex.LatticeData.dualCoinvariantsEquivInt")
The dual monodromy coinvariants form a free rank-one group detected by the invariant functional
$`\gamma`.
:::

:::theorem "atlas-transport" (parent := "construction_spine") (lean := "SphereSixComplex.isManifold_transportChartedSpace")
A manifold atlas and its differentiability structure transport along a homeomorphism without changing
the transition functions.
:::

:::proof "atlas-transport"
Conjugate every chart by the homeomorphism. In each transition map the conjugating maps cancel, leaving
the original transition map in the same structure groupoid.
:::

:::theorem "complex-quotient" (parent := "construction_spine") (lean := "SphereSixComplex.Geometry.quotientChartContDiff_of_contMDiff_smul, SphereSixComplex.Geometry.orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul")
A free properly discontinuous action by smooth translations gives the orbit space a manifold structure
and makes the quotient projection a local diffeomorphism.
:::

:::theorem "period-matrix-equivariance" (parent := "construction_spine") (lean := "SphereSixComplex.Periods.generatorOne_equivariance, SphereSixComplex.Periods.generatorTwo_equivariance, SphereSixComplex.Periods.cusp_equivariance")
The displayed period matrix transforms under the two elliptic generators and the cusp by the
prescribed dual monodromy matrices.
:::

:::proof "period-matrix-equivariance"
Substitute the three transformation laws for $`\tau,\mu,\beta` and verify the resulting matrix
identities entry by entry.
:::

:::theorem "period-lattice-nondegeneracy" (parent := "construction_spine") (lean := "SphereSixComplex.Periods.periodRealLinearEquiv, SphereSixComplex.Periods.setupInequalities_transformOne, SphereSixComplex.Periods.rhoParameters")
The Setup inequalities make the four period columns a real basis of $`\mathbb C^2`; the period domain
is preserved by the triangle-group action.
:::

:::theorem "period-functions" (parent := "construction_spine") (lean := "SphereSixComplex.Periods.Theorem3_4Existence") (priority := "high")
There are holomorphic functions $`\tau,\mu,\beta` on the upper half-plane satisfying the transformation,
cusp-growth, and nondegeneracy conditions listed in the Setup.
:::

:::proof "period-functions"
Use {uses "monodromy-identities"}[the monodromy identities], the distinct
$`(3,4,\infty)` source uniformization, and the two analytic torsor-vanishing arguments. Their
transformation laws feed
{uses "period-matrix-equivariance"}[the period-matrix equivariance identities].
:::

:::theorem "normalized-modular-function" (parent := "period-functions") (lean := "SphereSixComplex.Periods.normalizedJ_mdifferentiable, SphereSixComplex.Periods.normalizedJ_modular_invariant")
The normalized level-one modular function $`E_4^3/\Delta` is holomorphic on the upper half-plane and
invariant under $`\mathrm{SL}_2(\mathbb Z)`.
:::

:::theorem "identity-source-obstruction" (parent := "period-functions") (lean := "SphereSixComplex.Periods.rhoTauReal_g2_smul_twice, SphereSixComplex.Periods.not_exists_tau_mu_for_rhoTauReal, SphereSixComplex.Periods.not_nonempty_canonicalMuBetaEquivariantData")
The modular target upper half-plane cannot also serve as the source uniformizing upper half-plane.
The modular image of the order-four generator acts with order two, while the affine $`\mu` law has
genuine order four; identifying the two forces the impossible equation $`\tau=0`.
:::

:::theorem "fuchsian-source-action" (parent := "period-functions") (lean := "SphereSixComplex.TriangleGroup.orderOf_fuchsianOnePerm, SphereSixComplex.TriangleGroup.orderOf_fuchsianTwoPerm, SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint_fixed, SphereSixComplex.TriangleGroup.fuchsianTwoFixedPoint_fixed, SphereSixComplex.TriangleGroup.fuchsianSourceAction_g₀_apply, SphereSixComplex.TriangleGroup.fuchsianCuspRegion_invariant")
Explicit real special-linear matrices give the distinct source action of signature
$`(3,4,\infty)`: its elliptic generators have exact projective orders three and four, while the
cusp generator is a horizontal translation preserving the chosen horodisc.
:::

:::theorem "schur-compactness" (parent := "period-functions") (lean := "SphereSixComplex.Periods.PrePeriodFunctions.schurQuantity_invariant, SphereSixComplex.Periods.PrePeriodFunctions.schurQuantity_cusp_bounded_above, SphereSixComplex.Periods.PrePeriodFunctions.schurQuantity_bounded_above_of_compactCore, SphereSixComplex.Periods.PrePeriodFunctions.exists_shiftedPeriodFunctions")
The Schur quantity is continuous and invariant under the full triangle group. Its cusp-growth law
bounds it above on the distinguished horodisc; a compact core meeting every remaining orbit then
gives the global upper bound needed for the final imaginary shift of $`\beta`, producing the
nondegenerate period family.
:::

:::theorem "period-torsor-algebra" (parent := "period-functions") (lean := "SphereSixComplex.Periods.muAutomorphyOne_cycle, SphereSixComplex.Periods.muAutomorphyTwo_cycle, SphereSixComplex.Periods.betaCocycleOne_cycle, SphereSixComplex.Periods.betaCocycleTwo_cycle, SphereSixComplex.Periods.localBetaOne_transform, SphereSixComplex.Periods.localBetaTwo_transform")
The homogeneous automorphy factors and affine substitutions close around the order-three and
order-four orbits.  The inhomogeneous $`\beta` cocycles sum to zero, and weighted orbit sums give
the explicit local primitives used to build the two analytic torsors.
:::

:::theorem "projective-line-cech-splitting" (parent := "period-functions") (lean := "SphereSixComplex.Periods.ProjectiveLineCech.cechDifferentialNegOne_surjective, SphereSixComplex.Periods.ProjectiveLineCech.cechDifferentialZero_surjective, SphereSixComplex.Periods.ProjectiveLineCech.exists_compatible_negOne_adjustments, SphereSixComplex.Periods.ProjectiveLineCech.exists_compatible_zero_adjustments")
Every Laurent-polynomial overlap cocycle on the standard two-chart cover of the projective line is a
Čech coboundary for both $`\mathcal O(-1)` and $`\mathcal O`. This proves the algebraic splitting
underlying the paper's two torsor arguments; extending it to arbitrary holomorphic overlap functions
requires analytic Laurent-series infrastructure.
:::

:::theorem "torus-family" (parent := "construction_spine") (priority := "high")
The period matrix built from $`\tau,\mu,\beta` defines a proper holomorphic family of compact complex
two-tori over the thrice-punctured sphere.
:::

:::proof "torus-family"
Use {uses "period-functions"}[the period functions] to prove that each period subgroup is a lattice and
that the monodromy action descends freely away from the elliptic fixed points.
:::

:::theorem "complex-torus-fibres" (parent := "torus-family") (lean := "SphereSixComplex.Geometry.ComplexTorus.torus_compactSpace, SphereSixComplex.Geometry.ComplexTorus.torus_of_setupInequalities")
At each nondegenerate parameter, the four periods act freely and properly discontinuously by
holomorphic translations on $`\mathbb C^2`, and the quotient is a compact complex two-manifold.
:::

:::theorem "torus-family-equivariance" (parent := "torus-family") (lean := "SphereSixComplex.Geometry.FamilyEquivariance.rhoGOneTorusHomeomorph, SphereSixComplex.Geometry.FamilyEquivariance.rhoGTwoTorusHomeomorph, SphereSixComplex.Geometry.FamilyEquivariance.rhoGZeroTorusHomeomorph, SphereSixComplex.Geometry.FamilyEquivariance.generatorOneTorusHomeomorph_isLocalDiffeomorph")
The exact period-matrix identities descend to locally complex-diffeomorphic maps between the torus
quotients over all three triangle-group generators.
:::

:::theorem "global-torus-family-action" (parent := "torus-family") (lean := "SphereSixComplex.Geometry.GlobalTorusFamily.periodTransport_isComplexLinear, SphereSixComplex.Geometry.GlobalTorusFamily.parameterMap_equivariant, SphereSixComplex.Geometry.GlobalTorusFamily.regularDeckMap_orbitRel_iff, SphereSixComplex.Geometry.GlobalTorusFamily.regularFamilyDeckMap_mul, SphereSixComplex.Geometry.GlobalTorusFamily.PuncturedGlobalFamily")
Integral monodromy extends to complex-linear fibre transport for every triangle-group element.
The resulting deck action respects the varying period lattice and defines the punctured global
torus-family quotient before the three local fillings are attached.
:::

:::theorem "analytic-torus-family" (parent := "torus-family") (lean := "SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap_contMDiff, SphereSixComplex.Geometry.AnalyticTorusFamily.periodSection_contMDiff, SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap_compactUniformLowerBound, SphereSixComplex.Geometry.AnalyticTorusFamily.totalSpace_isManifold_and_projection_isLocalDiffeomorph")
The period domain is an open complex three-manifold, the analytic period map and every integral
period section are complex smooth.  Pointwise full rank gives a uniform lower bound over compact
base sets, hence a properly discontinuous quotient complex manifold with locally biholomorphic
projection.
:::

:::theorem "cusp-filling" (parent := "construction_spine") (priority := "high")
The unipotent end admits the toric filling whose central fibre is the opposite-edge quotient of the
degree-six del Pezzo surface.
:::

:::theorem "cusp-fan-combinatorics" (parent := "cusp-filling") (lean := "SphereSixComplex.Geometry.CuspCombinatorics.direction_sum_zero, SphereSixComplex.Geometry.CuspCombinatorics.direction_pair_det, SphereSixComplex.Geometry.CuspCombinatorics.hexagonRay_opposite, SphereSixComplex.Geometry.CuspCombinatorics.hexagonCone_det")
The three $`A_2` directions sum to zero and consecutive pairs form integral bases.  The six rays of
the degree-six del Pezzo fan occur in opposite pairs, and every two-dimensional cone is unimodular.
:::

:::theorem "cusp-action" (parent := "cusp-filling") (lean := "SphereSixComplex.Geometry.CuspFilling.shearMap_add, SphereSixComplex.Geometry.CuspFilling.CuspActionData.action_free, SphereSixComplex.Geometry.CuspFilling.CuspActionData.properlyDiscontinuous, SphereSixComplex.Geometry.CuspFilling.quotient_isQuotientCoveringMap, SphereSixComplex.Geometry.CuspFilling.cuspQuotient_isManifold, SphereSixComplex.Geometry.CuspFilling.cuspQuotient_projection_isLocalDiffeomorph")
The $`B_0` shear preserves the cusp height and translates both classes of $`A_2` triangles.  Given
the phase estimates of Theorem 4.5, the corrected maps form a free, properly discontinuous lattice
action.  Local sheets differ by analytic deck maps, so the covering quotient inherits a complex
manifold atlas.
:::

:::proof "cusp-filling"
Use {uses "torus-family"}[the torus family] and the unimodular cusp lattice map coming from
{uses "monodromy-identities"}[the explicit nilpotent monodromy].
:::

:::theorem "elliptic-fillings" (parent := "construction_spine") (lean := "SphereSixComplex.Geometry.epsilon_action_free, SphereSixComplex.Geometry.neg_epsilonPrime_action_free, SphereSixComplex.Geometry.quotient_isQuotientCoveringMap, SphereSixComplex.Geometry.epsilonQuotient_isManifold, SphereSixComplex.Geometry.negEpsilonPrimeQuotient_isManifold") (priority := "high")
The order-three and order-four ends admit free logarithmic-transform fillings with the twist vectors
specified in the Setup.  When the local affine actions are analytic, both covering quotients inherit
complex-manifold atlases.
:::

:::proof "elliptic-fillings"
Use {uses "torus-family"}[the torus family] and the invariant twist vectors fixed by $`A_1` and $`A_2`.
:::

:::theorem "compact-complex-threefold" (parent := "construction_spine") (lean := "SphereSixComplex.ComplexThreefold, SphereSixComplex.CompletedPaperThreefold, SphereSixComplex.exists_completedPaperThreefold") (priority := "high")
The global family and the three fillings glue to a compact connected complex threefold $`X`.
:::

:::proof "compact-complex-threefold"
Glue {uses "cusp-filling"}[the cusp filling] and
{uses "elliptic-fillings"}[the elliptic fillings] to the common collars of the punctured
{uses "torus-family"}[torus family], and verify the resulting charts and transition maps.
:::

:::theorem "manifold-gluing" (parent := "compact-complex-threefold") (lean := "SphereSixComplex.gluedChartedSpace, SphereSixComplex.isManifold_gluedChartedSpace, SphereSixComplex.compactSpace_gluedSpace, SphereSixComplex.connectedSpace_gluedSpace")
Compatible atlases on the filling pieces transport to their topological gluing and make the glued
space a manifold.  Finitely many compact pieces give a compact gluing, while connected pieces with
a connected overlap graph give a connected gluing.
:::

:::definition "complex-threefold-from-gluing" (parent := "compact-complex-threefold") (lean := "SphereSixComplex.complexThreefoldOfGluing")
A finite connected gluing of compact complex pieces with compatible complex and underlying real
atlases produces the exact compact connected `ComplexThreefold` contract used by the main theorem.
:::

:::theorem "paper-threefold-assembly" (parent := "compact-complex-threefold") (lean := "SphereSixComplex.completedPaperThreefoldOfGluing, SphereSixComplex.smoothRecognitionInputOfGluing")
If that gluing carries the concrete van Kampen generators with no extra relations and the
four-piece Mayer--Vietoris comparison, it produces the exact `CompletedPaperThreefold` object and
the simply connected integral-homology-sphere input for smooth recognition.
:::

:::theorem "fundamental-group" (parent := "construction_spine") (lean := "SphereSixComplex.CompletedPaperThreefold.fundamentalGroup") (priority := "high")
For the twists $`(\ell_0,\ell_1,\ell_2)=(0,1,-1)`, the fundamental group of $`X` is trivial.
:::

:::proof "fundamental-group"
Apply van Kampen to {uses "compact-complex-threefold"}[the glued threefold] and reduce the resulting
presentation using the explicit lattice coinvariants.
:::

:::theorem "twist-obstruction" (parent := "fundamental-group") (lean := "SphereSixComplex.Topology.TwistObstruction.abs_p, SphereSixComplex.Topology.TwistObstruction.obstruction_group_eq_zero")
For the chosen twist vectors the obstruction integer
$`12\ell_0-4\ell_1-3\ell_2` has absolute value one, so its cyclic quotient is trivial.
:::

:::theorem "fundamental-group-recognition" (parent := "fundamental-group") (lean := "SphereSixComplex.Topology.HasPaperFundamentalGroup, SphereSixComplex.Topology.simplyConnectedSpace_of_hasPaperFundamentalGroup")
Once van Kampen identifies the fundamental group with the obstruction group, the selected twists
make it trivial and hence make the path-connected threefold simply connected.
:::

:::theorem "fundamental-group-presentation" (parent := "fundamental-group") (lean := "SphereSixComplex.Topology.paperRelation_iff_classifier_zero, SphereSixComplex.Topology.paperPresentedGroupEquiv, SphereSixComplex.Topology.paperCanonicalEquiv, SphereSixComplex.Topology.HasVanKampenData.hasVanKampenPresentation, SphereSixComplex.Topology.HasVanKampenPresentation.hasPaperFundamentalGroup")
The three van Kampen generators reduce to a two-generator integral presentation.  Its relation
lattice is exactly the kernel of the cyclic classifier, so the quotient has order
$`|12\ell_0-4\ell_1-3\ell_2|`.  Concrete generators satisfying the relations, generating the
fundamental group, and having no additional exponent relations give the canonical presentation;
for the selected twists it supplies the paper's fundamental-group contract.
:::

:::theorem "integral-homology" (parent := "construction_spine") (lean := "SphereSixComplex.CompletedPaperThreefold.integralHomology") (priority := "high")
The integral homology of $`X` is the integral homology of $`S^6`.
:::

:::proof "integral-homology"
Compute the Mayer--Vietoris sequence of {uses "compact-complex-threefold"}[the same gluing], including
the integral specialization maps and their saturation.
:::

:::definition "homology-sphere-contract" (parent := "integral-homology") (lean := "SphereSixComplex.HasIntegralHomologyOfSixSphere, SphereSixComplex.SixSphereRecognitionInput")
The recognition input records path connectedness, simple connectedness, and degreewise integral
singular homology equivalence with the standard six-sphere.
:::

:::definition "mayer-vietoris-contract" (parent := "integral-homology") (lean := "SphereSixComplex.FourPieceMayerVietorisExactness, SphereSixComplex.FourPieceHomologyComputation, SphereSixComplex.FourPieceMayerVietorisContract.hasIntegralHomologyOfSixSphere")
The four-piece gluing is organized into three successive open unions.  Mayer--Vietoris exactness is
separated from the final finite chain-level computation, expressed as a quasi-isomorphism to the
integral singular chains of $`S^6`.
:::

:::theorem "section-seven-integer-algebra" (parent := "integral-homology") (lean := "SphereSixComplex.firstHomologyPresentation_exact, SphereSixComplex.alphaOne_kernel, SphereSixComplex.alphaTwoPresentation_exact, SphereSixComplex.chosenLerayDifferential_bijective, SphereSixComplex.hasIntegralHomologyOfSixSphere_of_sectionSevenRealizations")
The integral presentation, specialization, and Leray differential matrices from Section 7 have the
claimed kernels and images.  For the selected twists the final differential is an isomorphism; an
explicit realization contract records the remaining passage from these matrices to singular homology.
:::

:::theorem "section-seven-chain-model" (parent := "integral-homology") (lean := "SphereSixComplex.sectionSevenFirstBoundaryMatrix_det, SphereSixComplex.sectionSevenDegreeOneCellularComplex_homology_one_isZero, SphereSixComplex.sectionSevenDegreeOneCellularComplex_homology_two_isZero, SphereSixComplex.integralSingularHomology_one_subsingleton_of_sectionSevenCellularComparison")
The first two paper relations and final attachment form an explicit unimodular boundary matrix.
The resulting finite chain complex has zero homology in degrees one and two; a degreewise
cellular-to-singular comparison transfers this calculation to singular homology.
:::

:::theorem "smooth-recognition" (parent := "construction_spine") (lean := "SphereSixComplex.completedPaperThreefold_smoothRecognition, SphereSixComplex.exists_complex_threefold_diffeomorphic_sixSphere") (priority := "high")
The underlying standard smooth manifold of $`X` is diffeomorphic to $`S^6`.
:::

:::definition "smooth-recognition-obligations" (parent := "smooth-recognition") (lean := "SphereSixComplex.HomologyToHomotopySixSphereObligation, SphereSixComplex.HomotopyToDiffeomorphismSixSphereObligation, SphereSixComplex.smoothSixSphereRecognition_of_obligations")
The recognition step splits into the Whitehead--Hurewicz implication from a simply-connected
integral homology sphere to a homotopy sphere, followed by the dimension-six smooth Poincaré
classification.  Their composition gives the exact diffeomorphism required by the construction.
:::

:::theorem "hurewicz-whitehead-reduction" (parent := "smooth-recognition") (lean := "SphereSixComplex.HasIntegralHomologyComparisonToSixSphere, SphereSixComplex.homotopyEquivSixSphere_of_comparison_of_whitehead, SphereSixComplex.homologyToHomotopySixSphere_of_comparison_of_whitehead")
The homology-to-homotopy step is reduced to constructing one coherent integral-homology comparison
map $`X \to S^6` and applying the integral-homology Whitehead property to that map. Homotopy
equivalences are proved to induce integral singular-homology equivalences using Mathlib's homotopy
invariance theorem.
:::

:::theorem "smooth-recognition-foundations" (parent := "smooth-recognition") (lean := "SphereSixComplex.SmoothSimplyConnectedIntegralHomologySixSphere.homotopyGroup_zero_subsingleton, SphereSixComplex.SmoothSimplyConnectedIntegralHomologySixSphere.homotopyGroup_one_subsingleton, SphereSixComplex.homotopyToDiffeomorphismSixSphere_iff_topologicalPoincare_and_noExotic, SphereSixComplex.smoothSixSphereRecognition_of_comparison_whitehead_and_classification")
Simple connectivity kills the cubical zeroth and first homotopy groups. The remaining recognition
chain factors exactly through the Hurewicz--Whitehead comparison, generalized topological Poincaré,
and the dimension-six absence of exotic smooth spheres.
:::

:::proof "smooth-recognition"
Combine {uses "fundamental-group"}[simple connectedness] and
{uses "integral-homology"}[integral homology] to obtain a homotopy sphere, then use six-dimensional
smooth homotopy-sphere recognition.
:::

:::theorem "standard-six-sphere" (parent := "smooth-recognition") (lean := "SphereSixComplex.sixSphere_isCompact, SphereSixComplex.sixSphere_isPathConnected, SphereSixComplex.sixSphere_isManifold")
The target $`S^6` is compact, path-connected, and carries the standard smooth six-manifold atlas.
:::

:::theorem "sphere-stereographic-simple-connectivity" (parent := "standard-six-sphere") (lean := "SphereSixComplex.sixSphere_compl_singleton_simplyConnected, SphereSixComplex.sixSphere_simplyConnected_iff_loops_nullhomotopic")
Removing any point from the standard six-sphere gives a simply-connected Euclidean chart.  Global
simple connectedness is reduced exactly to nullhomotopy of every based loop.
:::
