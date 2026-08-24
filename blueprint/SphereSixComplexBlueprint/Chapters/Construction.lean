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
import SphereSixComplex.Geometry.CyclicCuspQuotient
import SphereSixComplex.Geometry.EllipticComplexFilling
import SphereSixComplex.Geometry.EllipticFilling
import SphereSixComplex.Geometry.EllipticCayleyHomeomorph
import SphereSixComplex.Geometry.EllipticFamilySpecialization
import SphereSixComplex.Geometry.EllipticFixedPointCriterion
import SphereSixComplex.Geometry.EllipticLocalCoordinates
import SphereSixComplex.Geometry.EllipticLocalTrivialization
import SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
import SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
import SphereSixComplex.Geometry.FamilyEquivariance
import SphereSixComplex.Geometry.FuchsianRegularTorusFamily
import SphereSixComplex.Geometry.Gluing
import SphereSixComplex.Geometry.GlobalTorusFamily
import SphereSixComplex.Geometry.GlobalDeckSmoothness
import SphereSixComplex.Geometry.GlobalDeckQuotient
import SphereSixComplex.Geometry.PaperAssembly
import SphereSixComplex.Final
import SphereSixComplex.Geometry.Quotient
import SphereSixComplex.Geometry.RegularBaseTopology
import SphereSixComplex.Geometry.RegularTorusFamily
import SphereSixComplex.Geometry.TorusFamily
import SphereSixComplex.LatticeData
import SphereSixComplex.Periods.Domain
import SphereSixComplex.Periods.CanonicalObstruction
import SphereSixComplex.Periods.Functions
import SphereSixComplex.Periods.EstablishedModularUniformization
import SphereSixComplex.Periods.EstablishedProjectiveLineCohomology
import SphereSixComplex.Periods.FuchsianCompactCore
import SphereSixComplex.Periods.FuchsianModularParameterExistence
import SphereSixComplex.Periods.FuchsianMuTorsor
import SphereSixComplex.Periods.FuchsianUniformizationBridge
import SphereSixComplex.Periods.Invariant
import SphereSixComplex.Periods.LocalOrbifoldCompatibility
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
import SphereSixComplex.Topology.SectionSevenLerayChainModel
import SphereSixComplex.Topology.SectionSevenLerayDuality
import SphereSixComplex.Topology.SectionSevenLerayChainDuality
import SphereSixComplex.Topology.SectionSevenLerayHomologyDuality
import SphereSixComplex.Topology.SectionSevenLerayRealization
import SphereSixComplex.Topology.EstablishedMayerVietoris
import SphereSixComplex.Topology.EstablishedRecognition
import SphereSixComplex.Topology.EstablishedSphereHomology
import SphereSixComplex.Topology.SmoothRecognition
import SphereSixComplex.Topology.SmoothRecognitionFoundations
import SphereSixComplex.Topology.SphereSimplyConnected
import SphereSixComplex.Topology.StandardSphere
import SphereSixComplex.Topology.StandardSphereHomologyZero
import SphereSixComplex.Topology.DiskBoundaryQuotient
import SphereSixComplex.Topology.RelativeSingularHomology
import SphereSixComplex.Topology.SingularExcision
import SphereSixComplex.Topology.SingularBarycentricAllDegrees
import SphereSixComplex.Topology.SingularBarycentricOuterFaces
import SphereSixComplex.Topology.SingularBarycentricHomotopy
import SphereSixComplex.Topology.SingularBarycentricChains
import SphereSixComplex.Topology.SingularSubdivision
import SphereSixComplex.Topology.TwistObstruction
import SphereSixComplex.TriangleGroup.ModularParameter
import SphereSixComplex.TriangleGroup.FuchsianAction
import SphereSixComplex.TriangleGroup.FuchsianArithmetic
import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
import SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
import SphereSixComplex.TriangleGroup.FuchsianPingPong
import SphereSixComplex.TriangleGroup.FuchsianTessellation
import SphereSixComplex.TriangleGroup.FuchsianTriangleCover
import SphereSixComplex.TriangleGroup.FuchsianSmoothAction
import SphereSixComplex.TriangleGroup.FreeProductTorsion
import SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
import SphereSixComplex.TriangleGroup.FuchsianProperFreeness
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

:::theorem "fuchsian-source-action" (parent := "period-functions") (lean := "SphereSixComplex.TriangleGroup.orderOf_fuchsianOnePerm, SphereSixComplex.TriangleGroup.orderOf_fuchsianTwoPerm, SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint_fixed, SphereSixComplex.TriangleGroup.fuchsianTwoFixedPoint_fixed, SphereSixComplex.TriangleGroup.fuchsianSourceAction_g₀_apply, SphereSixComplex.TriangleGroup.fuchsianCuspRegion_invariant, SphereSixComplex.TriangleGroup.fuchsianSourceAction_contMDiff, SphereSixComplex.TriangleGroup.explicitFuchsianTriangleSource")
Explicit real special-linear matrices give the distinct source action of signature
$`(3,4,\infty)`: its elliptic generators have exact projective orders three and four, while the
cusp generator is a horizontal translation preserving the chosen horodisc. Every group element
acts complex-smoothly by free-product induction.
:::

:::theorem "fuchsian-source-faithfulness" (parent := "fuchsian-source-action") (lean := "SphereSixComplex.TriangleGroup.FuchsianPingPong.inl_maps_left_to_right, SphereSixComplex.TriangleGroup.FuchsianPingPong.inr_maps_right_to_left, SphereSixComplex.TriangleGroup.FuchsianPingPong.factorAction_ping_pong, SphereSixComplex.TriangleGroup.FuchsianPingPong.fuchsianSourceAction_injective")
The two real half-planes form ping-pong regions for the cyclic factors. Hence the explicit
projective source representation of their free product is faithful.
:::

:::theorem "fuchsian-fundamental-region" (parent := "fuchsian-source-action") (lean := "SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain.fuchsianOneFixedPoint_mem_fundamentalTriangle, SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain.fuchsianTwoFixedPoint_mem_fundamentalTriangle, SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain.gOne_rightSide_normSq, SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain.gTwo_leftSide_normSq, SphereSixComplex.TriangleGroup.FuchsianTriangleCover.orientedFundamentalRegion, SphereSixComplex.TriangleGroup.FuchsianTriangleCover.exists_smul_mem_orientedFundamentalRegion")
The explicit triangle is one reflection chamber. Since $`\Delta=C_3*C_4` is the
orientation-preserving subgroup, its fundamental region is the union of two adjacent chambers.
Every upper-half-plane point has a $`\Delta`-translate in this doubled region.
:::

:::theorem "fuchsian-reduction" (parent := "fuchsian-fundamental-region") (lean := "SphereSixComplex.TriangleGroup.FuchsianTessellation.product_zpow_apply, SphereSixComplex.TriangleGroup.FuchsianTessellation.exists_product_zpow_mem_centered_strip, SphereSixComplex.TriangleGroup.FuchsianTessellation.reductionStep_mem_or_im_lt, SphereSixComplex.TriangleGroup.FuchsianTessellation.exists_smul_mem_coarseFordRegion")
Integral cusp powers center every point in a fixed strip. Outside the coarse Ford region, the
order-three generator strictly raises height. An orbit-height maximum therefore supplies a
translate in the region.
:::

:::theorem "fuchsian-arithmetic" (parent := "fuchsian-reduction") (lean := "SphereSixComplex.TriangleGroup.FuchsianArithmetic.quadraticProjectiveRepresentation, SphereSixComplex.TriangleGroup.FuchsianArithmetic.quadraticProjectiveRepresentation_inl_generator, SphereSixComplex.TriangleGroup.FuchsianArithmetic.quadraticProjectiveRepresentation_inr_generator, SphereSixComplex.TriangleGroup.FuchsianArithmetic.positive_bottomRow_bounded_of_normSq_le, SphereSixComplex.TriangleGroup.FuchsianArithmetic.finite_bottomRows_of_normSq_le_of_conjugate_bounded")
The Fuchsian generators lift to an explicit projective representation over $`\mathbb Z[\sqrt2]`.
Paired real embeddings make bounded denominator sublevels finite once the conjugate bottom rows are
uniformly bounded. The coefficient-cone invariant below supplies this bound.
:::

:::theorem "fuchsian-arithmetic-termination" (parent := "fuchsian-arithmetic") (lean := "SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.wordMatrix_matrixInCoefficientCone, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.finite_wordBottomRows_of_normSq_le, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.exists_fuchsian_orbitHeightMaximal, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.exists_smul_mem_coarseFordRegion, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.fuchsianSourceAction_properlyDiscontinuous, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.sourceActionProperlyDiscontinuous_of_eq, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.fuchsianRegular_isCancelSMul")
Reduced words have entrywise conjugate norm bounded by the distinguished embedding. Consequently,
denominator sublevels are finite, orbit heights attain maxima, every orbit meets the coarse Ford
region, and the source action is properly discontinuous. The regular-locus action is free.
:::

:::theorem "fuchsian-compact-core" (parent := "fuchsian-fundamental-region") (lean := "SphereSixComplex.Periods.orientedFuchsianCompactCore_isCompact, SphereSixComplex.Periods.orientedFundamentalRegion_mem_cusp_or_compactCore, SphereSixComplex.Periods.orientedFuchsianQuotientCompactCore, SphereSixComplex.Periods.FuchsianPrePeriodData.theorem3_4Existence_of_orientedTriangleCover")
The part of the doubled fundamental region below the standard horodisc lies in an explicit compact
rectangle. This gives the compact quotient core required by the Schur argument and converts
Fuchsian pre-period data into the full period family without a false single-chamber premise.
:::

:::theorem "fuchsian-uniformization-bridge" (parent := "period-functions") (lean := "SphereSixComplex.Periods.FuchsianModularParameter.equivariant, SphereSixComplex.Periods.FuchsianModularParameter.coordinate_invariant, SphereSixComplex.Periods.FuchsianModularParameter.toTriangleUniformization, SphereSixComplex.Periods.FuchsianPrePeriodData.toPrePeriodFunctions, SphereSixComplex.Periods.FuchsianPrePeriodData.theorem3_4Existence")
The two generator laws for a holomorphic modular parameter extend to the full free product. Its
normalized modular invariant supplies the quotient coordinate, and explicit additive period data
plus a compact quotient core gives the nondegenerate period family.
:::

:::definition "normalized-fuchsian-modular-lift-obligation" (parent := "fuchsian-uniformization-bridge") (lean := "SphereSixComplex.Periods.ExactFuchsianOrbifoldCoordinate, SphereSixComplex.Periods.ExactNormalizedModularJUniformization, SphereSixComplex.Periods.NormalizedFuchsianModularJLiftingExistence, SphereSixComplex.Periods.establishedExactFuchsianOrbifoldCoordinate, SphereSixComplex.Periods.establishedExactNormalizedModularJUniformization, SphereSixComplex.Periods.establishedNormalizedFuchsianModularJLifting, SphereSixComplex.Periods.exists_establishedFuchsianModularParameter")
Exact source and modular quotient uniformization, and the compatible branched-lifting theorem, are
explicit classical external inputs. Their statements include orbit fibres, special values, exact
elliptic branching, ordinary covering away from the branch values, and a simple completed cusp.
They produce the normalized modular parameter; arbitrary invariant holomorphic functions are not
admitted.
:::

:::theorem "local-orbifold-compatibility" (parent := "period-functions") (lean := "SphereSixComplex.Periods.orderOf_targetOnePerm, SphereSixComplex.Periods.orderOf_targetTwoPerm, SphereSixComplex.Periods.explicitLocalOrbifoldActionData, SphereSixComplex.Periods.IsLocallyOrbifoldCompatible.invariant_under_two_square, SphereSixComplex.Periods.IsLocallyOrbifoldCompatible.cusp_value_translation")
The order-three source and target actions agree, while the order-four source stabilizer maps to an
order-two target stabilizer. The explicit source and target cusp widths give the local branching
and translation conditions that the analytic modular parameter must satisfy.
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

:::theorem "projective-line-cech-splitting" (parent := "period-functions") (lean := "SphereSixComplex.Periods.ProjectiveLineCech.cechDifferentialNegOne_surjective, SphereSixComplex.Periods.ProjectiveLineCech.cechDifferentialZero_surjective, SphereSixComplex.Periods.establishedProjectiveLineCechNegOne, SphereSixComplex.Periods.establishedProjectiveLineCechZero, SphereSixComplex.Periods.exists_compatibleProjectiveLineNegOneAdjustments, SphereSixComplex.Periods.exists_compatibleProjectiveLineZeroAdjustments")
Every Laurent-polynomial overlap cocycle on the standard two-chart cover of the projective line is a
Čech coboundary for both $`\mathcal O(-1)` and $`\mathcal O`. The corresponding analytic Laurent
splittings for arbitrary holomorphic functions on $`\mathbb C^\times` are explicit established
external inputs. The remaining paper-specific task is to descend the $`\mu`- and $`\beta`-torsors
to these exact overlap cocycles.
:::

:::theorem "fuchsian-mu-torsor-descent" (parent := "projective-line-cech-splitting") (lean := "SphereSixComplex.Periods.MuTorsorCechLocalData, SphereSixComplex.Periods.exists_compatibleAdjustedMuSections, SphereSixComplex.Periods.gluedAdjustedMu_holomorphic, SphereSixComplex.Periods.gluedAdjustedMu_transform_one, SphereSixComplex.Periods.gluedAdjustedMu_transform_two, SphereSixComplex.Periods.gluedAdjustedMu_cusp_bounded, SphereSixComplex.Periods.exists_globalFuchsianMu")
Exact local $`\mathcal O(-1)` torsor data on two invariant quotient charts glues to a global
holomorphic $`\mu` with both affine generator laws and the required cusp bound. The remaining
paper-specific input is the construction of that local quotient-chart data and its infinity-frame
estimate; the global Čech correction and gluing are complete.
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

:::theorem "global-torus-family-action" (parent := "torus-family") (lean := "SphereSixComplex.Geometry.GlobalTorusFamily.periodTransport_isComplexLinear, SphereSixComplex.Geometry.GlobalTorusFamily.parameterMap_equivariant, SphereSixComplex.Geometry.GlobalTorusFamily.regularDeckMap_orbitRel_iff, SphereSixComplex.Geometry.GlobalTorusFamily.regularFamilyDeckMap_mul, SphereSixComplex.Geometry.GlobalTorusFamily.regularParameterMap_compactUniformLowerBound, SphereSixComplex.Geometry.GlobalTorusFamily.regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph, SphereSixComplex.Geometry.GlobalTorusFamily.regularFamilyDeckMap_contMDiff, SphereSixComplex.Geometry.GlobalTorusFamily.regularFamilyDeckAction_isCancelSMul_of_fuchsian, SphereSixComplex.Geometry.GlobalTorusFamily.regularFamilyDeckAction_properlyDiscontinuous_of_source, SphereSixComplex.Geometry.GlobalTorusFamily.puncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph, SphereSixComplex.Geometry.GlobalTorusFamily.fuchsianPuncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph, SphereSixComplex.Geometry.GlobalTorusFamily.PuncturedGlobalFamily")
Integral monodromy extends to complex-linear fibre transport for every triangle-group element.
The resulting deck action respects the varying period lattice and defines the punctured global
torus-family quotient before the three local fillings are attached. The regular lattice quotient
and every descended deck map are complex smooth. Source freeness and proper discontinuity transfer
through both quotients, giving the punctured family a complex-threefold atlas with locally
biholomorphic projection.
:::

:::theorem "elliptic-orbit-freeness" (parent := "torus-family") (lean := "SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.deltaIndexedEquiv, SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.deltaNormalForm, SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.finiteOrder_isConj_inl_or_inr, SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.finiteOrder_fixed_regular_eq_one, SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_inl_fixed_iff, SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_inr_fixed_iff, SphereSixComplex.TriangleGroup.FuchsianProperFreeness.isOfFinOrder_of_fixed_of_properlyDiscontinuous, SphereSixComplex.TriangleGroup.FuchsianProperFreeness.fuchsian_fixed_regular_eq_one, SphereSixComplex.TriangleGroup.FuchsianProperFreeness.regularLiftedDeckAction_isCancelSMul_of_fuchsian, SphereSixComplex.TriangleGroup.FuchsianProperFreeness.regularLiftedDeckAction_properlyDiscontinuous_of_source")
Every nonidentity element of either cyclic factor fixes exactly its marked elliptic point, and its
conjugates fix exactly the corresponding elliptic orbit. Removing those orbits eliminates all such
stabilizers. An explicit equivalence with the indexed free product proves every nontrivial
finite-order element is conjugate into a factor. Proper discontinuity makes point stabilizers
finite and therefore proves the regular action free; both properties then lift to the deck action.
The remaining step is proper discontinuity of the explicit projective Fuchsian source action.
:::

:::theorem "regular-base-topology" (parent := "elliptic-orbit-freeness") (lean := "SphereSixComplex.Geometry.GlobalTorusFamily.sourceOrbitSingletons_locallyFinite, SphereSixComplex.Geometry.GlobalTorusFamily.sourceOrbitSet_isClosed, SphereSixComplex.Geometry.GlobalTorusFamily.isOpen_isRegularBasePoint, SphereSixComplex.Geometry.GlobalTorusFamily.regularBase_isManifold, SphereSixComplex.Geometry.GlobalTorusFamily.regularDeckMap_contMDiff")
Proper discontinuity makes both elliptic orbits locally finite and closed. Their complement is
therefore an open complex one-manifold, giving the correct regular base for the punctured family.
Every lifted deck transformation restricts to a complex-smooth map over this base.
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

:::theorem "cyclic-cusp-quotient" (parent := "cusp-filling") (lean := "SphereSixComplex.Geometry.CyclicCuspQuotient.cuspTranslate_eq_fuchsian_gZero_zpow, SphereSixComplex.Geometry.CyclicCuspQuotient.cuspHorodisc_action_free, SphereSixComplex.Geometry.CyclicCuspQuotient.cuspHorodisc_action_properlyDiscontinuous, SphereSixComplex.Geometry.CyclicCuspQuotient.cuspHorodisc_quotient_isQuotientCoveringMap, SphereSixComplex.Geometry.CyclicCuspQuotient.cuspProduct_generator_agrees_with_familyDeckMap")
The explicit parabolic source generator acts by integer translations of the invariant horodisc.
This cyclic action and its product lift are free, properly discontinuous covering actions.
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

:::theorem "elliptic-local-coordinates" (parent := "elliptic-fillings") (lean := "SphereSixComplex.Geometry.EllipticLocalCoordinates.norm_cayleyCoordinate_lt_one, SphereSixComplex.Geometry.EllipticLocalCoordinates.orderThreeCayley_generator, SphereSixComplex.Geometry.EllipticLocalCoordinates.orderFourCayley_generator, SphereSixComplex.Geometry.EllipticCayleyHomeomorph.cayleyHomeomorph, SphereSixComplex.Geometry.EllipticCayleyHomeomorph.orderThreeCayleyHomeomorph_generator, SphereSixComplex.Geometry.EllipticCayleyHomeomorph.orderFourCayleyHomeomorph_generator, SphereSixComplex.Geometry.EllipticLocalCoordinates.EllipticFiberData.orderThreeActionData_quotient_isManifold, SphereSixComplex.Geometry.EllipticLocalCoordinates.EllipticFiberData.orderFourActionData_quotient_isManifold")
The explicit Cayley formulas give homeomorphisms from the upper half-plane to the unit disc and
conjugate the source generators to rotations of orders three and four. The remaining affine fibre
data then gives the free logarithmic-transform quotient manifolds.
:::

:::theorem "elliptic-local-trivialization" (parent := "elliptic-local-coordinates") (lean := "SphereSixComplex.Geometry.EllipticLocalTrivialization.cayleyDiffeomorph, SphereSixComplex.Geometry.EllipticLocalTrivialization.orderThreeCoverDiffeomorph, SphereSixComplex.Geometry.EllipticLocalTrivialization.orderFourCoverDiffeomorph, SphereSixComplex.Geometry.EllipticLocalTrivialization.orderThreeFamilyCayleyLocalDiffeomorph, SphereSixComplex.Geometry.EllipticLocalTrivialization.orderFourFamilyCayleyLocalDiffeomorph, SphereSixComplex.Geometry.EllipticLocalTrivialization.orderThreeChartDeckEquiv_pow, SphereSixComplex.Geometry.EllipticLocalTrivialization.orderFourChartDeckEquiv_pow, SphereSixComplex.Geometry.EllipticLocalTrivialization.orderThreeFamilyParam_generator_equivariant, SphereSixComplex.Geometry.EllipticLocalTrivialization.orderFourFamilyParam_generator_equivariant")
The Cayley coordinate and the locally biholomorphic varying-lattice quotient give honest
pointwise complex charts near both elliptic fibres, with exact cyclic generator formulas and
descent to the family quotient. Compactness gives finite chart covers of the central fibres, but
the filling must retain the varying lattice rather than replace it by a fixed torus.
:::

:::definition "elliptic-whole-fibre-compatibility" (parent := "elliptic-local-trivialization") (lean := "SphereSixComplex.Geometry.EllipticWholeFiberCompactCover.familyFiber_isCompact, SphereSixComplex.Geometry.EllipticWholeFiberCompactCover.exists_finite_orderThree_local_chart_cover, SphereSixComplex.Geometry.EllipticWholeFiberCompactCover.exists_finite_orderFour_local_chart_cover, SphereSixComplex.Geometry.EllipticWholeFiberCompactCover.orderThree_pointwise_maps_agree_on_central_fiber, SphereSixComplex.Geometry.EllipticWholeFiberCompactCover.orderFour_pointwise_maps_agree_on_central_fiber, SphereSixComplex.Geometry.EllipticWholeFiberCompactCover.orderThree_overlap_agreement_exact_obstruction, SphereSixComplex.Geometry.EllipticWholeFiberCompactCover.orderFour_overlap_agreement_exact_obstruction")
The central torus fibres are compact and admit finite covers by the pointwise charts. Their maps
agree on the central fibre, while agreement on a neighborhood is equivalent to the varying deck
period lying in the fixed central lattice. Thus a fixed-torus product is only a conditional
isotrivial model; the paper's required construction is the direct varying-family affine quotient.
:::

:::theorem "elliptic-family-specialization" (parent := "elliptic-local-trivialization") (lean := "SphereSixComplex.Geometry.EllipticFamilySpecialization.generatorOneAddEquiv_mk, SphereSixComplex.Geometry.EllipticFamilySpecialization.generatorTwoAddEquiv_mk, SphereSixComplex.Geometry.EllipticFamilySpecialization.orderThreeTranslation_torsion, SphereSixComplex.Geometry.EllipticFamilySpecialization.orderFourTranslation_torsion, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderThreeFiberFixedPointCriterion, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderFourFiberFixedPointCriterion, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderThreeFiberData, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderFourFiberData, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderThreeAction_free, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderFourAction_free")
The actual period-torus fibres carry the descended generator transports and the prescribed
$`\varepsilon/3` and $`-\varepsilon'/4` translations. Their affine automorphisms have exact orders
three and four. An invariant integral coordinate proves the two fixed-point divisibility criteria,
so both actual local affine actions are unconditionally free.
:::

:::proof "elliptic-fillings"
Use {uses "torus-family"}[the torus family] and the invariant twist vectors fixed by $`A_1` and $`A_2`.
:::

:::theorem "compact-complex-threefold" (parent := "construction_spine") (lean := "SphereSixComplex.ComplexThreefold, SphereSixComplex.CompletedPaperThreefold, SphereSixComplex.PaperGluingData, SphereSixComplex.exists_paperGluingData, SphereSixComplex.exists_completedPaperThreefold") (priority := "high")
The global family and the three fillings glue to a compact connected complex threefold $`X`.
:::

:::proof "compact-complex-threefold"
Glue {uses "cusp-filling"}[the cusp filling] and
{uses "elliptic-fillings"}[the elliptic fillings] to the common collars of the punctured
{uses "torus-family"}[torus family], and verify the resulting charts and transition maps.
:::

:::theorem "manifold-gluing" (parent := "compact-complex-threefold") (lean := "SphereSixComplex.gluedChartedSpace, SphereSixComplex.isManifold_gluedChartedSpace, SphereSixComplex.compactSpace_gluedSpace, SphereSixComplex.connectedSpace_gluedSpace")
Compatible atlases on the filling pieces transport to their topological gluing and make the glued
space a manifold. Connected pieces with a connected overlap graph give a connected gluing;
compactness of the completed space is a separate global construction obligation, since the open
punctured and filling pieces need not themselves be compact.
:::

:::definition "complex-threefold-from-gluing" (parent := "compact-complex-threefold") (lean := "SphereSixComplex.complexThreefoldOfGluing")
A finite connected gluing of complex pieces with compatible complex and underlying real atlases,
together with global compactness of the glued space, produces the exact compact connected
`ComplexThreefold` contract used by the main theorem.
:::

:::theorem "paper-threefold-assembly" (parent := "compact-complex-threefold") (lean := "SphereSixComplex.completedPaperThreefoldOfGluing, SphereSixComplex.smoothRecognitionInputOfGluing, SphereSixComplex.PaperGluingData.toCompletedPaperThreefold, SphereSixComplex.exists_completedPaperThreefold_of_paperGluingData")
If that gluing carries the concrete van Kampen generators with no extra relations and the
four-piece Mayer--Vietoris comparison, it produces the exact `CompletedPaperThreefold` object and
the simply connected integral-homology-sphere input for smooth recognition. `PaperGluingData`
lists every required compactness, separation, atlas, overlap, van Kampen, and homology field.
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

:::definition "mayer-vietoris-contract" (parent := "integral-homology") (lean := "SphereSixComplex.establishedIntegralMayerVietorisExactSequence, SphereSixComplex.establishedFourPieceMayerVietorisExactness, SphereSixComplex.fourPieceMayerVietorisContract_of_homologyComputation, SphereSixComplex.FourPieceMayerVietorisExactness, SphereSixComplex.FourPieceHomologyComputation")
Binary open-cover exactness for integral singular homology is an explicit established external
input. It supplies exactness for the three successive unions in the four-piece cover; the
paper-specific chain comparison remains separate.
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

:::theorem "section-seven-leray-chain-model" (parent := "integral-homology") (lean := "SphereSixComplex.sectionSevenLerayBoundary_comp, SphereSixComplex.sectionSevenLerayChainModel_homology_one_isZero, SphereSixComplex.sectionSevenLerayChainModel_homology_two_isZero, SphereSixComplex.sectionSevenLerayChainModel_homology_three_isZero, SphereSixComplex.sectionSevenLerayChainModel_middle_homology_isZero, SphereSixComplex.sectionSevenLerayChainModel_homology_six_equiv")
The three differentials computed in Section 7 define a finite integral chain complex with vanishing
homology in degrees one through three and top homology $`\mathbb Z`. The paper's fourth coefficient
is kept explicit; if it is a unit, degrees four and five vanish as well. The missing unit proof is
the precise Poincaré-duality or Leray-convergence step.
:::

:::theorem "section-seven-algebraic-duality" (parent := "integral-homology") (lean := "SphereSixComplex.sectionSevenOneFivePairingMatrix_bijective, SphereSixComplex.sectionSevenTwoFourPairingMatrix_bijective, SphereSixComplex.SectionSevenLerayAlgebraicDuality.top_eq_one_or_neg_one, SphereSixComplex.SectionSevenLerayAlgebraicDuality.sphere_shaped_model_homology, SphereSixComplex.sectionSevenDegreeComplementCompatible_iff, SphereSixComplex.exists_sectionSevenDegreeComplementCompatible_iff, SphereSixComplex.SectionSevenLerayAlgebraicDuality.chainSelfDualityIso, SphereSixComplex.SectionSevenLerayAlgebraicDuality.homologyDegreeComplementIso, SphereSixComplex.SectionSevenLerayAlgebraicDuality.reversed_sphere_shaped_model_homology")
Explicit unimodular complementary-degree pairings reduce the remaining duality calculation to one
boundary-adjointness identity. That identity forces the fourth coefficient to be $`\pm1`, gives
the complete sphere-shaped homology, and yields a genuine chain-complex self-duality isomorphism
whose homology maps give complementary-degree isomorphisms. Realizing this adjointness for the
glued space is the remaining topological Poincaré-duality bridge.
:::

:::theorem "section-seven-coherent-realization" (parent := "integral-homology") (lean := "SphereSixComplex.SectionSevenLerayCoherentRealization, SphereSixComplex.SectionSevenLerayCoherentRealization.sectionSevenHomologyRealization, SphereSixComplex.establishedSixSphereSectionSevenHomology, SphereSixComplex.SectionSevenLerayCoherentRealization.hasIntegralHomologyOfSixSphere_established")
The standard $`S^6` homology calculation is an explicit established external input. The exact
paper-specific remaining obligation is `SectionSevenLerayCoherentRealization X` for the glued
space: one coherent chain map from the finite Leray model to singular chains, inducing homology
isomorphisms in every degree.
:::

:::theorem "smooth-recognition" (parent := "construction_spine") (lean := "SphereSixComplex.completedPaperThreefold_smoothRecognition, SphereSixComplex.exists_complex_threefold_diffeomorphic_sixSphere") (priority := "high")
The underlying standard smooth manifold of $`X` is diffeomorphic to $`S^6`.
:::

:::definition "smooth-recognition-obligations" (parent := "smooth-recognition") (lean := "SphereSixComplex.HomologyToHomotopySixSphereObligation, SphereSixComplex.HomotopyToDiffeomorphismSixSphereObligation, SphereSixComplex.smoothSixSphereRecognition_of_obligations")
The recognition step splits into the Whitehead--Hurewicz implication from a simply-connected
integral homology sphere to a homotopy sphere, followed by the dimension-six smooth Poincaré
classification.  Their composition gives the exact diffeomorphism required by the construction.
:::

:::theorem "established-smooth-recognition" (parent := "smooth-recognition") (lean := "SphereSixComplex.establishedHomologyToHomotopySixSphere, SphereSixComplex.establishedSmoothPoincareSix, SphereSixComplex.establishedSmoothSixSphereRecognition")
The Whitehead--Hurewicz implication for simply connected smooth integral homology six-spheres and
the dimension-six smooth Poincare theorem are isolated as explicit established external inputs.
Their exact Lean statements imply the smooth-recognition obligation; neither input assumes any
part of the paper's complex-geometric construction.
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

:::theorem "standard-sphere-homology-zero" (parent := "standard-six-sphere") (lean := "SphereSixComplex.sixSphereHomeomorphTopCatSphereSix, SphereSixComplex.sixSphere_integralSingularHomology_zero_equiv_integer, SphereSixComplex.sixSphere_sectionSevenHomologyRealization_zero, SphereSixComplex.topCatDiskSeven_contractibleSpace, SphereSixComplex.topCatDiskSeven_integralSingularHomology_isZero")
The standard sphere has degree-zero integral homology $`\mathbb Z`; it is the boundary of the
contractible seven-disk, whose positive-degree integral homology vanishes.
:::

:::theorem "relative-disk-sphere-homology" (parent := "standard-six-sphere") (lean := "SphereSixComplex.relativeIntegralSingularShortComplex_shortExact, SphereSixComplex.relativeIntegralSingular_homology_exact_ambient, SphereSixComplex.relativeIntegralSingular_homology_exact_relative, SphereSixComplex.relativeIntegralSingular_homology_exact_subspace, SphereSixComplex.diskSevenSphereSix_relativeBoundaryIso")
Relative singular chains are defined as a categorical cokernel and fit into the long exact
homology sequence. For positive degrees, its boundary identifies $`H_{n+1}(D^7,S^6)` with
$`H_n(S^6)`; the remaining standard-sphere calculation is the relative disk-cell computation.
:::

:::theorem "disk-boundary-collapse" (parent := "relative-disk-sphere-homology") (lean := "SphereSixComplex.diskBoundaryQuotientSevenMap_isQuotientMap, SphereSixComplex.diskBoundaryCollapseToOnePointContinuous, SphereSixComplex.diskBoundaryQuotientSevenHomeomorphSphereSeven, SphereSixComplex.diskBoundaryQuotientSevenSphereIso_basepoint, SphereSixComplex.reducedDiskBoundaryQuotientChainsIsoReducedSphereSevenChains, SphereSixComplex.diskSevenRelativeChainsToReducedSphereSevenChains")
Collapsing the boundary of the seven-disk is homeomorphic to the standard seven-sphere, with the
collapsed basepoint tracked through a reduced-chain isomorphism. The canonical relative-chain map
is explicit; proving it is a homology isomorphism is precisely the remaining excision step.
:::

:::theorem "singular-small-chain-excision" (parent := "disk-boundary-collapse") (lean := "SphereSixComplex.CoverSmallChainRetractionData.approximation, SphereSixComplex.coverSmallIntegralSingularHomologyIso, SphereSixComplex.diskSevenExcisionCover_isOpen, SphereSixComplex.diskSevenExcisionCover_iUnion, SphereSixComplex.diskBoundaryToDiskSevenCoverSmallIntegralSingularChains_comp_inclusion, SphereSixComplex.DiskSevenSmallChainApproximation, SphereSixComplex.simplexSubdivisionLastVertex, SphereSixComplex.subdivisionLastVertex, SphereSixComplex.subdivisionLastVertexLiftChainMap_comp_inclusion, SphereSixComplex.barycentricOuterFaceIdentity, SphereSixComplex.barycentricSubdivisionChainMapCanonical, SphereSixComplex.BarycentricLastVertexPrismData, SphereSixComplex.barycentricSubdivisionLastVertexHomotopy")
The cover-small singular subcomplex and its monomorphic inclusion into all singular chains are
explicit. Retraction data yields a chain-homotopy equivalence and homology isomorphisms. For the
seven-disk, the boundary factors through the small chains for an explicit open two-set cover. The
global subdivision last-vertex map, induced chain map, and subcomplex lifts are constructed from
Mathlib's left-Kan-extension API. Signed maximal-flag chains give the canonical natural barycentric
subdivision chain map. A universal standard-simplex prism boundary identity now produces the actual
Mathlib chain homotopy from last-vertex-after-subdivision to the identity. Constructing that prism
by the classical cone contraction, then proving the Lebesgue-number iteration, remain.
:::

:::theorem "sphere-stereographic-simple-connectivity" (parent := "standard-six-sphere") (lean := "SphereSixComplex.sixSphere_compl_singleton_simplyConnected, SphereSixComplex.sixSphere_simplyConnected_iff_loops_nullhomotopic")
Removing any point from the standard six-sphere gives a simply-connected Euclidean chart.  Global
simple connectedness is reduced exactly to nullhomotopy of every based loop.
:::
