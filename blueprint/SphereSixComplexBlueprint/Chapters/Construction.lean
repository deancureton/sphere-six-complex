import Verso
import VersoBlueprint
import VersoManual
import SphereSixComplex.Main

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Construction Spine" =>

This chapter follows the construction used by the two Comparator endpoints. Its Lean links refer
to retained declarations; auxiliary calculations and alternative proof routes are omitted.

:::group "construction_spine"
The minimal construction and recognition path.
:::

:::definition "lattice-monodromy-data" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.T₁, SphereSixComplex.LatticeData.T₂, SphereSixComplex.LatticeData.A₁, SphereSixComplex.LatticeData.A₂, SphereSixComplex.LatticeData.M₀")
The rank-four lattice carries explicit local monodromies of orders three, four, and infinite order at
the cusp.
:::

:::theorem "monodromy-identities" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.T₁_det, SphereSixComplex.LatticeData.T₂_det, SphereSixComplex.LatticeData.T₁_pow_three, SphereSixComplex.LatticeData.T₂_pow_four, SphereSixComplex.LatticeData.A₁_mul_A₂_mul_M₀")
The displayed matrices are unimodular, the finite monodromies satisfy $`T_1^3=I` and $`T_2^4=I`,
and the nilpotent part $`N = T_0-I` satisfies $`N^2=0`.
:::

:::proof "monodromy-identities"
Expand the four-by-four matrices and check every integral entry. The Lean proof is kernel checked and
does not use a native evaluator.
:::

:::theorem "triangle-representation" (parent := "construction_spine") (lean := "SphereSixComplex.TriangleGroup.rhoLambda, SphereSixComplex.TriangleGroup.rhoLambda_g₀")
The free product $`(\mathbb Z/3)*(\mathbb Z/4)` acts on the dual rank-four lattice with the prescribed monodromies. The cusp relation identifies the inverse product of the elliptic generators.
:::

:::theorem "modular-parameter-action" (parent := "triangle-representation") (lean := "SphereSixComplex.TriangleGroup.rhoTau, SphereSixComplex.TriangleGroup.rhoTauReal_g1_smul, SphereSixComplex.TriangleGroup.rhoTauReal_g2_smul, SphereSixComplex.TriangleGroup.rhoTauReal_g0_smul")
The same triangle group acts on the upper half-plane by the displayed fractional-linear
transformations $`\tau \mapsto (\tau-1)/\tau`, $`\tau \mapsto -1/\tau`, and
$`\tau \mapsto \tau-1` at the cusp.
:::

:::proof "triangle-representation"
Descend the dual monodromy powers to the two cyclic factors, then use the coproduct universal property. The cusp relation identifies their inverse product.
:::

:::theorem "dual-coinvariants" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.dualCoinvariantRelations_eq_ker_gamma")
The dual monodromy relation lattice is exactly the kernel of the invariant functional $`\gamma`.
:::

:::theorem "atlas-transport" (parent := "construction_spine") (lean := "SphereSixComplex.isManifold_transportChartedSpace")
A manifold atlas and its differentiability structure transport along a homeomorphism without changing
the transition functions.
:::

:::proof "atlas-transport"
Conjugate every chart by the homeomorphism. In each transition map the conjugating maps cancel, leaving
the original transition map in the same structure groupoid.
:::

:::theorem "complex-quotient" (parent := "construction_spine") (lean := "SphereSixComplex.Geometry.quotientProjection_isOpenQuotientMap, SphereSixComplex.Geometry.orbitQuotient_t2Space, SphereSixComplex.Geometry.quotientChartContDiff_of_contMDiff_smul, SphereSixComplex.Geometry.orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul")
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

:::theorem "period-functions" (parent := "construction_spine") (lean := "SphereSixComplex.Periods.FuchsianAffineDescent.exists_fuchsianPeriodLocalData, SphereSixComplex.Periods.exists_assembledFuchsianPeriodFunctions") (priority := "high")
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

:::theorem "fuchsian-source-action" (parent := "period-functions") (lean := "SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint_fixed, SphereSixComplex.TriangleGroup.fuchsianTwoFixedPoint_fixed, SphereSixComplex.TriangleGroup.fuchsianSourceAction_g₀_apply, SphereSixComplex.TriangleGroup.fuchsianCuspRegion_invariant, SphereSixComplex.TriangleGroup.fuchsianSourceAction_contMDiff")
Explicit real special-linear matrices give the distinct source action of signature
$`(3,4,\infty)`: its elliptic generators have exact projective orders three and four, while the
cusp generator is a horizontal translation preserving the chosen horodisc. Every group element
acts complex-smoothly by free-product induction.
:::

:::theorem "fuchsian-source-faithfulness" (parent := "fuchsian-source-action") (lean := "SphereSixComplex.TriangleGroup.FuchsianPingPong.inl_maps_left_to_right, SphereSixComplex.TriangleGroup.FuchsianPingPong.inr_maps_right_to_left, SphereSixComplex.TriangleGroup.FuchsianPingPong.factorAction_ping_pong, SphereSixComplex.TriangleGroup.FuchsianPingPong.fuchsianSourceAction_injective")
The two real half-planes form ping-pong regions for the cyclic factors. Hence the explicit
projective source representation of their free product is faithful.
:::

:::theorem "fuchsian-fundamental-region" (parent := "fuchsian-source-action") (lean := "SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain.fuchsianOneFixedPoint_mem_fundamentalTriangle, SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain.fuchsianTwoFixedPoint_mem_fundamentalTriangle, SphereSixComplex.TriangleGroup.FuchsianTriangleCover.orientedFundamentalRegion, SphereSixComplex.TriangleGroup.FuchsianTriangleCover.exists_smul_mem_orientedFundamentalRegion")
The explicit triangle is one reflection chamber. Since $`\Delta=C_3*C_4` is the
orientation-preserving subgroup, its fundamental region is the union of two adjacent chambers.
Every upper-half-plane point has a $`\Delta`-translate in this doubled region.
:::

:::theorem "fuchsian-reduction" (parent := "fuchsian-fundamental-region") (lean := "SphereSixComplex.TriangleGroup.FuchsianTessellation.product_zpow_apply")
The product of the two Fuchsian generators acts by horizontal translation. Its integral powers give the explicit cusp translation formula used in reduction to the fundamental region.
:::

:::theorem "fuchsian-arithmetic" (parent := "fuchsian-reduction") (lean := "SphereSixComplex.TriangleGroup.FuchsianArithmetic.quadraticProjectiveRepresentation, SphereSixComplex.TriangleGroup.FuchsianArithmetic.quadraticProjectiveRepresentation_inl_generator, SphereSixComplex.TriangleGroup.FuchsianArithmetic.quadraticProjectiveRepresentation_inr_generator, SphereSixComplex.TriangleGroup.FuchsianArithmetic.positive_bottomRow_bounded_of_normSq_le")
The Fuchsian generators lift to an explicit projective representation over $`\mathbb Z[\sqrt2]`.
Paired real embeddings make bounded denominator sublevels finite once the conjugate bottom rows are
uniformly bounded. The coefficient-cone invariant below supplies this bound.
:::

:::theorem "fuchsian-arithmetic-termination" (parent := "fuchsian-arithmetic") (lean := "SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.wordMatrix_matrixInCoefficientCone, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.finite_wordBottomRows_of_normSq_le, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.exists_fuchsian_orbitHeightMaximal, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.fuchsianSourceAction_properlyDiscontinuous, SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination.sourceActionProperlyDiscontinuous_of_eq")
Reduced words have entrywise conjugate norm bounded by the distinguished embedding. Consequently,
denominator sublevels are finite, orbit heights attain maxima, every orbit meets the coarse Ford
region, and the source action is properly discontinuous. The regular-locus action is free.
:::

:::theorem "fuchsian-compact-core" (parent := "fuchsian-fundamental-region") (lean := "SphereSixComplex.Periods.orientedFuchsianCompactCore_isCompact, SphereSixComplex.Periods.orientedFundamentalRegion_mem_cusp_or_compactCore, SphereSixComplex.Periods.orientedFuchsianQuotientCompactCore")
The part of the doubled fundamental region below the standard horodisc lies in an explicit compact
rectangle. This gives the compact quotient core required by the Schur argument and converts
Fuchsian pre-period data into the full period family without a false single-chamber premise.
:::

:::theorem "fuchsian-uniformization-bridge" (parent := "period-functions") (lean := "SphereSixComplex.Periods.FuchsianModularParameter.equivariant, SphereSixComplex.Periods.FuchsianModularParameter.coordinate_invariant, SphereSixComplex.Periods.FuchsianModularParameter.toTriangleUniformization, SphereSixComplex.Periods.FuchsianPrePeriodData.toPrePeriodFunctions")
The two generator laws for a holomorphic modular parameter extend to the full free product. Its
normalized modular invariant supplies the quotient coordinate, and explicit additive period data
plus a compact quotient core gives the nondegenerate period family.
:::

:::definition "normalized-fuchsian-modular-lift-obligation" (parent := "fuchsian-uniformization-bridge") (lean := "SphereSixComplex.Periods.ExactFuchsianOrbifoldCoordinate, SphereSixComplex.Periods.ExactNormalizedModularJUniformization, SphereSixComplex.Periods.NormalizedFuchsianModularJLiftingExistence, SphereSixComplex.Periods.ExactFuchsianOrbifoldCoordinate.nonempty, SphereSixComplex.Periods.ExactNormalizedModularJUniformization.nonempty, SphereSixComplex.Periods.normalizedFuchsianModularJLiftingExistence, SphereSixComplex.Periods.nonempty_normalizedFuchsianModularParameter")
Exact source and modular quotient uniformization, together with compatible branched lifting, are
proved in Lean. Their contracts track orbit fibres, special values, exact elliptic branching,
ordinary covering away from the branch values, and a simple completed cusp. These results construct
the normalized modular parameter used by the period family.
:::

:::theorem "schur-compactness" (parent := "period-functions") (lean := "SphereSixComplex.Periods.PrePeriodFunctions.schurQuantity_invariant, SphereSixComplex.Periods.PrePeriodFunctions.schurQuantity_cusp_bounded_above, SphereSixComplex.Periods.PrePeriodFunctions.schurQuantity_bounded_above_of_compactCore, SphereSixComplex.Periods.PrePeriodFunctions.exists_shiftedPeriodFunctions")
The Schur quantity is continuous and invariant under the full triangle group. Its cusp-growth law
bounds it above on the distinguished horodisc; a compact core meeting every remaining orbit then
gives the global upper bound needed for the final imaginary shift of $`\beta`, producing the
nondegenerate period family.
:::

:::theorem "period-torsor-algebra" (parent := "period-functions") (lean := "SphereSixComplex.Periods.betaCocycleOne_cycle, SphereSixComplex.Periods.betaCocycleTwo_cycle, SphereSixComplex.Periods.localBetaOne_transform, SphereSixComplex.Periods.localBetaTwo_transform")
The homogeneous automorphy factors and affine substitutions close around the order-three and
order-four orbits.  The inhomogeneous $`\beta` cocycles sum to zero, and weighted orbit sums give
the explicit local primitives used to build the two analytic torsors.
:::

:::theorem "projective-line-cech-splitting" (parent := "period-functions") (lean := "SphereSixComplex.Periods.exists_cech_coboundary_neg_one, SphereSixComplex.Periods.exists_cech_coboundary_zero")
Holomorphic overlap cocycles on the standard two-chart cover of the projective line split for both $`\mathcal O(-1)` and $`\mathcal O`. These analytic Čech splittings are proved in Lean.
:::

:::theorem "fuchsian-modular-neg-one-frame" (parent := "projective-line-cech-splitting") (lean := "SphereSixComplex.Periods.AnalyticSquareRoot.exists_analyticOnNhd_sq_eq, SphereSixComplex.Periods.exists_exactFuchsianEisensteinSixRoot, SphereSixComplex.Periods.exists_exactFuchsianCuspFrameGerm, SphereSixComplex.Periods.ExactLiftedModularNegOneFrame, SphereSixComplex.Periods.nonempty_exactLiftedModularNegOneFrame, SphereSixComplex.Periods.FuchsianAffineDescent.liftedNegOneInfinityFrame, SphereSixComplex.Periods.FuchsianAffineDescent.cycleRelations")
The divisor, ramification, and cusp calculations for $`E_4^2\sqrt{E_6}/\Delta` construct the exact
two-chart frame for the pulled-back $`\mathcal O(-1)` bundle, including its elliptic orders and cusp
factorization. The modular uniformization and frame constructions are proved results.
:::

:::theorem "fuchsian-mu-torsor-descent" (parent := "fuchsian-modular-neg-one-frame") (lean := "SphereSixComplex.Periods.OrbifoldAffineDescentData.HasAcyclicProjectiveLineFrame, SphereSixComplex.Periods.OrbifoldAffineDescentData.nonempty_analyticDescentData, SphereSixComplex.Periods.FuchsianAffineDescent.muDescentData, SphereSixComplex.Periods.FuchsianAffineDescent.muAnalyticDescentData, SphereSixComplex.Periods.MuTorsorCechLocalData, SphereSixComplex.Periods.exists_compatibleAdjustedMuSections, SphereSixComplex.Periods.gluedAdjustedMu_holomorphic, SphereSixComplex.Periods.gluedAdjustedMu_transform_one, SphereSixComplex.Periods.gluedAdjustedMu_transform_two, SphereSixComplex.Periods.gluedAdjustedMu_cusp_bounded, SphereSixComplex.Periods.exists_globalFuchsianMu")
Exact local $`\mathcal O(-1)` torsor data on two invariant quotient charts glues to a global
holomorphic $`\mu` with both affine generator laws and the required cusp bound. The analytic
splitting, construction of `AnalyticDescentData`, Čech correction, and global gluing are all proved.
No Cartan--B or Cousin axiom is retained.
:::

:::theorem "fuchsian-beta-torsor-descent" (parent := "fuchsian-mu-torsor-descent") (lean := "SphereSixComplex.Periods.FuchsianAffineDescent.BetaDescentData, SphereSixComplex.Periods.FuchsianAffineDescent.betaAnalyticDescentData, SphereSixComplex.Periods.BetaTorsorCechLocalData, SphereSixComplex.Periods.FuchsianAffineDescent.exists_betaAffineCechSections, SphereSixComplex.Periods.exists_compatibleAdjustedBetaSections, SphereSixComplex.Periods.gluedAdjustedBeta_holomorphic, SphereSixComplex.Periods.gluedAdjustedBeta_transform_one, SphereSixComplex.Periods.gluedAdjustedBeta_transform_two, SphereSixComplex.Periods.gluedAdjustedBeta_add_tau_cusp_bounded, SphereSixComplex.Periods.exists_globalFuchsianBeta")
For a fixed global $`\mu`, exact local $`\mathcal O` torsor data likewise glues to a global
holomorphic $`\beta` with both affine generator laws and the normalized $`\beta+\tau` cusp bound.
Applying the same general analytic theorem to the torsor determined by the selected $`\mu`
constructs the dependent beta certificate; its overlap correction and global gluing are proved.
:::

:::theorem "fuchsian-period-assembly" (parent := "fuchsian-beta-torsor-descent") (lean := "SphereSixComplex.Periods.FuchsianPeriodLocalData, SphereSixComplex.Periods.assembledFuchsianPrePeriodData, SphereSixComplex.Periods.descendedFuchsianMu_transform_cusp, SphereSixComplex.Periods.descendedFuchsianBeta_transform_cusp, SphereSixComplex.Periods.FuchsianAffineDescent.exists_fuchsianPeriodLocalData, SphereSixComplex.Periods.exists_assembledFuchsianPeriodFunctions, SphereSixComplex.Periods.assembledFuchsianPeriodFunctions")
The two production torsor packages assemble with the established modular parameter into full
pre-period data. The elliptic generator laws imply the parabolic $`\mu` and $`\beta` laws, and the
doubled Fuchsian compact core supplies the Schur shift to an actual nondegenerate period family.
:::

:::theorem "fuchsian-cusp-normalization" (parent := "fuchsian-period-assembly") (lean := "SphereSixComplex.Periods.FuchsianCuspNormalization.ParabolicCuspLocalInverse, SphereSixComplex.Periods.FuchsianCuspNormalization.nonempty_parabolicCuspLocalInverse, SphereSixComplex.Periods.FuchsianCuspNormalization.assembledPeriodFunctions_tau_translate, SphereSixComplex.Periods.FuchsianCuspNormalization.exists_normalizedFuchsianCuspCoordinate")
A general degree-one parabolic cusp theorem turns a holomorphic map intertwining positive source
and target translations into a coherent holomorphic inverse high in the cusp. Applied to the
assembled period parameter, it constructs the normalized cusp lift, proves its exact translation
law, and places its image inside the distinguished source horodisc.
:::

:::theorem "torus-family" (parent := "construction_spine") (priority := "high")
The period matrix built from $`\tau,\mu,\beta` defines a proper holomorphic family of compact complex
two-tori over the thrice-punctured sphere.
:::

:::proof "torus-family"
Use {uses "period-functions"}[the period functions] to prove that each period subgroup is a lattice and
that the monodromy action descends freely away from the elliptic fixed points.
:::

:::theorem "complex-torus-fibres" (parent := "torus-family") (lean := "SphereSixComplex.Geometry.ComplexTorus.torus_compactSpace")
The quotient of $`\mathbb C^2` by the full-rank period lattice is compact.
:::

:::theorem "global-torus-family-action" (parent := "torus-family") (lean := "SphereSixComplex.Geometry.GlobalTorusFamily.parameterMap_equivariant, SphereSixComplex.Geometry.GlobalTorusFamily.regularDeckMap_orbitRel_iff, SphereSixComplex.Geometry.GlobalTorusFamily.regularFamilyDeckMap_mul, SphereSixComplex.Geometry.GlobalTorusFamily.regularParameterMap_compactUniformLowerBound, SphereSixComplex.Geometry.GlobalTorusFamily.regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph, SphereSixComplex.Geometry.GlobalTorusFamily.regularFamilyDeckMap_contMDiff, SphereSixComplex.Geometry.GlobalTorusFamily.regularFamilyDeckAction_isCancelSMul_of_fuchsian, SphereSixComplex.Geometry.GlobalTorusFamily.regularFamilyDeckAction_properlyDiscontinuous_of_source, SphereSixComplex.Geometry.GlobalTorusFamily.puncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph, SphereSixComplex.Geometry.GlobalTorusFamily.fuchsianPuncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph, SphereSixComplex.Geometry.GlobalTorusFamily.PuncturedGlobalFamily")
Integral monodromy extends to complex-linear fibre transport for every triangle-group element.
The resulting deck action respects the varying period lattice and defines the punctured global
torus-family quotient before the three local fillings are attached. The regular lattice quotient
and every descended deck map are complex smooth. Source freeness and proper discontinuity transfer
through both quotients, giving the punctured family a complex-threefold atlas with locally
biholomorphic projection.
:::

:::theorem "elliptic-orbit-freeness" (parent := "torus-family") (lean := "SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.deltaIndexedEquiv, SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.deltaNormalForm, SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.finiteOrder_isConj_inl_or_inr, SphereSixComplex.TriangleGroup.BinaryIndexedCoprod.finiteOrder_fixed_regular_eq_one, SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_inl_fixed_iff, SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_inr_fixed_iff, SphereSixComplex.TriangleGroup.FuchsianProperFreeness.isOfFinOrder_of_fixed_of_properlyDiscontinuous, SphereSixComplex.TriangleGroup.FuchsianProperFreeness.fuchsian_fixed_regular_eq_one")
Every nonidentity element of either cyclic factor fixes exactly its marked elliptic point, and its
conjugates fix exactly the corresponding elliptic orbit. Removing those orbits eliminates all such
stabilizers. An explicit equivalence with the indexed free product proves every nontrivial
finite-order element is conjugate into a factor. Proper discontinuity makes point stabilizers
finite and therefore proves the regular action free; both properties then lift to the deck action.
The explicit projective Fuchsian source action is properly discontinuous by the fundamental-region
calculation above.
:::

:::theorem "properly-discontinuous-stabilizer-slice" (parent := "elliptic-orbit-freeness") (lean := "SphereSixComplex.Geometry.exists_open_stabilizer_slice")
For a properly discontinuous continuous action on a locally compact Hausdorff space, every point
has an open neighborhood invariant under its finite stabilizer, and a translate meets that
neighborhood exactly when the translating element belongs to the stabilizer. This is the general
local separation theorem needed to compare each finite elliptic quotient with the global affine
free-product quotient.
:::

:::theorem "regular-base-topology" (parent := "elliptic-orbit-freeness") (lean := "SphereSixComplex.Geometry.GlobalTorusFamily.sourceOrbitSingletons_locallyFinite, SphereSixComplex.Geometry.GlobalTorusFamily.sourceOrbitSet_isClosed, SphereSixComplex.Geometry.GlobalTorusFamily.isOpen_isRegularBasePoint, SphereSixComplex.Geometry.GlobalTorusFamily.regularBase_isManifold, SphereSixComplex.Geometry.GlobalTorusFamily.regularDeckMap_contMDiff")
Proper discontinuity makes both elliptic orbits locally finite and closed. Their complement is
therefore an open complex one-manifold, giving the correct regular base for the punctured family.
Every lifted deck transformation restricts to a complex-smooth map over this base.
:::

:::theorem "analytic-torus-family" (parent := "torus-family") (lean := "SphereSixComplex.Geometry.AnalyticTorusFamily.periodSection_contMDiff, SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap_compactUniformLowerBound, SphereSixComplex.Geometry.AnalyticTorusFamily.totalSpace_isManifold_and_projection_isLocalDiffeomorph")
The period domain is an open complex three-manifold, the analytic period map and every integral
period section are complex smooth.  Pointwise full rank gives a uniform lower bound over compact
base sets, hence a properly discontinuous quotient complex manifold with locally biholomorphic
projection.
:::

:::theorem "cusp-filling" (parent := "construction_spine") (priority := "high")
The unipotent end admits the toric filling whose central fibre is the opposite-edge quotient of the
degree-six del Pezzo surface.
:::

:::definition "standard-infinite-a2-toric-model" (parent := "cusp-filling") (lean := "SphereSixComplex.Geometry.InfiniteA2Toric.heightOneRay, SphereSixComplex.Geometry.InfiniteA2Toric.a2ConeMatrix, SphereSixComplex.Geometry.InfiniteA2Toric.denseTorusShear, SphereSixComplex.Geometry.InfiniteA2Toric.Model, SphereSixComplex.Geometry.InfiniteA2Toric.Model.variableTorusAction_holomorphic")
The countable smooth fan over the height-one $`A_2` triangulation is constructed in Lean. Its model
is a connected Hausdorff second-countable complex three-manifold with a dense torus, a height
character, unimodular $`\mathbb C^3` charts with squarefree equation $`t=z_0z_1z_2`, ray components,
and integral fan shears. The torus action is jointly holomorphic in coefficientwise form on open
subsets. The phase estimates and quotient constructions are proved separately from this model.
:::

:::theorem "toric-phase-correction" (parent := "standard-infinite-a2-toric-model") (lean := "SphereSixComplex.Geometry.CuspToricPhaseAction.phaseEmbedding, SphereSixComplex.Geometry.CuspToricPhaseAction.denseTorusShear_phase_commute, SphereSixComplex.Geometry.CuspToricPhaseAction.ToricModel.fanShear_phase_commute")
The two phase coordinates embed in the dense torus, preserve the height character, and commute
with every integral fan shear. Exact holomorphic phase coefficients therefore produce the
corrected lattice action and its holomorphic maps. The fixed-point and compact-overlap estimates
from the cusp analysis remain explicit hypotheses for freeness and proper discontinuity.
:::

:::theorem "cusp-period-expansion" (parent := "toric-phase-correction") (lean := "SphereSixComplex.Geometry.CuspPeriodExpansion.nonempty_holomorphicCuspDescent, SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.periodBlock_eq_smul_B₀_add_correction, SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseCoefficient_add, SphereSixComplex.Geometry.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseCoefficient_holomorphicOn")
On an exact normalized cusp lift, bounded periodic holomorphic coefficients descend through
$`q=\exp(2\pi i s)` and extend over $`q=0`. This gives the local expansion
$`Z(s)=sB_0+C(q)` and the holomorphic phase factors
$`c_\lambda(q)=\exp(2\pi i C(q)\lambda)`. The normalized lift is supplied by
{uses "fuchsian-cusp-normalization"}[the parabolic cusp theorem], and no unjustified entire
extension of the local coefficients is assumed.
:::

:::theorem "cusp-local-phase-action" (parent := "cusp-period-expansion") (lean := "SphereSixComplex.Geometry.CuspLocalPhaseAction.cuspNeighborhood, SphereSixComplex.Geometry.CuspLocalPhaseAction.LocalHolomorphicPhaseCoefficients.localPhaseTwist_holomorphic, SphereSixComplex.Geometry.CuspLocalPhaseAction.LocalHolomorphicPhaseCoefficients.psiMap_add, SphereSixComplex.Geometry.CuspLocalPhaseAction.LocalHolomorphicPhaseCoefficients.psiMap_holomorphic, SphereSixComplex.Geometry.CuspLocalPhaseAction.LocalHolomorphicPhaseCoefficients.quotient_isQuotientCoveringMap, SphereSixComplex.Geometry.CuspLocalPhaseAction.LocalHolomorphicPhaseCoefficients.quotient_isManifold")
Restricting the toric model to the open cusp disc makes the local phase coefficients sufficient.
Joint holomorphicity of the standard torus action proves the variable phase twist is holomorphic,
so no entire extension is required. The corrected lattice quotient is a complex three-manifold
once the two fixed-point estimates and compact-overlap finiteness from the cusp analysis are
supplied on this restricted carrier.
:::

:::theorem "cusp-action" (parent := "cusp-local-phase-action") (lean := "SphereSixComplex.Geometry.CuspFilling.CuspActionData.isCancelSMul, SphereSixComplex.Geometry.CuspFilling.CuspActionData.properlyDiscontinuous, SphereSixComplex.Geometry.CuspFilling.quotient_isQuotientCoveringMap")
The $`B_0` shear preserves the cusp height and translates both classes of $`A_2` triangles.  Given
the phase estimates of Theorem 4.5, the corrected maps form a free, properly discontinuous lattice
action.  Local sheets differ by analytic deck maps, so the covering quotient inherits a complex
manifold atlas.
:::

:::proof "cusp-filling"
Use {uses "torus-family"}[the torus family] and the unimodular cusp lattice map coming from
{uses "monodromy-identities"}[the explicit nilpotent monodromy].
:::

:::theorem "elliptic-fillings" (parent := "construction_spine") (lean := "SphereSixComplex.Geometry.epsilon_action_free, SphereSixComplex.Geometry.neg_epsilonPrime_action_free") (priority := "high")
The selected order-three and order-four affine actions are free for the twist vectors in the Setup. Their varying-family quotients provide the elliptic filling pieces described below.
:::

:::theorem "elliptic-local-coordinates" (parent := "elliptic-fillings") (lean := "SphereSixComplex.UpperHalfPlane.norm_cayley_lt_one, SphereSixComplex.Geometry.EllipticLocalCoordinates.orderThreeCayley_generator, SphereSixComplex.Geometry.EllipticLocalCoordinates.orderFourCayley_generator, SphereSixComplex.UpperHalfPlane.cayleyHomeomorph, SphereSixComplex.Geometry.EllipticCayleyHomeomorph.orderThreeCayleyHomeomorph_generator, SphereSixComplex.Geometry.EllipticCayleyHomeomorph.orderFourCayleyHomeomorph_generator")
The explicit Cayley formulas give homeomorphisms from the upper half-plane to the unit disc and
conjugate the source generators to rotations of orders three and four. The remaining affine fibre
data then gives the free logarithmic-transform quotient manifolds.
:::

:::theorem "elliptic-local-trivialization" (parent := "elliptic-local-coordinates") (lean := "SphereSixComplex.Geometry.EllipticLocalTrivialization.cayleyDiffeomorph")
The Cayley map gives a complex diffeomorphism from the upper half-plane to the unit disc.
:::

:::theorem "elliptic-family-specialization" (parent := "elliptic-local-coordinates") (lean := "SphereSixComplex.Geometry.EllipticFamilySpecialization.generatorOneAddEquiv_mk, SphereSixComplex.Geometry.EllipticFamilySpecialization.generatorTwoAddEquiv_mk, SphereSixComplex.Geometry.EllipticFamilySpecialization.orderThreeTranslation_torsion, SphereSixComplex.Geometry.EllipticFamilySpecialization.orderFourTranslation_torsion, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderThreeFiberFixedPointCriterion, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderFourFiberFixedPointCriterion, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderThreeFiberData, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderFourFiberData, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderThreeAction_free, SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderFourAction_free")
The actual period-torus fibres carry the descended generator transports and the prescribed
$`\varepsilon/3` and $`-\varepsilon'/4` translations. Their affine automorphisms have exact orders
three and four. An invariant integral coordinate proves the two fixed-point divisibility criteria,
so both actual local affine actions are unconditionally free.
:::

:::theorem "elliptic-varying-family-quotients" (parent := "elliptic-family-specialization") (lean := "SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient.orderThreeAffineFamilyAction_free, SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient.orderFourAffineFamilyAction_free, SphereSixComplex.TriangleGroup.commute_gOne_of_fuchsianOneFixed, SphereSixComplex.TriangleGroup.FuchsianTwoFixedCommutation.commute_gTwo_of_fuchsianTwoFixedPoint_fixed, SphereSixComplex.TriangleGroup.eq_inl_of_commute_g₁, SphereSixComplex.TriangleGroup.eq_inr_of_commute_g₂, SphereSixComplex.TriangleGroup.fuchsianOneFixed_iff_mem_range_inl, SphereSixComplex.TriangleGroup.fuchsianTwoFixed_iff_mem_range_inr")
The actual varying torus family carries free analytic affine actions of orders three and four, so
their finite quotients are complex three-manifolds with locally biholomorphic projections. The two
actions extend by the free-product universal property to the honest affine $`\Delta` action; this
is distinct from the purely linear deck action. Open invariant punctured Cayley collars are
constructed, and their maps to the affine global quotient are injective once the exact local
orbit-separation propositions are proved. Proper discontinuity, stabilizer slices, and radius
refinement are complete. Fixing an elliptic point forces commutation with its generator, and the
free-product centralizer calculation proves that the stabilizers are precisely the embedded
$`C_3` and $`C_4` factors, closing both collar separations without an external axiom.
:::

:::proof "elliptic-fillings"
Use {uses "torus-family"}[the torus family] and the invariant twist vectors fixed by $`A_1` and $`A_2`.
:::

:::theorem "compact-complex-threefold" (parent := "construction_spine") (lean := "SphereSixComplex.ComplexThreefold, SphereSixComplex.exists_complexThreefold_simplyConnected_homologyEquiv_sixSphere, SphereSixComplex.CompactComplexStar, SphereSixComplex.Geometry.AnalyticData.compactComplexStar") (priority := "high")
The global family and the three fillings glue to a compact connected complex threefold $`X`.
The analytic package, the actual star's van Kampen data, and the positive-degree homology assembly
are constructed in Lean and combined by `exists_complexThreefold_simplyConnected_homologyEquiv_sixSphere`. No construction-specific axiom or
unfinished proof is required by this theorem.
:::

:::proof "compact-complex-threefold"
Glue {uses "cusp-filling"}[the cusp filling] and
{uses "elliptic-fillings"}[the elliptic fillings] to the common collars of the punctured
{uses "torus-family"}[torus family], and verify the resulting charts and transition maps.
:::

:::theorem "manifold-gluing" (parent := "compact-complex-threefold") (lean := "SphereSixComplex.CrossPieceGluingCompatible, SphereSixComplex.gluingAtlasCompatible_of_crossPiece, SphereSixComplex.gluedChartedSpace, SphereSixComplex.isManifold_gluedChartedSpace, SphereSixComplex.secondCountableTopology_gluedSpace, SphereSixComplex.connectedSpace_gluedSpace, SphereSixComplex.BiholomorphicStarGluing.BiholomorphicFourPieceStarData.gluing_atlas_compatible, SphereSixComplex.ComplexThreefold.RealAtlas.isManifold, SphereSixComplex.CompactComplexStar.gluedSecondCountable")
Compatible atlases on the filling pieces transport to their topological gluing and make the glued
space a manifold. A countable open gluing of second-countable pieces is second countable, and
connected pieces with a connected overlap graph give a connected gluing. Restriction of a complex atlas to
the underlying real manifold is proved from `ContDiffOn.restrict_scalars`, and compatibility of the
paper's four biholomorphic pieces is proved by identifying the six piece transitions with the collar
partial diffeomorphisms, their inverses, and the empty transitions between distinct fillings. The
gluing step therefore has no remaining external boundary. Compactness is a separate construction
obligation, since the open punctured and filling pieces need not themselves be compact.
:::

:::definition "complex-threefold-from-gluing" (parent := "compact-complex-threefold") (lean := "SphereSixComplex.complexThreefoldOfGluing")
A finite connected gluing with compatible complex atlases and a compact, Hausdorff,
second-countable glued space defines a compact connected complex threefold. Smoothness of its
underlying real atlas follows by restriction of scalars.
:::

:::theorem "paper-threefold-assembly" (parent := "compact-complex-threefold") (lean := "SphereSixComplex.Geometry.AnalyticData.compactComplexStar, SphereSixComplex.CompactComplexStar.toComplexThreefold, SphereSixComplex.SmoothSixSphere.nonempty_diffeomorph, SphereSixComplex.exists_complexThreefold_simplyConnected_homologyEquiv_sixSphere")
If that gluing carries the concrete van Kampen generators with no extra relations and the
four-piece Mayer--Vietoris comparison, the glued threefold is simply connected and has
degreewise integral homology isomorphic to that of the six-sphere. The recognition theorem
takes these properties directly and concludes existence of a diffeomorphism.
:::

:::theorem "fundamental-group" (parent := "construction_spine") (lean := "SphereSixComplex.Geometry.AnalyticData.star_simplyConnectedSpace") (priority := "high")
For the twists $`(\ell_0,\ell_1,\ell_2)=(0,1,-1)`, the fundamental group of $`X` is trivial.
:::

:::proof "fundamental-group"
Apply van Kampen to {uses "compact-complex-threefold"}[the glued threefold] and reduce the resulting
presentation using the explicit lattice coinvariants.
:::

:::theorem "fundamental-group-recognition" (parent := "fundamental-group") (lean := "SphereSixComplex.Topology.HasVanKampenData.exists_fundamentalGroup_equiv, SphereSixComplex.Topology.HasVanKampenData.simplyConnectedSpace")
Once van Kampen identifies the fundamental group with the obstruction group, the selected twists
make it trivial and hence make the path-connected threefold simply connected.
:::

:::theorem "fundamental-group-presentation" (parent := "fundamental-group") (lean := "SphereSixComplex.Topology.hasVanKampenData_of_fullRelations, SphereSixComplex.Topology.paperRelation_iff_classifier_zero, SphereSixComplex.Topology.paperPresentedGroupEquiv, SphereSixComplex.Topology.paperCanonicalEquiv, SphereSixComplex.Topology.HasVanKampenData.exists_fundamentalGroup_equiv, SphereSixComplex.Topology.HasVanKampenData.simplyConnectedSpace")
The three van Kampen generators reduce to a two-generator integral presentation.  Its relation
lattice is exactly the kernel of the cyclic classifier, so the quotient has order
$`|12\ell_0-4\ell_1-3\ell_2|`.  Concrete generators satisfying the relations, generating the
fundamental group, and having no additional exponent relations give the canonical presentation;
for the selected twists it supplies the paper's fundamental-group contract.
:::

:::theorem "van-kampen-generation" (parent := "fundamental-group-presentation") (lean := "SphereSixComplex.Topology.PaperVanKampenFourPieceCover.localFundamentalGroupImages_generate, SphereSixComplex.Topology.PaperVanKampenFourPieceCover.coreFundamentalGroupMap_surjective_of_overlap_surjective, SphereSixComplex.ChartedSpace.stronglyLocallyContractibleSpace, SphereSixComplex.ChartedSpace.semilocallySimplyConnectedSpace")
A subgroup of $`\pi_1(X)` containing the images of the four local fundamental groups is
everything.  The proof is the covering-space one: the subgroup is realised by a covering whose
recovered subgroup is exactly it, the hypotheses lift each piece through that covering, the lifts
agree on the path-connected overlaps, and the glued section splits the covering's $`\pi_1` map.
The covered space must be locally path connected and semilocally simply connected, which every
charted space over a normed model is.  Consequently the core inclusion surjects on $`\pi_1(X)`
as soon as each filling's fundamental group is generated by its overlap with the core.
:::

:::theorem "local-fundamental-groups" (parent := "fundamental-group-presentation") (lean := "SphereSixComplex.QuotientCoverMapData.fundamentalGroupEquiv_natural, SphereSixComplex.toricFillingPiOneData, SphereSixComplex.cyclicAffineFillingPiOneData")
For a regular quotient cover with simply connected total space the fundamental group of the base
is the opposite deck group, and an equivariant square induces the deck homomorphism, so the toric
and cyclic filling computations are pure group theory about that homomorphism: surjectivity and
the normal-closure presentation of its kernel.  Transporting the affine core presentation along
the surjection onto $`\pi_1(X)` reduces the van Kampen contract to collar surjectivity and the three
star filling relations. Both geometric statements are proved for the constructed star.
:::

:::theorem "integral-homology" (parent := "construction_spine") (lean := "SphereSixComplex.Geometry.AnalyticData.star_nonempty_homologyEquiv_sixSphere") (priority := "high")
The integral homology of $`X` is the integral homology of $`S^6`.
:::

:::proof "integral-homology"
Compute the Mayer--Vietoris sequence of {uses "compact-complex-threefold"}[the same gluing], including
the integral specialization maps and their saturation.
:::

:::definition "homology-sphere-contract" (parent := "integral-homology") (lean := "SphereSixComplex.HasIntegralHomologyOfSixSphere")
The homology condition is a degreewise additive equivalence between integral singular homology and that of the standard six-sphere. Simple connectedness is proved separately.
:::

:::definition "mayer-vietoris-contract" (parent := "integral-homology") (lean := "SphereSixComplex.IntegralMayerVietoris.exact_sequence_of_isOpen, SphereSixComplex.establishedFourPieceMayerVietorisExactness, SphereSixComplex.FourPieceMayerVietorisExactness")
Binary open-cover exactness for integral singular homology is proved using chain corestriction,
subdivision, excision, and the cover-small chain comparison. Applying it to the three successive
unions in the four-piece cover gives the Mayer--Vietoris sequences used in the construction.
The actual inclusion maps and their coordinate comparisons are computed separately.
:::

:::theorem "section-seven-integer-algebra" (parent := "integral-homology") (lean := "SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra.range_orderOneRelationMap_eq_ker, SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra.range_orderTwoRelationMap_eq_ker")
The two integral relation maps in Lemma 7.13 have images equal to the kernels of their respective coordinate classifiers. These identities give the required exact integral presentations.
:::

:::definition "section-seven-paper-assembly" (parent := "integral-homology") (lean := "SphereSixComplex.Geometry.AnalyticData.PositiveDegreeHomologyAssembly, SphereSixComplex.Geometry.AnalyticData.PositiveDegreeHomologyAssembly.toSectionSevenMayerVietorisHomologyAssembly")
For the actual four-piece star, degree zero is proved canonically. The constructed
`PositiveDegreeHomologyAssembly` records the positive-degree cusp-attachment identifications and
compatibility squares. Its fields describe the actual maps; none assumes the completed star's
homology.
:::

:::theorem "cusp-filling-homology" (parent := "section-seven-paper-assembly") (lean := "SphereSixComplex.CellularHomology.normalizedModel, SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberCWDecomposition, SphereSixComplex.Geometry.CuspPuncturedCollarBridge.establishedStandardA2ToricCentralFiberCellularIncidence, SphereSixComplex.Geometry.AnalyticData.cuspFillingHomologyOneEquiv, SphereSixComplex.Geometry.AnalyticData.cuspFillingHomologyTwoEquiv")
The cusp filling has homology $`\mathbb Z^2,\mathbb Z^4,\mathbb Z^2,\mathbb Z` in degrees one
through four. The standard $`A_2` CW decomposition and its incidence formula are proved. The
retained general cellular-to-singular comparison transfers this cellular calculation to singular
homology.
:::

:::theorem "elliptic-multiple-fibre-homology" (parent := "section-seven-paper-assembly") (lean := "SphereSixComplex.AffineCyclicQuotientHomology.reducedCentralFiberHOneEquivPresentation, SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.orderThreeReducedCentralFiberHOneEquivIntSquared, SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.orderFourReducedCentralFiberHOneEquivIntSquared, SphereSixComplex.Topology.FiniteCoverPerfectPairing.orderThreeFixedHOneBasis_projection, SphereSixComplex.Topology.FiniteCoverPerfectPairing.orderFourFixedHOneBasis_projection, SphereSixComplex.Topology.FiniteCoverPerfectPairing.orderThreeHOneNaturality, SphereSixComplex.Topology.FiniteCoverPerfectPairing.orderFourHOneNaturality, SphereSixComplex.Topology.FiniteCoverPerfectPairing.ellipticDegreeTwoPullbackBases, SphereSixComplex.Topology.FiniteCoverPerfectPairing.ellipticFiniteCoverHomologyRealization")
The order-three and order-four reduced central fibres have explicit first-homology presentations,
and the fixed bases satisfy the required covering-projection coordinate formulas. The affine
cyclic-quotient abelianization and degree-one naturality statements are proved.

In degree two, proved quotient-homology realizations are converted to perfect-pairing packages.
Together these give `ellipticFiniteCoverHomologyRealization` for the two covers, including the
actual pullback calculation. No specialized finite-cover realization axiom is retained.
:::

:::theorem "section-seven-top-degree-vanishing" (parent := "integral-homology") (lean := "SphereSixComplex.subsingleton_integralSingularHomology_of_isEmpty_cell, SphereSixComplex.FourTorusHomologicalModel.subsingleton_homology_five, SphereSixComplex.FourTorusHomologicalModel.subsingleton_homology_six, SphereSixComplex.subsingleton_homology_succ_finiteBouquetMappingTorus, SphereSixComplex.contractibleSpace_openInterval, SphereSixComplex.subsingleton_homology_prod_of_contractible, SphereSixComplex.subsingleton_homology_seven_union, SphereSixComplex.OpenEmbeddingStarData.sectionSevenStageTopDegreeVanishing_of_localFinite, SphereSixComplex.subsingleton_homology_six_of_radialMappingTorus, SphereSixComplex.Geometry.AnalyticData.subsingleton_homology_six_actualCuspCollar, SphereSixComplex.Geometry.AnalyticData.subsingleton_homology_six_orderThreeCollar, SphereSixComplex.Geometry.AnalyticData.subsingleton_homology_six_orderFourCollar, SphereSixComplex.Geometry.AnalyticData.subsingleton_homology_six_collarSource_of_cusp, SphereSixComplex.Geometry.AnalyticData.stageTopDegreeVanishing_of_actualCuspCollar, SphereSixComplex.Geometry.AnalyticData.stageTopDegreeVanishing")
The Mayer--Vietoris comparison of the four pieces needs the three intermediate unions to have no
seventh homology, which follows from the four pieces having none and the three collar sources
having no sixth. `stageTopDegreeVanishing` supplies that obligation for the
actual star, with no hypotheses left.

The deduction is a dimension argument. A CW complex has no homology in a degree carrying no cells,
since its cellular chain group there is already zero; a `FiniteCWModelSix` records a CW structure on
a homotopy-equivalent carrier, so a zero cell count in a degree suffices, and a `FourTorusCellModel`
has zero counts in degrees five and six. The Wang sequence transfers this to a mapping torus: its
incoming term is the fibre's homology in the same degree and its outgoing term the fibre's one
degree below, so a fibre with nothing in degrees five and six leaves the mapping torus with nothing
in degree six. A contractible factor is discarded up to homotopy equivalence, and an open real
interval is contractible because it is convex and nonempty.

Each collar is realized as a radial interval times a mapping torus. For the two elliptic collars the
fibre is the additive four-torus of the period family, and for the cusp collar the fibre is
identified with a full-rank additive four-torus by the corresponding field of
`_root_.SphereSixComplex.Geometry.CuspPuncturedCollarBridge.ActualPuncturedCuspCollarWitness.radialClutchingData`. In every case the four-torus cell model then gives the
fibre nothing in degrees five and six.

This deduction uses the retained general cellular-to-singular comparison. The Wang sequence,
standard four-torus cell model, elliptic angular fundamental domains, and cusp radial clutching
model, including its fibre identification, are proved in the development.
:::

:::theorem "smooth-recognition" (parent := "construction_spine") (lean := "SphereSixComplex.SmoothSixSphere.nonempty_diffeomorph, SphereSixComplex.exists_complexThreefold_nonempty_diffeomorph_sixSphere") (priority := "high")
The underlying standard smooth manifold of $`X` is diffeomorphic to $`S^6`.
:::

:::theorem "established-smooth-recognition" (parent := "smooth-recognition") (lean := "SphereSixComplex.SixSphere.has_spherical_generator_of_homology, SphereSixComplex.SmoothSixManifold.hasCWType, SphereSixComplex.CWType.homological_whitehead_property, SphereSixComplex.SmoothSixSphere.poincare, SphereSixComplex.SmoothSimplyConnectedIntegralHomologySixSphere.nonempty_homotopyEquiv")
The recognition argument uses the retained higher Hurewicz and homological Whitehead theorems,
CW type obtained from the general finite-CW-model theorem for compact smooth manifolds, and smooth
Poincaré classification in dimension six. The first three steps produce a homotopy sphere; the
last gives a diffeomorphism for its specified smooth atlas. These are general classical results,
not assumptions about the complex-geometric construction.
:::

:::theorem "hurewicz-whitehead-reduction" (parent := "smooth-recognition") (lean := "SphereSixComplex.HasTopDimensionalSphericalGenerator, SphereSixComplex.homotopyEquivSixSphere_of_sphericalGenerator_of_classicalCWWhitehead, SphereSixComplex.SmoothSimplyConnectedIntegralHomologySixSphere.nonempty_homotopyEquiv")
Hurewicz supplies a comparison map $`S^6 \to X` inducing an isomorphism on sixth homology. The
proved degree-zero calculation and vanishing in the other degrees make it an integral-homology
equivalence; simply connected homological Whitehead then makes that same map a homotopy equivalence.
:::

:::proof "smooth-recognition"
Combine {uses "fundamental-group"}[simple connectedness] and
{uses "integral-homology"}[integral homology] to obtain a homotopy sphere, then use six-dimensional
smooth homotopy-sphere recognition.
:::

:::theorem "standard-six-sphere" (parent := "smooth-recognition") (lean := "SphereSixComplex.sixSphere_isPathConnected")
The standard six-sphere is path connected.
:::

:::theorem "standard-sphere-homology-zero" (parent := "standard-six-sphere") (lean := "SphereSixComplex.sixSphereHomeomorphTopCatSphereSix, SphereSixComplex.sixSphere_integralSingularHomology_zero_equiv_integer")
The concrete six-sphere is homeomorphic to the standard topological sphere, and its degree-zero integral homology is $`\mathbb Z`.
:::

:::theorem "standard-sphere-positive-homology" (parent := "standard-six-sphere") (lean := "SphereSixComplex.SixSpherePositiveHomologyInputs, SphereSixComplex.sixSpherePositiveHomologyInputs")
The standard six-sphere has integral homology $`\mathbb Z` in degree six and zero in every other positive degree. The retained construction proves both parts of this calculation.
:::

:::proof "standard-sphere-positive-homology"
Apply {uses "mayer-vietoris-contract"}[the binary open-cover Mayer--Vietoris sequence] to the
complements of two antipodal points of $`S^{d+1}` and induct on the dimension from the circle.
:::

:::theorem "relative-disk-sphere-homology" (parent := "standard-six-sphere") (lean := "SphereSixComplex.relativeIntegralSingularShortComplex_shortExact")
Relative integral singular chains are defined by a categorical cokernel. The inclusion and quotient maps form a short exact sequence of chain complexes.
:::

:::theorem "singular-small-chain-excision" (parent := "relative-disk-sphere-homology") (lean := "SphereSixComplex.coverSmallAffineSubdivisionEventuallySmall_of_openCover, SphereSixComplex.coverSmallChainQuasiIsomorphism_of_openCover, SphereSixComplex.barycentricOuterFaceIdentity")
Iterated affine subdivision makes each singular chain subordinate to any open cover. The resulting cover-small inclusion is a quasi-isomorphism. The barycentric outer-face identity provides the boundary calculation used by subdivision.
:::

:::theorem "sphere-stereographic-simple-connectivity" (parent := "standard-six-sphere") (lean := "SphereSixComplex.sixSphere_compl_singleton_simplyConnected, SphereSixComplex.sixSphere_simplyConnected_iff_loops_nullhomotopic")
Removing any point from the standard six-sphere gives a simply-connected Euclidean chart.  Global
simple connectedness is reduced exactly to nullhomotopy of every based loop.
:::
