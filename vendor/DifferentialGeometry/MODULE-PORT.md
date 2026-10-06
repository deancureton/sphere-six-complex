# Mechanical Lean module-system port

Original source commit: 788efe97894474c032de6dfb1289d515f613d15a.
All 389 retained Lean files receive this header transformation:
insert `module` before the first import; prefix original imports with `public`;
insert `@[expose] public section` after the last import. Additional visibility and identifier adaptations are listed below. Mathematical
content is preserved; original copyright headers and comments
remain. Original hashes are in UPSTREAM-SHA256.json, and MODULE-PORT.patch records
the complete source diff with zero context. Apply it to the original sources using
`git apply --unidiff-zero MODULE-PORT.patch`.

Reason: Lean 4.35rc3 prohibits importing legacy non-module files from module-system
files. The mathematical development compiled and its final adapter's axiom closure
was exactly the three standard Lean axioms before this header conversion. The
ported package and the module-system adapter have also passed compilation and an
axiom audit with the same three standard axioms.

## Visibility adaptations

The following helpers become public because exposed public definitions refer to
them in data-bearing terms. Statements and proof bodies are unchanged:

- `External/CanonicalTopology/Topology/Homotopy/StarConvexComplement.lean`: `starConvexComplementHomotopyEquivOfBound`, `complementPointInclusion`, `starConvexComplementPush`.
- `External/CanonicalTopology/Topology/Homology/RelativeEmpty.lean`: `integralAbsoluteToRelative_empty_bijective`, `integralRelativeToAbsoluteCohomology_empty_bijective`.
- `External/CanonicalTopology/Topology/Homology/CapProduct.lean`: `integralSingularSimplexSubinterval`.
- `Topology/Homology/Algebra/CokernelHomotopy.lean`: `descHom`, `desc_condition`.
- `Topology/Homology/Subdivision/Support.lean`: `small_vertices_mem`.
- `Topology/OpenBox.lean`: `realIooHomeomorph`.

`External/CanonicalTopology/Topology/Homotopy/TriangleFaces.lean` additionally
imports all of `Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex`
to retain the legacy proof's unfolding of `StdSimplex.homeomorphI`.
- `External/CanonicalTopology/Topology/Homotopy/StarConvexComplement.lean`:
  additionally `radialExpansion` and `radialExpansion_zero_mem_closedBall_complement`,
  required by the exposed `starConvexComplementPush` construction.

## Second visibility pass

Additional exported helpers required by public data definitions and their
transitive definition dependencies (statements/proofs unchanged):

- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/LocalStarConvex.lean`: `integralBoundedStarConvexToLocalChainMap_quasiIso`, `integralSingularChainMap_quasiIso_of_homotopyEquiv`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/CompactlySupportedCohomology/Defs.lean`: `compactSupportCohomologyMap`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/RelativeCapProduct.lean`: `integralRelativeCapProductLinear`, `integralRelativeCapProduct_ker`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/CapHomology.lean`: `integralSingularCapCocycles`, `integralSingularCapCocycles_boundary`, `integralSingularCocycle_closed`, `integralSingularUnitCocycle`, `integralSingularCapCocycles_class`, `integralSingularCapHomology`, `integralSingularCapHomology_class`, `integralSingularCapProduct_coboundary_is_boundary`, `integralSingularHomologyClass_eq_zero_iff`, `integralSingularCapProduct_boundary_apply`, `integralSingularCapProduct_boundary_is_boundary`.
- `DifferentialGeometry/Topology/Homology/Subdivision/Universal.lean`: `convex_simplexRegion`, `simplexSupportedChainIso`, `simplexRegion`, `simplexSupportedIso`, `simplexAmbient`, `simplexRegionHomeo`.

## Instance visibility

Private local instances used by public data definitions become public constants
with module-qualified names to prevent collisions. Their **local instance registration**
is preserved; they do not add global typeclass instances. The private directed-system
instance becomes public because it is needed to define the exported direct limit.

- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/CapHomology.lean`: `CapHomology.integralSingularCycle_module`, `CapHomology.integralSingularCocycle_module`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/CompactlySupportedCohomology/Cap.lean`: `Cap.compactSupportIntegerComm`, `Cap.compactSupportIntegerLinearModule`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/CompactlySupportedCohomology/Defs.lean`: `Defs.compactSupportCohomologyDirectedSystem`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/RelativeCapCohomologyConnecting.lean`: `RelativeCapCohomologyConnecting.connectingCycle_module`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/RelativeCapHomology.lean`: `RelativeCapHomology.capIntegerComm`, `RelativeCapHomology.capIntegerLinearModule`, `RelativeCapHomology.integralRelativeCycle_module`, `RelativeCapHomology.capCocycle_module`, `RelativeCapHomology.relativeCapQuotientModule`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/RelativeCapProduct.lean`: `RelativeCapProduct.quotientIntegerModule`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/RelativeCapToAbsolute.lean`: `RelativeCapToAbsolute.quotientIntegerModule`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/RelativeCapToAbsoluteHomology.lean`: `RelativeCapToAbsoluteHomology.capIntegerComm`, `RelativeCapToAbsoluteHomology.capIntegerLinearModule`, `RelativeCapToAbsoluteHomology.integralRelativeCycle_module`, `RelativeCapToAbsoluteHomology.capCocycle_module`, `RelativeCapToAbsoluteHomology.capCycle_module`, `RelativeCapToAbsoluteHomology.relativeCapQuotientModule`, `RelativeCapToAbsoluteHomology.absoluteCocycle_module`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/TwoPointCapDuality.lean`: `TwoPointCapDuality.dualityCycle_module`.
- `DifferentialGeometry/Topology/Homology/CompactlySupportedCohomology/CapGluing.lean`: `CapGluing.integerSmulComm`.

## Proactive data-dependency visibility

Remaining private dependencies of exported data constructions are module-qualified
and public, including their helper dependencies. This prevents identical original
private names in different files from colliding; proof-only private helpers in
already-checked definitions are retained. Types and proof bodies only receive the
corresponding identifier renames.

- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/CompactlySupportedCohomology/OpenEmbedding.lean`: `OpenEmbedding.compactSupportExcision`, `OpenEmbedding.compact_support_excision_mapsTo`, `OpenEmbedding.compact_support_excision_natural`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/ConnectedZeroCohomology.lean`: `ConnectedZeroCohomology.integralSingularCocycle_zero_eq_smul_augmentation`, `ConnectedZeroCohomology.integralSingularCohomologyClass_zero_eq_smul_unit`, `ConnectedZeroCohomology.integralSingularCohomologyUnit_smul_injective`, `ConnectedZeroCohomology.integralSingularCohomologyUnit_smul_surjective`, `ConnectedZeroCohomology.integralSingularCohomologyUnit_span_apply`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/LocalBallHomology.lean`: `LocalBallHomology.closedBall_shift_complement_mapsTo`, `LocalBallHomology.closedBall_shift_symm_complement_mapsTo`, `LocalBallHomology.integralClosedBallToLocalHomologyIso`, `LocalBallHomology.integralClosedBallTranslateIso`, `LocalBallHomology.integralLocalTranslateToZeroIso`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/LocalCompactHomology.lean`: `LocalCompactHomology.chart_inverse_image_subset_source`, `LocalCompactHomology.chart_pair_complement_mapsTo`, `LocalCompactHomology.chart_pair_complement_symm_mapsTo`, `LocalCompactHomology.complement_union_eq_univ_of_subset`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/RelativeCapHomology.lean`: `RelativeCapHomology.cap_cocycle_closed`, `RelativeCapHomology.chain_homology_class_eq_zero_iff`, `RelativeCapHomology.relativeCapCycleClasses`, `RelativeCapHomology.relativeCapCycleClasses_boundary_left`, `RelativeCapHomology.relativeCapCycleClasses_boundary_right`, `RelativeCapHomology.relativeCapQuotientPairing`, `RelativeCapHomology.relative_cap_boundary_is_boundary`, `RelativeCapHomology.relative_cap_coboundary_is_boundary`, `RelativeCapHomology.relative_cap_cycle`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/RelativeCapToAbsolute.lean`: `RelativeCapToAbsolute.relativeCochainCapLinear`, `RelativeCapToAbsolute.relativeCochainCapLinear_π`, `RelativeCapToAbsolute.relative_cochain_cap_ker`, `RelativeCapToAbsolute.relative_cochain_pullback_zero`.
- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/RelativeCapToAbsoluteHomology.lean`: `RelativeCapToAbsoluteHomology.cap_cocycle_closed`, `RelativeCapToAbsoluteHomology.chain_homology_class_eq_zero_iff`, `RelativeCapToAbsoluteHomology.relativeCapCycleClasses`, `RelativeCapToAbsoluteHomology.relativeCapCycleClasses_boundary_left`, `RelativeCapToAbsoluteHomology.relativeCapCycleClasses_boundary_right`, `RelativeCapToAbsoluteHomology.relativeCapQuotientPairing`, `RelativeCapToAbsoluteHomology.relative_cap_boundary_is_boundary`, `RelativeCapToAbsoluteHomology.relative_cap_coboundary_is_boundary`, `RelativeCapToAbsoluteHomology.relative_cap_cycle`.
- `DifferentialGeometry/Topology/Homology/CompactlySupportedCohomology/MayerVietoris.lean`: `MayerVietoris.compactSupportCoverConnecting`, `MayerVietoris.exists_compact_support_pair`, `MayerVietoris.relativeSupportMap`, `MayerVietoris.relativeSupportMap_comp`, `MayerVietoris.supportCoverConnectingAt`, `MayerVietoris.supportCoverConnectingAt_eq`, `MayerVietoris.supportCoverConnectingAt_mono`, `MayerVietoris.supportCoverPair`, `MayerVietoris.supportPairConnecting`, `MayerVietoris.supportPairConnectingFrom`, `MayerVietoris.supportPairConnectingFrom_independent`, `MayerVietoris.supportPairConnectingFrom_mono`, `MayerVietoris.supportPairConnecting_mono`, `MayerVietoris.unionIntersectionHomeomorph`.
- `DifferentialGeometry/Topology/Homology/CompactlySupportedCohomology/RelativeSupport.lean`: `RelativeSupport.compactSupportIn`.
- `DifferentialGeometry/Topology/Homology/MayerVietoris.lean`: `MayerVietoris.twoSetFamily_cover`, `MayerVietoris.twoSetFamily_open`.
- `DifferentialGeometry/Topology/Homology/Subdivision/Restriction.lean`: `Restriction.smallHomotopy_comm`, `Restriction.smallStraightening_zero`, `Restriction.smallSubdivision_comm`.
- `DifferentialGeometry/Topology/Homology/Subdivision/SimplexSmallness.lean`: `SimplexSmallness.convex_coordinateSimplex`.
- `DifferentialGeometry/Topology/Homology/Subdivision/SingularSupport.lean`: `SingularSupport.smallSingularSubdivisionHomotopy_comm`, `SingularSupport.smallSingularSubdivision_comm`.

Third-pass LocalBallHomology exports two further proof arguments required in
public declaration types: `point_complement_center_translation_mapsTo` and
`closedBall_complement_subset_point_complement_at`. Bodies unchanged.

## Public statement dependency audit

Helpers appearing in exported declaration signatures also become public:

- `DifferentialGeometry/External/CanonicalTopology/Topology/Homology/LocalCompactHomology.lean`: `chart_inverse_image_mem`.

## H-cobordism extension

The additional 168 modules increase the extraction from 30,675 to 173,638 original
Lean lines. They use the same upstream commit and header conversion. Private helpers
needed by exposed definitions are exported and consistently renamed
`portPrivate_<module hash>_<original name>` to avoid collisions. This changes
visibility and identifiers only; the complete renaming is recorded in the patch.

`Topology/Homology/Naturality.lean` also renames
`ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace` to
`ZerothHomotopy.dg_mk_injective_of_totallyDisconnectedSpace`, including its two
local references, to avoid a collision with TauCeti's declaration. Its statement
and proof are unchanged.

The following explicit Mathlib imports replace legacy transitive availability:

- `Analysis/Calculus/Derivative/AlmostEverywhereLipschitz.lean`: `ContDiff.Operations`, `Deriv.Comp`, and `Deriv.Pow`.
- `Topology/Homology/Bockstein.lean`: `HomologicalComplexAbelian`.
- `Topology/Homology/MayerVietoris/ShortExact.lean`: `HomologicalComplexAbelian` and `Limits.Preserves.SigmaConst`.
- `Topology/Manifold/ChartDisk/Construction.lean`: `Deriv.Inv`.
- `Topology/Morse/Attachment/ModelCell.lean`: `ContDiff.WithLp` and `Deriv.Prod`.
- `Topology/Morse/CriticalPoint.lean`: `import all Mathlib.Geometry.Manifold.LocalDiffeomorph`, preserving an existing unfolding.
- `Topology/Morse/Handle/Middle/Geometry/MiddleSlide.lean` and `Topology/Morse/Handle/Partners/PartnerCircle.lean`: `Topology.Algebra.Order.Floor`.
- `Topology/Morse/Handle/Middle/Geometry/MiddleWhitney.lean`: `LinearAlgebra.Dimension.OrzechProperty`.
- `Topology/Morse/Rearrangement/DistinctValues.lean` and `Rearrange.lean`: `Geometry.Manifold.Algebra.Structures`.
- `Topology/Morse/Strip/Foundations/GradientLike.lean`: public import and `import all` of `LinearAlgebra.QuadraticForm.Signature`, preserving existing unfoldings.

Two type annotations resolve elaboration ambiguities without changing the argument:

- `Topology/Homology/MayerVietoris/Relative.lean`: explicitly type the second zero morphism of the snake lemma's zero short complex.
- `Topology/Morse/RegularLevel/NoCriticalValues.lean`: specify `b := f y.1` in a `le_trans` application.

The expanded files compile against this project's pinned Mathlib. The regenerated
patch passes `git apply --check --unidiff-zero` against fresh copies of all 389
upstream sources; applying it reproduces every vendored Lean file byte for byte.
No new axioms, placeholders, or mathematical hypotheses are introduced by the port.
