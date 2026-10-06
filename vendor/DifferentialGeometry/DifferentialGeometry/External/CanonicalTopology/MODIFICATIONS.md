# Local modifications to canonical-topology

The upstream snapshot is `4ca15d0de4c41f22bccc635a15178dfac88336bf`, authored by Ayush Khaitan. Original sources, documentation, package metadata and licenses are preserved in `upstream/source-4ca15d0de.tar.gz`; readable upstream documentation is under `upstream/canonical-topology/`.

## Common adaptation

- Replace code namespace `Poincare` with the existing `DifferentialGeometry` namespace, retaining the current public API.
- Redirect upstream imports to `DifferentialGeometry.External.CanonicalTopology`; file paths and namespaces intentionally differ.
- Restore original comments, docstrings and attribution. No source/documentation deletion policy for native code is applied to this vendor.
- Preserve local generalizations and proof repairs of upstream declarations as third-party-derived code. Keep newly added native mathematics in the original topic modules.
- `SOURCE_MAP.json`, unified migration patches and `migrate.py` record and replay every change. The snapshot contains 146 original leaf modules; three previously extracted upstream declarations occupy two additional external modules.

## Declaration-level reconciliation

### EuclideanLocalTop.lean

- All upstream declarations and original documentation restored unchanged except import and Poincare-to-DifferentialGeometry namespace remapping. Eight native generator declarations remain at the native path and consume the external equivalences.

### LocalDerivativeComparison.lean

- integralRelativeHomologyMap_eq_derivative: replace a show/from proof term for hcompare n with an explicitly typed term; statement unchanged.

- exists_ball_local_homologyMap_translation_eq_det_sign (private): replace three show/from type ascriptions for translated continuity with explicitly typed proof terms; statement unchanged.

- integralLocalHomologyOpenPartialHomeomorphIso_translation_eq_det_sign: replace two show/from ascriptions of eventually-left/right-inverse proofs with explicitly typed terms; statement unchanged.

- Original upstream module contains no comments or documentation to restore; all upstream declarations are retained in External. No native additions; delete the old native module and rewrite its importers.

### LocalLinearMaps.lean

- integralHomologyContractibleCoverEquiv_natural and integralHomologyOneContractibleCoverEquiv_natural (private): extract the naturality rewrite proof into a local hnat before rw; statements unchanged.

- integralLocalTopHomologyMap_reflection (private): extract the connecting-map naturality rewrite proof into a local hnat before rw; statement unchanged.

- integralRelativeHomologyMap_positive_diagonal (private): replace a show/from proof ascription with a typed funext term; statement unchanged.

- Original upstream module contains no comments or documentation to restore; all upstream declarations are retained in External. No native additions; delete the old native module and rewrite its importers.

### LocalOrientation.lean

- All upstream declarations restored unchanged except imports and namespace remapping. Original module has no comments/docstrings. Native integralLocalHomology_generator_of_orientation_coordinates remains native; its local J now composes the two public external homology isomorphisms directly, avoiding access to upstream private normalizedChartLocalIso. The upstream helper remains private and unique in External.

### OneDimensionalSphere.lean

- Generalize InnerProductSpace ℝ E to NormedSpace ℝ E and remove the public FiniteDimensional ℝ E assumption. The dimension-one equality supplies the finite-dimensional instance locally in oneDimUnitSphere_eq_or_antipode via Module.finite_of_finrank_eq_succ hd.

### Relative.lean

- Native additions retained: `integralAbsoluteToRelative_injective_of_subsingleton`, `integralRelativeConnecting_liftCycles_apply`.

### SpherePuncture.lean

- Move unitSphere_ne_antipode before the inner-product-space section and generalize its assumption to NormedSpace ℝ E; all other upstream declarations retain their original bodies and hypotheses.

- Native additions retained: `integralSingularHomology_subsingleton_of_punctured_sphere`.

### SphereRank.lean

- Move both declarations into a NormedSpace ℝ E section, removing their InnerProductSpace and FiniteDimensional hypotheses; retain the stronger original section for hyperplane rank and sphere path-connectedness, with the existing omit scope unchanged.

### CochainExcision.lean

### ManifoldFundamentalClass.lean

- Restored upstream proof of exists_unique_absolute_generator_of_tangent_orientation_locality: inline tangentChartOrientation definition and generator/bijectivity argument replace the local refactor through integralLocalHomology_generator_of_orientation_coordinates. Public signature unchanged; restoration removes backward dependency on a native extension.

### RelativeCapToAbsoluteHomology.lean

- Restored upstream proof body of integralRelativeCohomologyCapToAbsolute_bijective_map (direct naturality and composition of bijections), instead of local proof via the new native integralRelativeCohomologyCapToAbsolute_bijective_map_iff. Public signature unchanged; restoration prevents external-to-native import cycle.

- `Topology/Homology/PathCones.lean`: Retains local implementation strengthening: choose upstream exists_integralPathTriangle rather than exists_integralPathTriangle_boundary, preserving chosen face equations needed by native extensions.

- `Topology/Homology/PathCones.lean`: Retains local signed-boundary proof from prescribed faces; inlines a local choose_spec fact instead of depending on native integralSingularConeTriangle_face, to keep external dependency direction self-contained.

- `Topology/Homology/SphereCapDuality.lean`: Retains current generalization from InnerProductSpace plus FiniteDimensional to NormedSpace with finrank=1; consumes renamed/generalized upstream helper in external OneDimensionalLocalCapDuality.

- `Topology/Algebra/Module/Pairing.lean`: Retains existing extraction and promotion of upstream private helpers to public declarations in namespace DifferentialGeometry; exact original proof bodies, no duplicate private implementation.

- `Topology/Homology/OneDimensionalLocalCapDuality.lean`: Retains extraction, public renaming and NormedSpace generalization of upstream private exists_local_cap_bijective_of_finrank_one; proof body retained, no duplicate private implementation.


### Orientation

`orientation_map_trans` returns to the external module. The native determinant and orientation-negation theorems remain in `Tensor/LinearAlgebra/Orientation`.

## Later canonical-topology checkpoint

Commit `f457fa93fe0a417f8e4d0f6413cf63edb8699c1c` extends the original checkpoint to 157 source modules. Its untouched source, documentation and license archive is `upstream/source-f457fa93fe.tar.gz`. An audit of all 181 visible Ayush-authored commits identified 72 further upstream declarations in 16 native files. These now live in 14 additional external modules and the existing external CochainExcision and RelativeCapToAbsoluteHomology modules. They include compactly supported cohomology, cap duality, point restriction naturality, manifold generators, and sphere orientation. Existing namespace qualifications and the public top-cap name are preserved. SOURCE_MAP.json records every declaration origin, extraction, source hash and unified patch. The sphere-orientation comparison bridge and 18 separately verified native extensions remain native.

## Declaration-linter reconciliation

The standard declaration linter requires data-instance names without underscores. The following seven exported instance identifiers were normalized; their types and implementations are unchanged, and there were no explicit source call sites outside their declarations:

- `integralSingularCycles_module` → `integralSingularCyclesModule`.
- `integralZeroCycles_module` → `integralZeroCyclesModule`.
- `integralSingularChainsIn_module` → `integralSingularChainsInModule`.
- `integralSingularSmallChains_module` → `integralSingularSmallChainsModule`.
- `integralRelativeZeroKernel_module` → `integralRelativeZeroKernelModule`.
- `integralZeroMapKernel_module` → `integralZeroMapKernelModule`.
- `integralReducedHomologyZero_module` → `integralReducedHomologyZeroModule`.

The private `integralReducedZeroMap_oneDimSphere_neg` in `LocalLinearMaps` no longer assumes `FiniteDimensional ℝ E`: its `finrank = 1` input suffices for the existing one-dimensional-sphere API. This is a genuine generalization, with the proof body unchanged. The original names, hypotheses, comments and source remain available in the pinned archive; updated migration patches record these differences.

## Lean 4.34 and current Mathlib compatibility

- `Topology/Homology/SimplexBasis.lean`: follow Mathlib's singular-simplex representation change from the deprecated function subtype to `Convexity.StdSimplex`. `integralSingularSimplexEquiv` remains exactly `TopCat.toSSetObjEquiv`; no replacement singular set, chains, or map is introduced.
- `Topology/Homology/AffineSimplex.lean`, `AffineChains.lean`, `AffineNaturality.lean`, `AffineSubdivision.lean`, and `FineAffineImages.lean`: express the same affine barycentric maps using the canonical finite-support weights, vertices, pushforward, and barycenter. Remove the now-unused `DecidableEq` parameter from `affineSimplexMap_vertex`; the proof constructs decidability locally. The affine pushforward identity uses Mathlib's finite-support sum transport.
- `Topology/Homology/LiftedSimplex.lean` and `LiftedFaces.lean`: retain the lifted finite coordinate space and its original linear face maps. Describe the simplex body as the range of the canonical weight embedding, and obtain its homeomorphism from Mathlib's embedding-to-range construction. The naturality statements still bind those same linear maps to the canonical simplex pushforwards.
- `Topology/Homotopy/PlaneTriangle.lean` and `TriangleFaces.lean`, and `Topology/Homology/PathEvaluation.lean` and `TriangleFilling.lean`: use the canonical simplex representation and interval homeomorphism while preserving the ordered vertices, exact edge parameters, and prescribed singular faces.
- `Topology/Homology/RelativeEmpty.lean` and `CohomologyVanishing.lean`: use the canonical zeroth vertex as the same nonempty-domain witness.
- Replace deprecated conditional rewrite names in the touched `AffineCones.lean`, `AffineSubdivision.lean`, `SubdivisionHomotopy.lean`, `RelativeCochains.lean`, `CohomologyVanishing.lean`, and `Topology/Manifold/TangentOrientation.lean`; simplify the disk-boundary membership proof in `Topology/LoopSpace/SpanningDisk.lean` as required by the current linter. These edits do not change their mathematical statements.
- Preserve all original source comments, documentation, attribution, licenses, and pinned archives verbatim. `SOURCE_MAP.json` and the corresponding reconciliation patches record the compatibility changes.

- `Topology/Homology/SimplexPushFaces.lean`: prove face evaluation using the same lifted homeomorphism, its established face-map compatibility, and Mathlib's singular-face evaluation law. The former definitional equality is now a propositional equality because the canonical embedding-to-range homeomorphism has a non-definitional inverse; the statement is unchanged.

- `Topology/Homology/BarycenterBounds.lean`: replace the old definitional unfolding of barycenter coordinates with the canonical `StdSimplex.weights_barycenter_apply` equation; all estimate statements and constants are unchanged.

- `Topology/Homology/LocalOrientation.lean` (eight occurrences) and `ZeroSphereOrientation.lean` (two occurrences): replace `if_pos`/`if_neg` with the official Lean 4.34 `ite_eq_left`/`ite_eq_right` theorem names. The deprecated declarations are wrappers around those same theorems with the same arguments; statements, proof structure, all comments, attribution, and strings remain unchanged.

- `Topology/Homology/SubdivisionAffineAgreement.lean`: replace the former definitional equality for affine evaluation with extensionality, surjectivity of the same lifted simplex homeomorphism, and its inverse law. The original linear extension, vertex list, singular simplex, and public statements remain unchanged.

- `Topology/Homology/LocalLinearMaps.lean`: replace the deprecated `Mathlib.Data.Sign.Basic` import with its official target `Mathlib.Basic.Sign.Basic`. The old module only re-exports this target; all declarations, scopes, proof bodies, comments, and attribution remain byte-for-byte unchanged.
