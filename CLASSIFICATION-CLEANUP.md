# Statement audit and classification pruning

This pass starts from S6 `be9eb1d` and SmoothSixSphere
`89f53697e3a7f253b9969f5efe296dc3a9ba9ec0`. It audits the mathematical statements
and prunes unused classification declarations. Tactic modernization, general
linter cleanup and cold-build benchmarking are outside this pass.

## Preserved artifact surface

- S6: `sphere_six_admits_complex_structure` and `mathoverflow_1973`.
- SmoothSixSphere: `NoExoticSixSphere.noExoticSixSpheres`.
- Preserve the independently supplied smooth atlas in sphere recognition.
- Each endpoint must retain exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Baseline

The classification package contains 6,789 Lean modules and 641,776 lines.
Its build succeeds; existing upstream linter/deprecation warnings remain.
There are no `maxHeartbeats` overrides or wholesale `import Mathlib` commands.
The initial conservative inventory lists 2,419 candidate declarations covering
16,839 lines. Candidates require source-boundary review and successful rebuilds;
proof-term unreachability alone does not establish safe deletion.

An incremental baseline build took 9.64 seconds. This measures cache validation,
not fresh compilation, and is not evidence of a cleanup speedup. Raw logs and
inventories are kept locally under `.ci/classification-cleanup/`.

## Progress

- [x] Trace both endpoint statements to Mathlib's mathematical objects.
- [x] Independently review the classification interface.
- [x] Refresh compiled dependency ranges and review isolated theorem deletions.
- [x] Rebuild classification and audit its exact axiom closure.
- [x] Repeat tracing to identify newly exposed dead declarations.
- [x] Pin the verified dependency and rebuild/audit its S6 consumers.

Comparator's cleanup run was stopped at its five-minute limit without a verdict.
Its build step completed successfully. Its permitted axioms remain the three
standard axioms; no verification configuration was weakened. The local macOS run
uses fake-landrun and does not test Linux sandbox isolation.

The full S6 build passed all 17,298 jobs. Both endpoints and the construction
passed the exact axiom audit with only the standard three axioms. Import/layer
checks passed for all 733 project modules, and the placeholder check found only
the two intentional Comparator challenge placeholders. Blueprint built all 17,998
jobs and passed its HTML index, manifest and HTML-cache checks. Its manifest points
to the proved classification and excludes the removed smooth-Poincare axiom.
The final normal-context rebuild and exact axiom audit also passed. Comparator
remains incomplete, as recorded above. No cold-build speedup is claimed.

## Statement audit

`SphereSixComplex.SixSphere` is the unit sphere in `EuclideanSpace ℝ (Fin 7)`;
the complex chart model is `EuclideanSpace ℂ (Fin 3)`. The endpoint uses Mathlib's
`ChartedSpace` and `IsManifold`, whose transition maps are complex differentiable
on their open domains. This is a complex atlas, rather than an almost-complex
tangent structure. The standard real sphere instance is Mathlib's stereographic
atlas. Restriction of scalars supplies the underlying real structure.

The audit found a distinction worth making explicit: the previous
`SmoothlyCompatible` predicate asked for some diffeomorphism between two atlases.
This sufficed for the existence result after transport, but did not assert that
the particular atlas was compatible through the identity map. It now requires a
diffeomorphism `d` satisfying `∀ x, d x = x`. The existing transport construction
provides this stronger witness by `d.apply_symm_apply`. Endpoint names remain the
same; the primary endpoint's unfolded mathematical statement is stronger.

The external classification theorem quantifies independently over the source
topology, smooth atlas and manifold instance, and turns a homeomorphism to the
standard sphere into a Mathlib diffeomorphism for that same atlas. Its public
statement now spells out those quantifiers instead of the `SixSphereRigidity`
proposition wrapper; the type is definitionally unchanged.

These checks trace statement semantics and atlas preservation. They do not amount
to a human review of every proof in the classification development. The axiom
audit checks assumptions, while compilation checks proof terms.

The diffeomorphism is a noncomputable Lean object with smoothness proofs in both
directions. This supplies compatibility with the standard smooth sphere; it does
not provide a coordinate formula or an algorithm for evaluating the map.

## First deletion batch

An independent conservative source review approved 1,162 unused theorem commands
across 866 files, totaling 12,274 lines. It checked source hashes, disjoint ranges,
whole-command boundaries, attached comments, and absence of attributes or explicit
elaboration side effects. Definitions, abbreviations, and direct-term proofs were
deferred. The classification rebuild passed all 11,021 jobs without restoring a
deletion. The remaining source in all 866 pruning files matches the baseline
byte-for-byte after applying only those deletions. The package now contains
629,506 lines: a net reduction of 12,270 lines after expanding the public statement.

Build warnings decreased from 1,903 to 1,860. Comparing messages independently of
shifted source line numbers found no new warnings. The remaining upstream warnings
are outside this pass's scope. The strict classification audit checked 136,495
constants and found exactly the three standard axioms. A separate Lean check
confirmed that the expanded public theorem still inhabits the original
`SixSphereRigidity` type. The second full trace records 70,067 project constants,
49,308 live project constants, and the same 136,495-constant total closure with
exactly the standard axioms.

The verified dependency revision is
`613af5fc94f43562c18d4e9ae8936beebaaf1b29`. The second conservative inventory lists
1,652 remaining review candidates covering 8,851 lines, including newly exposed
dependencies of removed theorems. These are candidates for a subsequent batch;
this pass does not claim to remove all dead declarations.

The module inventory identifies 29 newly declaration-empty files and about
109,000 remaining lines in initially proof-term-dead modules. These are future
review opportunities, not approved deletions: imports, notation, attributes and
discarded tactic hints can be necessary for elaboration. Bypassing empty modules
requires preserving their import visibility and re-exports.
