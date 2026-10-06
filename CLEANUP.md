# Autoformalization cleanup

Baseline: `e3ab3d2` (2026-10-05), 733 library modules and 161,912 library lines.
Work stays on `main`. `Scratch/` is outside the task.

## Contract

The mathematical roots are the two declarations in `comparator.json`:
`sphere_six_admits_complex_structure` and `mathoverflow_1973`. This follows the
project's explicit retention policy; documentation and aggregate modules do not
add theorem roots. Preserve declaration names and docstrings. The user has explicitly authorized
refactoring proof internals: genuinely redundant internal hypotheses, instances,
and inert attributes may be removed, and proposition-valued definitions may
become theorems. Record those exceptions to the skill's default statement fence;
preserve all other surviving signatures. Preserve the endpoint statements
and the exact axiom allowlists. No new axioms, placeholders, heartbeat increases,
or linter suppression.

The checked baseline uses the standard three Lean axioms plus ten classical
assumptions for the final theorem, and the standard three plus seven for the
construction. Verbatim audit output is in `.ci/cleanup/baseline-axioms.log`.

## Inventory

- 279 project warning headers across 67 files in the preceding complete build.
- Zero `maxHeartbeats` overrides.
- Zero wholesale `import Mathlib` lines.
- 3,505 occurrences of `simp`, including 933 `simp only` occurrences.
- 579 unscoped `linarith` and 410 unscoped `nlinarith` occurrences. These counts
  identify candidates; they are not evidence that a tactic is slow.
- Lean 4.34.0: `lia`, `grind`, `fun_prop`, `grw`, and `bound` passed executable
  snippet checks. No toolchain upgrade is planned.

The inventory and file assignments are stored under `.ci/cleanup/`. All compiler
work runs at nice 15, with at most three active checker groups. Builds use
`LEAN_NUM_THREADS=3`; this is not a verified hard core cap. Direct profiling uses
explicit `lean -j1` after observing that the environment variable alone did not
keep direct Lean runs single-threaded. The user reports the
machine will be mostly idle for the timing comparison. Dependency caches are
retained; `lake clean sphere-six-complex` cleans only the root package (this
Lake version's `clean` command accepts package names, not library names).

## Phases

- [x] 0: clean baseline timing, critical path, surface and tactic inventory.
- [x] 1: remove project warnings in independent file batches; record any fixes
  that would cross the declaration-statement fence before applying them.
- [x] 2: repeat the endpoint dependency audit, protecting elaboration support.
- [x] 3: check unused imports and orphaned scaffolding; rebuild consumers.
- [x] 4: optional broad proof golfing is skipped; focus on warnings and measured costs.
- [x] 5: profile the slowest modules and their import floors; optimize only measured costs.
- [x] 6: wholesale-Mathlib slimming has no candidates.
- [x] 7: compare clean before/after builds under the same worker/priority limits.
- [x] 8: existing CI builds and import/placeholder/axiom gates retained; optional
  additional drift guard not added. Upstream warnings prevent a blanket warning-as-error gate.

Only the main agent runs Lake builds. Workers use Lean LSP for proof iteration.
Every editing checkpoint gets a root build, the relevant auxiliary checks, the
recursive axiom audit, and Comparator before commit/push. Dependency warnings and
the two intentional Comparator challenge placeholders are reported separately.

## Clean baseline

Root-package clean build passed: 1,106.10 seconds wall, 2,785.92 seconds user CPU,
and 824.62 seconds system CPU. All 733 library modules compiled. The sum of
per-module wall times is 2,737.1 seconds; the longest project import chain is
646.0 seconds. These are baseline measurements, not speedup claims.

Logs, `/usr/bin/time -l` output, module timings, and the full critical path are
under `.ci/cleanup/`. The dependency cache was already warm from a successful
source build; downloadable Mathlib caches reject the existing stable/RC
compiler-pin mismatch. No dependency pins or compiler version changed.

## Linter cleanup

The 67-file batch replaces deprecated names, removes unused simp arguments and
no-op tactics, and applies the compiler's proof-local instance and sequencing
recommendations. No linter was disabled. Local LSP checks were followed by a
combined build because several concurrent interface edits invalidated imports.

The authorized internal interface changes are:

- Reflection/Triangle and Reflection/Circle: remove unused seed parameters from
  three private closed-positive mapping helpers.
- Source/SidePairingClassification: remove the unused `hz` from
  `denominator_re_sq_le_half_of_bottomLeft_sq_eq_one`.
- Source/ChamberTopology: remove unused width hypotheses from
  `cuspExponential_differentiable` and `norm_cuspExponential`.
- Source/Branch: remove unused `hinvariant`, `hother`, and `other` from
  `ellipticChartFunction_order_le_stabilizer_card`.
- Reflection/TriangleSeed: remove unused boundary hypotheses from
  `scalarTriangleDiscMap_differentiableOn_ne_pole` and the unused first-boundary
  hypothesis from `scalarTriangleDiscMap_first`.
- Omit unused section instances from `toContinuesInside`, `mapOfEq_eq`,
  `mem_range_mapOfEq_of_path`, the three generator lemmas `piece_covers`,
  `lift_agree`, `range_map_id`, private `specializationHomologyOneMap_apply`,
  and its caller `specializationHomologyOneMap_fiberInclusion`.
- Remove inert `expose` attributes from the two elliptic boundary deck data
  definitions in FundamentalGroup/FillingCovers.
- MayerVietoris/Chains: make `coverSubcomplexBicartSq`,
  `coverSubcomplexIsPushout`, and `coverChainIsPushout` theorems rather than
  proposition-valued definitions, with the same propositions.

Callers were updated directly. No compatibility wrappers were introduced.
Endpoint statements, trust declarations, and axiom allowlists are unchanged.

The final root build passed with zero project warning headers (279 initially).
Warnings replayed from the external Jordan curve dependency and the two
intentional Challenge placeholders are outside this project-source count.
Blueprint, import-layer, placeholder, and exact recursive axiom checks passed.
Comparator accepted both endpoints with Lean's default kernel and the unchanged
allowlists. The macOS fake-Landrun wrapper checks functionality, not Linux process
isolation. The post-Blueprint root build also passed.

## Endpoint dependency audit

The first fresh trace contains 19,985 project constants. The endpoint term
closure contains 16,397; adding source references and 17 protected elaboration
helpers gives 16,498. There are no missing modules or source-range mismatches,
and no removable declaration ranges or modules. The two unresolved references
are linter-option metadata, not mathematical dependencies. Both endpoint proofs
have explicit dependency edges into the construction. The independent second trace reproduced all counts and found no deletions.

## Imports and scaffolding

Native `lake shake --keep-public` produced remove-only suggestions. Excluding
aggregate modules and the trusted Challenge module leaves 558 import lines in
228 implementation files. All non-import source text was checked unchanged;
module reachability and prerequisite layering still pass. The full consumer
build passed with zero project warnings. A reviewed follow-up removes 88 lines
of empty sections and trailing opens/variables from 13 files, preserving
proofs, signatures, docstrings, and attributes. Eight changed files passed LSP;
the full scaffold rebuild passed with zero project warnings. Import/layer,
placeholder, and protected-file checks passed again. Blueprint and the exact recursive axiom audit passed. The second Shake pass
reports only the two aggregate modules and trusted Challenge import retained by
policy; no implementation-file suggestions remain. Comparator accepted both
endpoints with the unchanged trust boundary. The post-Blueprint root build
also passed.

## Performance triage

Plain `lean -j1` profiles at nice 15 identify costs beyond import loading:

| Module | Wall seconds | User CPU seconds | Import-only wall |
| --- | ---: | ---: | ---: |
| Source/CuspWordCentralizer | 22.40 | 20.50 | 3.34 |
| Source/SidePairingClassification | 42.14 | 39.69 | 4.12 |
| Honeycomb/PositiveNeighbor | 49.06 | 45.57 | 3.37 |
| Honeycomb/SameCellMissingOrbit | 37.19 | 34.37 | 4.28 |
| Topology/Torus/Homology | 13.64 | 11.65 | 3.74 |
| Homology/First | 19.72 | 17.22 | 5.08 |

These diagnostic runs shared the machine with other checks and are not the
final A/B benchmark. Lightweight declaration profiles identify large-context
`simp_all`, repeated arithmetic preprocessing, and two expensive parallel
rewrites in first homology. Full tactic traces substantially perturb timings
and can exceed heartbeats; plain runs pass without overrides. Torus homology's
costs are diffuse and lower priority. The proof-only batches passed local and whole-project validation. Adjacent plain single-worker
measurements confirm CuspWordCentralizer at 20.42 → 10.62 user CPU seconds and
Homology/First at 17.15 → 5.62. The former avoids repeated normalization and
large-context Boolean simplification; the latter supplies explicit arguments
to two rewrites. SidePairingClassification reuses an existing norm-square lemma
to shorten two proofs by 30 lines (37.57 → 36.37 user CPU seconds). The smaller
change is not evidence of a substantial speedup. The honeycomb context-narrowing experiment was discarded after adjacent timings
showed no convincing gain. A different single-site experiment clears rational
denominators once before repeated arithmetic: PositiveNeighbor improves from
41.62 to 36.48 user CPU seconds. The two analogous sites also passed: against the one-site version, user CPU
fell from 36.72 to 25.61 seconds. PositiveNeighbor changes only three proof
lines. A separate SameCellFiniteIdentity reordering postpones coordinate case
splitting until after shared normalization, reducing user CPU from 14.99 to
12.90 seconds. Both have clean LSP, CLI, and targeted-build checks. CyclicOverlapIdentity
adds one denominator-clearing step and improves from 15.04 to 10.89 user CPU
seconds; its target build also passed. SameCellMissingOrbit applies the same
normalization at two sites, improving from 34.91 to 20.23 user CPU seconds with
clean LSP and adjacent CLI runs.
A second SidePairingClassification pass narrows arithmetic to its actual facts,
with adjacent timings of 34.24 → 32.43 user CPU seconds. All statements,
names, attributes, docstrings, and imports in this performance batch are
unchanged. An independent review checked every performance diff hunk against
`a9439da` and confirmed that all changes are inside existing proof bodies.

NeighborBoundary adds three denominator-clearing steps (18.15 → 12.25 user CPU
seconds). CorrectedPlaneTiles hoists fourfold duplicated normalization in two
proofs (19.70 → 10.25), and ThirdNeighbor does the same in one proof
(11.35 → 6.18). Each passed LSP and adjacent CLI checks. EllipticCorners and
Cells were also profiled: costs are distributed rather than concentrated in
a clear avoidable bottleneck. They remain unchanged; this is not a claim of
global optimality or that all files are import-bound.

## Final paired benchmark

The baseline checkout was `e3ab3d2` with an isolated
copy-on-write clone of the same dependency cache. Task-owned resident Lean
workers were closed. Both builds used nice 15 and `LEAN_NUM_THREADS=3`;
the root package alone was cleaned. A three-minute settling interval separated
the runs. The user reported mostly-idle machine conditions. Both builds passed,
compiling 733 library modules without rebuilding dependency modules. Source
fingerprints remained unchanged throughout the pair.

| Measurement | Before (`e3ab3d2`) | After |
| --- | ---: | ---: |
| Wall seconds | 1,007.64 | 970.30 |
| User CPU seconds | 2,445.69 | 2,350.17 |
| System CPU seconds | 745.02 | 738.44 |
| Sum of module wall seconds | 2,416.7 | 2,361.6 |
| Longest project import chain seconds | 618.3 | 588.6 |
| Project warning headers | 279 | 0 |

This pair measures 3.71% less wall time and 3.91% less user CPU time. The repeat
baseline itself was 8.90% faster than the initial baseline, so these are single
paired observations, not a precise or reproducible whole-project speedup claim.
The adjacent single-file measurements above give stronger evidence for the
specific retained proof optimizations. Unchanged files also varied substantially.

| Original slow modules | Before (s) | After (s) |
| --- | ---: | ---: |
| `Honeycomb.SameCellMissingOrbit` | 19 | 11 |
| `Honeycomb.PositiveNeighbor` | 18 | 12 |
| `Source.SidePairingClassification` | 15 | 15 |
| `Honeycomb.SameCellFiniteIdentity` | 15 | 13 |
| `Source.CuspWordCentralizer` | 14 | 7.7 |
| `PuncturedPlane.PairOfPants` | 13 | 6 |
| `Honeycomb.CyclicOverlapIdentity` | 13 | 10 |
| `Honeycomb.CorrectedPlaneTiles` | 12 | 7.6 |
| `Source.EllipticCorners` | 11 | 13 |
| `Homology.First` | 11 | 5.8 |

The final library has 733 files and 161,235 lines, 677 fewer than the baseline.
The performance batch alone removes 17 net lines across ten files.

## Final verification

The clean root build, Blueprint build, subsequent root build, and 263-name
Blueprint reference probe passed. The final endpoint dependency trace reproduced
the earlier closure counts: zero removable declaration ranges or modules, with
17 elaboration helpers protected. The final Shake pass suggests changes only to
the two aggregate modules and trusted Challenge import intentionally retained by
policy. Import reachability/layering, placeholder checks, and the exact recursive
axiom audit passed. The toolchain, dependency pins, Comparator endpoint contracts,
and axiom allowlists are unchanged.

Comparator accepted both endpoints with Lean's default kernel and the unchanged
allowlists. Its macOS fake-Landrun wrapper does not validate Linux process
isolation. The temporary baseline worktree was archived after benchmarking.
External dependency warnings and the two
intentional Challenge placeholders remain separate from the zero project-source
warning count. Benchmark logs, time output, dependency reports, and proof profiles
are retained locally under `.ci/cleanup/`; this ledger records their results.
