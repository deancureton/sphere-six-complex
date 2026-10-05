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
- [ ] 5: profile the slowest modules and their import floors; optimize only measured costs.
- [x] 6: wholesale-Mathlib slimming has no candidates.
- [ ] 7: compare clean before/after builds under the same worker/priority limits.
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
costs are diffuse and lower priority. No performance edits are included yet.
