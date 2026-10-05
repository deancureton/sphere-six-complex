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
work runs at nice 15, with at most three active workers. The user reports the
machine will be mostly idle for the timing comparison. Dependency caches are
retained; `lake clean sphere-six-complex` cleans only the root package (this
Lake version's `clean` command accepts package names, not library names).

## Phases

- [x] 0: clean baseline timing, critical path, surface and tactic inventory.
- [x] 1: remove project warnings in independent file batches; record any fixes
  that would cross the declaration-statement fence before applying them.
- [x] 2: repeat the endpoint dependency audit, protecting elaboration support.
- [ ] 3: check unused imports and orphaned scaffolding; rebuild consumers.
- [x] 4: optional broad proof golfing is skipped; focus on warnings and measured costs.
- [ ] 5: profile the slowest modules and their import floors; optimize only measured costs.
- [x] 6: wholesale-Mathlib slimming has no candidates.
- [ ] 7: compare clean before/after builds under the same worker/priority limits.
- [ ] 8: assess whether the existing import, placeholder, and axiom gates need a new guard.

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
