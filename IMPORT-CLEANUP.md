# Bounded import and dead-code cleanup

Baseline: `d41014f` (Lean 4.34.0-rc1).

## Import pass

Native `lake shake` supplied the candidates. This pass removed 325 public import lines from
238 files: only recommendations also independently verified as transitively redundant through
other public imports. Both the total and public import closures of every project module are
unchanged. All non-import source text is byte-identical to the baseline. The aggregate modules,
challenge files, solution, axiom catalog, and dependency pins are unchanged.

Shake's broader suggestions, including public-to-private changes and added tactic imports,
were not applied. This is an import-maintenance improvement, not a measured build-speed gain.

## Dead-code analysis

All 1,231 library modules are reachable from `SphereSixComplex.Main`. The final theorem's
module cone contains 1,095; the other 136 remain part of the complete library advertised in
`MODULE-LAYOUT.md`. Blueprint references and construction-audit roots also protect intermediate
results. No public module was deleted.

A source-only screen of 1,636 private declarations found three plausible unreferenced helpers:

- `normalizedAffineCover_positiveCircleCross_fixed_boundary`
- `normalizedAffineCover_positiveCircleCross_boundary_add`
- `boundarySevenFaceNeighborhoodCechRowXIso`

They remain in place. Deleting them requires compiled dependency analysis and checks for
elaboration-time uses; lexical absence alone is insufficient.

## Scope and validation

This pass excludes declaration deletion, lint cleanup, tactic modernization, proof golf,
heartbeat work, wholesale-Mathlib rewrites, and clean-build benchmarking. The baseline already
has no `maxHeartbeats` overrides or wholesale `import Mathlib` lines. Existing linter warnings
are outside this pass.

Validation passed: full build, Blueprint build, import-layer and placeholder checks,
unchanged non-import source and protected-file hashes, recursive axiom audits, and Comparator.
The recursive axiom allowlists have zero additions or removals. The full build introduced no
new warning headers relative to the baseline. Comparator accepted the solution with Lean's
default kernel; this macOS run does not provide Linux Landrun isolation.
