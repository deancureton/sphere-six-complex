# Direct disc homology refactor

The fixed endpoints are the two theorems in `comparator.json`; the permitted axioms
and challenge statements stay unchanged. This pass replaces the elliptic H₁ and
band-comparison proof routes. It does not attempt global tactic modernization.

## Baseline

- Commit: `a713389`, 771 library modules, 171,657 lines (verified from Git archive).
- Resumed on `codex/direct-disc-homology` on 2026-10-05.
- Lean 4.34.0 replaces 4.34.0-rc1 after the latter crashed on macOS.
- Mathlib cache retrieval refuses the toolchain mismatch; dependency source pins
  are unchanged. The resumed source build passed, 9,799 jobs, with existing warnings.
- Builds run at nice 15 with `LEAN_NUM_THREADS=3`; targeted emission uses one worker.
  Independent proof checks also run at low priority, with at most three active groups.
- No build-time speedup is claimed.

## Checkpoint gates

- [x] Check and integrate ordinary disc-circle H₁ relations.
- [x] Check and integrate midpoint band comparisons for orders three and four.
- [x] Trace dependencies from the two endpoints and prune superseded declarations.
- [x] Rebuild and repeat dependency analysis after pruning.
- [x] Check all 263 Blueprint references and build (10,114 jobs).
- [x] Run recursive axiom audit, import/layer and placeholder checks.
- [x] Run Comparator; default Lean kernel accepted both endpoints.
- [x] Record measured source inventory and final validation results.

The replacement files began as unimported drafts. A passing baseline build does
not validate those drafts. Only checked, integrated replacements justify deletion.

## Checked replacement components

LSP and targeted builds passed for the product-slice homotopy, product-loop
homology splitting, arbitrary circle winding at both punctures, complex-disc
circle logarithm, gluing identity, regular-period homology invariance, principal
gauge identity, disc null-homology, modular-coordinate factorization, marked
meridian identification, and the central-to-star Hurewicz comparison.

Both unconditional disc-circle filling relations and both midpoint band
compatibilities now pass LSP. Production consumers use the new routes. Shared radius and overlap
equivalence declarations have moved into their lower-level prerequisite modules,
without changing their statements.

The full integrated root build passed (9,817 jobs). Existing warnings remain;
the newly checked replacement modules have no diagnostics.

The fresh export contained 21,062 project constants; 16,398 were in the two
endpoint term closures, and 16,490 in the source-supported closure. All source
ranges matched their `.ilean` files. The two unresolved references are the known
linter-option metadata entries. Module-level scaffolding references and the
seventeen previously reviewed elaboration helpers are protected.

The first pruning pass selected 56 modules and 39 additional ranges. Three ranges
were local notation and have been restored; syntax is now protected separately.
Import visibility (`import all`) is preserved when bypassing deleted modules.
Original whitespace in unrelated files is preserved.

The current library inventory is 733 modules and 161,912 lines, compared with
771 modules and 171,657 lines in the Git baseline: a net reduction
of 9,745 lines including the new proofs. This is not a build-time benchmark.

The pruned root build passed (9,761 jobs). The second export also uses Lean's
canonical first-import ownership for generated constants, with source attribution
to the enclosing declaration for rangeless auxiliaries.

The second fresh export has 19,986 constants, with 16,397 in the endpoint term
closures and 16,498 in the source-supported closure. It reports zero remaining
dead source ranges or modules, zero missing `.ilean` files, and zero range
mismatches. The same two linter metadata references remain unresolved.

## Final validation

The Blueprint build passed (10,114 jobs), followed by another root build (9,761
jobs). All 263 unique Blueprint declaration references checked. Source and
`.ilean` hashes still match the second dependency audit after these builds.
Import/layer, placeholder, whitespace, and strict recursive axiom checks passed.
Comparator exited successfully with `Lean default kernel accepts the solution`
and `Your solution is okay!`. Its macOS fake-Landrun path does not provide Linux
process isolation.

The final theorem uses the standard three Lean axioms plus the same ten classical
assumptions; the construction uses the standard three plus the same seven.
Challenge statements, solution endpoints, Comparator configuration, axiom
allowlists, and dependency pins are unchanged. Existing linter/docstring warnings
remain. Audit scripts, reports, exports, and logs are retained locally under
`.ci/direct-disc-cleanup/` (ignored).
