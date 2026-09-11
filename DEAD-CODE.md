# Declaration-level pruning

The retained formalization is rooted only at the two entries in `comparator.json`'s
`theorem_names`:

- `sphere_six_admits_complex_structure`
- `mathoverflow_1973`

These are the unqualified declarations in `Solution.lean`. The first delegates to the project's
smooth-compatible complex structure theorem; the second forgets the additional smooth-atlas
compatibility. README and Blueprint references, historical notes, and aggregate imports do not
add mathematical roots.

## Method

Starting from the compiled baseline `309b081`, the audit follows constants occurring in both
types and proof or definition bodies. Opaque values are read with `allowOpaque := true`.
Private declarations and generated helpers participate in the same graph. Inductive families,
constructors, and recursor rules are followed so that the analysis does not treat an isolated
projection or constructor as independent of its datatype.

A constant outside this term dependency closure is not automatically safe to delete. Lean source
elaboration can still need notation, instances, simplification lemmas, local helpers, or named
intermediate rewrites that disappear from the final proof term. Lean’s `.ilean` metadata records
the constants actually referenced in retained source ranges;
these resolved references, rather than matching identifier spellings, extend the closure. Full
rebuilds identify additional implicit dependencies. These are elaboration requirements, not extra
mathematical endpoints. Declaration-range deletion also protects ranges
shared with retained generated declarations.

The initial conservative source-name scan was refined using resolved `.ilean` references after
review found collisions between local variables or Mathlib methods and unrelated project names.
The final analysis follows proof dependencies and resolved source dependencies to a fixed point,
with 19 required elaboration helpers and four local notations retained separately. The extra
`SmoothOpenEmbedding` coercion needed only by the false-positive cluster was removed with it.
The final rebuilt trace reports zero deletable source ranges and zero unused declaration-bearing
modules. Its two unresolved metadata references are existing `Lean.Linter.linter.defProp` option
names, not mathematical declarations.

In total, 282 empty modules were removed. Their importers now refer directly to surviving modules,
preserving public/private and `import all` visibility. Multiline imports were checked against the
compiled import inventory and pre-deletion source headers.

| Inventory | Before | After |
|---|---:|---:|
| Compiled project constants, including private/generated declarations | 40,020 | 25,902 |
| Constants in the two endpoints' term dependency closure | 21,228 | 21,228 |
| Lean files under `SphereSixComplex/` | 1,231 | 949 |
| Lines under `SphereSixComplex/` | 312,632 | 211,766 |

The constant counts include the solution and shared challenge-definition/catalog modules imported
by the trace. Generated constants without independent source declarations are not individually
removable. Source-range overlap protects a retained datatype and its generated declarations as a
unit. The larger retained environment also contains helpers needed to elaborate the source.

An exact-text audit checked 14,130 retained baseline source fragments. The sole exception is
`FullVanKampenRelations.translationMul_tailBasis_eq_one`: two `by simp` arguments became `by rfl`,
allowing two private coordinate lemmas to remain deleted. The retained theorem statements were not changed.

Obsolete Blueprint nodes were removed and mixed nodes narrowed to surviving results. The 292
distinct declaration links (301 occurrences) are checked against the retained environment. Historical
reduction notes remain explicitly historical. Documentation and aggregate imports do not retain
otherwise unused mathematics.

## Validation

The final tree passed:

- The full root `lake build`, including the solution endpoints.
- The separate Blueprint `lake build` and compiled checks of all 292 referenced declarations.
- `scripts/check-imports.py`: all 949 modules reachable, with no prerequisite-to-paper imports.
- `scripts/check-sorries.py`: only the two trusted challenge placeholders, none in the development.
- The strict recursive axiom audit and generated-catalog check.
- Comparator: “Lean default kernel accepts the solution” and “Your solution is okay!”
- `git diff --check` and the retained-source preservation audit described above.

The axiom refresh added and removed no constants. Comparator still uses Lean's three standard
axioms and ten classical results; the construction uses the standard three and seven classical
results. The challenge, shared definitions, axiom catalog, solution, Comparator configuration,
toolchain, and dependency manifest match their baseline hashes.

Comparator ran with the repository's macOS functionality wrapper; Linux Landrun isolation was
not tested by this run. Existing lint and missing-docstring warnings remain. Tactic modernization,
linter cleanup, and clean-build performance benchmarking were outside this pass.
