# Declaration-level pruning

The retained formalization is rooted only at the two entries in `comparator.json`'s
`theorem_names`:

- `sphere_six_admits_complex_structure`
- `mathoverflow_1973`

These are the unqualified declarations in `Solution.lean`. The first delegates to the project's
smooth-compatible complex structure theorem; the second forgets the additional smooth-atlas
compatibility. README and Blueprint references, historical notes, and aggregate imports do not
add mathematical roots.

## Initial pruning pass

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

## Initial validation

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

## Follow-up after interface cleanup

The later API cleanup made the separate intermediate-union vanishing branch unused. A fresh
compiled audit, again rooted only at the two Comparator theorems, found 37 candidate source ranges.
Eighteen declarations were removed, including five now-empty modules. The remaining 19 are the
previously established simp/elaboration helpers; their retained clients still need them. The live
Mayer–Vietoris union-vanishing lemma was moved unchanged into prerequisites. Its obsolete paper
module and the unused Blueprint branch were removed.

| Follow-up inventory | Before deletion | After deletion |
|---|---:|---:|
| Compiled project constants | 25,502 | 25,483 |
| Constants in the two endpoints' term closure | 21,031 | 21,031 |
| Library modules | 955 | 950 |

The live sets differ only in one generated proof helper after Lean re-elaborated the owner of
the removed predicate. Named mathematical dependencies are unchanged. The new resolved-source
audit has no missing `.ilean` files and only the same two linter-option metadata references.
No further deletion is justified by this audit without changing the retained proofs' elaboration
strategy. At that checkpoint, the library contained 210,895 lines and the Blueprint had 278
distinct declaration links.

The follow-up passed the full root and Blueprint builds, all 278 declaration-link checks, the
import/layer and placeholder checks, and the strict axiom audit. Comparator's default kernel
accepted the solution with the same permitted axioms. The construction audit no longer lists
the deleted helper as an extra root; its axiom closure is unchanged.

The subsequent naming and shared-homotopy cleanup was audited again. It retained the same 19
elaboration helpers and introduced no new candidate ranges: 25,473 compiled project constants,
21,024 in the endpoints' term closure. Both original fiber slices and both complete homotopies
were compared with the shared prerequisite definitions by four kernel-checked `rfl` proofs.

## Direct homology route

The final topology now uses cusp relations to prove that the fundamental group is abelian,
then applies first Hurewicz to its vanishing first homology. The elliptic full-iterate equation
is proved directly in first homology: the fiber and base factors can be transported independently,
because conjugation and basepoint transport preserve their homology classes.

A fresh compiled audit found 248 newly unused source ranges. Neither
`ellipticRelatorMembership` nor `actualStarHasVanKampenData` remained in either the endpoint term
closure or its resolved-source elaboration closure. The same 19 previously reviewed elaboration
helpers were retained. Review covered the complete records behind overlapping generated ranges,
attributes, syntax, and surviving source references before deletion.

The deletion removed 19 complete proof modules. Two further modules contained only base-point
lemmas, which were moved beside their chart definitions. Ten preexisting modules contained only
imports and empty scopes; their consumers now import the actual owners. Four new modules provide
the shorter argument and its general Hurewicz/free-loop prerequisites, for a net reduction of
27 modules. The old construction-audit presentation root and Blueprint presentation branch were
removed. `ChallengeAxioms` only lost its import of an obsolete module; its generated signatures
are byte-identical. The Comparator theorem statements, permitted axioms, and dependency pins
are unchanged.

| Library inventory | Before | After |
|---|---:|---:|
| Lean modules, including the root import | 952 | 925 |
| Source lines | 210,884 | 206,815 |

This is a net reduction of 4,069 lines, including the new proofs. No clean A/B build benchmark
was run, so these structural reductions are not presented as a measured speedup.

The post-deletion audit has 25,095 compiled project constants, with exactly the same 20,730
constants in the endpoint term closure as immediately before deletion. It reports only the
same 19 elaboration-helper ranges, no missing `.ilean` files, and the two known linter-option
metadata references. The new proof route, rather than the deletion itself, reduced the
endpoint closure from its original 21,024 constants.
Every live declaration also retains the same direct dependency list across deletion, including
references to external libraries.

Validation passed: the full root build (9,953 jobs), all 276 Blueprint declaration checks, the
Blueprint build (10,306 jobs), the post-Blueprint root build, import/layer and placeholder checks,
and the strict recursive axiom audit. Comparator reported “Lean default kernel accepts the
solution” and “Your solution is okay!” against the unchanged permitted-axiom list. The final
boundary remains three Lean axioms plus ten classical assumptions; the construction still uses
three Lean axioms plus seven classical assumptions. Existing linter/docstring warnings remain.

## Global circle translation replaces the elliptic H₂ coordinate calculation

The new production argument extends fourth-period translation across both elliptic fillings and
across the cusp. A general circle-product homology lemma shows that a torus swept by this map
has zero image in H₂ whenever the target has trivial H₁. The actual fixed-loop sweeps and the
projected planes involving the fourth period satisfy this hypothesis.

The remaining projected classes satisfy integral relations
`x₁ + 2x₃ = 0`, `x₀ + 3x₃ = 0`, and `x₀ = 2x₁`.
They imply `x₃ = 0` without division or a torsion-free hypothesis. Local Wang generation,
elliptic Mayer–Vietoris, and the existing primitive cusp boundary calculation then show that the
elliptic inclusion induces zero on H₂. Cusp specialization is onto on H₂; the final
Mayer–Vietoris argument uses the already established H₁ vanishing and equal integral H₁ ranks.
The old full elliptic H₂ basis and cusp raw-five normalization are no longer dependencies.

Only the two Comparator theorems were mathematical roots of the deletion analysis. The export
included opaque theorem values and type dependencies; resolved `.ilean` source references
protected elaboration support. It was captured after the new proof passed a full root build.
Declaration deletion was followed by import repair, removal of dangling section variables, and
another full build. The shared `CuspAttachmentHomology` import now contains the actual cusp
surjectivity theorem, so the Comparator challenge files remain unchanged.

The requested 10,000-line reduction was not reached. A further candidate is to replace the
selected elliptic relation loops with ordinary circles bounding discs in the fixed local
product charts, and replace full marked-band homotopies with the homology comparisons actually
used. A joint dependency cut gives an optimistic ceiling of 11,249 existing source lines,
before replacement proofs and elaboration support. The unproved obligations are the new loops'
exact logarithmic period-lift endpoints, base winding multiplicities three and four, and local
period-equivariance of the weaker band comparisons. This is a research direction, not a
verified deletion estimate. Reusing the current selected loops retains most of that machinery.


| Library inventory | Before | After |
|---|---:|---:|
| Lean modules, including the root import | 780 | 771 |
| Source lines | 174,475 | 171,657 |

This is a net reduction of **2,818 lines**, including all new proofs. Twenty-three obsolete
modules were removed and fourteen modules were added. No clean A/B timing benchmark was run;
this is a source reduction, not a measured build speedup.

The post-deletion export contains 20,704 compiled project constants and 17,094 constants in the
two endpoint term closures. The source-supported closure has 18,142 constants. It reports
exactly the same seventeen previously reviewed elaboration-helper ranges, no missing `.ilean`
files, and only the two known linter-option metadata references. Generated auxiliary proof names
changed after deletion, and one surviving proof now closes a definitional equality explicitly;
the endpoint closure size is unchanged from the pre-deletion export of the new route.

Validation passed: the full root build (9,799 jobs), Blueprint build (10,152 jobs),
post-Blueprint root build, all 263 Blueprint declaration checks, import/layer and placeholder
checks, and the strict recursive axiom audit. Comparator's default Lean kernel accepted the
unchanged challenge. Its macOS fake-Landrun path checks functionality, not Linux process
isolation. The endpoint boundary remains three standard Lean axioms plus ten classical
assumptions; the construction uses the standard three plus seven classical assumptions.
Existing linter/docstring warnings remain. The challenge files, Comparator configuration,
axiom allowlists, and dependency pins are unchanged.
