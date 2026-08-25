# A Complex Structure on the Six-Sphere

This project formalizes the construction in [`references/s6.pdf`](https://alpo.ge/s6.pdf): a
compact complex threefold diffeomorphic to the standard smooth six-sphere.

The Lean development is in `SphereSixComplex/`. The `blueprint/` directory tracks the
paper-to-Lean dependency graph. `ChallengeDefs.lean`, `Challenge.lean`, `Solution.lean`, and
`comparator.json` form the Comparator boundary for the final theorem. `ChallengeDefs.lean` holds
every definition the statement mentions and depends only on Mathlib; both `Challenge` and the
development import it, so Comparator compares one shared copy. Nothing imports `Challenge` itself.

## Status

This is an active formalization, not yet a proof of the headline theorem. The root project and the
Verso Blueprint build, but `SphereSixComplex/Final.lean` still contains the paper-specific gluing
`sorry`. The `sorry` in `Challenge.lean` is the trusted Comparator challenge boundary.

The library now includes the construction's analytic, gluing, homology, van Kampen, and smooth
recognition foundations. The Blueprint records the remaining paper-specific obligation.

`exists_paperGluingData` is the sole remaining `sorry`, and
`toPaperGluingData_of_positiveDegree` reduces it to three inputs:

1. `HasVanKampenData` for the glued star. The generic van Kampen machinery is proved, and
   `hasVanKampenData_of_overlapSurjective_of_relations` derives the datum from two geometric
   facts about the fillings: that each collar surjects on its filling's fundamental group, and
   the three star filling relations. Both come from a filling cover square (issues #1, #2).
2. `SectionSevenPositiveDegreeHomologyAssembly`: the actual H₁/H₂ bases and compatibility
   squares of Section 7 (issues #6, #7).
3. `SectionSevenStageTopDegreeVanishing`, which reduces to each collar source having no sixth
   integral homology.

Past that, the headline theorem rests on four axioms: the general integral Mayer--Vietoris exact
sequence, and the three classical recognition inputs (Hurewicz--Whitehead for smooth manifolds,
the generalized topological Poincare theorem in dimension six, and the triviality of the group of
smooth structures on the six-sphere). `./scripts/check-axioms.sh` prints and enforces exactly that
list.

## Build

```sh
lake exe cache get
lake build
```

## Dependencies and acknowledgements

This formalization depends on:

- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
- the [Jordan Curve Theorem project](https://github.com/epfl-lara/jordan-curve-theorem)
- Thomas Zhu's fundamental-groupoid van Kampen development in Mathlib
  [PR #41603](https://github.com/leanprover-community/mathlib4/pull/41603)

We thank Thomas Zhu for giving us permission to use and port the van Kampen development.

## Trust boundary

Every `axiom` in the development is a trust boundary, so two scripts keep them visible.

`./scripts/check-axioms.sh` is the gate: it runs `#print axioms` on the final theorem and fails if
anything appears outside `scripts/allowed-axioms.txt`, which lists each permitted constant with a
justification. Set `CHECK_AXIOMS_SKIP_BUILD=1` to reuse an existing build.

`./scripts/axiom_inventory.py` is the static counterpart: it lists every `axiom` declaration in
`SphereSixComplex/` and marks whether it is reachable from `Final` (so the headline theorem may
come to depend on it), only from `Main`, or from neither.

`./scripts/check-sorries.py` checks that no `sorry`, `admit`, or `native_decide` appears outside
the two declared boundaries: the paper-specific gluing `sorry` in `Final.lean` and the trusted
Comparator statements in `Challenge.lean`. It counts them, so a second placeholder in an already
listed file also fails.

`./scripts/check-imports.py` checks that every module is reachable from `SphereSixComplex.Main`.
A module outside the build cone is elaborated by nothing and its axioms are invisible to the
audit, so this keeps the two scripts above honest.

Both gates run in CI after `lake build`.

## Comparator

```sh
./scripts/setup-comparator.sh
./scripts/run-comparator.sh
```
