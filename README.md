# A Complex Structure on the Six-Sphere

This project formalizes the construction in [`references/s6.pdf`](https://alpo.ge/s6.pdf): a
compact complex threefold diffeomorphic to the standard smooth six-sphere.

The Lean development is in `SphereSixComplex/`. The `blueprint/` directory tracks the
paper-to-Lean dependency graph. `ChallengeDefs.lean`, `ChallengeAxioms.lean`, `Challenge.lean`,
`Solution.lean`, and `comparator.json` form the Comparator boundary. `ChallengeDefs` contains
the Mathlib-only statement definitions; `ChallengeAxioms` exposes the audited established results
to both Comparator environments. Nothing imports `Challenge` itself.

## Status

The headline theorem is source-sorry-free. Paper-specific and classical results not yet available
in Mathlib are explicit axioms, documented and checked by the allowlists in `scripts/`. The two
`sorry`s in `Challenge.lean` are the trusted Comparator challenge boundary.

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
the trusted Comparator statements in `Challenge.lean`. It counts them, so an extra placeholder in
an already listed file also fails.

`./scripts/check-imports.py` checks that every module is reachable from `SphereSixComplex.Main`.
A module outside the build cone is elaborated by nothing and its axioms are invisible to the
audit, so this keeps the two scripts above honest.

Both gates run in CI after `lake build`.

## Comparator

```sh
./scripts/setup-comparator.sh
./scripts/run-comparator.sh
```
