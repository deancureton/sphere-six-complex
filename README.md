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

## Comparator

```sh
./scripts/setup-comparator.sh
./scripts/run-comparator.sh
```
