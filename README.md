# A Complex Structure on the Six-Sphere

This project formalizes the construction in [`references/s6.pdf`](https://alpo.ge/s6.pdf): a
compact complex threefold diffeomorphic to the standard smooth six-sphere.

The Lean development is in `SphereSixComplex/`. The `blueprint/` directory tracks the
paper-to-Lean dependency graph. `Challenge.lean`, `Solution.lean`, and `comparator.json` form the
Comparator boundary for the final theorem.

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

## Comparator

```sh
./scripts/setup-comparator.sh
./scripts/run-comparator.sh
```
