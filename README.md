# A Complex Structure on the Six-Sphere

This project formalizes the construction in [`references/s6.pdf`](https://alpo.ge/s6.pdf): a
compact complex threefold diffeomorphic to the six-sphere.

The Lean development is in `SphereSixComplex/`. The `blueprint/` directory tracks the
paper-to-Lean dependency graph. `Challenge.lean`, `Solution.lean`, and `comparator.json` form the
Comparator boundary for the final theorem.

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
