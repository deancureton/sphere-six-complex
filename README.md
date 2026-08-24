# A Complex Structure on the Six-Sphere

This project formalizes the construction in [`references/s6.pdf`](https://alpo.ge/s6.pdf): a
compact complex threefold diffeomorphic to the standard smooth six-sphere.

The Lean development is in `SphereSixComplex/`. The `blueprint/` directory tracks the
paper-to-Lean dependency graph. `Challenge.lean`, `Solution.lean`, and `comparator.json` form the
Comparator boundary for the final theorem.

The formalization follows the minimal construction spine stated in the first two pages of the source:
period functions, the torus family, its three local fillings, the glued compact complex threefold, integral
topology, and six-dimensional smooth recognition. The later computations of analytic invariants are outside
the dependency closure of the main theorem.

## Status

This is an active formalization, not yet a proof of the headline theorem. The root project and the
Verso Blueprint build, but `SphereSixComplex/Final.lean` still contains the paper-specific gluing
`sorry`. The `sorry` in `Challenge.lean` is the trusted Comparator challenge boundary.

The verified development covers the construction's algebraic foundations and several analytic and
topological reductions. The source triangle action is kept distinct from the modular target action;
the Blueprint records the remaining construction and smooth-recognition obligations.

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
