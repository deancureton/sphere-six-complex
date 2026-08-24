# A Complex Structure on the Six-Sphere

This project formalizes the construction in [`references/s6.pdf`](https://alpo.ge/s6.pdf): a
compact complex threefold diffeomorphic to the standard smooth six-sphere.

The Lean development is in `SphereSixComplex/`. The `blueprint/` directory tracks the
paper-to-Lean dependency graph. `Challenge.lean`, `Solution.lean`, and `comparator.json` form the
Comparator boundary for the final theorem.

The formalization follows the minimal construction spine stated in the first two pages of the
source: period functions, the torus family, its three local fillings, the glued compact complex
threefold, integral topology, and six-dimensional smooth recognition. The later computations of
analytic invariants are outside the dependency closure of the main theorem.

## Status

This is an active formalization, not yet a proof of the headline theorem. The root project and the
Verso Blueprint build, but `SphereSixComplex/Final.lean` still contains the paper-specific gluing
`sorry`. The `sorry` in `Challenge.lean` is the trusted Comparator challenge boundary.

The verified development covers the construction's algebraic foundations and several analytic and
topological reductions. The source triangle action is kept distinct from the modular target action;
the Blueprint records the remaining construction and smooth-recognition obligations.

The topology library also contains reusable foundations for this gap: a direct contraction of
loops on the standard six-sphere, an explicit finite two-cell CW model, degree-zero and punctured
sphere homology lemmas, and a binary-open-cover singular-chain sequence. The latter reduces
singular Mayer--Vietoris to a generatorwise subdivision certificate, so it can be combined with
the project's explicit barycentric subdivision and prism operators. The final atlas-transport
adapter records the stronger identity-normalized compatibility with the standard smooth atlas.

The geometry library proves unimodularity of the explicit height-one `A₂` cones, reduces gluing
atlas compatibility to transitions between distinct pieces, proves regularity of the canonical
piece inclusions, and records the standard topological consequences of the orbit projections.
The paper's van Kampen input now retains its four-piece cover and named meridian loops instead of
assuming only the resulting group presentation. Classical sphere homology and smooth recognition
remain isolated behind narrowly stated external inputs where the required theorems are absent
from Mathlib.

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
