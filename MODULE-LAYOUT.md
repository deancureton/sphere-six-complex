# Module layout

The library is organized by mathematical objects, following the topic-based layout of
[MovingSofa](https://github.com/deancureton/MovingSofa). Reusable classical mathematics remains
under `Prerequisites/`; the other directories contain the particular six-sphere construction.
Directory names carry the context, so filenames do not repeat `Paper`, section numbers, or the
full name of their subject.

## Construction

| Directory | Contents |
| --- | --- |
| `TriangleGroup/` | The chosen representation and its action |
| `Periods/` | Lattice, period functions, modular frames, and affine torsors |
| `TorusFamily/` | Analytic torus families, deck quotients, and real period trivializations |
| `Regular/` | Punctured base, regular covers, period transport, and central homology |
| `Elliptic/` | Elliptic fillings, logarithmic gauges, collars, bands, disc circles, and homology |
| `Cusp/` | Cusp filling, straightening, retraction, specialization, Wang sequence, and sweeps |
| `Toric/` | The A₂ model, positive part, honeycomb cells, central fiber, and boundary |
| `Construction/` | Gluing the pieces, separation, compactness, and complex structure |
| `Gluing/` | Open-cover identifications, intersections, and connectedness |
| `FundamentalGroup/` | Cover geometry and van Kampen for the glued space |
| `Homology/` | Global first and second homology, Euler characteristic, and sphere comparison |

All paths in this table are relative to `SphereSixComplex/`. Larger topics have subdirectories:
for example, `Elliptic/DiscCircle/` contains the filling relations, `Elliptic/Band/` contains
band comparisons, and `Toric/CentralFiber/` contains the cell model's homology calculations.

## Prerequisites

| Directory under `Prerequisites/` | Contents |
| --- | --- |
| `Algebra/` | Integral presentations, exact sequences, and basis calculations |
| `Analysis/` | Analytic and holomorphic cocycle tools |
| `Geometry/` | General manifold, quotient, gluing, and complex-disc constructions |
| `Periods/` | Modular functions and classical uniformization |
| `Topology/` | Covering spaces, homotopies, CW complexes, singular homology, Mayer–Vietoris, mapping tori, Hurewicz, manifolds, spheres, and tori |
| `TriangleGroup/` | Abstract source group and classical Fuchsian geometry |

Topology is subdivided by these subjects. Singular homology has separate `Subdivision/` and
`Excision/` directories; uniformization separates branched maps, lifting, reflection, the
modular j-function, and source geometry.

Classification follows the mathematical statement. General results about mapping tori or CW
complexes belong to the prerequisites. Results specifying the selected lattice, A₂ cell labels,
or particular attaching maps belong with the construction. The prerequisite layer imports no
construction modules or aggregates; `scripts/check-imports.py` enforces this boundary.

## Entry points

```lean
import SphereSixComplex.Final          -- the final complex-structure theorem
import SphereSixComplex.Construction   -- all retained construction modules
import SphereSixComplex.Prerequisites  -- all retained reusable prerequisites
import SphereSixComplex                -- the entire retained development
```

For smaller imports, select a specific module, such as
`SphereSixComplex.Elliptic.DiscCircle.FirstHomology` or
`SphereSixComplex.Prerequisites.Topology.Torus.Homology`.
`Final.lean` assembles the homology comparison and smooth sphere recognition; `Solution.lean`
exports the two fixed Comparator endpoints.

## Maintenance

Use a mathematical object or result for a new module's name. Put closely related files in its
topic directory rather than adding construction-history prefixes. Generalize reusable results
into `Prerequisites/` when their statements support it. See [NAMING.md](NAMING.md) and
[API-DESIGN.md](API-DESIGN.md) for declaration naming and mathematical interfaces.

The reorganization preserves declaration names, statements, and proof bodies. Some historical
namespaces still contain `Paper` or `SectionSeven`; these do not describe module paths. Old
module paths have no compatibility copies. Imports, including `public import` and `import all`,
retain their original order and visibility.

The retained development is rooted at `sphere_six_admits_complex_structure` and
`mathoverflow_1973`. Documentation does not add mathematical roots. The import checker also
ensures every library module is reachable from `Main.lean`; the axiom audit and Comparator check
the unchanged trust boundary described in [TRUST-BOUNDARY.md](TRUST-BOUNDARY.md).

## Reorganization checkpoint

The 2026-10-05 reorganization moved 713 modules. The library retains 733 modules and 161,912
source lines; its largest directory now contains 29 files rather than 248. A source comparison
verified all 745 tracked Lean files unchanged except for import paths, with the ordered import
graph preserved. No declaration names or proof bodies changed.

Validation passed: full root build (9,761 jobs), Blueprint build (10,114 jobs), post-Blueprint
root build, all 263 Blueprint declaration checks, import/layer and placeholder checks, strict
recursive axiom audit, and Comparator's default Lean kernel replay. Existing warnings remain.
Comparator's macOS runner verifies functionality without Linux process isolation. Builds used
nice 15 and at most three compiler workers. No build-speed improvement is claimed.
