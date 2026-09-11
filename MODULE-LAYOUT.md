# Module layout

The library has two layers. `Prerequisites/` contains classical mathematics and reusable
infrastructure; `Paper/` contains the selected construction, its computations, and the final
assembly. Both retain the subject subdirectories `Analysis`, `Geometry`, `Periods`, `Topology`,
and `TriangleGroup` where applicable.

| Layer | Contents |
| --- | --- |
| `Prerequisites/Analysis` | General analytic and holomorphic cocycle tools |
| `Prerequisites/Geometry` | Manifold transport, quotient topology, disc and Cayley coordinates, general gluing operations |
| `Prerequisites/Periods` | Modular functions, classical uniformization, and projective-line cohomology and torsors |
| `Prerequisites/Topology` | Singular and cellular homology, excision, Mayer–Vietoris, Wang sequences, tori, covering spaces, van Kampen, manifold duality, and sphere recognition |
| `Prerequisites/TriangleGroup` | The abstract source group and its classical Fuchsian geometry |
| `Paper/` | The chosen lattice and monodromy representation, additive period construction, elliptic and cusp fillings, the selected A₂ cell model, Section 7 calculations, and final complex structure |

Classification follows the mathematical statement. A theorem about arbitrary mapping tori or
CW complexes belongs to the prerequisites even if it was introduced while proving Section 7.
A theorem specifying the selected lattice, the particular period transformation laws, the A₂
cell labels, or the construction's attaching maps belongs to the paper layer. A classical
calculation for a standard torus, sphere, or Fuchsian triangle belongs to the prerequisites even
when its dimension or triangle orders are fixed.

Mixed modules have been split at these interfaces. For example, the general torus homology,
finite cyclic mapping-torus, equivariant retraction, cellular-boundary algebra, and compact
complex-threefold homology results are independent modules. Their adapters to the selected
periods, filling models, and cell labels remain with the paper. Small local proof helpers stay
with their applications.

## Imports

```lean
import SphereSixComplex.Prerequisites -- all reusable prerequisite modules
import SphereSixComplex.Paper         -- all paper modules and their dependencies
import SphereSixComplex               -- the complete development, as before
```

For a smaller import, select an individual module, for example
`SphereSixComplex.Prerequisites.Topology.StandardTorusHomology` or
`SphereSixComplex.Paper.Final`.

The initial folder separation preserved declaration names. Naming cleanup follows
[NAMING.md](NAMING.md), and mathematical interfaces follow [API-DESIGN.md](API-DESIGN.md).
Some prerequisite declarations still retain
historical namespaces containing `Paper` or `SectionSeven`; these names do not express an import
dependency. Module imports use the new paths. No compatibility copies of the old modules are
kept.

`scripts/check-imports.py` enforces that every module is built, every project import exists, and
prerequisites import no paper module or aggregate. Thus the prerequisite library can be used
independently. The axiom audit and Comparator track the current declaration names and unchanged
trust boundary; see [TRUST-BOUNDARY.md](TRUST-BOUNDARY.md).
