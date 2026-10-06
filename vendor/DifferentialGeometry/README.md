# Poincaré duality and h-cobordism dependency

This is a 389-module extraction supporting integral Poincaré duality, chart disks,
Morse theory, and h-cobordism
from [DifferentialGeometry](https://github.com/qinz1yang/differential-geometry)
at commit `788efe97894474c032de6dfb1289d515f613d15a`.
The original sources contain 173,638 Lean lines. The first extraction contained
221 modules and 30,675 lines for
`DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Manifold`.
The additional 168 modules provide the closure needed for `Topology.Cobordism.HCobordism`,
`Topology.Cobordism.HomotopySphere`, `Topology.Morse.Strip.ModelTransport`, and
`Topology.HighDimensional.TwistedSphere`. The umbrella library and unrelated
geometric developments are excluded. The twisted-sphere result constructs a homeomorphism;
it does not prove uniqueness of the smooth structure on the six-sphere.

The source derives in part from Ayush Khaitan's CanonicalTopology project.
Original copyright headers, Apache-2.0 licenses, NOTICE and nested attribution
records are preserved. One attributed 73-line derivative-homotopy fragment comes
from Boris Alexeev's HopfProblem; no large portion of that formalization is imported.

`UPSTREAM-SHA256.json` records the original source hashes. `MODULE-PORT.patch`
records the exact source adaptations, and `MODULE-PORT.md` explains them. The
adaptations permit imports from Lean's module system: public import/export headers,
helper visibility and qualification, explicit Mathlib imports, and two elaboration
annotations. Mathematical content is unchanged.

Both upstream and this package use Lean 4.35.0-rc3. Upstream's Mathlib pin was
`c55e6e786f49471c72fbddbec5415808896aec1e`; this project uses
`6b7abb3c7686292736be2955bd3eb9ebf63b456a`. The selected dependency builds against
that pin. Only required modules are imported by the main development.

The original duality extraction was checked both before and after conversion. The
expanded port has also compiled. The duality adapter for this project's actual
integral singular homology and cohomology uses only `propext`, `Classical.choice`,
and `Quot.sound`. See the root trust-boundary documentation and exact endpoint
axiom audits for integration gates.
