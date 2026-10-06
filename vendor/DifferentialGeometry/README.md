# Integral Poincaré duality dependency

This is the 221-module import closure of
`DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Manifold`
from [DifferentialGeometry](https://github.com/qinz1yang/differential-geometry)
at commit `788efe97894474c032de6dfb1289d515f613d15a`.
The original sources contain 30,675 Lean lines. The umbrella library and unrelated
geometric developments are excluded.

The source derives in part from Ayush Khaitan's CanonicalTopology project.
Original copyright headers, Apache-2.0 licenses, NOTICE and nested attribution
records are preserved. One attributed 73-line derivative-homotopy fragment comes
from Boris Alexeev's HopfProblem; no large portion of that formalization is imported.

`UPSTREAM-SHA256.json` records the original source hashes. `MODULE-PORT.patch`
records the exact source adaptations, and `MODULE-PORT.md` explains them. The
adaptations permit imports from Lean's module system: public import/export headers,
helper visibility and qualification, and one explicit Mathlib implementation import.
Mathematical statements and proof steps are preserved, apart from helper renaming.

Both upstream and this package use Lean 4.35.0-rc3. Upstream's Mathlib pin was
`c55e6e786f49471c72fbddbec5415808896aec1e`; this project uses
`6b7abb3c7686292736be2955bd3eb9ebf63b456a`. The selected dependency builds against
that pin. Only required modules are imported by the main development.

The unported and ported dependency have both compiled. The module-system adapter
proves duality for this project's actual integral singular homology and cohomology
with only `propext`, `Classical.choice`, and `Quot.sound`. See the root `UPGRADE.md`
and exact endpoint axiom audits for integration gates.
