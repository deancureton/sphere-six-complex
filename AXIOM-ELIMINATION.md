# Remaining axiom elimination

The endpoint statements in `comparator.json` remain fixed. Each replacement must pass
the full build, compiled axiom audit and Comparator before its assumption is removed
from the permitted boundary.

| Assumption | Route | Status |
| --- | --- | --- |
| Integral universal coefficients | Split a projective chain complex using projective lower homology; apply in degrees zero through three | Removed; full build, exact endpoint audit and Comparator passed |
| Relative CW decomposition with corners | Replace the particular positive quotient argument with a homotopy into its collar | Removed; full build, exact endpoint audit and Comparator passed |
| Whitehead for CW pairs | Use the same collar homotopy and homotopy extension to construct the deformation retraction | Removed; full build, exact endpoint audit and Comparator passed |
| Finite CW model of a compact smooth manifold | Replace homology consequences using the explicit open cover; investigate a separate CW-type proof | Removed from the construction; compiled construction closure has only the standard three axioms. Final recognition still uses CW type |
| Higher Hurewicz | General sphere representation in the Hurewicz range | Not yet attempted |
| Homological Whitehead | Relative Hurewicz and CW Whitehead | Not yet attempted |
| Smooth six-sphere recognition | Smooth classification, or an explicit diffeomorphism for the constructed manifold | Not yet attempted |

The UCT replacement does not assume an injective integer coefficient module. Instead,
the chain objects and lower homology objects are projective. This gives a general
Kronecker equivalence in a linear abelian category. For the manifold calculation the
lower groups are independently known to be `H₀ ≃ ℤ`, `H₁ = 0`, and `H₂ = 0`.

The geometric route does not assume that interior logarithmic coordinates
extend to the boundary. Compact height sublevels and a collar are used to move into
the collar neighborhood, where the retraction is explicit.

The old relative CW and quadrant-manifold route has been deleted, including ten
obsolete modules. Together with the UCT replacement, this removes 1,324 project Lean
lines net. The final endpoint statements are unchanged.

## Geometric homology bounds

The finite-CW assumption had two homology uses and one recognition use. The new
`Homology/Euler/Finiteness.lean` proves the homology consequences directly: collars
are mapping tori of four-tori, so their sixth homology vanishes. Mayer–Vietoris then
preserves finite generation and vanishing above degree six through the four-piece
cover. The Poincare/UCT interface now contains only the proved duality pairings.
The final recognition step still uses finite CW models to obtain CW homotopy type.

The full build, exact final and construction axiom audits, Blueprint output checks,
and Comparator kernel verification passed. The construction closure is exactly
`propext`, `Classical.choice`, and `Quot.sound`; the final closure retains the four
classical assumptions. Local macOS verification does not test Linux sandbox isolation.

## Further recognition routes (unverified)

A search of pinned Mathlib/TauCeti and public Palomar/Lean Pool sources found no
ready-made manifold CW-type theorem. Mathlib Whitney embedding and TauCeti tubular
neighborhoods provide a possible reduction to open Euclidean subsets. The missing
step is an actual CW homotopy model, for example through a convex-cover nerve theorem
and a classical CW realization bridge. A weak equivalence alone does not meet the
current interface.

A different route may bypass all three topological recognition assumptions. At
DifferentialGeometry revision `788efe97894474c032de6dfb1289d515f613d15a`, the files
`Topology/Cobordism/HCobordism.lean` and `Topology/HighDimensional/TwistedSphere.lean`
can potentially supply a sphere homeomorphism from the two-disk complement argument.
The missing bridges are a natural comparison of relative homology for the global-to-local
fundamental class, and a homological version of
`Topology/Homology/Punctures/PuncturedAcyclic.lean` and `DiskComplement.lean`.
The existing chart-disk construction supplies the geometric disks and separating function.

The estimated additional dependency closure is 168 modules (142,963 lines). The
upstream source scan found no axioms or proof placeholders, but this route has not
been ported, compiled, or axiom-audited. Its conclusion is a homeomorphism, not a
diffeomorphism: it would still use smooth six-sphere recognition. No new dependency
has been added for this investigation.
