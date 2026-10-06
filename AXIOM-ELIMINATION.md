# Remaining axiom elimination

The endpoint statements in `comparator.json` remain fixed. Each replacement must pass
the full build, compiled axiom audit and Comparator before its assumption is removed
from the permitted boundary.

| Assumption | Route | Status |
| --- | --- | --- |
| Integral universal coefficients | Split a projective chain complex using projective lower homology; apply in degrees zero through three | Removed; full build, exact endpoint audit and Comparator passed |
| Relative CW decomposition with corners | Replace the particular positive quotient argument with a homotopy into its collar | Removed; full build, exact endpoint audit and Comparator passed |
| Whitehead for CW pairs | Use the same collar homotopy and homotopy extension to construct the deformation retraction | Removed; full build, exact endpoint audit and Comparator passed |
| Finite CW model of a compact smooth manifold | Construct a model or replace finite generation, dimension bounds and CW type separately | Not yet attempted |
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
