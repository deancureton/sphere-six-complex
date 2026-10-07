# Remaining axiom elimination

The endpoint statements in `comparator.json` remain fixed. Each replacement must pass
the full build, compiled axiom audit and Comparator before its assumption is removed
from the permitted boundary.

| Assumption | Route | Status |
| --- | --- | --- |
| Integral universal coefficients | Split a projective chain complex using projective lower homology; apply in degrees zero through three | Removed; full build, exact endpoint audit and Comparator passed |
| Relative CW decomposition with corners | Replace the particular positive quotient argument with a homotopy into its collar | Removed; full build, exact endpoint audit and Comparator passed |
| Whitehead for CW pairs | Use the same collar homotopy and homotopy extension to construct the deformation retraction | Removed; full build, exact endpoint audit and Comparator passed |
| Finite CW model of a compact smooth manifold | Replace homology consequences using the explicit open cover and recognition using h-cobordism | Removed; full build, exact audits, Blueprint and Comparator passed |
| Higher Hurewicz | Replace homological recognition with the h-cobordism homeomorphism route | Removed; full build, exact audits, Blueprint and Comparator passed |
| Homological Whitehead | Same h-cobordism homeomorphism route | Removed; full build, exact audits, Blueprint and Comparator passed |
| Smooth six-sphere recognition | Smooth classification, or an explicit diffeomorphism for the constructed manifold | Investigated: available Alexander-trick assembly proves only a homeomorphism; smooth extension remains missing |

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
The recognition replacement below removes the remaining use of finite CW models.

At the preceding geometric-homology checkpoint, the full build, exact final and
construction axiom audits, Blueprint output checks, and Comparator kernel verification
passed. The construction closure was exactly
`propext`, `Classical.choice`, and `Quot.sound`; the final closure still retained the four
classical assumptions. Local macOS verification does not test Linux sandbox isolation.

## Homology-sphere recognition

The recognition theorem now constructs a homeomorphism using the proved h-cobordism
and twisted-sphere results from DifferentialGeometry at revision
`788efe97894474c032de6dfb1289d515f613d15a`. The new bridges compare the actual relative
chain complexes, show that the global fundamental class generates local top homology,
and prove acyclicity of the puncture and the required two-disk complement pair.
The general homeomorphism theorem has only Lean's three standard axioms.

This bypasses higher Hurewicz, homological Whitehead and finite CW models; their
axiom declarations and obsolete proof route have been deleted. It does not formalize
those three general theorems. Final endpoint statements remain unchanged.

The additional dependency closure contains 168 modules (142,963 original lines).
It is extracted from the same pinned source as the existing Poincaré duality dependency
and hosted in the pinned DifferentialGeometry fork,
with licenses, original hashes and an exact module-system port patch. No large Boris
Alexeev development is imported. The selected modules compile against the project's
pinned Mathlib.

## Remaining smooth classification

The available Alexander-trick assembly concludes a homeomorphism. A radial extension
of a boundary homeomorphism need not be differentiable at its center, so it cannot
supply the final diffeomorphism. Removing `SmoothSixSphere.poincare` still requires a
formal smooth classification argument (the triviality of the group of homotopy
six-spheres), an appropriate smooth extension theorem, or an explicit diffeomorphism
for this particular construction. The inspected dependencies do not supply that bridge.

The `mathoverflow_1973` endpoint now transports the complex atlas directly along the
proved homeomorphism. Its statement does not require compatibility with the standard
real smooth structure, so this endpoint needs no classical axioms. The stronger endpoint
retains smooth six-sphere recognition. Both statement types are unchanged.

All checkpoint gates passed: full project build (10,509 jobs), exact final and
construction axiom audits, a separate recursive closure check for `mathoverflow_1973`,
Blueprint build and output checks (11,209 jobs), and Comparator with Lean's default
kernel. The topological endpoint uses only the three standard axioms; the stronger
smooth-compatible endpoint additionally uses `SmoothSixSphere.poincare`.
The local macOS Comparator run checks kernel acceptance, not Linux sandbox isolation.
