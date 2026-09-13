# Cusp attachment replacement

The cellular proof remains the production route to the Comparator endpoints. The replacement
below is being developed alongside it; none of its prospective deletions has been made.
The endpoint statements and trust boundary are unchanged.

## Verified geometric model

Write `X` for the actual cusp central orbit quotient and `B` for the complement of its
singleton-support locus. `Construction/CentralAttachment.lean` proves:

- The original positive-cell phase map gives a continuous surjection `D² × T² → X`.
- Its preimage of `B` is exactly `∂D² × T²`, and it is injective on the interior.
- `B` is compact and closed.
- `centralAttachmentHomeomorph` identifies `X` with the attachment along this actual map.
  Its inclusion formulas retain the original phase map and inclusion of `B`.

Here `D²` is the closed unit ball of `Fin 2 → ℝ` with its sup norm.
`Construction/CentralBoundaryCharts.lean` proves coverage and the exact equality relations
between the six complex axis charts in the actual deck quotient. Corresponding charts have
transition `z ↦ z⁻¹`; distinct branches meet only at the two poles.
`Construction/CentralBoundaryModel.lean` consequently identifies `B` with the quotient of
`Fin 3 × OnePoint ℂ` that identifies the three zeros and separately the three infinities.
`centralFiberAttachmentHomeomorph` combines these results into the concrete attachment model.

The reusable attachment, inversion-chart gluing, quotient-homotopy, and exact-sequence tools
live in `Prerequisites/Topology`. They do not assume the cusp homology calculation.

## Remaining mathematical work

A radial open cover should reduce the attachment calculation to

| Space | Homotopy type |
| --- | --- |
| Inner open set | `T²` |
| Outer open set | `B` |
| Intersection | `S¹ × T²` |

A second open cover of `B` removes one pole from each member. Its members contract, and
its intersection consists of three copies of `ℂ \ {0}`. These give `H₁(B) = ℤ²` and
`H₂(B) = ℤ³`.

The actual inclusion maps still need to be computed. In degrees one and two, the proposed
Mayer–Vietoris difference maps are projection onto the pure phase coordinates in the inner
piece and zero in the boundary piece. This must be proved from the attaching map, including
the cancellation of opposite sides of the positive-cell boundary. Correct ranks alone do
not establish these formulas.

The resulting degree-two sequence should be `0 → ℤ³ → H₂(X) → ℤ → 0`.
`IntegralMayerVietoris.exists_homologyEquiv_coker_prod_ker` already supplies a splitting that
preserves the actual inclusion and boundary coordinates. To replace the specialization
proof, the three mixed torus classes must be shown to form a primitive basis of its `ℤ³`
subgroup, and the positive class must map to a unit in `ℤ`. The remaining degrees must also
be computed to recover the finite homology and Euler characteristic used by the endpoints.

Only after those results replace their existing producers should the compiled dependency
closure be retraced and the bypassed cellular declarations removed. The earlier estimate
of about 7,600 removable old lines is conditional and excludes the replacement's cost.
