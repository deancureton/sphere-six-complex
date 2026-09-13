# Cusp attachment and global homology

The finite attachment model and the global fourth-circle argument are now the production
route. They replace the former high-dimensional cellular calculation and the full elliptic
second-homology coordinate comparison. The Comparator endpoint statements and classical
trust boundary are unchanged.

## Actual cusp geometry

Write `X` for the cusp central orbit quotient and `B` for the complement of its
singleton-support locus. `Construction/CentralAttachment.lean` identifies `X` with

`B ∪ (D² × T²)`, attached along `∂D² × T²`.

Here `D²` is the closed unit ball of `Fin 2 → ℝ` with its sup norm. The actual disk-phase
map is surjective, has boundary preimage exactly `∂D² × T²`, and is injective on the
interior. The attachment homeomorphism preserves the inclusion of `B` and this map.

`CentralBoundaryCharts.lean` proves the exact relations between the six complex axis charts.
Corresponding charts have transition `z ↦ z⁻¹`; distinct branches meet only at the two poles.
`CentralBoundaryModel.lean` identifies `B` with three copies of `OnePoint ℂ`, identifying
all zeros and, separately, all infinities. These are statements about the actual quotient.

## Integral Mayer–Vietoris calculation

The radial open cover of the attachment has the following homotopy types:

| Space | Homotopy type |
| --- | --- |
| Inner open set | `T²` |
| Outer open set | `B` |
| Intersection | `S¹ × T²` |

A second cover of `B` removes one pole from each member. Both members contract, and their
intersection is three punctured planes. It gives `H₁(B) ≃ ℤ²` and `H₂(B) ≃ ℤ³`.

The attaching map induces zero into `B` in degrees one and two. Opposite hexagon sides lie
in the same sphere component, so their paired loop classes vanish because
`H₁(OnePoint ℂ) = 0`. The remaining mixed torus classes vanish by the circle cross product
applied to this null homology class. Thus the Mayer–Vietoris difference maps are the pure
phase projections into `T²`, with zero boundary components.

The degree-two calculation gives `0 → ℤ³ → H₂(X) → ℤ → 0`, with a splitting that retains
the inclusion and boundary coordinates. The resulting cusp filling homology in degrees
one through four is `ℤ², ℤ⁴, ℤ², ℤ`, and its Euler characteristic is two. These results
are implemented in the `CentralFiberHomology` and `CentralFiberEuler` modules and
transported through the actual cusp retraction.

The explicit cusp specialization remains available. In particular,
`AnalyticData.cuspToFilling_homologyTwo_surjective` proves that the collar maps onto the
filling's second homology. This is the cusp input to the final argument.

## Global fourth-circle argument

`StarFourthTranslation.lean` extends translation in the fourth period direction over both
elliptic fillings and the cusp, producing a continuous circle action on the glued space.
The already proved vanishing of global first homology makes every loop sweep by this action
zero in global second homology.

`StarFourthTranslationGenerators.lean` identifies the actual local fixed-loop sweeps with
these global sweeps. `EllipticProjectedFourthSweeps.lean` also kills the projected planes
involving the fourth direction. Common-source alignment and the local deck relation now
suffice; no full second-homology basis of the elliptic union is needed.

Concretely, let `xᵢ` be the global image of the order-three projected plane `Pᵢ`. The
order-four images agree at indices zero and three. The two fixed-loop sweep relations and
the order-three deck relation give

`x₁ + 2x₃ = 0`, `x₀ + 3x₃ = 0`, and `x₀ = 2x₁`.

Twice the first relation minus the second gives `x₃ = 0`. Together with the vanishing
fixed-loop sweeps, this kills the local mapping-torus generators integrally.
`EllipticHomologyVanishing.lean` concludes that the elliptic interior's map into global
second homology is zero.

`StarSecondHomology.lean` finishes with the final two-set Mayer–Vietoris sequence. Collar
surjectivity and compatibility of the two inclusions imply that the cusp piece also maps
trivially. Exactness makes the degree-two difference map surjective. The degree-one map is
surjective between free abelian groups of rank three, hence injective; exactness then gives
vanishing global second homology. Finally, `StarHomology.lean` combines the two low-degree
vanishing results with the geometric Euler characteristic, Poincaré duality, and universal
coefficients to recover the integral homology of the six-sphere on the same carrier.
