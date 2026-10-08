# Proof guide

The construction produces a compact complex threefold, computes its fundamental
group and integral homology, recognizes its underlying smooth manifold as the
standard six-sphere, and transports the complex atlas. The assembly is short:
[Final.lean](../SphereSixComplex/Final.lean) contains the resulting existence
theorems. Intermediate statements concern the actual spaces, maps, and atlases.

## Statements and atlases

[ChallengeDefs.lean](../ChallengeDefs.lean) depends only on Mathlib. `SixSphere` is
the unit sphere in real seven-space, with its induced topology and Mathlib's
stereographic atlas. `ComplexModel` is complex three-space. Mathlib's
`ChartedSpace` requires charts to be open partial homeomorphisms covering every
point; `IsManifold 𝓘(ℂ, ComplexModel) ∞` requires complex-smooth transition maps.
This expresses an integrable complex atlas.

The underlying real atlas is obtained by composing complex charts with a real
continuous linear equivalence from complex three-space to real six-space.
`SmoothlyCompatible` requires a diffeomorphism to the specified real atlas whose
underlying map is the identity. Thus compatibility concerns the given atlas,
not just its diffeomorphism class. The generic
[atlas-transport theorem](../SphereSixComplex/Prerequisites/Geometry/Manifold/AtlasTransport.lean)
proves this condition when transporting a complex atlas along a diffeomorphism.

The secondary endpoint `mathoverflow_1973` in [Solution.lean](../Solution.lean)
requires only a complex atlas on the standard topological sphere, with complex
`C¹` transition maps. It transports the same construction along a homeomorphism
and does not require smooth classification.

## Analytic construction

The four pieces are the regular torus family, two elliptic fillings, and the cusp
filling. [AnalyticData.lean](../SphereSixComplex/Construction/AnalyticData.lean)
keeps their dependent choices coherent. The affine torsor construction selects
the global section μ once, constructs β for that same μ, and then applies the
Schur shift. The period and quotient constructions use these sections directly.

The glued space has an actual complex atlas. Hausdorffness, second countability,
connectedness, and compactness are proved before the topological calculation.
For compactness, the continuous orbifold coordinate separates central compact
sets from elliptic collars; at the cusp, the modular coordinate escapes to
infinity. Moving inverse period coordinates are continuous by continuity of
inversion on invertible linear maps.

The cusp's positive quotient has a compact core, represented by six squares.
Compact Brown collaring supplies a collar. An explicit homotopy first moves into
the interior, then compresses the height into this collar; projection along it
gives a homotopy inverse to the boundary inclusion. Homotopy extension upgrades
this to a strong deformation retraction, which lifts through the quotient
covering. See [Toric/Positive](../SphereSixComplex/Toric/Positive/).

## Cusp attachment

Let X be the cusp central orbit quotient and B the complement of its
singleton-support locus.
[CentralFiber/Attachment.lean](../SphereSixComplex/Toric/CentralFiber/Attachment.lean)
identifies X with B together with a copy of `D² × T²` attached along
`∂D² × T²`. Here `D²` is the closed unit ball of `Fin 2 → ℝ` with its sup norm.
The disk-phase map is surjective, its boundary preimage is exactly `∂D² × T²`,
and it is injective on the interior. The homeomorphism preserves these actual maps.

The six complex axis charts have transition `z ↦ z⁻¹` on corresponding branches;
distinct branches meet only at the two poles.
[Boundary/Model.lean](../SphereSixComplex/Toric/Boundary/Model.lean) identifies B
with three copies of `OnePoint ℂ`, identifying all zeros and, separately, all
infinities. A cover removing the two poles gives `H₁(B) ≃ ℤ²` and `H₂(B) ≃ ℤ³`.

The attachment's radial cover has homotopy types T², B, and `S¹ × T²` for its
two members and intersection. The attaching map induces zero into B in degrees
one and two: opposite hexagon sides lie in the same sphere component, and the
mixed torus classes vanish by the circle cross product of the resulting zero
loop class. The Mayer–Vietoris difference maps are therefore the phase projections
into T², with zero B components.

The degree-two sequence is `0 → ℤ³ → H₂(X) → ℤ → 0`, with a splitting preserving
the inclusion and boundary coordinates. The cusp filling's homology in degrees
one through four is `ℤ², ℤ⁴, ℤ², ℤ`; its Euler characteristic is two.
See [CentralFiber/Homology.lean](../SphereSixComplex/Toric/CentralFiber/Homology.lean)
and [CentralFiber/Euler.lean](../SphereSixComplex/Toric/CentralFiber/Euler.lean).
The actual collar-to-filling map is surjective in degree two.

Specialization comparisons retain the source's canonical period markings.
The boundary class is raw coordinate four; the fourth-period sweep has unit
coefficient in raw coordinate five. They must not be interchanged. The actual
mixed torus columns and positive projection give an integral isomorphism whose
inverse fixes the target filling coordinates. The Wang section is normalized in
the specialization kernel. These comparisons are in
[Cusp/Specialization](../SphereSixComplex/Cusp/Specialization/).

## Global topology

The open-cover small-chain theorem is transferred from DifferentialGeometry through the
natural comparison from integer modules to additive groups. This proves that the
existing chain inclusion is a quasi-isomorphism, preserving the Mayer–Vietoris
maps and their signs without a second subdivision implementation.

The elliptic and cusp relations first give vanishing first homology. For the
fundamental group, the cusp kills two lattice directions and monodromy kills a
third. The remaining translation is central and the two meridians are inverse,
so the group is abelian. First Hurewicz then gives simple connectedness.
See [FundamentalGroup](../SphereSixComplex/FundamentalGroup/) and
[Homology/First.lean](../SphereSixComplex/Homology/First.lean).

[FourthTranslation.lean](../SphereSixComplex/Homology/FourthTranslation.lean)
extends fourth-period translation to a continuous circle action on the glued
space. Since global first homology vanishes, every loop sweep is zero in global
second homology. Local fixed-loop sweeps and projected planes are identified with
these global sweeps.

Writing xᵢ for the global images of the order-three projected planes, the sweep
and deck relations give

```text
x₁ + 2x₃ = 0,    x₀ + 3x₃ = 0,    x₀ = 2x₁.
```

Twice the first relation minus the second gives x₃ = 0. This kills the local
mapping-torus generators integrally, without a full second-homology coordinate
calculation for the elliptic union. Collar surjectivity also kills the cusp
piece's map to global second homology. In the final Mayer–Vietoris sequence, the
degree-two difference map is onto, and the degree-one map is a surjection between
free abelian groups of rank three, hence an isomorphism. Exactness gives `H₂ = 0`.
See [Homology/Second.lean](../SphereSixComplex/Homology/Second.lean).

The four-piece cover also proves finite generation and vanishing above degree
six. Euler characteristic, integral Poincaré duality, and universal coefficients
then determine every homology group. Duality uses independently proved simple
connectedness. The universal-coefficient comparison splits projective chain
complexes using the already known lower homology groups; no injectivity of ℤ or
general `Ext` splitting is assumed.
[Homology/Assembly.lean](../SphereSixComplex/Homology/Assembly.lean) combines these
results on the same carrier.

## Sphere recognition

[HomologyRecognition.lean](../SphereSixComplex/Prerequisites/Topology/Sphere/HomologyRecognition.lean)
uses a global fundamental class to show that the punctured manifold is acyclic.
Removing two chart disks yields the simply connected, relatively acyclic
cobordism needed by the imported h-cobordism proof. Twisted-sphere assembly gives
a homeomorphism to the sphere.

Alexander's radial extension need not be smooth at its center. The separate
SmoothSixSphere theorem therefore takes the independently supplied smooth atlas
and the homeomorphism and supplies a Mathlib diffeomorphism for that atlas.
[Recognition.lean](../SphereSixComplex/Prerequisites/Topology/Sphere/Recognition.lean)
applies it, and the final theorem transports the complex atlas. The diffeomorphism
is a noncomputable Lean object with smoothness proofs, not a coordinate formula.

## Navigating the library

All paths below are under `SphereSixComplex/`.

| Directories | Subject |
| --- | --- |
| `TriangleGroup/`, `Periods/` | Representation, modular periods, affine torsors |
| `TorusFamily/`, `Regular/` | Torus families, regular quotient, period transport |
| `Elliptic/`, `Cusp/`, `Toric/` | Fillings, collars, attachment maps, local homology |
| `Construction/`, `Gluing/` | Complex structure, separation, compactness, open covers |
| `FundamentalGroup/`, `Homology/` | Global topology and homology-sphere calculation |
| `Prerequisites/` | Reusable algebra, analysis, geometry, and topology |

Use a specific module when possible. `SphereSixComplex.Final` contains the final
argument; `SphereSixComplex.Construction` and `SphereSixComplex.Prerequisites`
are aggregates. `SphereSixComplex` imports the final argument; import
`SphereSixComplex.All` for the full library. The default build checks both.

The repository-root [ForMathlib](../ForMathlib/) directory contains reusable
upstream candidates, separated from the construction and its broader prerequisites:

| Directory | Reusable results |
| --- | --- |
| `Algebra/`, `GroupTheory/`, `LinearAlgebra/` | Exact sequences, integral modules, cyclic extensions, free products |
| `Analysis/` | Cauchy–Green and holomorphic cocycles, analytic square roots, the unit disc and Cayley transform |
| `Geometry/Manifold/` | Atlas transport and gluing, local diffeomorphisms, quotient manifolds |
| `Topology/` | Proper actions, covering spaces, collars, homotopy extension, mapping cylinders and gluing |
| `AlgebraicTopology/` | Fundamental groups, degree-zero homology, Mayer–Vietoris chains and naturality |

These modules import only Mathlib or other `ForMathlib` modules, and their
declarations use mathematical namespaces rather than `SphereSixComplex`.
The import checker enforces this dependency boundary. Placement here identifies
an extraction candidate, not an accepted or submission-ready Mathlib contribution:
current upstream overlap, generality, and API integration still need review.
In particular, the closed-cover construction's quotient helper overlaps existing
Mathlib quotient-homeomorphism APIs and should be reconsidered before submission.

Follow Mathlib's [naming](https://leanprover-community.github.io/contribute/naming.html)
and [style](https://leanprover-community.github.io/contribute/style.html) conventions.
State actual equalities, isomorphisms, continuity, and homotopy properties rather
than wrapping individual conclusions in certificates. Bundle dependent choices
when their coherence matters. General Mathlib-only statements belong in `ForMathlib/` when their interfaces
are reusable. Broader classical material belongs in `Prerequisites/`, which must
not import construction modules. Specialized coordinate calculations and bespoke
interfaces remain there even when their imports happen to be Mathlib-only. Preserve the specified maps and
markings: an abstract isomorphism alone does not prove their compatibility.
