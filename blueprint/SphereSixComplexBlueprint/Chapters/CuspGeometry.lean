import Verso
import VersoBlueprint
import VersoManual
import SphereSixComplex.All

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "The cusp and its central fiber" =>

The cusp is where the construction replaces a degenerating family by a space whose topology can
be computed. There are three different objects to keep apart: the infinite toric space, its
quotient filling, and the central fiber inside that filling. The total filling is a complex
three-manifold. Its central fiber need not be a manifold.

This chapter explains two bridges. The first reduces the filling to its central fiber by a
homotopy. The second describes that central fiber as an attachment of familiar spaces. Together
they turn the local analytic construction into the input needed for Mayer–Vietoris.

:::group "companion-cusp-geometry"
The toric replacement, its positive quotient, and the central attachment.
:::

# Why the elliptic recipe does not describe the cusp

At an elliptic end, the monodromy has finite order, three or four. A disc coordinate makes the
base action a rotation. On the torus fiber, a prescribed torsion translation accompanies the
linear action. This translation is essential: the base rotation fixes the center, but the
combined affine action on the total family is free. Taking its finite quotient therefore
produces a smooth filling, including over the center.

At the cusp, the monodromy is unipotent instead. A normalized coordinate $`s` on the covering
half-plane gives a disc coordinate $`q=\exp(2\pi i s)`. The period matrix takes the form
$`Z(s)=sB_0+C(q)`, with $`C` holomorphic across $`q=0`. The logarithmic term records the infinite
monodromy; the finite cyclic quotient construction does not describe this end. The proof uses a
toric replacement adapted to $`B_0` and then corrects its lattice action using $`C(q)`.

The exact expansion and its holomorphic extension are recorded in
{bpref "cusp-period-expansion"}[the cusp period expansion]. Only a neighborhood of the cusp is
needed. There is no need to extend these coefficients to the whole complex plane.

# A smooth total space with a crossing central fiber

Start with the triangular $`A_2` tiling of a real plane. Lift each lattice vertex $`v` to the ray
through $`(v_0,v_1,1)` in a rank-three lattice. The cones over the triangles form an infinite
fan. Each maximal cone gives a complex three-dimensional coordinate chart, and the integral
bases make the coordinate changes monomial on their overlaps.

In these charts the map to the base is
$`t=z_0z_1z_2`. Consequently the total chart is an ordinary copy of $`\mathbb C^3`, whereas its
zero fiber is the union of the three coordinate planes. A singular fiber is compatible with a
smooth total space; confusing these two smoothness questions would obscure the construction.

On the dense torus, a lattice shear has the form
$`(x_0,x_1,t)\mapsto(x_0t^a,x_1t^b,t)`. The height coordinate $`t` is unchanged. Multiplication
by the holomorphic factors obtained from $`C(q)` corrects the first two coordinates. The
resulting action agrees with the actual period family away from the central fiber. Freeness
and proper discontinuity then allow its quotient to inherit the complex atlas.

This is the role of {bpref "standard-infinite-a2-toric-model"}[the toric model] and
{bpref "cusp-local-phase-action"}[the corrected local action]. The infinite toric space is a
covering model, not the compact central fiber of the quotient.

# Forgetting phase reveals a compact cell

Absolute values separate the positive geometry from the circle phases. On the positive part,
the complex base coordinate becomes a nonnegative real height. The central positive locus is a
planar honeycomb before taking the deck quotient. Its cells are associated to the rays of the
fan, and the deck action moves these rays by lattice translations.

Every central orbit can therefore be represented in a cell around one chosen ray. Six closed
squares cover that cell. This gives a finite compact source mapping onto the positive quotient
core; compactness is a consequence of this actual surjection.

:::theorem "companion-positive-core" (parent := "companion-cusp-geometry") (lean := "SphereSixComplex.Geometry.InfiniteA2Toric.Construction.isCompact_positiveQuotientCore")
The height-zero core of the positive quotient is compact. A continuous map from six copies of
a closed square covers it.
:::

The squares can be assembled into a hexagonal picture. A radial homeomorphism identifies the
closed cell with a closed two-dimensional ball. The Lean ball uses the sup norm on
$`\mathbb R^2`, so its literal coordinate picture is a square; its topological role is a disc.
This choice has no effect on the attachment calculation.

# A collar alone is not a global retraction

Local half-space charts and compact Brown collaring provide a neighborhood of the positive
core with a collar coordinate. A collar permits projection onto the core inside that
neighborhood. It does not, by itself, move every point of the entire positive quotient into
the neighborhood. The proof needs a second, global ingredient.

Away from the core, the positive quotient has product coordinates: a two-torus and a positive
height interval. Compact height sublevels show that every open neighborhood of the core
contains all points of sufficiently small height. Thus a height compression can reach the
collar uniformly.

:::theorem "companion-positive-collar" (parent := "companion-cusp-geometry") (lean := "SphereSixComplex.Geometry.InfiniteA2Toric.constructedPositiveQuotientCollar, SphereSixComplex.Geometry.InfiniteA2Toric.Construction.exists_positiveQuotientHeight_sublevel_subset, SphereSixComplex.Geometry.InfiniteA2Toric.Construction.positiveQuotientCore_isHomotopyEquivalence")
The positive quotient core has a collar, every neighborhood of it contains a sufficiently small
height sublevel, and its inclusion into the positive quotient is a homotopy equivalence.
:::

The homotopy first pushes core points slightly into the interior. It can then use the product
coordinates to compress the height to a small positive constant. The endpoint lies in the
collar, where projection returns it to the core. The proof also controls the tracks of the
original core points, which is needed to show that this projection is a homotopy inverse.

Homotopy extension for the collared inclusion upgrades this homotopy equivalence to a strong
deformation retraction: points already on the core remain fixed throughout.

:::definition "companion-positive-retraction" (parent := "companion-cusp-geometry") (lean := "SphereSixComplex.Geometry.InfiniteA2Toric.Construction.constructedPositiveQuotientRetraction")
There is a strong deformation retraction of the positive quotient onto its height-zero core.
:::

Here height is a real function derived from the modulus of the toric base coordinate. The
homotopy time is a separate interval parameter. Compressing height is a continuous topological
operation, not a holomorphic contraction of the threefold.

Lifting through the quotient covering and restoring phases requires compatibility with deck
transformations and phase stabilizers. The construction proves these compatibilities before
using the central fiber to compute the homology of the cusp filling. A retraction of an
unrelated positive model would not suffice.

# The central fiber as one attachment

Write $`X_0` for the central fiber in the quotient filling and $`B` for its lower-dimensional
orbit locus. The open part of $`X_0` outside $`B` has a cell coordinate and two effective circle
phases. Restoring those phases to the closed positive cell gives a map
$`D^2\times T^2\longrightarrow X_0`.

Three facts identify the resulting space. This map is surjective. A point maps to $`B` exactly
when its disc coordinate is on $`\partial D^2`. On the interior it is injective. Hence all
identifications occur on the boundary, and the map gives the following adjunction description.

:::theorem "companion-central-attachment" (parent := "companion-cusp-geometry") (lean := "SphereSixComplex.Geometry.InfiniteA2Toric.Construction.centralDiskMap_surjective, SphereSixComplex.Geometry.InfiniteA2Toric.Construction.centralDiskMap_mem_boundary_iff, SphereSixComplex.Geometry.InfiniteA2Toric.Construction.centralDiskMap_injOn_interior, SphereSixComplex.Geometry.InfiniteA2Toric.Construction.centralAttachmentHomeomorph")
The actual central fiber is homeomorphic to
$`B\cup_f(D^2\times T^2)`, where $`f:\partial D^2\times T^2\to B` is the restriction of the
constructed disc-phase map. The homeomorphism respects these maps.
:::

The space $`B` has a particularly concrete description. Six complex axis charts pair by the
transition $`z\mapsto z^{-1}` to form three copies of the complex sphere. All three zero poles
are identified to one point; all three infinity poles are identified to another point. These
two common poles remain distinct. Thus this is not a wedge of three spheres.

Removing one or the other common pole gives an open cover whose intersection consists of three
punctured planes. It yields $`H_1(B;\mathbb Z)\cong\mathbb Z^2` and
$`H_2(B;\mathbb Z)\cong\mathbb Z^3`. The shared pair of poles is responsible for the two
independent degree-one classes.

A radial open cover of the attachment has pieces homotopy equivalent to $`B` and $`T^2`, with
intersection homotopy equivalent to $`S^1\times T^2`. Computing the groups alone is not enough:
Mayer–Vietoris also needs the homomorphisms induced by the attaching map. Opposite hexagon sides
lie in the same sphere component; the corresponding loop classes cancel, and circle-product
naturality handles the mixed degree-two classes. This leads to the local calculation recorded
in {bpref "cusp-filling-homology"}[the cusp homology theorem].

# Compactness of the completed threefold

The compact positive core is useful for the retraction, but it is not yet a proof that the
whole glued threefold is compact. The filling is an open piece, and a family with compact
fibers over an open base need not itself be compact.

For the cusp, the proof reduces logarithmic positions by the lattice until they have bounded
representatives in two toric charts. It treats nonzero height and zero height separately, then
obtains compact closed radial sublevels strictly below the filling radius. The radius here belongs to the
filling's compactness construction; it should not be silently substituted for the positive
height coordinate used in the preceding homotopy.

:::theorem "companion-cusp-compactness" (parent := "companion-cusp-geometry") (lean := "SphereSixComplex.Geometry.CuspFillingRadialCompactness.actualA2TwoChartRadialSublevelRepresentatives, SphereSixComplex.Geometry.CuspFillingRadialCompactness.actualLocalCuspFillingRadiusSublevel_isCompact, SphereSixComplex.Geometry.AnalyticData.compactSpace_starGlued")
For $`0\leq a<R`, where $`R` is the filling radius, the closed radial sublevel of radius
$`a` admits bounded representatives in two charts and is compact. Combined
with the central and elliptic compact cores and the end-coverage theorem, they give a compact
cover of the completed threefold.
:::

The geometric work therefore has two separate outputs. Retraction and the attachment model
make the local homology accessible. Compact representative sets control escape through the
ends and establish global compactness. Both are needed before the final sphere-recognition
argument can apply.
