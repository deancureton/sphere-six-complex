import Verso
import VersoBlueprint
import VersoManual

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Why the threefold is a sphere" =>

The analytic construction produces a compact connected complex threefold $`X`.
Its complex charts also give it a smooth real six-dimensional atlas.
The remaining problem is to recognize this particular manifold.
Knowing its dimension, or even its Euler characteristic, is far from enough.
We will prove simple connectedness and compute integral homology before invoking
the recognition theorems.

All homology groups in this chapter have coefficients in $`\mathbb Z`.
This matters throughout: a calculation over $`\mathbb Q` could miss precisely
the torsion that would prevent sphere recognition.
The proof uses the regular torus-family region, the two elliptic fillings, and
the cusp filling, with the overlap identifications supplied by the construction.
These are the pieces of {bpref "compact-complex-threefold"}[the glued threefold].

# The order of the argument

There are two distinct reasons for introducing first homology early.
It is an abelian group, so the local filling relations become short integer
calculations. Its vanishing also kills the two-dimensional classes obtained
by sweeping loops around a global circle action.

The logical order is therefore as follows.
First, prove $`H_1(X)=0` from explicit relations and prove independently that
$`\pi_1(X)` is abelian. First Hurewicz then gives $`\pi_1(X)=0`.
Next use the circle action and Mayer–Vietoris to prove $`H_2(X)=0`.
Finally, duality, universal coefficients, and the Euler calculation give all
the remaining homology groups. Recognition is applied only after these steps.
In particular, no sphere identification is used to calculate the homology of $`X`.

# Why the core controls the fundamental group

The regular region has lattice translations and two base meridians as
fundamental-group generators. Denote the translation lattice by
$`L=\mathbb Z^4`, its images by $`t(a)`, and the meridians by $`r_1,r_2`.
Conjugating a translation by a meridian applies the corresponding monodromy
matrix to $`a`. These are relations in an affine group, before abelianization.

To use these generators globally, one must show that the fillings do not
introduce additional generators. Each collar maps surjectively onto the
fundamental group of its filling. The four-piece van Kampen argument then
makes the core group surject onto $`\pi_1(X)`.
Thus every global class comes from the affine core, even though some of its
relations become stronger after filling.
The geometric input is {bpref "local-fundamental-groups"}[the quotient-cover calculation];
the gluing input is {bpref "van-kampen-generation"}[generation by the local groups].

The cusp filling kills the last two coordinate translations.
The order-three monodromy relation then kills the second coordinate
translation as well. The surviving first-coordinate translation commutes
with both meridians, and the cusp meridian relation makes the meridians
inverse to one another. Hence the global fundamental group is abelian.
This is {bpref "cusp-fundamental-group"}[the cusp-only group calculation].
It does not yet prove that the surviving translation or meridian is trivial.

# First homology: two adjacent integers

Pass to $`H_1(X)` and write the group operation additively.
The toric and monodromy relations reduce every translation image to a
multiple of one class $`T`. More precisely, for the chosen lattice basis,
$`t(a)=a_0 T`.
The two elliptic fillings and the cusp filling give
$`3r_1=-T`, $`4r_2=T`, and $`r_1+r_2=0`.

Substitute $`r_2=-r_1` in the second equation. Together with the first,
this gives $`3r_1=4r_1`. Subtracting $`3r_1` gives $`r_1=0`.
Consequently $`r_2=0` and $`T=0`.
No division by three or four occurs, and there is no assumption that the
ambient group is torsion free. The conclusion holds in any abelian group
with these relations.

The coefficients three and four come from actual bounding discs.
A small circle in each elliptic filling bounds a disc there. When expressed
in the regular region, its logarithmic gauge lift separates into a period
loop and a base loop. The modular coordinate winds three or four times
around the puncture; its remaining nonvanishing factor contracts.
The signs in the displayed relations reflect the chosen orientations and
period conventions. The formal calculation tracks those choices in
{bpref "elliptic-filling-relations"}[the filling relations].

The core-to-global map is surjective on the fundamental group, and the
degree-one Hurewicz map is surjective. Thus these classes generate all of
$`H_1(X)`, proving its vanishing. Separately, the cusp calculation made
$`\pi_1(X)` abelian. First Hurewicz identifies its abelianization with
$`H_1(X)`, so the group itself is trivial.
This last implication is {bpref "fundamental-group-recognition"}[simple-connectedness recognition].
Vanishing first homology by itself would not suffice.

# Sweeping a loop into a surface

Translation in the fourth period direction defines a circle action
$`a:S^1\times X\to X`. Constructing this action globally requires compatibility
with both elliptic quotient actions, the cusp model, and the collar gluing.
It is not enough to have translation on the regular torus fibers alone.

For a loop $`\gamma:S^1\to X`, the action gives a torus
$`(s,t)\mapsto a(s,\gamma(t))` in $`X`.
Its homology class is the image under $`a_*` of the cross product
$`[S^1]\times\gamma_*[S^1]`.
Since $`H_1(X)=0`, that cross product, and hence the swept torus class,
is zero. This is the mechanism behind {bpref "fourth-circle-homology"}[the circle-sweep argument].

The useful local generators are tori in mapping-torus models of the reduced
elliptic fibers. Some are precisely fixed-loop sweeps for this action;
others are projected coordinate planes. The proof checks the actual maps
to $`X`, so that naturality applies to the geometric generators rather
than to an arbitrarily chosen abstract homology basis.

Write $`x_i` for the global image of the order-three projected plane
$`P_i`. Common-source comparisons identify $`P_0` and $`P_3` with their
order-four counterparts. The local sweep and deck calculations give
$`x_1+2x_3=0`, $`x_0+3x_3=0`, and $`x_0=2x_1`.
The integral combination
$`2(x_1+2x_3)-(x_0+3x_3)=x_3`
therefore proves $`x_3=0`.
The remaining local generator relations kill the images of both reduced
elliptic fibers in degree two.

Passing from these fibers to the whole elliptic interior uses the proved
mapping-torus generation and overlap comparisons.
The result needed next is exactly that the inclusion of the elliptic
interior into $`X` induces the zero map on $`H_2`.
It is not a claim that the interior itself has zero second homology.
This distinction saves a much larger calculation of its full degree-two
group and an explicit basis for that group.

# The last Mayer–Vietoris sequence

Let $`U` be the elliptic interior, let $`V` be the cusp filling in the
final open cover, and let $`W=U\cap V` be their collar overlap.
Up to the specified homeomorphisms, $`U\cup V=X`.
The relevant exact sequence has the segment
$`H_2(W)\xrightarrow{d_2}H_2(U)\oplus H_2(V)\xrightarrow{s_2}H_2(X)`
followed by
$`H_2(X)\xrightarrow{\partial}H_1(W)\xrightarrow{d_1}H_1(U)\oplus H_1(V)\to H_1(X)`.
Here $`d_k` is the difference of the two inclusion maps and $`s_k`
is their sum into the union.

We already know that the inclusion from $`U` induces zero on $`H_2`.
The map $`H_2(W)\to H_2(V)` is surjective by cusp specialization.
Every degree-two class of $`V` therefore comes from the overlap, where
its two maps into $`X` agree. Its image is consequently zero as well.
Thus $`s_2=0`, and exactness makes $`d_2` surjective.

One more input is needed: exactness alone still allows $`H_2(X)` to
inject into $`H_1(W)`. The computed degree-one groups are
$`H_1(W)\cong\mathbb Z^3`, $`H_1(U)\cong\mathbb Z`, and
$`H_1(V)\cong\mathbb Z^2`.
Since $`H_1(X)=0`, the map $`d_1` is surjective.
It is therefore a surjective map between free abelian groups of the same
finite rank, hence an isomorphism.

Now $`\partial=0` because its image is the kernel of $`d_1`.
Exactness makes $`s_2` surjective, but $`s_2` was already zero.
This proves $`H_2(X)=0`.
The construction uses {bpref "cusp-filling-homology"}[cusp specialization],
{bpref "elliptic-multiple-fibre-homology"}[the elliptic degree-one calculation], and
{bpref "mayer-vietoris-contract"}[open-cover exactness] in precisely these roles.

# Why Euler characteristic finishes the integral calculation

The four-piece homology calculation also supplies finite generation in
each degree and vanishing above degree six. Euler additivity applies to
the same open pieces and collars. The regular region, the elliptic
fillings, and the collars contribute zero; the cusp filling contributes
two. Hence $`\chi(X)=2`.
The cusp contribution is computed from its central-fiber model, using its
own two Mayer–Vietoris sequences, as described in
{bpref "cusp-filling-homology"}[the local homology calculation].

For the compact simply connected smooth six-manifold underlying $`X`,
integral Poincaré duality and universal coefficients give
$`H_6(X)\cong\mathbb Z`, $`H_5(X)=0`, and $`H_4(X)=0` from the
known groups in degrees zero, one, and two.
In the middle degree they identify $`H_3(X)` with its integer dual
$`\operatorname{Hom}(H_3(X),\mathbb Z)` because the lower groups are free.
That dual is torsion free, so $`H_3(X)` is torsion free as well.

The Euler formula now reads $`2=\chi(X)=2-\operatorname{rank}H_3(X)`.
Thus $`H_3(X)` has rank zero. Finite generation and torsion freeness
then force $`H_3(X)=0`.
This is why the Euler calculation alone would have been insufficient:
rank zero without the duality argument could leave a finite torsion group.
We have proved {bpref "integral-homology"}[sphere homology] in every degree.

# Two recognition steps, two endpoints

Simple connectedness and integral sphere homology are now properties of
the actual compact manifold built by gluing. The proved recognition
development yields a homeomorphism $`X\cong S^6`.
The smooth classification result in dimension six upgrades the conclusion
to existence of a diffeomorphism for the specified real smooth atlas.
These are separate stages of {bpref "established-smooth-recognition"}[recognition].

A homeomorphism already transports the complex charts to the topological
six-sphere: the transition maps in complex coordinates do not change.
This gives the endpoint named `mathoverflow_1973`, whose statement asks
for a complex atlas without compatibility with the fixed standard real atlas.

For {bpref "sphere-six-admits-complex-structure"}[the smooth-compatible endpoint],
transport along the diffeomorphism instead. Its smooth inverse ensures
that the real atlas underlying the transported complex charts agrees
smoothly with the standard sphere atlas.
The final theorem proves existence of this diffeomorphism; it does not
provide a coordinate formula for it. The gain over the topological endpoint
is the verified compatibility with the standard smooth structure.
