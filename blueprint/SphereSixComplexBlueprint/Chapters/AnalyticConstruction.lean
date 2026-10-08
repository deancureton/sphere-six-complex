import Verso
import VersoBlueprint
import VersoManual

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Building the complex family" =>

The analytic construction begins with a family of complex two-dimensional tori over a
one-dimensional base. Its total space therefore has complex dimension three. Three missing
fibres must eventually be filled. The periods are chosen with those fillings in mind: the
monodromy controls which local models can be attached, and those local models later control
the topology of the completed space.

This chapter explains the decisions behind the family. The linked entries in the construction
spine provide the corresponding declarations. The formulas are useful for following the
argument, but the existence of the required holomorphic functions is a separate theorem,
not something a displayed matrix supplies by itself.

# The base and the period parameter are different

Write $`\Delta=C_3*C_4`. There are two upper half-planes in the construction, and confusing them
hides a substantial part of the proof.

The first is the *source*. Its coordinate will be denoted by $`z`. The group acts on this
upper half-plane through a faithful Fuchsian representation of signature $`(3,4,\infty)`.
The two cyclic factors have elliptic fixed points of orders three and four. There is also
one cusp. Removing the two elliptic orbits gives the regular source on which the action is
free. Its quotient is the base of the punctured family.

The second upper half-plane contains a holomorphic *period parameter* $`\tau(z)`. On this
parameter the generators act by $`\tau\mapsto(\tau-1)/\tau` and $`\tau\mapsto-1/\tau`.
In particular the second of these fractional-linear transformations has order two, even
though the corresponding source generator has order four. These actions cannot be identified.
The period parameter intertwines them.

The distinction is recorded by {bpref "fuchsian-source-action"}[the source action] and
{bpref "modular-parameter-action"}[the modular parameter action]. The
{bpref "fuchsian-uniformization-bridge"}[uniformization bridge] constructs a holomorphic map
between them with the required generator laws. Its normalization also relates the modular
invariant to a coordinate on the source quotient: $`j(\tau(z))=1728u(z)`, where the convention
here is $`j=E_4^3/\Delta_{\mathrm{mod}}`, with $`\Delta_{\mathrm{mod}}` the modular discriminant.

The quotient statements carry more information than just this equation. Orbit fibres,
elliptic branching, and behavior at the completed cusp are needed to obtain the chosen lift.
An arbitrary solution of a pointwise equation would not provide those properties. See
{bpref "normalized-fuchsian-modular-lift-obligation"}[the exact lifting construction].

# Four periods in two complex coordinates

For holomorphic functions $`\tau,\mu,\beta`, put
$`Z=\begin{pmatrix}6\mu&\tau\\\beta&\mu\end{pmatrix}` and
$`P=(Z\mid I_2)`. Thus the four columns of $`P` are
$`(6\mu,\beta)`, $`(\tau,\mu)`, $`(1,0)`, and $`(0,1)`.
At a source point $`z`, the intended fibre is $`\mathbb C^2/P(z)\mathbb Z^4`.

Why should these columns define a lattice? Complex rank two is insufficient: four real
vectors must be independent. The construction imposes the two inequalities
$`\operatorname{Im}\tau>0` and
$`S:=\operatorname{Im}\beta-6(\operatorname{Im}\mu)^2/\operatorname{Im}\tau<0`.

Their role can be seen directly. Suppose a real linear combination of the columns vanishes,
with coefficients $`a_0,a_1,a_2,a_3`. Taking imaginary parts gives
$`6\operatorname{Im}\mu\,a_0+\operatorname{Im}\tau\,a_1=0` and
$`\operatorname{Im}\beta\,a_0+\operatorname{Im}\mu\,a_1=0`.
Eliminating $`a_1` gives $`S a_0=0`. The inequalities force $`a_0=a_1=0`, and the real parts
then give $`a_2=a_3=0`.

Consequently $`P` is a real-linear isomorphism $`\mathbb R^4\to\mathbb C^2`.
It carries the integer lattice to a discrete full-rank subgroup, and its quotient is a
compact real four-torus with a complex atlas. This is the content behind
{bpref "period-lattice-nondegeneracy"}[nondegeneracy] and
{bpref "complex-torus-fibres"}[compactness of the fibres]. The condition is a real-rank
condition; it should not be read as a claim that $`Z` is a symmetric polarization matrix.

# Monodromy tells the functions how to transform

Going around a puncture changes an integral basis of periods. The matrices
$`A_1,A_2,M_0` encode these changes. At the same time, the complex coordinates on a fibre
change by an invertible complex-linear map. The
{bpref "period-matrix-equivariance"}[matrix identities] say that these changes describe the
same lattice, so they descend to identifications of the quotient tori.

This dictates the transformation rules for the functions. Under the first generator,
$`\mu` becomes $`(1-\mu)/\tau` and $`\beta` becomes
$`\beta+2-6(1-\mu)^2/\tau`. Under the second, they become
$`1+\mu/\tau` and $`\beta-3-6\mu^2/\tau`. At the cusp the three functions transform as
$`(\tau,\mu,\beta)\mapsto(\tau-1,\mu,\beta+1)`.

These are functional equations on the source, with the source action on the left and the
parameter formulas on the right. Checking that they respect the finite-order relations is
necessary before trying to solve them analytically. The
{bpref "period-torsor-algebra"}[cocycle calculations] perform this consistency check.

# Solving the affine equations in the right order

Once $`\tau` is chosen, the equation for $`\mu` is affine-linear. Local solutions can differ
by sections of a line bundle. An affine torsor is a convenient description of this situation:
locally there are coordinates for solutions, but there is no preferred zero compatible with
all coordinate changes. A global section is precisely a compatible choice of local solutions.

The first problem has the line-bundle transition behavior of $`\mathcal O(-1)`.
The {bpref "fuchsian-modular-neg-one-frame"}[modular frame construction] identifies the actual
transition functions, including their behavior near the elliptic points and the cusp.
This identification matters: the name of a familiar line bundle alone would not establish
that the functional equation has been solved with the required local behavior.

The analytic input is a {bpref "projective-line-cech-splitting"}[holomorphic cocycle splitting].
Starting from local solutions, their differences form an additive cocycle. Holomorphic
corrections split that cocycle, so the corrected local solutions agree on overlaps.
The normalization on the chart near infinity also controls the cusp. This is how the
{bpref "fuchsian-mu-torsor-descent"}[first descent] obtains a global $`\mu`.

Only then is the second torsor formed. Its inhomogeneous terms involve the chosen $`\mu`,
so it is not an independent choice of an arbitrary second section. With $`\mu` fixed,
{bpref "fuchsian-beta-torsor-descent"}[the second descent] produces $`\beta` with its affine
transformation laws. The cusp estimates bound $`\mu` and $`\beta+\tau`, rather than
$`\beta` itself. The latter naturally has a linear term at the cusp.

The {bpref "fuchsian-period-assembly"}[assembly theorem] retains these choices together.
This dependency is important later: a local filling must use the same periods as the global
family to which it is glued.

# Turning equivariance into nondegeneracy

The affine equations do not yet force the strict inequality $`S<0`. The useful freedom is
to replace $`\beta` by $`\beta-ic` for a real constant $`c`. This preserves all generator
laws and lowers $`S` by $`c`. It therefore suffices to bound $`S` above globally.

There are two ingredients in that bound. First, $`S` is invariant under the whole source
group, even though its individual terms are not. Second, the cusp estimates bound it above
on a chosen horodisc. The remaining orbits meet a compact core, where continuity supplies
another upper bound. A single sufficiently large $`c` now makes $`S` strictly negative
everywhere. See {bpref "schur-compactness"}[the Schur compactness argument].

Compactness here concerns a core of the base quotient; the source upper half-plane is not
compact. The proof uses a fundamental region consisting of two adjacent reflection chambers
for the orientation-preserving group. The
{bpref "fuchsian-compact-core"}[compact-core theorem] accounts for this distinction and
provides the finite part of the global estimate.

This separates two jobs which otherwise look entangled: solve the holomorphic equations
with controlled cusp behavior first, then enforce real nondegeneracy by a constant shift.

# Forming the regular total space

Over the regular source, take the product with $`\mathbb C^2` and divide by the varying
integer lattice. Full rank at each point is only the beginning of the quotient argument.
To control translates uniformly, the proof obtains a lower bound for the real period maps
over compact subsets of the base. This yields proper discontinuity of the lattice action
and allows local complex charts to descend. See
{bpref "analytic-torus-family"}[the analytic torus-family construction].

The group action then identifies fibres over equivalent source points. The source action
is properly discontinuous, and deleting the elliptic orbits removes its stabilizers.
The corresponding quotient arguments give the regular complex threefold. These steps are
recorded in {bpref "elliptic-orbit-freeness"}[regular freeness] and
{bpref "global-torus-family-action"}[the global family action].

There is a further distinction here: the linear fibre transport records the period
identifications, whereas the filling construction uses affine transports with additional
translations. Those translations change the quotient geometry. The finite affine actions
extend together by the universal property of $`C_3*C_4`; they are not interchangeable with
the purely linear action merely because their base maps agree.

# Filling an elliptic point without introducing a singularity

A small disc about a source elliptic point is rotated by its finite stabilizer. On the base
alone, the center is fixed. If one simply divided a product by an action with fixed points
in the total space, a smooth quotient atlas would require additional justification.

Instead, the construction combines the rotation and linear fibre transport with a torsion
translation in the torus. In lattice coordinates the two translations are
$`\varepsilon/3` and $`-\varepsilon'/4`, where
$`\varepsilon=(1,2,-4,0)` and $`\varepsilon'=(1,3,-3,0)`. Their actual torus values are
$`P(z)\varepsilon/3` and $`-P(z)\varepsilon'/4`, modulo $`P(z)\mathbb Z^4`. The invariant integral coordinate used in the
{bpref "elliptic-family-specialization"}[fixed-point calculation] rules out fixed points
for the relevant nontrivial group elements. The affine actions have orders three and four
and are free on the actual varying families.

Their finite quotients therefore furnish smooth complex fillings. The projection to the
base can still have a multiple fibre; smoothness of the total space does not assert that
the projection is a submersion at that fibre. The
{bpref "elliptic-varying-family-quotients"}[varying-family construction] supplies the local
quotients and their punctured collars.

To attach a local quotient, the collar must embed into the global quotient. This requires
knowing exactly which global group elements identify points in a sufficiently small
neighborhood. A {bpref "properly-discontinuous-stabilizer-slice"}[stabilizer slice] reduces
the question to the local finite group. The exact stabilizer calculations then ensure that
the local and global identifications agree.

# What remains at the cusp

The third end has unipotent monodromy and uses a different filling. The period functions
first yield a normalized local cusp coordinate and an expansion
$`Z(s)=sB_0+C(q)`, with $`q=\exp(2\pi i s)`. The correction $`C` is holomorphic across
$`q=0` on a sufficiently small disc. Its exponentials correct the lattice action on the
toric model. The {bpref "cusp-period-expansion"}[cusp expansion] is a local result; it does
not assert that the correction extends to the whole complex plane.

At this point the analytic family has supplied what the three fillings need: equivariant
period lattices, free finite affine models at the elliptic points, and a controlled toric
model at the cusp. Gluing still requires matching the collars, proving Hausdorffness, and
proving compactness. Identifying the resulting manifold with the standard six-sphere is a
further topological and smooth argument, not a consequence of the period formulas alone.
