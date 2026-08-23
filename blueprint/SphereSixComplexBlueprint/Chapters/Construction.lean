import Verso
import VersoBlueprint
import VersoManual
import SphereSixComplex.Construction
import SphereSixComplex.Geometry.AtlasTransport
import SphereSixComplex.Geometry.Quotient
import SphereSixComplex.LatticeData
import SphereSixComplex.Periods.Matrix
import SphereSixComplex.Topology.StandardSphere
import SphereSixComplex.Topology.TwistObstruction
import SphereSixComplex.TriangleGroup.Representation

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Construction Spine" =>

This chapter follows the condensed Setup and Theorem on the first two PDF pages. Later sections of the
paper are consulted only when they are needed to prove one of these nodes.

:::group "construction_spine"
The minimal construction and recognition path.
:::

:::definition "lattice-monodromy-data" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.T₁, SphereSixComplex.LatticeData.T₂, SphereSixComplex.LatticeData.T₀, SphereSixComplex.LatticeData.A₁, SphereSixComplex.LatticeData.A₂, SphereSixComplex.LatticeData.M₀")
The rank-four lattice carries explicit local monodromies of orders three, four, and infinite order at
the cusp.
:::

:::theorem "monodromy-identities" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.T₁_det, SphereSixComplex.LatticeData.T₂_det, SphereSixComplex.LatticeData.T₁_pow_three, SphereSixComplex.LatticeData.T₂_pow_four, SphereSixComplex.LatticeData.N_sq, SphereSixComplex.LatticeData.A₁_mul_A₂_mul_M₀")
The displayed matrices are unimodular, the finite monodromies have exact orders three and four, and
the nilpotent part $`N = T_0-I` satisfies $`N^2=0`.
:::

:::proof "monodromy-identities"
Expand the four-by-four matrices and check every integral entry. The Lean proof is kernel checked and
does not use a native evaluator.
:::

:::theorem "triangle-representation" (parent := "construction_spine") (lean := "SphereSixComplex.TriangleGroup.rhoV, SphereSixComplex.TriangleGroup.rhoLambda, SphereSixComplex.TriangleGroup.rhoV_g₀, SphereSixComplex.TriangleGroup.rhoLambda_g₀")
The free product $`(\mathbb Z/3)*(\mathbb Z/4)` acts on the rank-four lattice and its dual with the
prescribed monodromies at the two elliptic points and the cusp.
:::

:::proof "triangle-representation"
Descend the powers of $`T_1` and $`T_2` to the two cyclic factors, then use the coproduct universal
property. The cusp relation identifies the inverse product with $`T_0`.
:::

:::theorem "invariant-polarization" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.invariant_alternating_matrix_classification, SphereSixComplex.LatticeData.Q₀Matrix_T₁_invariant, SphereSixComplex.LatticeData.Q₀Matrix_T₂_invariant")
Every integral alternating form invariant under both finite monodromies is an integral multiple of
the displayed form $`Q_0`.
:::

:::theorem "dual-coinvariants" (parent := "construction_spine") (lean := "SphereSixComplex.LatticeData.dualCoinvariantRelations_eq_ker_gamma, SphereSixComplex.LatticeData.dualCoinvariantsEquivInt")
The dual monodromy coinvariants form a free rank-one group detected by the invariant functional
$`\gamma`.
:::

:::theorem "atlas-transport" (parent := "construction_spine") (lean := "SphereSixComplex.isManifold_transportChartedSpace")
A manifold atlas and its differentiability structure transport along a homeomorphism without changing
the transition functions.
:::

:::proof "atlas-transport"
Conjugate every chart by the homeomorphism. In each transition map the conjugating maps cancel, leaving
the original transition map in the same structure groupoid.
:::

:::theorem "complex-quotient" (parent := "construction_spine") (lean := "SphereSixComplex.Geometry.quotientChartContDiff_of_contMDiff_smul, SphereSixComplex.Geometry.orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul")
A free properly discontinuous action by smooth translations gives the orbit space a manifold structure
and makes the quotient projection a local diffeomorphism.
:::

:::theorem "period-matrix-equivariance" (parent := "construction_spine") (lean := "SphereSixComplex.Periods.generatorOne_equivariance, SphereSixComplex.Periods.generatorTwo_equivariance, SphereSixComplex.Periods.cusp_equivariance")
The displayed period matrix transforms under the two elliptic generators and the cusp by the
prescribed dual monodromy matrices.
:::

:::proof "period-matrix-equivariance"
Substitute the three transformation laws for $`\tau,\mu,\beta` and verify the resulting matrix
identities entry by entry.
:::

:::theorem "period-functions" (parent := "construction_spine") (priority := "high")
There are holomorphic functions $`\tau,\mu,\beta` on the upper half-plane satisfying the transformation,
cusp-growth, and nondegeneracy conditions listed in the Setup.
:::

:::proof "period-functions"
Use {uses "monodromy-identities"}[the monodromy identities] and construct the three functions directly
from modular forms. Their transformation laws feed
{uses "period-matrix-equivariance"}[the period-matrix equivariance identities].
:::

:::theorem "torus-family" (parent := "construction_spine") (priority := "high")
The period matrix built from $`\tau,\mu,\beta` defines a proper holomorphic family of compact complex
two-tori over the thrice-punctured sphere.
:::

:::proof "torus-family"
Use {uses "period-functions"}[the period functions] to prove that each period subgroup is a lattice and
that the monodromy action descends freely away from the elliptic fixed points.
:::

:::theorem "cusp-filling" (parent := "construction_spine") (priority := "high")
The unipotent end admits the toric filling whose central fibre is the opposite-edge quotient of the
degree-six del Pezzo surface.
:::

:::proof "cusp-filling"
Use {uses "torus-family"}[the torus family] and the unimodular cusp lattice map coming from
{uses "monodromy-identities"}[the explicit nilpotent monodromy].
:::

:::theorem "elliptic-fillings" (parent := "construction_spine") (priority := "high")
The order-three and order-four ends admit free logarithmic-transform fillings with the twist vectors
specified in the Setup.
:::

:::proof "elliptic-fillings"
Use {uses "torus-family"}[the torus family] and the invariant twist vectors fixed by $`A_1` and $`A_2`.
:::

:::theorem "compact-complex-threefold" (parent := "construction_spine") (lean := "SphereSixComplex.ComplexThreefold") (priority := "high")
The global family and the three fillings glue to a compact connected complex threefold $`X`.
:::

:::proof "compact-complex-threefold"
Glue {uses "cusp-filling"}[the cusp filling] and
{uses "elliptic-fillings"}[the elliptic fillings] to the common collars of the punctured
{uses "torus-family"}[torus family], and verify the resulting charts and transition maps.
:::

:::theorem "fundamental-group" (parent := "construction_spine") (priority := "high")
For the twists $`(\ell_0,\ell_1,\ell_2)=(0,1,-1)`, the fundamental group of $`X` is trivial.
:::

:::proof "fundamental-group"
Apply van Kampen to {uses "compact-complex-threefold"}[the glued threefold] and reduce the resulting
presentation using the explicit lattice coinvariants.
:::

:::theorem "twist-obstruction" (parent := "fundamental-group") (lean := "SphereSixComplex.Topology.TwistObstruction.abs_p, SphereSixComplex.Topology.TwistObstruction.obstruction_group_eq_zero")
For the chosen twist vectors the obstruction integer
$`12\ell_0-4\ell_1-3\ell_2` has absolute value one, so its cyclic quotient is trivial.
:::

:::theorem "integral-homology" (parent := "construction_spine") (priority := "high")
The integral homology of $`X` is the integral homology of $`S^6`.
:::

:::proof "integral-homology"
Compute the Mayer--Vietoris sequence of {uses "compact-complex-threefold"}[the same gluing], including
the integral specialization maps and their saturation.
:::

:::theorem "smooth-recognition" (parent := "construction_spine") (lean := "SphereSixComplex.exists_complex_threefold_diffeomorphic_sixSphere") (priority := "high")
The underlying standard smooth manifold of $`X` is diffeomorphic to $`S^6`.
:::

:::proof "smooth-recognition"
Combine {uses "fundamental-group"}[simple connectedness] and
{uses "integral-homology"}[integral homology] to obtain a homotopy sphere, then use six-dimensional
smooth homotopy-sphere recognition.
:::

:::theorem "standard-six-sphere" (parent := "smooth-recognition") (lean := "SphereSixComplex.sixSphere_isCompact, SphereSixComplex.sixSphere_isPathConnected, SphereSixComplex.sixSphere_isManifold")
The target $`S^6` is compact, path-connected, and carries the standard smooth six-manifold atlas.
:::
