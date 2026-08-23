import Verso
import VersoBlueprint
import VersoManual
import SphereSixComplex.LatticeData

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

:::theorem "period-functions" (parent := "construction_spine") (priority := "high")
There are holomorphic functions $`\tau,\mu,\beta` on the upper half-plane satisfying the transformation,
cusp-growth, and nondegeneracy conditions listed in the Setup.
:::

:::proof "period-functions"
Use {uses "monodromy-identities"}[the monodromy identities] and construct the three functions directly
from modular forms, retaining only the properties used by the quotient and filling constructions.
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

:::theorem "compact-complex-threefold" (parent := "construction_spine") (priority := "high")
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

:::theorem "integral-homology" (parent := "construction_spine") (priority := "high")
The integral homology of $`X` is the integral homology of $`S^6`.
:::

:::proof "integral-homology"
Compute the Mayer--Vietoris sequence of {uses "compact-complex-threefold"}[the same gluing], including
the integral specialization maps and their saturation.
:::

:::theorem "smooth-recognition" (parent := "construction_spine") (priority := "high")
The underlying standard smooth manifold of $`X` is diffeomorphic to $`S^6`.
:::

:::proof "smooth-recognition"
Combine {uses "fundamental-group"}[simple connectedness] and
{uses "integral-homology"}[integral homology] to obtain a homotopy sphere, then use six-dimensional
smooth homotopy-sphere recognition.
:::
