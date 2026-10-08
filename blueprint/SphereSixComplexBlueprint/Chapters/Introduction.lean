import Verso
import VersoBlueprint
import VersoManual
import Solution

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "The theorem and the route to it" =>

The aim is to construct a compact complex manifold of complex dimension three and then identify
its underlying real manifold with the standard six-sphere. The two halves of that sentence require
rather different arguments. Holomorphic periods and quotient charts supply the complex geometry;
fundamental groups, integral homology, and manifold recognition identify the underlying space.

This companion explains the route followed by the Lean development. It is organized by the
mathematical problems that have to be solved, rather than by the order in which the code was
written. The original paper motivates the construction. The statements linked here, and the
proofs behind them, describe the present formalization.

:::source_document "s6-paper"
%%%
title := "A compact complex threefold fibred by tori over the projective line, and the six-sphere"
kind := .pdf
pdf := "source/s6.pdf"
%%%
:::

# What is actually proved?

Fix the unit sphere in real seven-dimensional Euclidean space, with its usual topology and
stereographic smooth atlas. The conclusion gives this specific smooth manifold a complex atlas.
The transition maps are complex smooth, so this is an integrable complex structure. An
almost-complex structure alone would not supply those charts.

:::group "main_construction"
Construction and recognition of the complex threefold.
:::

:::definition "six-sphere-complex-structure" (parent := "main_construction") (lean := "SphereSixComplex.AdmitsComplexStructure, SphereSixComplex.SixSphere, SphereSixComplex.SmoothlyCompatible")
A complex structure compatible with the standard smooth six-sphere is a complex-smooth atlas
modeled on $`\mathbb C^3` whose underlying real atlas is smoothly compatible with the fixed
stereographic atlas through the identity map on the sphere.
:::

:::theorem "sphere-six-admits-complex-structure" (parent := "main_construction") (lean := "SphereSixComplex.sphere_six_admits_complex_structure") (tags := "main theorem, complex geometry") (priority := "high")
The standard smooth six-sphere admits an integrable complex structure in the sense of
{uses "six-sphere-complex-structure"}[the preceding definition].
:::

:::proof "sphere-six-admits-complex-structure"
Construct a compact complex threefold with trivial fundamental group and the integral homology
of the six-sphere. Obtain a diffeomorphism to the standard sphere by
{uses "smooth-recognition"}[smooth recognition], and transport the complex atlas along it.
:::

There is a second endpoint, corresponding to a question about the underlying topological sphere.
It asks for a complex atlas without prescribing how its underlying real atlas relates to the
standard smooth structure.

:::theorem "topological-six-sphere-complex-structure" (parent := "main_construction") (lean := "mathoverflow_1973")
The underlying topological six-sphere admits an atlas modeled on $`\mathbb C^3` with complex
$`C^1` transition maps.
:::

:::proof "topological-six-sphere-complex-structure"
Transport the same constructed complex atlas along the sphere homeomorphism. The complex
transition maps are unchanged by this transport. Smooth classification of the target sphere is
not needed for this endpoint.
:::

Complex $`C^1` transition maps are holomorphic. Thus both endpoints ask for genuine complex
structures. The additional requirement in the first endpoint is compatibility with the specified
real smooth atlas. The proof produces a diffeomorphism as a Lean object with proofs of smoothness
in both directions; it does not give a closed coordinate formula for that diffeomorphism.

# Read the proof in two passes

On a first pass, keep four questions in view.

1. How can four moving real periods in $`\mathbb C^2` define a holomorphic family of compact tori?
2. How can the family be filled at its two elliptic ends and its unipotent cusp without losing
   a smooth complex total space?
3. Why do the fillings kill the fundamental group and second integral homology of the glued space?
4. Which recognition results turn those calculations into a diffeomorphism with $`S^6`?

The next chapters address these questions. The analytic chapter explains the period construction
and finite cyclic fillings. The cusp chapter explains the toric model, the geometry needed for
compactness, and the central attachment used in homology. The topology chapter follows the
low-degree vanishing argument through sphere recognition.

On a second pass, follow a linked result to the declaration reference and its Lean statement.
The final reference chapter retains the detailed construction catalog and dependency graph.
It is useful for locating a lemma after its purpose is clear.

# A map of the argument

Start with a regular family over a sphere with three points removed. A typical fiber is a complex
two-torus, so the total space has complex dimension three. Around the missing points the periods
have prescribed monodromy: two finite-order behaviors and one unipotent behavior. These determine
three different local fillings.

Glue the regular family to the three fillings along holomorphic collars. Prove that the result
is Hausdorff, second countable, connected, and compact. These properties are essential inputs to
later topology, not automatic consequences of writing down the quotient charts.

The global topology is then reduced in stages:

- Local relations give $`H_1(X;\mathbb Z)=0`.
- The cusp relations separately make $`\pi_1(X)` abelian. First Hurewicz then gives
  $`\pi_1(X)=0`.
- A global circle action, local integral relations, and Mayer–Vietoris give
  $`H_2(X;\mathbb Z)=0`.
- Finite generation, the Euler characteristic, integral duality, and universal coefficients
  determine the remaining homology groups.
- Sphere recognition gives a homeomorphism, and smooth classification in dimension six gives
  the diffeomorphism needed for the smooth-compatible endpoint.

This order matters. Vanishing first homology alone does not give simple connectedness, and
vanishing rational homology alone would not rule out integral torsion. The topology chapter
explains where the proof supplies the stronger information.

# What the formal verification covers

The audited endpoints use only Lean's standard logical axioms: `propext`, `Classical.choice`, and
`Quot.sound`. Classical mathematical inputs, including smooth six-sphere classification, are
proved in the imported developments rather than postulated as additional axioms.

The mathematical dependencies include covering-space and homotopy theory, singular homology,
compact collaring, integral duality, h-cobordism, and smooth sphere classification. Their role is
to connect specific geometric inputs to specific conclusions. The recognition argument still
has to prove those inputs for the constructed threefold.

The exposition is an explanation of the proof, not itself a machine-checked informal proof.
Lean checks the linked declarations and their formal dependencies. The prose and the dictionary
between mathematical language and formal definitions still require human review. Compilation,
the axiom audit, and independent Comparator verification are separate checks; the repository's
verification guide records how to run them and the local platform limits.
