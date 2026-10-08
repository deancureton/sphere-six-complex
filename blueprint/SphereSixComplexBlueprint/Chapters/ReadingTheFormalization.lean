import Verso
import VersoBlueprint
import VersoManual

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Following the argument into Lean" =>

A useful way to inspect the formalization is to choose one mathematical claim, identify the
space and maps in its statement, and follow only the inputs needed for that claim. Reading every
auxiliary lemma in file order obscures the mathematical structure.

# Start at the assembly

The final existence proof is short because its inputs have already been proved for one coherent
construction. The object `AnalyticData` holds the choices used throughout: the periods, local
models, and the comparisons that make their gluing meaningful. Results parameterized by the same
object concern the same choices.

The topological assembly proves three facts about that glued carrier: first homology vanishes,
its fundamental group is trivial, and its integral homology agrees degree by degree with that of
the six-sphere. The final theorem packages the carrier as a compact complex threefold, applies
recognition, and transports its atlas. These are the steps linked by
{bpref "paper-threefold-assembly"}[the assembly entry].

Working backward from this assembly is usually more informative than starting with a matrix or
quotient implementation. Ask which hypothesis of the next theorem a calculation establishes.
The period inequalities justify a lattice quotient; the compactness proof justifies manifold
recognition; the degree-one rank calculation closes a specific gap in Mayer–Vietoris.

# Isomorphism types do not determine maps

Many intermediate spaces have familiar homology groups. Knowing those groups is not sufficient
for a gluing calculation. For example, two homomorphisms from $`\mathbb Z` to $`\mathbb Z` can
have the same source and target but completely different cokernels: multiplication by one has
zero cokernel, while multiplication by two has cokernel $`\mathbb Z/2`.

The same issue occurs in the collar maps. An abstract isomorphism with a free abelian group does
not determine where a particular loop, projected plane, or boundary class goes. The proof needs
coordinate comparisons that commute with the geometric inclusion, covering, or specialization
map. This is the purpose of the naturality results surrounding the local calculations.

When reading a long coordinate theorem, isolate three items:

- The geometric map whose induced homomorphism is being calculated.
- The chosen source and target identifications with explicit abelian groups.
- The equality that says these identifications intertwine the geometric and algebraic maps.

The names of intermediate coordinate systems can then be treated as bookkeeping. The content is
the commuting comparison, including the signs and integral coefficients. In particular, a
boundary generator and a period-sweep generator cannot be interchanged merely because both lie
in free summands of rank one.

# The carrier and its structures

Lean distinguishes the underlying type, its topology, its charted-space structure, and the
proof that the charts are compatible. This separation makes the final atlas transport precise.
A homeomorphism can transport a complex atlas, while a diffeomorphism also controls its relation
to a previously specified real atlas.

There are therefore several presentations of the same geometry in the files: a quotient,
a glued space, a toric model, or a carrier equipped with a manifold structure. An equivalence
between presentations is useful only when it preserves the relevant maps. The proof explicitly
tracks these comparisons before using functoriality of homology or the fundamental group.

A statement of the form `Nonempty (X ≃ₜ Y)` asserts existence of a homeomorphism, with continuity
proofs in both directions. A `Diffeomorph` adds the differentiability conditions relative to
specified atlases. Neither notation promises a convenient coordinate formula. The smooth endpoint
uses the latter object to prove compatibility through the identity on the sphere.

# How the library is divided

The construction-specific directories contain the periods, torus families, fillings, gluing,
and global topology. `Prerequisites` contains the broader classical material used by those
arguments. `ForMathlib` isolates reusable results whose imports are confined to Mathlib and other
modules in that folder. This is an enforced dependency boundary, not a claim that every such
result is already ready for an upstream submission.

The dependency libraries supply further proved mathematics. A declaration imported from another
repository is still a mathematical input to understand: its name alone does not explain its
hypotheses. For the final recognition step, inspect the compactness, manifold, simple-connectedness,
and integral-homology hypotheses, then follow the construction results that discharge them.

# Using the declaration reference

The following chapter gives linked statements and short proof descriptions. Its entries are
selected landmarks, not a claim that each informal paragraph is itself checked by Lean. The
dependency graph offers another route through those landmarks. Use it to locate the analytic,
geometric, or topological inputs to a result, then read the corresponding formal declarations.

For a focused audit, good entry points are
{bpref "period-lattice-nondegeneracy"}[the real-rank condition],
{bpref "fourth-circle-homology"}[the circle-sweep comparison],
{bpref "section-seven-paper-assembly"}[the low-degree homology assembly], and
{bpref "established-smooth-recognition"}[the recognition contracts]. Together they expose the
main changes of mathematical viewpoint: analysis to geometry, local cycles to global homology,
and homology to manifold classification.
