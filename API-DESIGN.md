# Mathematical interfaces

The paper-facing API should expose the maps and propositions being proved. A name such as
`CompletionInput` is not a substitute for a readable mathematical statement.

## Principles

- State a theorem using the actual equality, isomorphism, continuity, homotopy, or typeclass
  property when a separate predicate would only name that one assertion.
- Bundle dependent choices when later constructions need the same maps, bases, charts, or
  homotopies. Do not bundle a theorem's conclusion together with an arbitrary object and a
  function that already supplies that conclusion.
- Define an action before proving it free or properly discontinuous. Quotient types must not
  acquire irrelevant proof parameters through the definition of their action.
- Use Mathlib objects such as `HomotopyEquiv`, `IsCancelSMul`, and
  `ProperlyDiscontinuousSMul` instead of project records duplicating their fields.
- Make canonical choices parameters or definitions, rather than storing arbitrary copies and
  copying them through adapters. Preserve markings: an abstract isomorphism does not replace a
  commuting square for specified maps.
- Keep general manifold and homology results in `Prerequisites`; specialize them to the
  constructed space in `Paper`.

These follow the [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html).
Concrete precedents in the pinned Mathlib are `Geometry/Manifold/PoincareConjecture.lean`,
`Topology/Homotopy/Equiv.lean`, `Algebra/Group/Action/Defs.lean`, and
`Topology/Covering/Quotient.lean`.

## Construction and recognition

`exists_complexThreefold_simplyConnected_homologyEquiv_sixSphere` exhibits a compact complex threefold, asserts
`SimplyConnectedSpace` on its carrier, and gives an additive isomorphism with the integral
homology of the six-sphere in every degree. It no longer returns a `CompletedPaperThreefold`
certificate. The recognition theorem takes ordinary manifold, compactness, and simple
connectedness hypotheses and the displayed degreewise homology isomorphisms; its conclusion
is `Nonempty` of an actual `Diffeomorph`.

`ComplexThreefold` remains a bundle for existential quantification over a carrier, topology,
and atlas. Its induced real smoothness is derived from the complex atlas. Generic gluing of
such manifolds belongs to the prerequisite library. `CompactComplexStar` contains only the
geometric gluing inputs. Simple connectedness and degreewise homology are separate theorems
about its actual glued carrier, rather than prerequisites to constructing the manifold.
`AnalyticData` retains coherent dependent choices of parameters, periods, and cusp
coordinates. Atlas transport is stated for arbitrary source and target manifolds with the
specified atlases; the six-sphere result is its paper-specific application.

## Cusp action and analytic descent

The phase-corrected action depends on its algebraic coefficients, not on the proof that it is
free. Freeness supplies `IsCancelSMul` separately; compact-overlap estimates give
`ProperlyDiscontinuousSMul`. Joint continuity of the torus action is stated as `Continuous`,
without a one-field record. Čech splitting uses the actual descended torsor and its comparison
maps, without the former `CousinCechReduction` function package.

## Homology and markings

The Mayer–Vietoris calculation exposes equalities of the actual difference homomorphisms in
chosen coordinates and their bijectivity. Arbitrary model families with reflexive equivalences
are not part of that certificate. The canonical affine band specializes one radial homotopy
record; it does not copy the same four fields into a second record. The side inverses and
marked compatibility homotopies are retained. Boundary comparisons display equalities of the
actual homomorphisms. The production coordinates use raw four for the cusp boundary and
normalized raw five for the fourth-period sweep. Alternative marking conventions must not be
substituted into those equalities.

## Homotopies and cycles

The elliptic relator results display the connector path and fundamental-group equality.
Synchronized factor homotopies retain both equations at the common moving basepoint.
`ContinuousMap.Homotopy.hcompLoop` supplies their reusable concatenation in the prerequisite
library; two unrelated homotopy-existence statements would lose the required synchronization.

The band comparison theorems state the two marked `Homotopic` assertions as a conjunction.
Phase spreading takes a chosen equivariant strong deformation retraction and the explicit
orbit-fiber descent equation for that same retraction. The constructed instance supplies its
canonical retraction directly, rather than selecting one through an intermediate existence record.

Cellular incidence is an equality of boundary homomorphisms in every degree. The calculation
recovering dependent entries from the chain-complex identity remains an explicit theorem; four
overlapping records of finite incidence tables are unnecessary.

Integral singular cycles use Mathlib's `cycles` object, `cyclesMap`, `iCycles`, and `homologyπ`
in every degree. The marked prism comparison still asserts equality of actual chain morphisms,
not only equality of their homology classes. Quotient retractions specialize the existing
`EquivariantStrongDeformationRetraction` instead of wrapping it in another record.

## Retained surface

Only the two Comparator endpoints determine the mathematical roots of the development.
Intermediate APIs remain when their declarations or elaboration support those proofs. The
Blueprint and examples describe this retained surface rather than adding preservation roots.
Historical names in reduction notes are not promises of current APIs.

## Validation

The externally checked challenge is preserved. Changes to a classical axiom interface must
preserve its mathematical contract; explicit expansion of a definition is permitted. Full builds,
placeholder and import-layer checks, recursive axiom audits, and Comparator kernel validation
are separate gates. Intermediate API changes require mathematical review as well as elaboration:
removing a redundant field, weakening an unnecessary hypothesis, and merely renaming a
constant are different operations. Review combines the compiled environment's predicate and
small-structure inventory with inspection of fields, consumers, and mathematical dependencies;
it does not infer correctness from a declaration's name or size.

## Statement transparency

The universal coefficient axiom displays its degree-zero duality and positive-degree
`Ext`/dual decomposition, rather than returning a record named after the theorem. Its former
record and the new proposition are equivalent using `Classical.choice`; no natural splitting
has been added. The Hurewicz range and smooth Poincaré hypotheses are also displayed at their
axiom declarations. The cellular comparison still bundles dependent choices of disk generators,
cell bases and comparison maps: its compatibility equations must remain synchronized.

The modular frame is computed from its Eisenstein root, rather than stored alongside an equation
fixing its value. Equivariant roots extend the same root object. Cellular incidence, elliptic
endpoint period identities, and degree-one homology coordinate comparisons state their equations
directly. A proposition already proved about elliptic relators is used directly without
`Nonempty` or a choice operation.


## Mathematical ownership

Cusp straightening, elliptic logarithmic gauges, and real-period trivializations use a shared
namespace for each construction, with separate files for its algebra, descent, and continuity
proofs. Integral multiple-fiber calculations live under `MultipleFiberCoinvariants` and
`AffineCyclicQuotientHomology`, rather than namespaces named after paper sections or proof status.
The modular lift, its Eisenstein root, and its modular frame share the same selected root.

Locally finite closed-cover gluing and the Cayley manifold construction belong to prerequisites.
The quotient comparison uses Mathlib's `IsQuotientMap.lift`. The constructed toric model is named
directly where it is used; it no longer appears to depend on an unused analytic-data argument.
