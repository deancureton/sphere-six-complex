# Lean 4.35 and trust-boundary reduction

Starting checkpoint: `88402cc`, Lean 4.34.0, ten mathematical axioms in the final
endpoint closure. Work is isolated on `codex/lean435-axioms`. Comparator endpoint
statements remain fixed. `Scratch/` is outside this task.

## Checkpoints

- [x] Coordinate Lean 4.35.0-rc3, Mathlib, Tau Ceti and Blueprint dependencies;
  preserve required fork additions; repair API migration; build, audit and Comparator.
- [x] Replace finite-dimensional cellular-homology consumers with proved Tau Ceti
  results; remove the unused general comparison axiom; repeat gates.
- [x] Use compact Brown collaring on the quotient and covering homotopy lifting
  upstairs; remove collar axiom; repeat gates.
- [x] Integrate simply-connected integral Poincare duality with coefficient and
  cochain bridges; remove duality axiom; repeat gates.

Only the main agent runs Lake builds. Local compiler work runs at nice 15 with
`LEAN_NUM_THREADS=3`; direct checks use `lean -j1` when available. LSP is preferred
for proof iteration after dependency bootstrap. Commit and push verified
checkpoints with lowercase one-line messages. Do not reduce axiom allowlists until
compiled endpoint dependency audits establish the reduction.

Research and source pins are recorded in `.ci/reuse-research/REPORT.md`; this
ledger tracks implemented work and gate results, not source-audit promises.

## Upgrade progress

- Root and Blueprint use Lean 4.35.0-rc3, official Mathlib `6b7abb3c`, and
  Tau Ceti `6175f404`. Shared git pins agree and both Mathlib cache fetches passed.
- The required van Kampen fork additions are preserved in `vendor/VanKampen`
  with upstream hashes, license and migration notes. The placeholder gate now
  includes vendored sources; it passes.
- The inverse-boundary cluster argument is now imported from Tau Ceti, which
  incorporated this project's earlier proof. Remaining reflection proofs pass
  targeted Lean checks.
- An explicit finite-simplex homeomorphism connects Mathlib's new representation
  to the coordinate metric used by subdivision. All twelve subdivision files
  pass LSP checks; the old coordinate API still emits deprecation warnings.
- The whole-project build, import/layer check, placeholder check, exact axiom
  audit and Comparator pass. Final endpoints retain ten mathematical axioms;
  the construction retains seven. Both also use Lean's three standard axioms.
- Comparator's exported solution passed Lean's default kernel. This local
  macOS run uses fake-landrun and does not test Linux sandbox isolation.
- Blueprint's build tool and full `ci-pages.sh` site build pass, including the
  HTML index, manifest and HTML-cache output checks.
- The pinned Comparator and exporter both build with the new compiler. No
  mathematical axiom has been discharged at this checkpoint yet.

## Cellular comparison checkpoint

- Replaced the general cellular comparison axiom with a proved finite-dimensional
  cellular model from Tau Ceti. Every consumer supplies the finite-dimensional
  hypothesis from an existing finite CW model; endpoint statements are unchanged.
- The constructor, sphere homology inputs and finite-model homology consequences
  have only Lean's three standard axioms. The full project builds (10,119 jobs).
- Compiled endpoint closures contain nine mathematical axioms for the final
  theorems and six for the construction, plus the three standard axioms in each.
  The exact allowlists, Comparator configuration and generated catalog agree.
- Comparator passed with Lean's default kernel. Import/layer and placeholder
  checks pass. The source replacement removes roughly 350 lines.
- Proof-only exactness instances stay behind a private import; concrete homology
  functor uses specify their category universe to avoid ambiguous instance search.
- Blueprint site generation and its HTML index, manifest and HTML-cache checks pass.

## Compact collar checkpoint

- Proved compact Brown collaring for a subset inclusion with local collars that
  meet the whole boundary only on the zero slice. Strengthened local chart
  witnesses supply exactly that property.
- Proved compactness of the quotient core via its six square cells. Constructed
  its collar and lifted the interior deformation through the covering to prove
  upstairs contractibility. Deleted three unused declarations from the old route.
- All four new ingredients have only Lean's three standard axioms. The full
  project build passes (10,123 jobs), as do import/layer and placeholder checks.
- Compiled closures contain eight mathematical axioms for the final theorems and
  five for the construction. The exact audit and regenerated catalog pass.
- Comparator passes with Lean's default kernel; the updated Blueprint introduction
  also compiles against the proved collar dependency.

## Simply-connected duality checkpoint

- Integrated the proved compact-support and cap-product duality results from
  DifferentialGeometry at `788efe97894474c032de6dfb1289d515f613d15a`.
  The initial 221-module extraction (now expanded and hosted in the pinned
  DifferentialGeometry fork) preserves
  licenses, original hashes, attribution and an exact module-system port patch.
- The upstream legacy file format cannot be imported by this project's module
  files. The port adds module/export headers, adjusts helper visibility and
  qualification, and imports one Mathlib implementation for an existing unfolding
  proof. It preserves mathematical statements and proof steps up to those renames.
- Explicit chain, homology, cochain and cohomology isomorphisms connect its lifted
  integer module coefficients to this project's additive-group complexes. The
  new duality theorem and cohomology adapter have only the three standard axioms.
- Simple connectedness is proved independently before homology-sphere comparison.
  Internal consumers now use that hypothesis. The redundant orientation bundle
  and orientation proofs are deleted; only the general real-restriction lemma
  remains in `Manifold/RestrictScalars.lean`.
- The full project build passes (10,346 jobs). Exact compiled closures contain
  seven mathematical axioms for the final theorems and four for the construction,
  with the three standard axioms in each. Allowlists and the generated catalog agree.
- Import/layer checks pass for 734 project modules. The placeholder gate includes
  VanKampen and DifferentialGeometry and finds only the two intentional Challenge placeholders.
- Independent review confirmed the coefficient comparisons, dimension transport,
  acyclic proof order, all 221 original hashes and reversibility of the port patch.
- Comparator accepts both unchanged endpoint statements with Lean's default kernel
  under the exact seven-result classical boundary.
- Final Blueprint site generation passes, including HTML index, manifest and
  HTML-cache checks. Static inventory finds exactly seven project axioms, all
  reachable from the final theorem, with no additional unused axioms.

## Smooth six-sphere classification dependency

The SmoothSixSphere package extracts `NoExoticSixSphere.noExoticSixSpheres` from
Boris Alexeev's `plby/lean-proofs` at
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Its package branch preserves that commit
as its parent, original license notices, and source hashes. The Lake revision
`89f53697e3a7f253b9969f5efe296dc3a9ba9ec0` pins the port to this project's Lean
and Mathlib versions on the `codex/smooth-six-sphere` branch of
[deancureton/lean-proofs](https://github.com/deancureton/lean-proofs/tree/89f53697e3a7f253b9969f5efe296dc3a9ba9ec0).

The port changes the module format and adapts Mathlib APIs, including a proved
coordinate equivalence between the old and current simplex representations.
Unused import branches and a reviewed batch of unused theorems are removed.

The upstream Hopf-fibration argument used the constructed threefold's circle
action. A direct normalized Hermitian projector now supplies homotopy lifting on
the ordinary unit Hopf spheres. Elementary orbit algebra identifies the fibers
with the circle, and real linear isometries identify the unit spheres with the
standard Euclidean spheres. This removes the analytic threefold construction from
the classification dependency and cuts about 104,000 lines from its import closure.
The remaining package is substantial; making it external does not eliminate its
build or maintenance cost.

S6 applies the proved classification directly to its existing homeomorphism. The
independently supplied smooth atlas and both final theorem statements are
unchanged. The old smooth-classification axiom and homotopy-sphere wrappers are
removed; the permitted axiom list now contains only the standard three.

The full project and Blueprint builds passed. Exact recursive audits of both
endpoints and the construction report only `propext`, `Quot.sound`, and
`Classical.choice`. Import/layer and placeholder checks also passed. Comparator's
kernel replay was interrupted after approximately 34 minutes without a verdict;
its configuration remains unchanged apart from removing the final permitted
mathematical axiom.
