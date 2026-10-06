# Lean 4.35 and trust-boundary reduction

Starting checkpoint: `88402cc`, Lean 4.34.0, ten mathematical axioms in the final
endpoint closure. Work is isolated on `codex/lean435-axioms`. Comparator endpoint
statements remain fixed. `Scratch/` is outside this task.

## Checkpoints

- [x] Coordinate Lean 4.35.0-rc3, Mathlib, Tau Ceti and Blueprint dependencies;
  preserve required fork additions; repair API migration; build, audit and Comparator.
- [x] Replace finite-dimensional cellular-homology consumers with proved Tau Ceti
  results; remove the unused general comparison axiom; repeat gates.
- [ ] Use compact Brown collaring on the quotient and covering homotopy lifting
  upstairs; remove collar axiom; repeat gates.
- [ ] Integrate simply-connected integral Poincare duality with coefficient and
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
