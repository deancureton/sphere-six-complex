# Verification

The permitted axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
All other mathematical inputs are proved dependencies. The theorem names and
axiom policy are recorded in [comparator.json](../comparator.json).

## Local checks

Run from the repository root:

```sh
lake exe cache get
LEAN_NUM_THREADS=3 nice -n 15 lake build
CHECK_AXIOMS_SKIP_BUILD=1 LEAN_NUM_THREADS=1 nice -n 15 ./scripts/check-axioms.sh
uv run --no-project python scripts/check-imports.py
uv run --no-project python scripts/check-sorries.py
lake shake --keep-public SphereSixComplex.All Solution
```

[AxiomAudit.lean](../scripts/AxiomAudit.lean) traverses the compiled dependency
closure of both endpoints and the principal construction theorems, following
types, proof bodies, inductive constructors, and recursor rules. It rejects every
nonstandard axiom, including `sorryAx`, and requires that the audited closure
contain the standard three. Its shell wrapper also checks Comparator's permitted
axioms. Skipping the build is appropriate only when the artifacts are current.

The import checker enforces the prerequisite/construction layering, rejects
missing project imports, and checks reachability from the library aggregate.
It also requires `ForMathlib` modules to import only Mathlib or other `ForMathlib`
modules; prerequisite and construction modules may use that layer.
The placeholder checker rejects `sorry`, `admit`, and `native_decide` in its
configured project and dependency sources. Its only exceptions are the two
intentional statement placeholders in [Challenge.lean](../Challenge.lean).
[Solution.lean](../Solution.lean) proves those statements without importing
Challenge. The compiled axiom audit checks imported proof dependencies as well;
a source scan alone is not a proof audit.

Run the import audit without `Challenge`: it intentionally declares the same
endpoint names as `Solution`, so those modules cannot share an environment.
The two library indexes retain explicit project-module imports, as Mathlib's
own index does; their `shake: keep-all` annotations preserve that organization.

## Comparator and Blueprint

On Linux with bubblewrap available, run the toolchain's bundled verifier:

```sh
lake comparator
```

Comparator checks the declared endpoint statements and exported proof environment.
It complements the build and axiom audit. The current bundled command requires
Linux sandbox support; it has not completed successfully in the local macOS
environment. Earlier local runs with the replaced runner ended without a verdict
on the present mathematical boundary. Neither those runs nor the local axiom
audit establish Linux sandbox isolation. A successful Comparator run must be
reported separately.

CI reports the proof build and axiom audit separately from Comparator and the
Blueprint. Comparator runs on Linux with bubblewrap; publishing documentation
does not stand in for proof verification.
GitHub Pages uses the Actions workflow as its publishing source.

The [Blueprint](../blueprint/) has its own Lake project. To build it and check the
generated index, declaration manifest, and HTML cache:

```sh
cd blueprint
LEAN_NUM_THREADS=3 nice -n 15 bash scripts/ci-pages.sh
```

The cleanup checkpoint passed the full project build, compiled axiom audit, source
checks, targeted import audit, Blueprint build, and workflow linting. The axiom audit
traversed 184,756 constants
and found only the standard three axioms. Existing Lean and documentation warnings
remain. These are local checks; they do not establish a successful remote Comparator
run or a cold-build speedup. Workflow definitions are under
[.github/workflows](../.github/workflows/).

## Dependency provenance

The authoritative pins are in [lakefile.toml](../lakefile.toml) and
[lake-manifest.json](../lake-manifest.json). Package licenses and original source
notices remain with the corresponding code.

- **SmoothSixSphere:**
  [fork revision `613af5fc`](https://github.com/deancureton/lean-proofs/tree/613af5fc94f43562c18d4e9ae8936beebaaf1b29),
  extracted from Boris Alexeev's `plby/lean-proofs` at
  [`8822f7dd`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e).
  Its branch preserves upstream ancestry, license notices, and original hashes in
  `UPSTREAM-SHA256.json`. It supplies classical smooth classification, not the
  upstream complex-structure construction. The port uses a direct Hopf-fibration
  argument based on a normalized Hermitian projector and circle-orbit algebra,
  removing the upstream dependency on a constructed threefold. Its pinned source
  contains 6,789 Lean modules and 629,506 lines after a reviewed deletion of 1,162
  unused theorem commands. These are source counts, not build-time improvements.
- **DifferentialGeometry:**
  [fork revision `67e3631e`](https://github.com/deancureton/differential-geometry/tree/67e3631e3b8f532a31ac2375b2d50a4369044eec),
  selected from `qinz1yang/differential-geometry` at
  `788efe97894474c032de6dfb1289d515f613d15a`. The package records original hashes,
  licenses, and the module-system port patch. Its duality and h-cobordism proofs
  are connected to this project's actual singular chains and coefficient groups
  through explicit comparison isomorphisms.
- **VanKampen:** the retained local package comes from `Paul-Lez/mathlib4` at
  `97d303eb50436be7c4bac4388bdb49459ae9140b`; its
  [README](../vendor/VanKampen/README.md) records the upstream proposal, Apache-2.0
  license, original hashes, and compiler adaptations.
- **Focused HopfProblem ports:** scalar Cauchy–Green inversion, holomorphic
  cocycle splitting, toric arguments, and a mapping-torus boundary comparison
  adapt Boris Alexeev's
  [revision `9ac8a456`](https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean).
  The retained source headers record attribution and Apache-2.0 provenance.

## Maintenance limits

Develop further proof simplifications internally. Do not port additional code or
proof arguments from plby's HopfProblem development. The provenance above records
earlier imports, not a source for future cleanup.

The mathematical statement audit traced the atlas definitions to Mathlib and
checked that recognition preserves the independently supplied smooth atlas. It
was not a human review of every proof in the dependency libraries. Compilation
checks proof terms; axiom inspection checks assumptions; reviewing definitions
checks whether the statement expresses the intended mathematics.

The classification dependency is not declaration-minimal. A second conservative
inventory at the pinned revision found 1,652 review candidates covering 8,851
lines. Proof-term unreachability alone does not authorize deletion: notation,
instances, attributes, tactic hints, and other elaboration dependencies matter.
Review whole source commands and rebuild actual consumers after pruning.

No current cold-build speedup is claimed. Historical cleanup ledgers, measurements,
and superseded proof routes remain available in Git history; they are not the
current mathematical contract.
