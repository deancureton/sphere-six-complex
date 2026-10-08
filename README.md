# A Complex Structure on the Six-Sphere

A Lean formalization of the construction in [the paper](https://alpo.ge/s6.pdf)
([local copy](references/s6.pdf)): a compact complex threefold diffeomorphic to the
standard smooth six-sphere.

The main theorem is:

```lean
SphereSixComplex.sphere_six_admits_complex_structure :
  AdmitsComplexStructure SixSphere
```

Here `SixSphere` is the unit sphere in `EuclideanSpace ℝ (Fin 7)`.
`AdmitsComplexStructure` asserts the existence of a complex atlas modeled on
`EuclideanSpace ℂ (Fin 3)`, with complex-smooth transition maps, whose underlying
real atlas agrees with the standard stereographic smooth structure through the
identity map. The definitions are in [ChallengeDefs.lean](ChallengeDefs.lean).

## The two Comparator statements

[Comparator](comparator.json) checks two endpoints in [Solution.lean](Solution.lean):

| Statement | What it requires |
| --- | --- |
| `sphere_six_admits_complex_structure` | A complex-smooth atlas on **the standard smooth six-sphere**, whose underlying real atlas is compatible with the standard stereographic atlas through the identity map. |
| `mathoverflow_1973` | A complex `C¹` atlas on **the underlying topological six-sphere**, with no requirement relating its real smooth structure to the standard one. |

Both assert genuine complex structures, not merely almost-complex structures.
The substantive extra condition in the first statement is **compatibility with
the prescribed smooth structure**. Its proof transports the complex atlas along
a diffeomorphism; the second uses only a homeomorphism and avoids smooth sphere
classification. See [the statement guide](docs/Proof.md#statements-and-atlases)
for the definitions and proof routes.

The compiled proof uses only Lean's three standard axioms: `propext`,
`Classical.choice`, and `Quot.sound`. There are no additional mathematical axioms.
Build and axiom-audit results are distinct from independent Comparator verification;
see [verification](docs/Verification.md) for the checks and current limits.

## Build

The pinned toolchain is Lean 4.35.0-rc3. With Lean installed:

```sh
lake exe cache get
LEAN_NUM_THREADS=3 nice -n 15 lake build
```

Start with [Final.lean](SphereSixComplex/Final.lean) for the assembled proof,
[the proof guide](docs/Proof.md) for its mathematical organization, or
[the Verso companion](blueprint/) for an explanation of the analytic construction, cusp
geometry, and sphere-recognition argument, followed by a linked declaration reference.
Mathlib-only upstream candidates live in [ForMathlib](ForMathlib/); see the
[library guide](docs/Proof.md#navigating-the-library) for their scope and review status.

## Dependencies

Exact revisions are pinned in [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json).

- [Mathlib](https://github.com/leanprover-community/mathlib4).
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti), including cellular homology
  and compact collaring results.
- [Jordan Curve Theorem](https://github.com/Paul-Lez/jordan-curve-theorem), a fork
  of [the EPFL-LARA project](https://github.com/epfl-lara/jordan-curve-theorem).
- [DifferentialGeometry](https://github.com/deancureton/differential-geometry/tree/67e3631e3b8f532a31ac2375b2d50a4369044eec),
  an extracted and ported dependency from
  [qinz1yang/differential-geometry](https://github.com/qinz1yang/differential-geometry),
  derived in part from Ayush Khaitan's CanonicalTopology development. It supplies
  small-chain approximation, integral duality, and h-cobordism results.
- [SmoothSixSphere](https://github.com/deancureton/lean-proofs/tree/613af5fc94f43562c18d4e9ae8936beebaaf1b29),
  an extraction of Boris Alexeev's smooth six-sphere classification from
  [plby/lean-proofs](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e).
- Thomas Zhu's fundamental-groupoid van Kampen development, proposed in
  [Mathlib PR #41603](https://github.com/leanprover-community/mathlib4/pull/41603)
  and retained in [vendor/VanKampen](vendor/VanKampen/README.md) with source hashes,
  license, and port notes. We thank Thomas Zhu for permission to use and port it.

Several focused analytic and toric arguments also adapt Boris Alexeev's
[HopfProblem development](https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean).
Their source files retain attribution and license notices. See
[dependency provenance](docs/Verification.md#dependency-provenance) for details.
