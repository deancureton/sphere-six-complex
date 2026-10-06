# Fundamental groupoid van Kampen theorem

This is the minimal import closure of the van Kampen development used by
SphereSixComplex, extracted from
[Paul-Lez/mathlib4](https://github.com/Paul-Lez/mathlib4/tree/97d303eb50436be7c4bac4388bdb49459ae9140b/Mathlib/AlgebraicTopology/FundamentalGroupoid)
at commit `97d303eb50436be7c4bac4388bdb49459ae9140b`.
The upstream work was proposed in
[mathlib4 PR #41603](https://github.com/leanprover-community/mathlib4/pull/41603).
The source is licensed under Apache 2.0; see `LICENSE`.

The 34 retained modules contain 11,673 original lines. Their original SHA-256
hashes are recorded in `UPSTREAM-SHA256.json`. Three files outside the import
closure are omitted: `HomotopyInvHelpers`, `HomotopyInvProof`, and
`ConsecutiveRowsProof`.

Initial extraction changes:

- Rename module prefix `Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen`
  to `VanKampen`; declaration names are unchanged.
- Import `VanKampen.Opposites` in each retained module. It carries the two
  `PreservesColimit.op` and `PreservesLimit.op` instances added by the same fork
  to `Mathlib.CategoryTheory.Limits.Preserves.Opposites`.
- Package the files independently of Mathlib, using official Mathlib commit
  `6b7abb3c7686292736be2955bd3eb9ebf63b456a` and Lean 4.35.0-rc3.

This package does not introduce any axioms or incomplete proofs. Compatibility
with the new compiler and Mathlib revision is checked by the enclosing project's
build and axiom audit.

Lean 4.35.0-rc3 compatibility adaptations:

- `CleanMapFromAdapted`, `CompositionFinal`, and `CleanRefinement`: six finite-image equalities are transported
  extensionally. Lean now distinguishes the subtype and linear-order decidable
  equality implementations on the unit interval; finite-set membership is
  independent of this implementation choice. The theorem statements are unchanged.
