# Naming

Follow the [Mathlib naming guide](https://leanprover-community.github.io/contribute/naming.html)
and [style guide](https://leanprover-community.github.io/contribute/style.html).
Names describe mathematics; module paths distinguish prerequisites from the paper.

- Use `UpperCamelCase` for types, structures, and predicates, `lowerCamelCase` for
  data and functions, and `snake_case` for proofs. Classify an axiom by its result:
  a chosen CW model is data, whereas existence of a collar is a proposition.
- Put operations and lemmas in the namespace of their mathematical object. Prefer
  `WangHomologyPresentation.linearEquivOfSection` to a name repeating every summand
  of its codomain. Keep hypotheses in the statement; include distinctions in the
  name when callers need them to choose the right result.
- Preserve function spelling inside theorem names, as in `continuous_cayleyToDisc`.
  Refer to a type or predicate with a lowercase initial, as in Mathlib's `neZero_iff`.
  Do not mechanically convert every capital letter to an underscore.
- Avoid proof-development labels such as `Established`, `Foundation`, and
  `Completion`. Retain distinctions between a model and its realization when both
  occur in the same API.
- Keep theorem statements, implicit parameters, instances, and the trust boundary
  unchanged during renaming. Update callers and documentation together.

Concrete precedents in the pinned Mathlib include `Homeomorph.toHomotopyEquiv` and
`Homeomorph.coe_toHomotopyEquiv` in `Topology/Homotopy/Equiv.lean`, the namespace
`Complex.UnitDisc` in `Analysis/Complex/UnitDisc/Basic.lean`, and
`zmodMulEquivOfGenerator` in `GroupTheory/SpecificGroups/Cyclic.lean`.

The migrations cover the ten classical assumptions and their principal interfaces,
Wang sections and splitting, general disc/Cayley coordinates, first Hurewicz and
relative CW tools, cusp angular methods, and affine torsor descent. Methods stay in
the namespace of their receiver so that dot notation remains available.
Historical names elsewhere remain candidates for subsequent API migrations; this
document does not certify that every declaration already follows these conventions.
