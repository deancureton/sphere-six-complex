# Paused theta-six stable-framing workstream

Status date: 2026-08-25

This branch preserves the unmerged rank-seven stable-framing and `SO(7)` homotopy work while the
workstream is paused.  The independent proof that `pi_5(S^6) = 0` is being extracted from this
stack and merged separately.

## Established on this branch

The branch contains the stacked work from pull requests #74--#95.  In particular, it proves:

- the rank-seven clutching reductions from `GL(7, R)` through `SL(7, R)` to `SO(7)`;
- the concrete cube-boundary model of the clutching five-sphere;
- the first-column Stiefel geometry `SO(6) -> SO(7) -> S^6`, including its standard fiber, local
  sections, product trivializations, bundle charts, and relative five-cube transport;
- exactness at `pi_5(SO(7))`;
- `pi_5(S^6) = 0`, by boundary-exact smooth approximation, dimension avoidance, radial
  projection, and contraction in a punctured sphere; and
- surjectivity of stabilization `pi_5(SO(6)) -> pi_5(SO(7))`, together with a reduction of
  `pi_5(SO(7)) = 0` to the assertion that this stabilization homomorphism is trivial.

The public declarations added by this stack were built both as focused modules and through
`SphereSixComplex.Main`.  Their audits use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact remaining homotopy-group gap

The remaining input is

```lean
forall g : Omega^(Fin 5) SO6 1,
  GenLoop.Homotopic
    (GenLoop.map stabilizeMap stabilizeMap_one g)
    GenLoop.const
```

Equivalently, stabilization `pi_5(SO(6)) -> pi_5(SO(7))` must be proved to be the trivial
homomorphism.

Independent probes established the following useful boundaries:

1. A relation-valued connecting construction from six-cube loops in `S^6` to five-cube loops in
   `SO(6)` can be defined.  Any exact connecting witness stabilizes trivially, and every class in
   the kernel of stabilization has such a witness.  This gives relation-valued exactness at
   `pi_5(SO(6))` without assuming a long exact sequence API.
2. The currently public relative-transport theorem retains the endpoint projection and endpoint
   homotopy, but forgets that the total-space homotopy projects pointwise to the supplied base
   homotopy.  Therefore an arbitrarily chosen transported endpoint is not yet a sufficiently
   computable connecting map for an Euler or degree calculation.
3. No usable theorem for Euler classes of real vector bundles, clutching classification,
   `pi_5(SO(6)) = Z`, topological Bott periodicity, or the required Stiefel long exact sequence was
   found in the pinned Mathlib, current Mathlib upstream, or TauCeti.
4. The separate boundary-seven degree stack ending at commit `be55aa3` computes degree for the
   project's simplicial model of `S^6`; it does not provide the rank-six Euler invariant or the
   Brouwer-degree calculation needed here.

The recommended resumption route is:

1. define the explicit tangent clutching loop in `SO(6)` from the north/south Stiefel sections;
2. prove directly that its block stabilization is null in `SO(7)`;
3. construct a normalized Euler coordinate
   `pi_5(SO(6)) ~= Multiplicative Z` and calculate that the tangent clutching class has coordinate
   one; and
4. use `piFiveSO7_subsingleton_of_stabilize_eq_one` from
   `SpecialOrthogonalSevenPiFiveSphereReduction.lean`.

Strengthening relative transport to retain its projected homotopy is a useful alternative first
step if the proof is resumed through a genuine connecting map rather than the explicit transition
function.

## Remaining geometric gap after `pi_5(SO(7))`

Vanishing of `pi_5(SO(7))` is not by itself the final hemispherical theorem.  The downstream polar
and cube-collapse reductions still require an unconditional construction of
`HomotopySixSphereBufferedRadialRankSevenClutchingPresentation`.  The standard-sphere cover module
does not currently establish this presentation for an arbitrary marked homotopy six-sphere.

Thus resumption has two distinct targets:

- the normalized Euler/generator calculation proving `pi_5(SO(7)) = 0`; and
- the buffered radial clutching presentation needed to apply that computation to the original
  homotopy-sphere theorem.

## Pull-request checkpoint

The last pull request in the paused stack is #95, commit `029ae77`.  The unconditional
`pi_5(S^6) = 0` proof consists of the three commits `2a0d56a`, `319b792`, and `2a12d02`; those
commits have no source dependency on the intervening `SO(7)` stack and can be restacked directly
on `main`.
