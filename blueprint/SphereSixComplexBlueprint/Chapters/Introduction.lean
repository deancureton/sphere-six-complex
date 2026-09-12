import Verso
import VersoBlueprint
import VersoManual
import SphereSixComplex.Paper.Final

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Introduction and Main Theorem" =>

:::source_document "s6-paper"
%%%
title := "A compact complex threefold fibred by tori over the projective line, and the six-sphere"
kind := .pdf
pdf := "source/s6.pdf"
%%%
:::

:::group "main_construction"
Construction and recognition of the complex threefold.
:::

:::definition "six-sphere-complex-structure" (parent := "main_construction") (lean := "SphereSixComplex.AdmitsComplexStructure, SphereSixComplex.SixSphere")
An integrable complex structure on the standard six-sphere is a complex-manifold atlas modeled on
$`\mathbb{C}^3` whose underlying real atlas is diffeomorphic to the standard smooth atlas of $`S^6`.
:::

:::theorem "sphere-six-admits-complex-structure" (parent := "main_construction") (lean := "SphereSixComplex.sphere_six_admits_complex_structure") (tags := "main theorem, complex geometry") (priority := "high")
%%%
source := {
  document := "s6-paper"
  spans := #[
    {
      page := "2"
      pdf := some { path := "source/s6.pdf" }
    }
  ]
}
%%%

The standard smooth six-sphere $`S^6` admits an integrable complex structure.
This is the final consequence of {uses "six-sphere-complex-structure"}[the definition above] and
{uses "smooth-recognition"}[smooth recognition of the constructed threefold].
:::

:::proof "sphere-six-admits-complex-structure"
Transport the complex atlas of the constructed threefold along the diffeomorphism supplied by
{uses "smooth-recognition"}[smooth recognition].
:::

:::definition "classical-trust-boundary" (parent := "main_construction") (lean := "SphereSixComplex.Hurewicz.exists_map, SphereSixComplex.CWType.homological_whitehead, SphereSixComplex.SmoothSixSphere.poincare, SphereSixComplex.PoincareDuality.nonempty_addEquiv, SphereSixComplex.IntegralCohomology.universal_coefficients, SphereSixComplex.SmoothManifold.finiteCWModel, SphereSixComplex.CellularHomology.integralComparison, SphereSixComplex.CWPair.whitehead, SphereSixComplex.LocallyCollared.nonempty_collar, SphereSixComplex.ManifoldWithCorners.relativeCWComplex")
The final theorem depends on Lean's three standard logical axioms and ten general classical
results: higher Hurewicz, homological Whitehead, smooth Poincaré in dimension six, integral
Poincaré duality, universal coefficients, finite CW models of compact smooth manifolds,
cellular-to-singular homology comparison, Whitehead for CW pairs, local-to-global collaring,
and relative CW structures for manifolds with corners. Their exact contracts are reviewed in the
repository's `TRUST-BOUNDARY.md`.

The modular uniformization, analytic descent, toric construction, and specialized filling and
homology computations are proved. No construction-specific axiom remains. This describes the
mathematical dependency boundary; build and Comparator acceptance are checked separately.
:::
