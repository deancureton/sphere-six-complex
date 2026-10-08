import Verso
import VersoBlueprint
import VersoManual
import SphereSixComplex.Final

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

:::definition "classical-trust-boundary" (parent := "main_construction") (lean := "NoExoticSixSphere.noExoticSixSpheres")
The smooth-compatible theorem depends only on Lean's three standard logical axioms.
Smooth classification in dimension six is proved by the SmoothSixSphere dependency.
Its exact contract is reviewed in `docs/Verification.md`.
The topological endpoint `mathoverflow_1973` instead transports the complex atlas directly
along the proved homeomorphism and uses only the three standard logical axioms.

Finite-dimensional cellular comparison and compact Brown collaring are proved using Tau Ceti.
Integral Poincaré duality for simply connected compact manifolds is proved using the
DifferentialGeometry development and an explicit comparison of singular chain complexes.
The required universal-coefficient comparisons follow from splitting projective chain complexes.
The positive quotient retracts onto its boundary core by a small collar push and height
compression; relative triangulation and Whitehead for CW pairs are no longer assumed.
The four-piece Mayer–Vietoris calculation supplies finite generation and vanishing above
degree six directly. The construction of the simply connected complex homology six-sphere
uses only Lean’s three standard axioms. A proved h-cobordism argument supplies a sphere
homeomorphism; smooth six-sphere classification supplies the diffeomorphism.
The modular uniformization, analytic descent, toric construction, and specialized filling and
homology computations are proved. No construction-specific axiom remains. This describes the
mathematical dependency boundary; build and Comparator acceptance are checked separately.
:::
