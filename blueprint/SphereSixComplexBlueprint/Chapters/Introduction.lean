import Verso
import VersoBlueprint
import VersoManual
import SphereSixComplex.ComplexStructure

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
$`\mathbb{C}^3` whose underlying topology is the usual topology of $`S^6`.
:::

:::theorem "sphere-six-admits-complex-structure" (parent := "main_construction") (lean := "SphereSixComplex.sphere_six_admits_complex_structure") (tags := "main theorem, complex geometry") (priority := "high")
%%%
source := {
  document := "s6-paper"
  spans := #[
    {
      page := "4"
      pdf := some { path := "source/s6.pdf" }
    }
  ]
}
%%%

The standard smooth six-sphere $`S^6` admits an integrable complex structure.
This is the final consequence of {uses "six-sphere-complex-structure"}[the definition above].
:::

:::proof "sphere-six-admits-complex-structure"
Construct the compact complex threefold $`X` of the paper, prove that it is simply connected and has
the integral homology of $`S^6`, and identify its smooth manifold with the standard sphere. Transport
the complex atlas of $`X` along that diffeomorphism.
:::
