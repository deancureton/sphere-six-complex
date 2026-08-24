/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.StandardSphereHomologyBase
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Punctured standard spheres

Stereographic projection identifies a standard sphere with one point removed with Euclidean
space. In particular, each member of the classical two-puncture cover used in the suspension
Mayer--Vietoris calculation is contractible.
-/

@[expose] public section

noncomputable section

open Metric Module Set Topology

namespace SphereSixComplex

/-- Stereographic projection gives a homeomorphism from a punctured standard sphere to
Euclidean space of the same dimension. -/
public noncomputable def puncturedStandardSphereHomeomorph (d : ℕ)
    (v : StandardSphere (d + 1)) :
    ({v}ᶜ : Set (StandardSphere (d + 1))) ≃ₜ EuclideanSpace ℝ (Fin (d + 1)) := by
  letI : Fact
      (finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + 1))) = (d + 1) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact
    (Homeomorph.setCongr (stereographic'_source v).symm).trans
      ((stereographic' (d + 1) v).toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target v)).trans
          (Homeomorph.Set.univ _)))

/-- A standard sphere with one point removed is contractible. -/
public theorem puncturedStandardSphere_contractible (d : ℕ)
    (v : StandardSphere (d + 1)) :
    ContractibleSpace ({v}ᶜ : Set (StandardSphere (d + 1))) :=
  (puncturedStandardSphereHomeomorph d v).contractibleSpace

end SphereSixComplex
