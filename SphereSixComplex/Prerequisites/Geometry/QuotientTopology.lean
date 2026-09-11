/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Prerequisites.Geometry.Quotient

/-!
# Topological consequences for orbit quotients

This file names the general topological facts about the orbit projection that are used around
the paper's quotient constructions. It complements `Quotient`, which already defines
`OrbitQuotient` and `quotientProjection` and develops their manifold theory.

The wrappers are adapted from Paul Lezeau's independent
`ComplexStructures.Foundation.HolomorphicQuotientSetup`. They use the upstream projection and
typeclass hypotheses directly, without duplicating the quotient or its charted-space structure.
-/

@[expose] public section

noncomputable section

open Topology

namespace SphereSixComplex.Geometry

/-! ## The orbit projection as an open quotient map -/

section OpenProjection

variable {M G : Type*} [TopologicalSpace M] [Group G] [MulAction G M]
  [ContinuousConstSMul G M]

/-- The orbit projection is an open quotient map. -/
public theorem quotientProjection_isOpenQuotientMap :
    IsOpenQuotientMap (quotientProjection (M := M) (G := G)) := by
  simpa only [quotientProjection] using
    (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := M))




end OpenProjection

/-! ## Covering-space consequences -/

/-! ## Separation, compactness, and countability -/

section Separation

variable {M G : Type*} [TopologicalSpace M] [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
  [T2Space M] [LocallyCompactSpace M]

/-- A properly discontinuous quotient of a locally compact Hausdorff space is Hausdorff. -/
public theorem orbitQuotient_t2Space : T2Space (OrbitQuotient (M := M) (G := G)) := by
  infer_instance

end Separation

section LocalCompactness

variable {M G : Type*} [TopologicalSpace M] [Group G] [MulAction G M]
  [ContinuousConstSMul G M] [LocallyCompactSpace M]

/-- An open orbit quotient of a locally compact space is locally compact. -/
public theorem orbitQuotient_locallyCompactSpace :
    LocallyCompactSpace (OrbitQuotient (M := M) (G := G)) :=
  quotientProjection_isOpenQuotientMap.locallyCompactSpace

end LocalCompactness

section SecondCountability

variable {M G : Type*} [TopologicalSpace M] [Group G] [MulAction G M]
  [ContinuousConstSMul G M] [SecondCountableTopology M]

/-- An orbit quotient of a second-countable space is second countable. -/
public theorem orbitQuotient_secondCountableTopology :
    SecondCountableTopology (OrbitQuotient (M := M) (G := G)) :=
  ContinuousConstSMul.secondCountableTopology

end SecondCountability

end SphereSixComplex.Geometry
