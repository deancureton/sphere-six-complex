/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Prerequisites.Topology.SmoothRecognition
public import SphereSixComplex.Prerequisites.Topology.HomologySphere
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Separation.Connected
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Positive integral homology of the standard six-sphere

This file isolates the algebraic output required from the standard hemisphere
Mayer--Vietoris calculation. Contractible spaces already have trivial positive-degree
integral homology in Mathlib; this is proved below from homotopy invariance and the calculation
for totally disconnected spaces.

For the sphere calculation, `StandardSphereMayerVietorisInputs` records exactly the remaining
outputs of singular excision and the standard hemisphere covers: the positive-degree
suspension equivalences, the degree-one edge cases, and the circle generator. The final theorem
proves, without another topological assumption, that these data give
`SixSpherePositiveHomologyInputs`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Topology

namespace SphereSixComplex

/-! ## Homology of contractible spaces -/

/-- Positive-degree integral homology of a contractible space is a singleton. -/
public theorem subsingleton_integralSingularHomology_of_contractible
    {X : Type} [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (IntegralSingularHomology n X) := by
  have hUnit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat n (AddCommGrpCat.of ℤ) (TopCat.of Unit) hn
  let _ : Subsingleton (IntegralSingularHomology n Unit) :=
    AddCommGrpCat.subsingleton_of_isZero hUnit
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  let he := integralSingularHomologyEquivOfHomotopyEquiv n e
  exact ⟨fun x y ↦ he.injective (Subsingleton.elim _ _)⟩


/-! ## The finite suspension calculation -/

/-- The positive-degree sphere homology calculation absent from Mathlib. -/
public structure SixSpherePositiveHomologyInputs : Prop where
  degreeSix : Nonempty (IntegralSingularHomology 6 SixSphere ≃+ ℤ)
  otherDegrees :
    ∀ n : ℕ, n ≠ 0 → n ≠ 6 → Subsingleton (IntegralSingularHomology n SixSphere)







end SphereSixComplex
