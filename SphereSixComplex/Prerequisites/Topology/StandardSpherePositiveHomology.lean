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
# Positive integral homology

Positive-degree homology vanishes for contractible spaces. The sphere homology specification
records that the six-sphere has integral homology ℤ in degree six and zero in other positive degrees.
`SixSphereHomology` proves it from the explicit two-cell CW model and cellular/singular comparison.
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

/-! ## The sphere homology specification -/

/-- Integral homology of the six-sphere in positive degrees. -/
public structure SixSpherePositiveHomologyInputs : Prop where
  degreeSix : Nonempty (IntegralSingularHomology 6 SixSphere ≃+ ℤ)
  otherDegrees :
    ∀ n : ℕ, n ≠ 0 → n ≠ 6 → Subsingleton (IntegralSingularHomology n SixSphere)

end SphereSixComplex
