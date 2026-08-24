/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.HomologySphere
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Separation.Connected

/-!
# The zero-dimensional base of the sphere homology calculation

The standard zero-sphere consists of two points. This file proves directly that it is finite
and totally disconnected, so Mathlib's calculation for totally disconnected spaces gives its
positive-degree integral homology.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Topology

namespace SphereSixComplex

/-- The standard `d`-sphere in `ℝ^(d+1)`. -/
public abbrev StandardSphere (d : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1

/-- Every point of the standard zero-sphere has coordinate square equal to one. -/
private theorem standardSphereZero_coordinate_sq (x : StandardSphere 0) :
    x.1 0 ^ 2 = (1 : ℝ) := by
  have hx :
      x.1 ∈ {y : EuclideanSpace ℝ (Fin 1) | ∑ i, y i ^ 2 = (1 : ℝ) ^ 2} := by
    rw [← EuclideanSpace.sphere_zero_eq 1 (by norm_num)]
    exact x.2
  simpa using hx

/-- Record which of the two possible coordinates a point of the zero-sphere has. -/
private def standardSphereZeroSign (x : StandardSphere 0) : Fin 2 :=
  if x.1 0 = 1 then 0 else 1

private theorem standardSphereZeroSign_injective :
    Function.Injective standardSphereZeroSign := by
  intro x y hxy
  apply Subtype.ext
  ext i
  fin_cases i
  have hx : x.1 0 = 1 ∨ x.1 0 = -1 :=
    sq_eq_one_iff.mp (standardSphereZero_coordinate_sq x)
  have hy : y.1 0 = 1 ∨ y.1 0 = -1 :=
    sq_eq_one_iff.mp (standardSphereZero_coordinate_sq y)
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · simp [hx, hy]
  · simp [standardSphereZeroSign, hx, hy] at hxy
    norm_num at hxy
  · simp [standardSphereZeroSign, hx, hy] at hxy
    norm_num at hxy
  · simp [hx, hy]

public noncomputable instance standardSphereZero_finite : Finite (StandardSphere 0) :=
  Finite.of_injective standardSphereZeroSign standardSphereZeroSign_injective

public instance standardSphereZero_totallyDisconnected :
    TotallyDisconnectedSpace (StandardSphere 0) := by
  letI : DiscreteTopology (StandardSphere 0) := Finite.instDiscreteTopology
  constructor
  intro s _ hs x hx y hy
  letI : PreconnectedSpace s := Subtype.preconnectedSpace hs
  letI : DiscreteTopology s := inferInstance
  letI : Subsingleton s := PreconnectedSpace.trivial_of_discrete
  exact congrArg Subtype.val (Subsingleton.elim ⟨x, hx⟩ ⟨y, hy⟩)

/-- Positive-degree integral homology of the standard zero-sphere is a singleton. -/
public theorem standardSphereZero_positiveHomology (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (IntegralSingularHomology k (StandardSphere 0)) := by
  apply AddCommGrpCat.subsingleton_of_isZero
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    AddCommGrpCat k (AddCommGrpCat.of ℤ) (TopCat.of (StandardSphere 0)) hk

end SphereSixComplex
