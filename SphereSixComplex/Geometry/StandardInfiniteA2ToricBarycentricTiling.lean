/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCarrierGeometry

/-!
# Barycentric coordinates for the `A₂` toric fan
-/

@[expose] public section

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-- Barycentric coordinates of the two standard `A₂` triangles based at an integral vertex. -/
public def a2Barycentric
    (upper : Bool) (v : ToricLattice) (y : Fin 2 → ℝ) : Fin 3 → ℝ :=
  if upper then
    ![1 - (y 1 - (v 1 : ℝ)),
      1 - (y 0 - (v 0 : ℝ)),
      (y 0 - (v 0 : ℝ)) + (y 1 - (v 1 : ℝ)) - 1]
  else
    ![1 - (y 0 - (v 0 : ℝ)) - (y 1 - (v 1 : ℝ)),
      y 0 - (v 0 : ℝ),
      y 1 - (v 1 : ℝ)]

public theorem a2Barycentric_sum (upper : Bool) (v : ToricLattice) (y : Fin 2 → ℝ) :
    ∑ i, a2Barycentric upper v y i = 1 := by
  cases upper <;> simp [a2Barycentric, Fin.sum_univ_succ]

/-- The two standard integral `A₂` triangles tile the real affine plane. -/
public theorem exists_a2Barycentric_nonneg (y : Fin 2 → ℝ) :
    ∃ upper v, ∀ i, 0 ≤ a2Barycentric upper v y i := by
  let v : ToricLattice := ![⌊y 0⌋, ⌊y 1⌋]
  have h0 : (v 0 : ℝ) ≤ y 0 := by
    simpa [v] using Int.floor_le (y 0)
  have h0' : y 0 < (v 0 : ℝ) + 1 := by
    change y 0 < (⌊y 0⌋ : ℝ) + 1
    exact Int.lt_floor_add_one (y 0)
  have h1 : (v 1 : ℝ) ≤ y 1 := by
    simpa [v] using Int.floor_le (y 1)
  have h1' : y 1 < (v 1 : ℝ) + 1 := by
    change y 1 < (⌊y 1⌋ : ℝ) + 1
    exact Int.lt_floor_add_one (y 1)
  by_cases hsum : (y 0 - (v 0 : ℝ)) + (y 1 - (v 1 : ℝ)) ≤ 1
  · refine ⟨false, v, fun i ↦ ?_⟩
    fin_cases i <;> norm_num [a2Barycentric] <;> linarith
  · refine ⟨true, v, fun i ↦ ?_⟩
    fin_cases i <;> norm_num [a2Barycentric] <;> linarith

/-- The logarithmic norm of a torus character is the corresponding integral linear form. -/
public theorem log_norm_evaluateCharacter (m : FanLattice) (x : DenseTorus) :
    Real.log ‖((evaluateCharacter m x : ℂˣ) : ℂ)‖ =
      ∑ j, (m j : ℝ) * Real.log ‖((x j : ℂˣ) : ℂ)‖ := by
  rw [show evaluateCharacter m x = x 0 ^ m 0 * x 1 ^ m 1 * x 2 ^ m 2 by
    simp [evaluateCharacter, Fin.prod_univ_succ, mul_assoc]]
  simp only [Units.val_mul, norm_mul]
  rw [Real.log_mul
      (mul_ne_zero (ne_of_gt (Units.norm_pos _)) (ne_of_gt (Units.norm_pos _)))
      (ne_of_gt (Units.norm_pos _)),
    Real.log_mul (ne_of_gt (Units.norm_pos _)) (ne_of_gt (Units.norm_pos _))]
  simp only [show ((↑(x 0 ^ m 0) : ℂ)) = ((x 0 : ℂ)) ^ m 0 by
      exact map_zpow (Units.coeHom ℂ) _ _,
    show ((↑(x 1 ^ m 1) : ℂ)) = ((x 1 : ℂ)) ^ m 1 by
      exact map_zpow (Units.coeHom ℂ) _ _,
    show ((↑(x 2 ^ m 2) : ℂ)) = ((x 2 : ℂ)) ^ m 2 by
      exact map_zpow (Units.coeHom ℂ) _ _,
    norm_zpow, Real.log_zpow, Fin.sum_univ_succ]
  norm_num
  ring

end SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions
