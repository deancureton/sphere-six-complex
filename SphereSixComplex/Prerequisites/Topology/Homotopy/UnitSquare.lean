/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval

/-! # Retraction of the unit square onto two adjacent sides

Adapted from the square retraction in `TauCeti.Topology.Homotopy.Extension.MappingCylinder`.
-/

public section
noncomputable section

open Set unitInterval

namespace SphereSixComplex

/-- The height coordinate of the retraction of the square onto the union of the side of height
`0` and the bottom face of time `0`, by projection from the point of height `1` and time `2`.
The first coordinate of the argument is the height, the second is the time. -/
private def squareFst : I × I → ℝ := fun p ↦
  if (p.2 : ℝ) ≤ 2 * (p.1 : ℝ) then (2 * (p.1 : ℝ) - p.2) / (2 - (p.2 : ℝ)) else 0

/-- The time coordinate of the retraction described at `squareFst`.  The
denominator is `1 - p.1` wherever this branch is used, and is truncated below at `1 / 2` only so
that the formula is continuous on the whole square. -/
private def squareSnd : I × I → ℝ := fun p ↦
  if (p.2 : ℝ) ≤ 2 * (p.1 : ℝ) then 0
  else ((p.2 : ℝ) - 2 * (p.1 : ℝ)) / max (1 - (p.1 : ℝ)) (1 / 2)

private lemma squareFst_def (p : I × I) :
    squareFst p =
      if (p.2 : ℝ) ≤ 2 * (p.1 : ℝ) then (2 * (p.1 : ℝ) - p.2) / (2 - (p.2 : ℝ)) else 0 := rfl

private lemma squareSnd_def (p : I × I) :
    squareSnd p =
      if (p.2 : ℝ) ≤ 2 * (p.1 : ℝ) then 0
      else ((p.2 : ℝ) - 2 * (p.1 : ℝ)) / max (1 - (p.1 : ℝ)) (1 / 2) := rfl

private lemma squareFst_mem (p : I × I) : squareFst p ∈ I := by
  have h2 : (p.1 : ℝ) ≤ 1 := p.1.2.2
  have h3 : (0 : ℝ) ≤ (p.2 : ℝ) := p.2.2.1
  have h4 : (p.2 : ℝ) ≤ 1 := p.2.2.2
  have hd : (0 : ℝ) < 2 - (p.2 : ℝ) := by linarith
  rw [squareFst_def]
  split_ifs with h
  · exact ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith)⟩
  · exact ⟨le_rfl, zero_le_one⟩

private lemma squareSnd_mem (p : I × I) : squareSnd p ∈ I := by
  have h1 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
  have h4 : (p.2 : ℝ) ≤ 1 := p.2.2.2
  rw [squareSnd_def]
  split_ifs with h
  · exact ⟨le_rfl, zero_le_one⟩
  · have hlt : 2 * (p.1 : ℝ) < (p.2 : ℝ) := not_le.1 h
    rw [max_eq_left (by linarith : (1 : ℝ) / 2 ≤ 1 - (p.1 : ℝ))]
    exact ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

private lemma continuous_squareFst : Continuous fun p : I × I ↦ squareFst p := by
  have hd : Continuous fun p : I × I ↦ (2 * (p.1 : ℝ) - p.2) / (2 - (p.2 : ℝ)) := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun p ↦ ?_
    have : (p.2 : ℝ) ≤ 1 := p.2.2.2
    linarith
  simp only [squareFst_def]
  exact hd.if_le continuous_const (by fun_prop) (by fun_prop) fun p hp ↦ by
    rw [← hp, sub_self, zero_div]

private lemma continuous_squareSnd : Continuous fun p : I × I ↦ squareSnd p := by
  have hd : Continuous fun p : I × I ↦
      ((p.2 : ℝ) - 2 * (p.1 : ℝ)) / max (1 - (p.1 : ℝ)) (1 / 2) := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun p ↦ ?_
    have : (1 : ℝ) / 2 ≤ max (1 - (p.1 : ℝ)) (1 / 2) := le_max_right _ _
    linarith
  simp only [squareSnd_def]
  exact continuous_const.if_le hd (by fun_prop) (by fun_prop) fun p hp ↦ by
    rw [← hp, sub_self, zero_div]

/-- The retraction of the square `I × I` onto the union of the side of height `0` with the
bottom face of time `0`, by projection from the point of height `1` and time `2`. -/
def unitSquareCornerRetraction : C(I × I, I × I) where
  toFun p := (⟨squareFst p, squareFst_mem p⟩, ⟨squareSnd p, squareSnd_mem p⟩)
  continuous_toFun :=
    (continuous_squareFst.subtype_mk _).prodMk (continuous_squareSnd.subtype_mk _)

private lemma unitSquareCornerRetraction_fst (p : I × I) :
    ((unitSquareCornerRetraction p).1 : ℝ) = squareFst p := rfl

private lemma unitSquareCornerRetraction_snd (p : I × I) :
    ((unitSquareCornerRetraction p).2 : ℝ) = squareSnd p := rfl

/-- The retracted point lies on the side of height `0` or on the bottom face of time `0`. -/
theorem unitSquareCornerRetraction_mem (p : I × I) :
    (unitSquareCornerRetraction p).2 = 0 ∨ (unitSquareCornerRetraction p).1 = 0 := by
  by_cases h : (p.2 : ℝ) ≤ 2 * (p.1 : ℝ)
  · refine Or.inl (Subtype.ext ?_)
    rw [unitSquareCornerRetraction_snd, squareSnd_def, ite_eq_left h, Set.Icc.coe_zero]
  · refine Or.inr (Subtype.ext ?_)
    rw [unitSquareCornerRetraction_fst, squareFst_def, ite_eq_right h, Set.Icc.coe_zero]

/-- The projection point lies on the line of height `1`, so the whole top face keeps its height
and only has its time reset to `0`. -/
theorem unitSquareCornerRetraction_one_left (t : I) : unitSquareCornerRetraction (1, t) = (1, 0) := by
  have h4 : (t : ℝ) ≤ 1 := t.2.2
  have hle : ((((1 : I), t) : I × I).2 : ℝ) ≤ 2 * ((((1 : I), t) : I × I).1 : ℝ) := by
    simp only [Set.Icc.coe_one]
    linarith
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [unitSquareCornerRetraction_fst, squareFst_def, ite_eq_left hle, Set.Icc.coe_one, mul_one]
    exact div_self (by linarith)
  · rw [unitSquareCornerRetraction_snd, squareSnd_def, ite_eq_left hle, Set.Icc.coe_zero]

theorem unitSquareCornerRetraction_zero_right (s : I) : unitSquareCornerRetraction (s, 0) = (s, 0) := by
  have h1 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hle : (((s, (0 : I)) : I × I).2 : ℝ) ≤ 2 * (((s, (0 : I)) : I × I).1 : ℝ) := by
    simp only [Set.Icc.coe_zero]
    linarith
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [unitSquareCornerRetraction_fst, squareFst_def, ite_eq_left hle]
    simp only [Set.Icc.coe_zero, sub_zero]
    ring
  · rw [unitSquareCornerRetraction_snd, squareSnd_def, ite_eq_left hle, Set.Icc.coe_zero]

theorem unitSquareCornerRetraction_zero_left (t : I) : unitSquareCornerRetraction (0, t) = (0, t) := by
  have h3 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp only [unitSquareCornerRetraction_fst, squareFst_def, Set.Icc.coe_zero, mul_zero]
    split_ifs with h
    · rw [le_antisymm h h3]
      norm_num
    · rfl
  · simp only [unitSquareCornerRetraction_snd, squareSnd_def, Set.Icc.coe_zero, mul_zero]
    split_ifs with h
    · exact (le_antisymm h h3).symm
    · rw [sub_zero, sub_zero, max_eq_left (by norm_num : (1 : ℝ) / 2 ≤ 1), div_one]

end SphereSixComplex
