/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCarrierGeometry
import SphereSixComplex.Geometry.StandardInfiniteA2ToricBarycentricTiling

/-!
# Closed unit polydiscs in the standard infinite `A₂` toric carrier

This module proves the properness fragment of the explicit infinite fan construction.  The
noncentral part is controlled by the two-triangle tiling of the real affine plane, while the
central fibre is covered by the six maximal cones in the star of each height-one ray.
-/

@[expose] public section

noncomputable section

open Function Matrix Set Topology
open scoped ContDiff Manifold
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

public def unitPolydisc (a : ChartIndex) : Set Carrier :=
  {p | p ∈ (toricChart a).source ∧ ∀ i, ‖toricChart a p i‖ ≤ 1}

private theorem inclusion_mem_unitPolydisc_self (a : ChartIndex) (z : RawCoordinates)
    (hz : ∀ i, ‖z i‖ ≤ 1) : inclusion a z ∈ unitPolydisc a := by
  let _ := chartedSpace
  constructor
  · rw [toricChart_source]
    exact Set.mem_range_self _
  · intro i
    rw [toricChart_inclusion]
    exact hz i

private theorem inclusion_mem_unitPolydisc_of_change
    (a b : ChartIndex) (z : RawCoordinates)
    (hz : z ∈ (chartChange a b).source)
    (hbound : ∀ i, ‖chartChange a b z i‖ ≤ 1) :
    inclusion a z ∈ unitPolydisc b := by
  let _ := chartedSpace
  have he : inclusion a z = inclusion b (chartChange a b z) :=
    (inclusion_eq_iff a b z _).2 ⟨hz, rfl⟩
  rw [he]
  exact inclusion_mem_unitPolydisc_self b _ hbound

private theorem transitionMatrix_lower_left (v : ToricLattice) :
    transitionMatrix (false, v) (false, v - e₁) =
      !![(0 : ℤ), -1, -1; 1, 2, 1; 0, 0, 1] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_lower_down (v : ToricLattice) :
    transitionMatrix (false, v) (false, v - e₂) =
      !![(0 : ℤ), -1, -1; 0, 1, 0; 1, 1, 2] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_upper_left (v : ToricLattice) :
    transitionMatrix (false, v) (true, v - e₁) =
      !![(1 : ℤ), 1, 0; 0, -1, 0; 0, 1, 1] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_upper_down (v : ToricLattice) :
    transitionMatrix (false, v) (true, v - e₂) =
      !![(0 : ℤ), 0, -1; 1, 0, 1; 0, 1, 1] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_upper_opposite (v : ToricLattice) :
    transitionMatrix (false, v) (true, v - e₁ - e₂) =
      !![(0 : ℤ), 0, -1; 0, -1, 0; 1, 2, 2] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem lower_zero_mem_upper_opposite
    (v : ToricLattice) (z : RawCoordinates) (h0 : z 0 = 0)
    (h1 : z 1 ≠ 0) (h2 : z 2 ≠ 0) (hb1 : 1 ≤ ‖z 1‖) (hb2 : 1 ≤ ‖z 2‖) :
    inclusion (false, v) z ∈ unitPolydisc (true, v - e₁ - e₂) := by
  apply inclusion_mem_unitPolydisc_of_change
  · rw [chartChange_source, transitionMatrix_upper_opposite]
    intro i j hneg
    fin_cases i <;> fin_cases j <;> norm_num at hneg
    all_goals first | simpa using h1 | simpa using h2
  · intro i
    change ‖monomial (transitionMatrix (false, v) (true, v - e₁ - e₂)) z i‖ ≤ 1
    rw [transitionMatrix_upper_opposite]
    fin_cases i
    · simp [monomial, Fin.prod_univ_succ, norm_inv]
      exact inv_le_one_of_one_le₀ hb2
    · simp [monomial, Fin.prod_univ_succ, norm_inv]
      exact inv_le_one_of_one_le₀ hb1
    · simp [monomial, Fin.prod_univ_succ, h0]

private theorem lower_zero_mem_lower_left
    (v : ToricLattice) (z : RawCoordinates) (h0 : z 0 = 0)
    (h1 : z 1 ≠ 0) (h2 : z 2 ≠ 0)
    (hprod : 1 ≤ ‖z 1 * z 2‖) (hb2 : ‖z 2‖ ≤ 1) :
    inclusion (false, v) z ∈ unitPolydisc (false, v - e₁) := by
  apply inclusion_mem_unitPolydisc_of_change
  · rw [chartChange_source, transitionMatrix_lower_left]
    intro i j hneg
    fin_cases i <;> fin_cases j <;> norm_num at hneg
    all_goals first | simpa using h1 | simpa using h2
  · intro i
    change ‖monomial (transitionMatrix (false, v) (false, v - e₁)) z i‖ ≤ 1
    rw [transitionMatrix_lower_left]
    fin_cases i
    · simp [monomial, Fin.prod_univ_succ, norm_inv]
      simpa [norm_mul, mul_comm] using inv_le_one_of_one_le₀ hprod
    · simp [monomial, Fin.prod_univ_succ, h0]
    · simpa [monomial, Fin.prod_univ_succ] using hb2

private theorem lower_zero_mem_lower_down
    (v : ToricLattice) (z : RawCoordinates) (h0 : z 0 = 0)
    (h1 : z 1 ≠ 0) (h2 : z 2 ≠ 0)
    (hprod : 1 ≤ ‖z 1 * z 2‖) (hb1 : ‖z 1‖ ≤ 1) :
    inclusion (false, v) z ∈ unitPolydisc (false, v - e₂) := by
  apply inclusion_mem_unitPolydisc_of_change
  · rw [chartChange_source, transitionMatrix_lower_down]
    intro i j hneg
    fin_cases i <;> fin_cases j <;> norm_num at hneg
    all_goals first | simpa using h1 | simpa using h2
  · intro i
    change ‖monomial (transitionMatrix (false, v) (false, v - e₂)) z i‖ ≤ 1
    rw [transitionMatrix_lower_down]
    fin_cases i
    · simp [monomial, Fin.prod_univ_succ, norm_inv]
      simpa [norm_mul, mul_comm] using inv_le_one_of_one_le₀ hprod
    · simpa [monomial, Fin.prod_univ_succ] using hb1
    · simp [monomial, Fin.prod_univ_succ, h0]

private theorem lower_zero_mem_upper_left
    (v : ToricLattice) (z : RawCoordinates) (h0 : z 0 = 0)
    (h1 : z 1 ≠ 0) (hb1 : 1 ≤ ‖z 1‖) (hprod : ‖z 1 * z 2‖ ≤ 1) :
    inclusion (false, v) z ∈ unitPolydisc (true, v - e₁) := by
  apply inclusion_mem_unitPolydisc_of_change
  · rw [chartChange_source, transitionMatrix_upper_left]
    intro i j hneg
    fin_cases i <;> fin_cases j <;> norm_num at hneg
    simpa using h1
  · intro i
    change ‖monomial (transitionMatrix (false, v) (true, v - e₁)) z i‖ ≤ 1
    rw [transitionMatrix_upper_left]
    fin_cases i
    · simp [monomial, Fin.prod_univ_succ, h0]
    · simp [monomial, Fin.prod_univ_succ, norm_inv]
      exact inv_le_one_of_one_le₀ hb1
    · simpa [monomial, Fin.prod_univ_succ] using hprod

private theorem lower_zero_mem_upper_down
    (v : ToricLattice) (z : RawCoordinates) (h0 : z 0 = 0)
    (h2 : z 2 ≠ 0) (hb2 : 1 ≤ ‖z 2‖) (hprod : ‖z 1 * z 2‖ ≤ 1) :
    inclusion (false, v) z ∈ unitPolydisc (true, v - e₂) := by
  apply inclusion_mem_unitPolydisc_of_change
  · rw [chartChange_source, transitionMatrix_upper_down]
    intro i j hneg
    fin_cases i <;> fin_cases j <;> norm_num at hneg
    simpa using h2
  · intro i
    change ‖monomial (transitionMatrix (false, v) (true, v - e₂)) z i‖ ≤ 1
    rw [transitionMatrix_upper_down]
    fin_cases i
    · simp [monomial, Fin.prod_univ_succ, norm_inv]
      exact inv_le_one_of_one_le₀ hb2
    · simp [monomial, Fin.prod_univ_succ, h0]
    · simpa [monomial, Fin.prod_univ_succ] using hprod

/-- The six maximal cones in the star of the ray `v` cover its coordinate hyperplane by
closed unit polydiscs. -/
private theorem lower_zero_unit_cover
    (v : ToricLattice) (z : RawCoordinates) (h0 : z 0 = 0) :
    ∃ a, inclusion (false, v) z ∈ unitPolydisc a := by
  by_cases h1le : ‖z 1‖ ≤ 1
  · by_cases h2le : ‖z 2‖ ≤ 1
    · refine ⟨(false, v), inclusion_mem_unitPolydisc_self _ _ ?_⟩
      intro i
      fin_cases i
      · simp [h0]
      · exact h1le
      · exact h2le
    · have h2gt : 1 < ‖z 2‖ := lt_of_not_ge h2le
      have h2 : z 2 ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans h2gt))
      by_cases h1 : z 1 = 0
      · refine ⟨(true, v - e₂), lower_zero_mem_upper_down v z h0 h2 h2gt.le ?_⟩
        simp [h1]
      · by_cases hprod : 1 ≤ ‖z 1 * z 2‖
        · exact ⟨(false, v - e₂),
            lower_zero_mem_lower_down v z h0 h1 h2 hprod h1le⟩
        · exact ⟨(true, v - e₂),
            lower_zero_mem_upper_down v z h0 h2 h2gt.le (le_of_not_ge hprod)⟩
  · have h1gt : 1 < ‖z 1‖ := lt_of_not_ge h1le
    have h1 : z 1 ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans h1gt))
    by_cases h2le : ‖z 2‖ ≤ 1
    · by_cases h2 : z 2 = 0
      · refine ⟨(true, v - e₁), lower_zero_mem_upper_left v z h0 h1 h1gt.le ?_⟩
        simp [h2]
      · by_cases hprod : 1 ≤ ‖z 1 * z 2‖
        · exact ⟨(false, v - e₁),
            lower_zero_mem_lower_left v z h0 h1 h2 hprod h2le⟩
        · exact ⟨(true, v - e₁),
            lower_zero_mem_upper_left v z h0 h1 h1gt.le (le_of_not_ge hprod)⟩
    · have h2gt : 1 < ‖z 2‖ := lt_of_not_ge h2le
      have h2 : z 2 ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans h2gt))
      exact ⟨(true, v - e₁ - e₂),
        lower_zero_mem_upper_opposite v z h0 h1 h2 h1gt.le h2gt.le⟩

private theorem transitionMatrix_lower_left_to_center (v : ToricLattice) :
    transitionMatrix (false, v - e₁) (false, v) =
      !![(2 : ℤ), 1, 1; -1, 0, -1; 0, 0, 1] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_lower_down_to_center (v : ToricLattice) :
    transitionMatrix (false, v - e₂) (false, v) =
      !![(2 : ℤ), 1, 1; 0, 1, 0; -1, -1, 0] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_upper_left_to_center (v : ToricLattice) :
    transitionMatrix (true, v - e₁) (false, v) =
      !![(1 : ℤ), 1, 0; 0, -1, 0; 0, 1, 1] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_upper_down_to_center (v : ToricLattice) :
    transitionMatrix (true, v - e₂) (false, v) =
      !![(1 : ℤ), 1, 0; 1, 0, 1; -1, 0, 0] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_upper_opposite_to_center (v : ToricLattice) :
    transitionMatrix (true, v - e₁ - e₂) (false, v) =
      !![(2 : ℤ), 2, 1; 0, -1, 0; -1, 0, 0] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_lower_to_right (v : ToricLattice) :
    transitionMatrix (false, v) (false, v + e₁) =
      !![(2 : ℤ), 1, 1; -1, 0, -1; 0, 0, 1] := by
  convert transitionMatrix_lower_left_to_center (v + e₁) using 1
  all_goals abel

private theorem transitionMatrix_lower_to_up (v : ToricLattice) :
    transitionMatrix (false, v) (false, v + e₂) =
      !![(2 : ℤ), 1, 1; 0, 1, 0; -1, -1, 0] := by
  convert transitionMatrix_lower_down_to_center (v + e₂) using 1
  all_goals abel

private theorem transitionMatrix_upper_to_lower_right (v : ToricLattice) :
    transitionMatrix (true, v) (false, v + e₁) =
      !![(1 : ℤ), 1, 0; 0, -1, 0; 0, 1, 1] := by
  convert transitionMatrix_upper_left_to_center (v + e₁) using 1
  all_goals abel

private theorem transitionMatrix_upper_to_lower_up (v : ToricLattice) :
    transitionMatrix (true, v) (false, v + e₂) =
      !![(1 : ℤ), 1, 0; 1, 0, 1; -1, 0, 0] := by
  convert transitionMatrix_upper_down_to_center (v + e₂) using 1
  all_goals abel

private theorem transitionMatrix_upper_to_lower_diagonal (v : ToricLattice) :
    transitionMatrix (true, v) (false, v + e₁ + e₂) =
      !![(2 : ℤ), 2, 1; 0, -1, 0; -1, 0, 0] := by
  convert transitionMatrix_upper_opposite_to_center (v + e₁ + e₂) using 1
  all_goals abel

private theorem transitionMatrix_lower_to_upper_same (v : ToricLattice) :
    transitionMatrix (false, v) (true, v) =
      !![(1 : ℤ), 1, 0; 1, 0, 1; -1, 0, 0] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem transitionMatrix_upper_to_lower_same (v : ToricLattice) :
    transitionMatrix (true, v) (false, v) =
      !![(0 : ℤ), 0, -1; 1, 0, 1; 0, 1, 1] := by
  have hv0 : Matrix.vecHead v = v 0 := rfl
  have hv1 : Matrix.vecHead (Matrix.vecTail v) = v 1 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_succ, hv0, hv1] <;>
    ring

private theorem unit_cover_of_change_to_lower
    (a : ChartIndex) (v : ToricLattice) (z : RawCoordinates)
    (hdom : z ∈ (chartChange a (false, v)).source)
    (hzero : chartChange a (false, v) z 0 = 0) :
    ∃ b, inclusion a z ∈ unitPolydisc b := by
  have he : inclusion a z = inclusion (false, v) (chartChange a (false, v) z) :=
    (inclusion_eq_iff a (false, v) z _).2 ⟨hdom, rfl⟩
  obtain ⟨b, hb⟩ := lower_zero_unit_cover v (chartChange a (false, v) z) hzero
  exact ⟨b, he.symm ▸ hb⟩

private theorem single_zero_unit_cover
    (upper : Bool) (v : ToricLattice) (k : Fin 3) (z : RawCoordinates)
    (hk : z k = 0) (hnonzero : ∀ j, j ≠ k → z j ≠ 0) :
    ∃ a, inclusion (upper, v) z ∈ unitPolydisc a := by
  cases upper
  · fin_cases k
    · exact lower_zero_unit_cover v z hk
    · have hk' : z 1 = 0 := by simpa using hk
      have h0 : z 0 ≠ 0 := hnonzero 0 (by decide)
      have h2 : z 2 ≠ 0 := hnonzero 2 (by decide)
      apply unit_cover_of_change_to_lower (false, v) (v + e₁) z
      · rw [chartChange_source, transitionMatrix_lower_to_right]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        all_goals first | simpa using h0 | simpa using h2
      · change monomial (transitionMatrix (false, v) (false, v + e₁)) z 0 = 0
        rw [transitionMatrix_lower_to_right]
        simp [monomial, Fin.prod_univ_succ, hk']
    · have hk' : z 2 = 0 := by simpa using hk
      have h0 : z 0 ≠ 0 := hnonzero 0 (by decide)
      have h1 : z 1 ≠ 0 := hnonzero 1 (by decide)
      apply unit_cover_of_change_to_lower (false, v) (v + e₂) z
      · rw [chartChange_source, transitionMatrix_lower_to_up]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        all_goals first | simpa using h0 | simpa using h1
      · change monomial (transitionMatrix (false, v) (false, v + e₂)) z 0 = 0
        rw [transitionMatrix_lower_to_up]
        simp [monomial, Fin.prod_univ_succ, hk']
  · fin_cases k
    · have hk' : z 0 = 0 := by simpa using hk
      have h1 : z 1 ≠ 0 := hnonzero 1 (by decide)
      apply unit_cover_of_change_to_lower (true, v) (v + e₁) z
      · rw [chartChange_source, transitionMatrix_upper_to_lower_right]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        simpa using h1
      · change monomial (transitionMatrix (true, v) (false, v + e₁)) z 0 = 0
        rw [transitionMatrix_upper_to_lower_right]
        simp [monomial, Fin.prod_univ_succ, hk']
    · have hk' : z 1 = 0 := by simpa using hk
      have h0 : z 0 ≠ 0 := hnonzero 0 (by decide)
      apply unit_cover_of_change_to_lower (true, v) (v + e₂) z
      · rw [chartChange_source, transitionMatrix_upper_to_lower_up]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        simpa using h0
      · change monomial (transitionMatrix (true, v) (false, v + e₂)) z 0 = 0
        rw [transitionMatrix_upper_to_lower_up]
        simp [monomial, Fin.prod_univ_succ, hk']
    · have hk' : z 2 = 0 := by simpa using hk
      have h0 : z 0 ≠ 0 := hnonzero 0 (by decide)
      have h1 : z 1 ≠ 0 := hnonzero 1 (by decide)
      apply unit_cover_of_change_to_lower (true, v) (v + e₁ + e₂) z
      · rw [chartChange_source, transitionMatrix_upper_to_lower_diagonal]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        all_goals first | simpa using h0 | simpa using h1
      · change monomial
          (transitionMatrix (true, v) (false, v + e₁ + e₂)) z 0 = 0
        rw [transitionMatrix_upper_to_lower_diagonal]
        simp [monomial, Fin.prod_univ_succ, hk']

private theorem double_zero_01_unit_cover
    (upper : Bool) (v : ToricLattice) (z : RawCoordinates)
    (h0 : z 0 = 0) (h1 : z 1 = 0) :
    ∃ a, inclusion (upper, v) z ∈ unitPolydisc a := by
  by_cases h2le : ‖z 2‖ ≤ 1
  · refine ⟨(upper, v), inclusion_mem_unitPolydisc_self _ _ ?_⟩
    intro i
    fin_cases i
    · simp [h0]
    · simp [h1]
    · exact h2le
  · have h2gt : 1 < ‖z 2‖ := lt_of_not_ge h2le
    have h2 : z 2 ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans h2gt))
    cases upper
    · refine ⟨(true, v - e₂), inclusion_mem_unitPolydisc_of_change _ _ _ ?_ ?_⟩
      · rw [chartChange_source, transitionMatrix_upper_down]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        simpa using h2
      · intro i
        change ‖monomial (transitionMatrix (false, v) (true, v - e₂)) z i‖ ≤ 1
        rw [transitionMatrix_upper_down]
        fin_cases i
        · simp [monomial, Fin.prod_univ_succ, norm_inv]
          exact inv_le_one_of_one_le₀ h2gt.le
        · simp [monomial, Fin.prod_univ_succ, h0]
        · simp [monomial, Fin.prod_univ_succ, h1]
    · refine ⟨(false, v), inclusion_mem_unitPolydisc_of_change _ _ _ ?_ ?_⟩
      · rw [chartChange_source, transitionMatrix_upper_to_lower_same]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        simpa using h2
      · intro i
        change ‖monomial (transitionMatrix (true, v) (false, v)) z i‖ ≤ 1
        rw [transitionMatrix_upper_to_lower_same]
        fin_cases i
        · simp [monomial, Fin.prod_univ_succ, norm_inv]
          exact inv_le_one_of_one_le₀ h2gt.le
        · simp [monomial, Fin.prod_univ_succ, h0]
        · simp [monomial, Fin.prod_univ_succ, h1]

private theorem double_zero_02_unit_cover
    (upper : Bool) (v : ToricLattice) (z : RawCoordinates)
    (h0 : z 0 = 0) (h2 : z 2 = 0) :
    ∃ a, inclusion (upper, v) z ∈ unitPolydisc a := by
  by_cases h1le : ‖z 1‖ ≤ 1
  · refine ⟨(upper, v), inclusion_mem_unitPolydisc_self _ _ ?_⟩
    intro i
    fin_cases i
    · simp [h0]
    · exact h1le
    · simp [h2]
  · have h1gt : 1 < ‖z 1‖ := lt_of_not_ge h1le
    have h1 : z 1 ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans h1gt))
    cases upper
    · refine ⟨(true, v - e₁), inclusion_mem_unitPolydisc_of_change _ _ _ ?_ ?_⟩
      · rw [chartChange_source, transitionMatrix_upper_left]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        simpa using h1
      · intro i
        change ‖monomial (transitionMatrix (false, v) (true, v - e₁)) z i‖ ≤ 1
        rw [transitionMatrix_upper_left]
        fin_cases i
        · simp [monomial, Fin.prod_univ_succ, h0]
        · simp [monomial, Fin.prod_univ_succ, norm_inv]
          exact inv_le_one_of_one_le₀ h1gt.le
        · simp [monomial, Fin.prod_univ_succ, h2]
    · refine ⟨(false, v + e₁), inclusion_mem_unitPolydisc_of_change _ _ _ ?_ ?_⟩
      · rw [chartChange_source, transitionMatrix_upper_to_lower_right]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        simpa using h1
      · intro i
        change ‖monomial (transitionMatrix (true, v) (false, v + e₁)) z i‖ ≤ 1
        rw [transitionMatrix_upper_to_lower_right]
        fin_cases i
        · simp [monomial, Fin.prod_univ_succ, h0]
        · simp [monomial, Fin.prod_univ_succ, norm_inv]
          exact inv_le_one_of_one_le₀ h1gt.le
        · simp [monomial, Fin.prod_univ_succ, h2]

private theorem double_zero_12_unit_cover
    (upper : Bool) (v : ToricLattice) (z : RawCoordinates)
    (h1 : z 1 = 0) (h2 : z 2 = 0) :
    ∃ a, inclusion (upper, v) z ∈ unitPolydisc a := by
  by_cases h0le : ‖z 0‖ ≤ 1
  · refine ⟨(upper, v), inclusion_mem_unitPolydisc_self _ _ ?_⟩
    intro i
    fin_cases i
    · exact h0le
    · simp [h1]
    · simp [h2]
  · have h0gt : 1 < ‖z 0‖ := lt_of_not_ge h0le
    have h0 : z 0 ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans h0gt))
    cases upper
    · refine ⟨(true, v), inclusion_mem_unitPolydisc_of_change _ _ _ ?_ ?_⟩
      · rw [chartChange_source, transitionMatrix_lower_to_upper_same]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        simpa using h0
      · intro i
        change ‖monomial (transitionMatrix (false, v) (true, v)) z i‖ ≤ 1
        rw [transitionMatrix_lower_to_upper_same]
        fin_cases i
        · simp [monomial, Fin.prod_univ_succ, h1]
        · simp [monomial, Fin.prod_univ_succ, h2]
        · simp [monomial, Fin.prod_univ_succ, norm_inv]
          exact inv_le_one_of_one_le₀ h0gt.le
    · refine ⟨(false, v + e₂), inclusion_mem_unitPolydisc_of_change _ _ _ ?_ ?_⟩
      · rw [chartChange_source, transitionMatrix_upper_to_lower_up]
        intro i j hneg
        fin_cases i <;> fin_cases j <;> norm_num at hneg
        simpa using h0
      · intro i
        change ‖monomial (transitionMatrix (true, v) (false, v + e₂)) z i‖ ≤ 1
        rw [transitionMatrix_upper_to_lower_up]
        fin_cases i
        · simp [monomial, Fin.prod_univ_succ, h1]
        · simp [monomial, Fin.prod_univ_succ, h2]
        · simp [monomial, Fin.prod_univ_succ, norm_inv]
          exact inv_le_one_of_one_le₀ h0gt.le

/-- Every point of the central fibre lies in a closed unit polydisc of one of the finitely many
cones adjacent to a chart containing it. -/
public theorem carrierCentralFiber_unitPolydisc_cover
    (p : Carrier) (hp : carrierHeight p = 0) :
    ∃ a, p ∈ unitPolydisc a := by
  obtain ⟨⟨upper, v⟩, z, rfl⟩ := inclusion_jointly_surjective p
  rw [carrierHeight_inclusion] at hp
  change z 0 * z 1 * z 2 = 0 at hp
  by_cases h0 : z 0 = 0
  · by_cases h1 : z 1 = 0
    · exact double_zero_01_unit_cover upper v z h0 h1
    · by_cases h2 : z 2 = 0
      · exact double_zero_02_unit_cover upper v z h0 h2
      · exact single_zero_unit_cover upper v 0 z h0 (by
          intro j hj
          fin_cases j <;> simp_all)
  · have h12 : z 1 = 0 ∨ z 2 = 0 := by
      rcases mul_eq_zero.mp hp with h01 | h2
      · exact Or.inl ((mul_eq_zero.mp h01).resolve_left h0)
      · exact Or.inr h2
    rcases h12 with h1 | h2
    · by_cases h2' : z 2 = 0
      · exact double_zero_12_unit_cover upper v z h1 h2'
      · exact single_zero_unit_cover upper v 1 z h1 (by
          intro j hj
          fin_cases j <;> simp_all)
    · by_cases h1' : z 1 = 0
      · exact double_zero_12_unit_cover upper v z h1' h2
      · exact single_zero_unit_cover upper v 2 z h2 (by
          intro j hj
          fin_cases j <;> simp_all)

private theorem log_norm_toricChart_torus
    (upper : Bool) (v : ToricLattice) (x : DenseTorus)
    (hlog : Real.log ‖((x 2 : ℂˣ) : ℂ)‖ ≠ 0) (i : Fin 3) :
    letI := chartedSpace
    Real.log ‖toricChart (upper, v) (carrierTorusEmbedding x) i‖ =
      Real.log ‖((x 2 : ℂˣ) : ℂ)‖ *
        a2Barycentric upper v
          (fun j ↦ Real.log ‖((x j.castSucc : ℂˣ) : ℂ)‖ /
            Real.log ‖((x 2 : ℂˣ) : ℂ)‖) i := by
  let _ := chartedSpace
  rw [toricChart_torus_character, log_norm_evaluateCharacter]
  cases upper <;> fin_cases i <;>
    simp [a2DualCharacter, a2Barycentric, Fin.sum_univ_succ] <;>
    field_simp [hlog] <;> ring

/-- The real `A₂` triangulation chooses a unit polydisc for every noncentral point with
height norm strictly below one. -/
public theorem carrierNoncentral_unitPolydisc_cover
    (p : Carrier) (hp : carrierHeight p ≠ 0) (ht : ‖carrierHeight p‖ < 1) :
    ∃ a, p ∈ unitPolydisc a := by
  let _ := chartedSpace
  have hmem : p ∈ {q : Carrier | carrierHeight q ≠ 0} := hp
  rw [← carrierTorusEmbedding_range] at hmem
  obtain ⟨x, rfl⟩ := hmem
  rw [carrierHeight_torus] at ht
  have hnormPos : 0 < ‖((x 2 : ℂˣ) : ℂ)‖ := Units.norm_pos _
  have hlog : Real.log ‖((x 2 : ℂˣ) : ℂ)‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hnormPos (ne_of_lt ht)
  obtain ⟨upper, v, hv⟩ := exists_a2Barycentric_nonneg
    (fun j ↦ Real.log ‖((x j.castSucc : ℂˣ) : ℂ)‖ /
      Real.log ‖((x 2 : ℂˣ) : ℂ)‖)
  refine ⟨(upper, v), ⟨carrierTorusEmbedding_mem_toricChart (upper, v) x, ?_⟩⟩
  intro i
  apply (Real.log_nonpos_iff (norm_nonneg _)).mp
  rw [log_norm_toricChart_torus upper v x hlog i]
  exact mul_nonpos_of_nonpos_of_nonneg
    (le_of_lt (Real.log_neg hnormPos ht)) (hv i)

public theorem carrierSublevel_unitPolydisc_cover
    (p : Carrier) (ht : ‖carrierHeight p‖ < 1) :
    ∃ a, p ∈ unitPolydisc a := by
  by_cases hp : carrierHeight p = 0
  · exact carrierCentralFiber_unitPolydisc_cover p hp
  · exact carrierNoncentral_unitPolydisc_cover p hp ht

public theorem unitPolydisc_union_below_eq (c : ℝ) (hc : c < 1) :
    letI := chartedSpace
    (⋃ a : ChartIndex, unitPolydisc a ∩ {p | ‖carrierHeight p‖ ≤ c}) =
      {p | ‖carrierHeight p‖ ≤ c} := by
  let _ := chartedSpace
  ext p
  constructor
  · rintro hp
    obtain ⟨a, _, hpBound⟩ := Set.mem_iUnion.mp hp
    exact hpBound
  · intro hp
    obtain ⟨a, ha⟩ := carrierSublevel_unitPolydisc_cover p (hp.trans_lt hc)
    exact Set.mem_iUnion.mpr ⟨a, ha, hp⟩

/-- Below height one, the locally finite union of closed unit toric polydiscs is the closed
height sublevel itself.  This has exactly the type required by `RemainingGeometry`. -/
public theorem closedUnitPolydisc_union_below_closed :
    letI := chartedSpace
    ∀ c : ℝ, c < 1 → IsClosed (⋃ a : ChartIndex,
      {p | p ∈ (toricChart a).source ∧ ∀ i, ‖toricChart a p i‖ ≤ 1} ∩
        {p | ‖carrierHeight p‖ ≤ c}) := by
  let _ := chartedSpace
  intro c hc
  change IsClosed (⋃ a : ChartIndex,
    unitPolydisc a ∩ {p | ‖carrierHeight p‖ ≤ c})
  rw [unitPolydisc_union_below_eq c hc]
  exact isClosed_le carrierHeight_contMDiff.continuous.norm continuous_const
end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
