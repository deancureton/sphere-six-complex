module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Tactic

@[expose] public section
noncomputable section

open scoped NNReal

namespace SphereSixComplex

public abbrev ClosedOrthantThree := {x : Fin 3 → ℝ // ∀ i, 0 ≤ x i}

public def orthantBaseShift (y : Fin 2 → ℝ) : ℝ :=
  max 0 (max (-y 0) (-y 1))

private theorem orthantBaseShift_sub (x : Fin 3 → ℝ) :
    orthantBaseShift ![x 0 - x 2, x 1 - x 2] = x 2 - min (x 0) (min (x 1) (x 2)) := by
  simp [orthantBaseShift, ← max_sub_sub_left, neg_sub, max_comm, max_left_comm]

private theorem min_add_orthantBaseShift (y : Fin 2 → ℝ) :
    min (y 0) (min (y 1) 0) + orthantBaseShift y = 0 := by
  have h : min (y 0) (min (y 1) 0) = -orthantBaseShift y := by
    simp [orthantBaseShift, ← min_neg_neg, min_comm, min_left_comm]
  rw [h]
  ring

public def orthantThreeHalfSpaceHomeomorph : ClosedOrthantThree ≃ₜ ((Fin 2 → ℝ) × ℝ≥0) where
  toFun x := (![x.1 0 - x.1 2, x.1 1 - x.1 2],
    ⟨min (x.1 0) (min (x.1 1) (x.1 2)), le_min (x.2 0) (le_min (x.2 1) (x.2 2))⟩)
  invFun y := ⟨![y.1 0 + orthantBaseShift y.1 + y.2,
    y.1 1 + orthantBaseShift y.1 + y.2, orthantBaseShift y.1 + y.2], by
    have h0 : -y.1 0 ≤ orthantBaseShift y.1 :=
      (le_max_left _ _).trans (le_max_right _ _)
    have h1 : -y.1 1 ≤ orthantBaseShift y.1 :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hm : 0 ≤ orthantBaseShift y.1 := le_max_left _ _
    intro i
    fin_cases i
    · change 0 ≤ y.1 0 + orthantBaseShift y.1 + (y.2 : ℝ)
      linarith [y.2.coe_nonneg]
    · change 0 ≤ y.1 1 + orthantBaseShift y.1 + (y.2 : ℝ)
      linarith [y.2.coe_nonneg]
    · change 0 ≤ orthantBaseShift y.1 + (y.2 : ℝ)
      positivity⟩
  left_inv x := by
    apply Subtype.ext
    change ![x.1 0 - x.1 2 + orthantBaseShift ![x.1 0 - x.1 2, x.1 1 - x.1 2] + min (x.1 0) (min (x.1 1) (x.1 2)), x.1 1 - x.1 2 + orthantBaseShift ![x.1 0 - x.1 2, x.1 1 - x.1 2] + min (x.1 0) (min (x.1 1) (x.1 2)), orthantBaseShift ![x.1 0 - x.1 2, x.1 1 - x.1 2] + min (x.1 0) (min (x.1 1) (x.1 2))] = x.1
    rw [orthantBaseShift_sub]
    funext i
    fin_cases i <;> simp
  right_inv y := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · apply NNReal.eq
      change min (y.1 0 + orthantBaseShift y.1 + y.2)
        (min (y.1 1 + orthantBaseShift y.1 + y.2)
          (orthantBaseShift y.1 + y.2)) = y.2
      have h := min_add_orthantBaseShift y.1
      have he : min (y.1 0 + orthantBaseShift y.1 + y.2)
          (min (y.1 1 + orthantBaseShift y.1 + y.2)
            (orthantBaseShift y.1 + y.2)) =
          min (y.1 0) (min (y.1 1) 0) + orthantBaseShift y.1 + y.2 := by
        simp only [add_assoc, ← min_add_add_right, zero_add]
      rw [he, h, zero_add]
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      fin_cases i
      · exact ((continuous_apply 0).comp continuous_subtype_val).sub
          ((continuous_apply 2).comp continuous_subtype_val)
      · exact ((continuous_apply 1).comp continuous_subtype_val).sub
          ((continuous_apply 2).comp continuous_subtype_val)
    · apply Continuous.subtype_mk
      exact ((continuous_apply 0).comp continuous_subtype_val).min
        (((continuous_apply 1).comp continuous_subtype_val).min
          ((continuous_apply 2).comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold orthantBaseShift
    fun_prop

public theorem orthantThreeHalfSpaceHomeomorph_boundary (x : ClosedOrthantThree) :
    (orthantThreeHalfSpaceHomeomorph x).2 = 0 ↔ ∃ i, x.1 i = 0 := by
  change (⟨min (x.1 0) (min (x.1 1) (x.1 2)), _⟩ : ℝ≥0) = 0 ↔ _
  have hc : (⟨min (x.1 0) (min (x.1 1) (x.1 2)), le_min (x.2 0) (le_min (x.2 1) (x.2 2))⟩ : ℝ≥0) = 0 ↔
      min (x.1 0) (min (x.1 1) (x.1 2)) = 0 := by
    constructor
    · intro h
      exact congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) h
    · intro h
      exact Subtype.ext h
  rw [hc]
  constructor
  · intro h
    rcases min_cases (x.1 0) (min (x.1 1) (x.1 2)) with h0 | h12
    · exact ⟨0, h0.1.symm.trans h⟩
    · rcases min_cases (x.1 1) (x.1 2) with h1 | h2
      · exact ⟨1, h1.1.symm.trans (h12.1.symm.trans h)⟩
      · exact ⟨2, h2.1.symm.trans (h12.1.symm.trans h)⟩
  · rintro ⟨i, hi⟩
    apply le_antisymm _ (le_min (x.2 0) (le_min (x.2 1) (x.2 2)))
    fin_cases i
    · exact (min_le_left _ _).trans hi.le
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans hi.le
    · exact ((min_le_right _ _).trans (min_le_right _ _)).trans hi.le

end SphereSixComplex
