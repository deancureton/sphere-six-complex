module

public import SphereSixComplex.Topology.CylinderSmoothEmbedding

/-!
# Smooth affine geometry for a cylinder seam

The interior of the standard collar interval is split at `1 / 2`.  The two halves are
smoothly identified with the whole interior by the affine rescalings used in a three-piece
open gluing.
-/

@[expose] public section

noncomputable section

open Function Set
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

/-- The central seam parameter `1 / 2`. -/
public def collarMidpoint : CollarParameter :=
  ⟨1 / 2, by norm_num⟩

@[simp]
public theorem collarMidpoint_val : (collarMidpoint : ℝ) = 1 / 2 :=
  rfl

/-- The open interior `(0, 1)` of the closed collar parameter. -/
public def collarInterior : TopologicalSpace.Opens CollarParameter where
  carrier := {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
  is_open' := (isOpen_Ioi.inter isOpen_Iio).preimage continuous_subtype_val

/-- The left open half `(0, 1 / 2)` of the collar parameter. -/
public def collarLeftOpenInterval : TopologicalSpace.Opens CollarParameter where
  carrier := {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2}
  is_open' := (isOpen_Ioi.inter isOpen_Iio).preimage continuous_subtype_val

/-- The right open half `(1 / 2, 1)` of the collar parameter. -/
public def collarRightOpenInterval : TopologicalSpace.Opens CollarParameter where
  carrier := {t | 1 / 2 < (t : ℝ) ∧ (t : ℝ) < 1}
  is_open' := (isOpen_Ioi.inter isOpen_Iio).preimage continuous_subtype_val

@[simp]
public theorem mem_collarInterior (t : CollarParameter) :
    t ∈ collarInterior ↔ 0 < (t : ℝ) ∧ (t : ℝ) < 1 :=
  Iff.rfl

@[simp]
public theorem mem_collarLeftOpenInterval (t : CollarParameter) :
    t ∈ collarLeftOpenInterval ↔ 0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2 :=
  Iff.rfl

@[simp]
public theorem mem_collarRightOpenInterval (t : CollarParameter) :
    t ∈ collarRightOpenInterval ↔ 1 / 2 < (t : ℝ) ∧ (t : ℝ) < 1 :=
  Iff.rfl

@[simp]
public theorem collarMidpoint_mem_interior : collarMidpoint ∈ collarInterior := by
  change 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1
  norm_num

/-- The left open half lies in the open collar interval. -/
public theorem collarLeftOpenInterval_le_interior :
    collarLeftOpenInterval ≤ collarInterior := by
  intro t ht
  change 0 < (t : ℝ) ∧ (t : ℝ) < 1 / 2 at ht
  change 0 < (t : ℝ) ∧ (t : ℝ) < 1
  exact ⟨ht.1, lt_trans ht.2 (by norm_num)⟩

/-- The right open half lies in the open collar interval. -/
public theorem collarRightOpenInterval_le_interior :
    collarRightOpenInterval ≤ collarInterior := by
  intro t ht
  change 1 / 2 < (t : ℝ) ∧ (t : ℝ) < 1 at ht
  change 0 < (t : ℝ) ∧ (t : ℝ) < 1
  exact ⟨lt_trans (by norm_num) ht.1, ht.2⟩

/-- The two open halves of the collar interval are disjoint. -/
public theorem collarLeftOpenInterval_disjoint_right :
    Disjoint collarLeftOpenInterval collarRightOpenInterval := by
  rw [disjoint_iff_inf_le]
  intro t ht
  exact (not_lt_of_ge (le_of_lt ht.1.2)) ht.2.1

/-- The open collar interval `(0, 1)`, as an open submanifold of `CollarParameter`. -/
public abbrev OpenCollarParameter := collarInterior

/-- The left half `(0, 1 / 2)`, as an open submanifold of `CollarParameter`. -/
public abbrev LeftOpenCollarParameter := collarLeftOpenInterval

/-- The right half `(1 / 2, 1)`, as an open submanifold of `CollarParameter`. -/
public abbrev RightOpenCollarParameter := collarRightOpenInterval

/-- Reflection restricts to a smooth involution of the open collar interval. -/
public def openCollarReflection :
    OpenCollarParameter ≃ₘ⟮(𝓡∂ 1), (𝓡∂ 1)⟯ OpenCollarParameter where
  toEquiv :=
    { toFun := fun t ↦
        ⟨collarReflection t.1, by
          change 0 < 1 - (t.1 : ℝ) ∧ 1 - (t.1 : ℝ) < 1
          constructor <;> linarith [t.2.1, t.2.2]⟩
      invFun := fun t ↦
        ⟨collarReflection t.1, by
          change 0 < 1 - (t.1 : ℝ) ∧ 1 - (t.1 : ℝ) < 1
          constructor <;> linarith [t.2.1, t.2.2]⟩
      left_inv := by
        intro t
        apply Subtype.ext
        exact collarReflection_involutive t.1
      right_inv := by
        intro t
        apply Subtype.ext
        exact collarReflection_involutive t.1 }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff collarInterior _).mp
    exact collarReflectionDiffeomorph.contMDiff.comp
      (contMDiff_subtype_val (I := (𝓡∂ 1)) (U := collarInterior))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff collarInterior _).mp
    exact collarReflectionDiffeomorph.contMDiff.comp
      (contMDiff_subtype_val (I := (𝓡∂ 1)) (U := collarInterior))

@[simp]
public theorem openCollarReflection_val (t : OpenCollarParameter) :
    (openCollarReflection t : CollarParameter) = collarReflection t.1 :=
  rfl

/-- Affine rescaling `t ↦ t / 2` from `(0, 1)` onto `(0, 1 / 2)`. -/
public def openCollarToLeftHalf :
    OpenCollarParameter ≃ₘ⟮(𝓡∂ 1), (𝓡∂ 1)⟯ LeftOpenCollarParameter where
  toEquiv :=
    { toFun := fun t ↦
        ⟨⟨(t.1 : ℝ) / 2, by
            constructor
            · linarith [t.1.property.1]
            · linarith [t.1.property.2]⟩, by
          change 0 < (t.1 : ℝ) / 2 ∧ (t.1 : ℝ) / 2 < 1 / 2
          constructor <;> linarith [t.2.1, t.2.2]⟩
      invFun := fun t ↦
        ⟨⟨2 * (t.1 : ℝ), by
            constructor
            · linarith [t.1.property.1]
            · linarith [t.2.2]⟩, by
          change 0 < 2 * (t.1 : ℝ) ∧ 2 * (t.1 : ℝ) < 1
          constructor <;> linarith [t.2.1, t.2.2]⟩
      left_inv := by
        intro t
        apply Subtype.ext
        apply Subtype.ext
        ring
      right_inv := by
        intro t
        apply Subtype.ext
        apply Subtype.ext
        ring }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff collarLeftOpenInterval _).mp
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    constructor
    · fun_prop
    · have h : ContDiff ℝ ∞ (fun x : ℝ ↦ x / 2) := by fun_prop
      exact h.comp_contMDiff
        (contMDiff_subtypeVal_Icc.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff collarInterior _).mp
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    constructor
    · fun_prop
    · have h : ContDiff ℝ ∞ (fun x : ℝ ↦ 2 * x) := by fun_prop
      exact h.comp_contMDiff
        (contMDiff_subtypeVal_Icc.comp contMDiff_subtype_val)

/-- Reversed affine coordinate `t ↦ (1 - t) / 2` from an inward left collar parameter to the
left half of the signed seam interval. -/
public def openCollarToReversedLeftHalf :
    OpenCollarParameter ≃ₘ⟮(𝓡∂ 1), (𝓡∂ 1)⟯ LeftOpenCollarParameter :=
  openCollarReflection.trans openCollarToLeftHalf

@[simp]
public theorem openCollarToReversedLeftHalf_val (t : OpenCollarParameter) :
    ((openCollarToReversedLeftHalf t : CollarParameter) : ℝ) =
      (1 - (t.1 : ℝ)) / 2 :=
  rfl

/-- Affine rescaling `t ↦ (t + 1) / 2` from `(0, 1)` onto `(1 / 2, 1)`. -/
public def openCollarToRightHalf :
    OpenCollarParameter ≃ₘ⟮(𝓡∂ 1), (𝓡∂ 1)⟯ RightOpenCollarParameter where
  toEquiv :=
    { toFun := fun t ↦
        ⟨⟨((t.1 : ℝ) + 1) / 2, by
            constructor
            · linarith [t.1.property.1]
            · linarith [t.2.2]⟩, by
          change 1 / 2 < ((t.1 : ℝ) + 1) / 2 ∧ ((t.1 : ℝ) + 1) / 2 < 1
          constructor <;> linarith [t.2.1, t.2.2]⟩
      invFun := fun t ↦
        ⟨⟨2 * (t.1 : ℝ) - 1, by
            constructor
            · linarith [t.2.1]
            · linarith [t.1.property.2]⟩, by
          change 0 < 2 * (t.1 : ℝ) - 1 ∧ 2 * (t.1 : ℝ) - 1 < 1
          constructor <;> linarith [t.2.1, t.2.2]⟩
      left_inv := by
        intro t
        apply Subtype.ext
        apply Subtype.ext
        ring
      right_inv := by
        intro t
        apply Subtype.ext
        apply Subtype.ext
        ring }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff collarRightOpenInterval _).mp
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    constructor
    · fun_prop
    · have h : ContDiff ℝ ∞ (fun x : ℝ ↦ (x + 1) / 2) := by fun_prop
      exact h.comp_contMDiff
        (contMDiff_subtypeVal_Icc.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff collarInterior _).mp
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    constructor
    · fun_prop
    · have h : ContDiff ℝ ∞ (fun x : ℝ ↦ 2 * x - 1) := by fun_prop
      exact h.comp_contMDiff
        (contMDiff_subtypeVal_Icc.comp contMDiff_subtype_val)

@[simp]
public theorem openCollarToLeftHalf_val (t : OpenCollarParameter) :
    ((openCollarToLeftHalf t : CollarParameter) : ℝ) = (t.1 : ℝ) / 2 :=
  rfl

@[simp]
public theorem openCollarToLeftHalf_symm_val (t : LeftOpenCollarParameter) :
    ((openCollarToLeftHalf.symm t : CollarParameter) : ℝ) = 2 * (t.1 : ℝ) :=
  rfl

@[simp]
public theorem openCollarToRightHalf_val (t : OpenCollarParameter) :
    ((openCollarToRightHalf t : CollarParameter) : ℝ) = ((t.1 : ℝ) + 1) / 2 :=
  rfl

@[simp]
public theorem openCollarToRightHalf_symm_val (t : RightOpenCollarParameter) :
    ((openCollarToRightHalf.symm t : CollarParameter) : ℝ) = 2 * (t.1 : ℝ) - 1 :=
  rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Product with the identity on a manifold of the affine identification with the left half. -/
public def cylinderInteriorToLeftHalf :
    (M × OpenCollarParameter) ≃ₘ⟮I.prod (𝓡∂ 1), I.prod (𝓡∂ 1)⟯
      M × LeftOpenCollarParameter :=
  (Diffeomorph.refl I M ∞).prodCongr openCollarToLeftHalf

/-- Product with the identity on a manifold of the affine identification with the right half. -/
public def cylinderInteriorToRightHalf :
    (M × OpenCollarParameter) ≃ₘ⟮I.prod (𝓡∂ 1), I.prod (𝓡∂ 1)⟯
      M × RightOpenCollarParameter :=
  (Diffeomorph.refl I M ∞).prodCongr openCollarToRightHalf

@[simp]
public theorem cylinderInteriorToLeftHalf_apply (x : M) (t : OpenCollarParameter) :
    cylinderInteriorToLeftHalf (I := I) (x, t) = (x, openCollarToLeftHalf t) :=
  rfl

@[simp]
public theorem cylinderInteriorToRightHalf_apply (x : M) (t : OpenCollarParameter) :
    cylinderInteriorToRightHalf (I := I) (x, t) = (x, openCollarToRightHalf t) :=
  rfl

@[simp]
public theorem cylinderInteriorToLeftHalf_symm_apply (x : M) (t : LeftOpenCollarParameter) :
    (cylinderInteriorToLeftHalf (I := I)).symm (x, t) =
      (x, openCollarToLeftHalf.symm t) :=
  rfl

@[simp]
public theorem cylinderInteriorToRightHalf_symm_apply (x : M) (t : RightOpenCollarParameter) :
    (cylinderInteriorToRightHalf (I := I)).symm (x, t) =
      (x, openCollarToRightHalf.symm t) :=
  rfl

end SphereSixComplex
