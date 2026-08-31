module

public import SphereSixComplex.Topology.SpecialOrthogonalSevenLocalSections

/-!
# Product trivializations of the `SO(7) → S⁶` patches

The explicit local sections constructed in the preceding module identify each restricted fiber
with the standard fiber and hence with `SO(6)`.  This file assembles those identifications into
homeomorphisms from the north and south restricted total spaces to products with `SO(6)`.
-/

@[expose] public section

noncomputable section

open ContinuousMap Matrix Set Topology
open scoped Classical MatrixGroups RealInnerProductSpace Topology

namespace SphereSixComplex.SpecialOrthogonalSevenStiefel

public theorem col_mul (A B : Matrix (Fin 7) (Fin 7) ℝ) (j : Fin 7) :
    Matrix.col (A * B) j = A *ᵥ Matrix.col B j :=
  rfl

public theorem col_eq_of_firstColumn_eq {A B : SO7}
    (h : firstColumn A = firstColumn B) :
    Matrix.col (A : Matrix (Fin 7) (Fin 7) ℝ) 0 =
      Matrix.col (B : Matrix (Fin 7) (Fin 7) ℝ) 0 := by
  have hval := congr_arg Subtype.val h
  change WithLp.toLp 2 (Matrix.col (A : Matrix (Fin 7) (Fin 7) ℝ) 0) =
    WithLp.toLp 2 (Matrix.col (B : Matrix (Fin 7) (Fin 7) ℝ) 0) at hval
  exact WithLp.toLp_injective 2 hval

public theorem firstColumn_inv_mul_eq_one (A B : SO7)
    (h : firstColumn A = firstColumn B) :
    firstColumn (A⁻¹ * B) = firstColumn (1 : SO7) := by
  apply Subtype.ext
  apply congr_arg (WithLp.toLp 2)
  change Matrix.col (((A⁻¹ * B : SO7) : Matrix (Fin 7) (Fin 7) ℝ)) 0 =
    Matrix.col (1 : Matrix (Fin 7) (Fin 7) ℝ) 0
  rw [show (((A⁻¹ * B : SO7) : Matrix (Fin 7) (Fin 7) ℝ)) =
      ((A⁻¹ : SO7) : Matrix (Fin 7) (Fin 7) ℝ) *
        (B : Matrix (Fin 7) (Fin 7) ℝ) by rfl]
  rw [col_mul, ← col_eq_of_firstColumn_eq h]
  rw [← col_mul]
  have hinv : A⁻¹ * A = (1 : SO7) := by simp
  change Matrix.col (((A⁻¹ * A : SO7) : Matrix (Fin 7) (Fin 7) ℝ)) 0 =
    Matrix.col (((1 : SO7) : Matrix (Fin 7) (Fin 7) ℝ)) 0
  exact congr_arg
    (fun Q : SO7 ↦ Matrix.col (Q : Matrix (Fin 7) (Fin 7) ℝ) 0) hinv

public theorem firstColumn_mul_of_right_standard (A R : SO7)
    (hR : firstColumn R = firstColumn (1 : SO7)) :
    firstColumn (A * R) = firstColumn A := by
  apply Subtype.ext
  apply congr_arg (WithLp.toLp 2)
  change Matrix.col (((A * R : SO7) : Matrix (Fin 7) (Fin 7) ℝ)) 0 =
    Matrix.col (A : Matrix (Fin 7) (Fin 7) ℝ) 0
  rw [show (((A * R : SO7) : Matrix (Fin 7) (Fin 7) ℝ)) =
      (A : Matrix (Fin 7) (Fin 7) ℝ) *
        (R : Matrix (Fin 7) (Fin 7) ℝ) by rfl]
  rw [col_mul, col_eq_of_firstColumn_eq hR, ← col_mul]
  simp

/-- The point-set fiber over an arbitrary point of `S⁶`. -/
public abbrev FiberAt (x : Sphere6) :=
  {Q : SO7 // firstColumn Q = x}

public def northFiberToStandard (x : NorthPatch) (Q : FiberAt x.1) :
    StandardFiber :=
  ⟨(northSection x)⁻¹ * Q.1,
    firstColumn_inv_mul_eq_one (northSection x) Q.1
      ((firstColumn_northSection x).trans Q.2.symm)⟩

public def northFiberFromStandard (x : NorthPatch)
    (R : StandardFiber) : FiberAt x.1 :=
  ⟨northSection x * R.1,
    (firstColumn_mul_of_right_standard (northSection x) R.1 R.2).trans
      (firstColumn_northSection x)⟩

public theorem continuous_northFiberToStandard (x : NorthPatch) :
    Continuous (northFiberToStandard x) :=
  continuous_induced_rng.mpr (continuous_const.mul continuous_subtype_val)

public theorem continuous_northFiberFromStandard (x : NorthPatch) :
    Continuous (northFiberFromStandard x) :=
  continuous_induced_rng.mpr (continuous_const.mul continuous_subtype_val)

@[simp] public theorem northFiberFromStandard_toStandard (x : NorthPatch)
    (Q : FiberAt x.1) :
    northFiberFromStandard x (northFiberToStandard x Q) = Q := by
  apply Subtype.ext
  simp [northFiberFromStandard, northFiberToStandard]

@[simp] public theorem northFiberToStandard_fromStandard (x : NorthPatch)
    (R : StandardFiber) :
    northFiberToStandard x (northFiberFromStandard x R) = R := by
  apply Subtype.ext
  simp [northFiberFromStandard, northFiberToStandard]

/-- Each fiber over the north patch is explicitly homeomorphic to the standard fiber. -/
public def northFiberHomeomorphStandard (x : NorthPatch) :
    FiberAt x.1 ≃ₜ StandardFiber where
  toFun := northFiberToStandard x
  invFun := northFiberFromStandard x
  left_inv := northFiberFromStandard_toStandard x
  right_inv := northFiberToStandard_fromStandard x
  continuous_toFun := continuous_northFiberToStandard x
  continuous_invFun := continuous_northFiberFromStandard x

/-- Consequently, each north-patch fiber is homeomorphic to `SO(6)`. -/
public def northFiberHomeomorphSO6 (x : NorthPatch) : FiberAt x.1 ≃ₜ SO6 :=
  (northFiberHomeomorphStandard x).trans standardFiberHomeomorphSO6

/-- The total space restricted to the north patch. -/
public abbrev NorthTotal :=
  {Q : SO7 // firstColumn Q ∈ northSet}

public def northTotalBase (Q : NorthTotal) : NorthPatch :=
  ⟨firstColumn Q.1, Q.2⟩

public theorem continuous_northTotalBase : Continuous northTotalBase :=
  continuous_induced_rng.mpr
    (continuous_firstColumn.comp continuous_subtype_val)

public def northTotalStandardFiber (Q : NorthTotal) : StandardFiber :=
  ⟨(northSection (northTotalBase Q))⁻¹ * Q.1,
    firstColumn_inv_mul_eq_one (northSection (northTotalBase Q)) Q.1 (by
      simp [northTotalBase])⟩

public theorem continuous_northTotalStandardFiber :
    Continuous northTotalStandardFiber :=
  continuous_induced_rng.mpr
    ((continuous_inv.comp
      (continuous_northSection.comp continuous_northTotalBase)).mul continuous_subtype_val)

public def northTrivializationForward (Q : NorthTotal) : NorthPatch × SO6 :=
  (northTotalBase Q, lowerSpecialOrthogonal (northTotalStandardFiber Q))

public theorem continuous_northTrivializationForward :
    Continuous northTrivializationForward :=
  continuous_northTotalBase.prodMk
    (continuous_lowerSpecialOrthogonal.comp continuous_northTotalStandardFiber)

public def northTrivializationInverse (p : NorthPatch × SO6) : NorthTotal :=
  ⟨northSection p.1 * stabilize p.2, by
    rw [firstColumn_mul_of_right_standard _ _ (firstColumn_stabilize p.2),
      firstColumn_northSection]
    exact p.1.2⟩

public theorem continuous_northTrivializationInverse :
    Continuous northTrivializationInverse :=
  continuous_induced_rng.mpr
    ((continuous_northSection.comp continuous_fst).mul
      (continuous_stabilize.comp continuous_snd))

@[simp] public theorem northTrivializationForward_inverse (p : NorthPatch × SO6) :
    northTrivializationForward (northTrivializationInverse p) = p := by
  have hbase : northTotalBase (northTrivializationInverse p) = p.1 := by
    apply Subtype.ext
    change firstColumn (northSection p.1 * stabilize p.2) = p.1.1
    rw [firstColumn_mul_of_right_standard _ _ (firstColumn_stabilize p.2),
      firstColumn_northSection]
  apply Prod.ext
  · exact hbase
  · change lowerSpecialOrthogonal
      (northTotalStandardFiber (northTrivializationInverse p)) = p.2
    have hfiber :
        northTotalStandardFiber (northTrivializationInverse p) = stabilizeFiber p.2 := by
      apply Subtype.ext
      change (northSection
          (northTotalBase (northTrivializationInverse p)))⁻¹ *
          (northSection p.1 * stabilize p.2) = stabilize p.2
      rw [hbase]
      simp
    rw [hfiber]
    exact lowerSpecialOrthogonal_stabilizeFiber p.2

@[simp] public theorem northTrivializationInverse_forward (Q : NorthTotal) :
    northTrivializationInverse (northTrivializationForward Q) = Q := by
  apply Subtype.ext
  change northSection (northTotalBase Q) *
      stabilize (lowerSpecialOrthogonal (northTotalStandardFiber Q)) = Q.1
  have hstab := congr_arg Subtype.val
    (stabilizeFiber_lowerSpecialOrthogonal (northTotalStandardFiber Q))
  change stabilize (lowerSpecialOrthogonal (northTotalStandardFiber Q)) =
    (northSection (northTotalBase Q))⁻¹ * Q.1 at hstab
  rw [hstab]
  simp

/-- Explicit product trivialization of `SO(7) → S⁶` over the north patch. -/
public def northPatchTrivialization : NorthTotal ≃ₜ (NorthPatch × SO6) where
  toFun := northTrivializationForward
  invFun := northTrivializationInverse
  left_inv := northTrivializationInverse_forward
  right_inv := northTrivializationForward_inverse
  continuous_toFun := continuous_northTrivializationForward
  continuous_invFun := continuous_northTrivializationInverse

@[simp] public theorem northPatchTrivialization_fst (Q : NorthTotal) :
    (northPatchTrivialization Q).1 = northTotalBase Q :=
  rfl

@[simp] public theorem northPatchTrivialization_symm_base (p : NorthPatch × SO6) :
    northTotalBase (northPatchTrivialization.symm p) = p.1 := by
  exact congr_arg Prod.fst (northPatchTrivialization.apply_symm_apply p)

@[simp] public theorem coe_northTotalBase (Q : NorthTotal) :
    (northTotalBase Q : Sphere6) = firstColumn Q.1 :=
  rfl

@[simp] public theorem firstColumn_northPatchTrivialization_symm
    (p : NorthPatch × SO6) :
    firstColumn (northPatchTrivialization.symm p).1 = p.1.1 := by
  exact congr_arg Subtype.val (northPatchTrivialization_symm_base p)

public def southFiberToStandard (x : SouthPatch) (Q : FiberAt x.1) :
    StandardFiber :=
  ⟨(southSection x)⁻¹ * Q.1,
    firstColumn_inv_mul_eq_one (southSection x) Q.1
      ((firstColumn_southSection x).trans Q.2.symm)⟩

public def southFiberFromStandard (x : SouthPatch)
    (R : StandardFiber) : FiberAt x.1 :=
  ⟨southSection x * R.1,
    (firstColumn_mul_of_right_standard (southSection x) R.1 R.2).trans
      (firstColumn_southSection x)⟩

public theorem continuous_southFiberToStandard (x : SouthPatch) :
    Continuous (southFiberToStandard x) :=
  continuous_induced_rng.mpr (continuous_const.mul continuous_subtype_val)

public theorem continuous_southFiberFromStandard (x : SouthPatch) :
    Continuous (southFiberFromStandard x) :=
  continuous_induced_rng.mpr (continuous_const.mul continuous_subtype_val)

@[simp] public theorem southFiberFromStandard_toStandard (x : SouthPatch)
    (Q : FiberAt x.1) :
    southFiberFromStandard x (southFiberToStandard x Q) = Q := by
  apply Subtype.ext
  simp [southFiberFromStandard, southFiberToStandard]

@[simp] public theorem southFiberToStandard_fromStandard (x : SouthPatch)
    (R : StandardFiber) :
    southFiberToStandard x (southFiberFromStandard x R) = R := by
  apply Subtype.ext
  simp [southFiberFromStandard, southFiberToStandard]

/-- Each fiber over the south patch is explicitly homeomorphic to the standard fiber. -/
public def southFiberHomeomorphStandard (x : SouthPatch) :
    FiberAt x.1 ≃ₜ StandardFiber where
  toFun := southFiberToStandard x
  invFun := southFiberFromStandard x
  left_inv := southFiberFromStandard_toStandard x
  right_inv := southFiberToStandard_fromStandard x
  continuous_toFun := continuous_southFiberToStandard x
  continuous_invFun := continuous_southFiberFromStandard x

/-- Consequently, each south-patch fiber is homeomorphic to `SO(6)`. -/
public def southFiberHomeomorphSO6 (x : SouthPatch) : FiberAt x.1 ≃ₜ SO6 :=
  (southFiberHomeomorphStandard x).trans standardFiberHomeomorphSO6

/-- The total space restricted to the south patch. -/
public abbrev SouthTotal :=
  {Q : SO7 // firstColumn Q ∈ southSet}

public def southTotalBase (Q : SouthTotal) : SouthPatch :=
  ⟨firstColumn Q.1, Q.2⟩

public theorem continuous_southTotalBase : Continuous southTotalBase :=
  continuous_induced_rng.mpr
    (continuous_firstColumn.comp continuous_subtype_val)

public def southTotalStandardFiber (Q : SouthTotal) : StandardFiber :=
  ⟨(southSection (southTotalBase Q))⁻¹ * Q.1,
    firstColumn_inv_mul_eq_one (southSection (southTotalBase Q)) Q.1 (by
      simp [southTotalBase])⟩

public theorem continuous_southTotalStandardFiber :
    Continuous southTotalStandardFiber :=
  continuous_induced_rng.mpr
    ((continuous_inv.comp
      (continuous_southSection.comp continuous_southTotalBase)).mul continuous_subtype_val)

public def southTrivializationForward (Q : SouthTotal) : SouthPatch × SO6 :=
  (southTotalBase Q, lowerSpecialOrthogonal (southTotalStandardFiber Q))

public theorem continuous_southTrivializationForward :
    Continuous southTrivializationForward :=
  continuous_southTotalBase.prodMk
    (continuous_lowerSpecialOrthogonal.comp continuous_southTotalStandardFiber)

public def southTrivializationInverse (p : SouthPatch × SO6) : SouthTotal :=
  ⟨southSection p.1 * stabilize p.2, by
    rw [firstColumn_mul_of_right_standard _ _ (firstColumn_stabilize p.2),
      firstColumn_southSection]
    exact p.1.2⟩

public theorem continuous_southTrivializationInverse :
    Continuous southTrivializationInverse :=
  continuous_induced_rng.mpr
    ((continuous_southSection.comp continuous_fst).mul
      (continuous_stabilize.comp continuous_snd))

@[simp] public theorem southTrivializationForward_inverse (p : SouthPatch × SO6) :
    southTrivializationForward (southTrivializationInverse p) = p := by
  have hbase : southTotalBase (southTrivializationInverse p) = p.1 := by
    apply Subtype.ext
    change firstColumn (southSection p.1 * stabilize p.2) = p.1.1
    rw [firstColumn_mul_of_right_standard _ _ (firstColumn_stabilize p.2),
      firstColumn_southSection]
  apply Prod.ext
  · exact hbase
  · change lowerSpecialOrthogonal
      (southTotalStandardFiber (southTrivializationInverse p)) = p.2
    have hfiber :
        southTotalStandardFiber (southTrivializationInverse p) = stabilizeFiber p.2 := by
      apply Subtype.ext
      change (southSection
          (southTotalBase (southTrivializationInverse p)))⁻¹ *
          (southSection p.1 * stabilize p.2) = stabilize p.2
      rw [hbase]
      simp
    rw [hfiber]
    exact lowerSpecialOrthogonal_stabilizeFiber p.2

@[simp] public theorem southTrivializationInverse_forward (Q : SouthTotal) :
    southTrivializationInverse (southTrivializationForward Q) = Q := by
  apply Subtype.ext
  change southSection (southTotalBase Q) *
      stabilize (lowerSpecialOrthogonal (southTotalStandardFiber Q)) = Q.1
  have hstab := congr_arg Subtype.val
    (stabilizeFiber_lowerSpecialOrthogonal (southTotalStandardFiber Q))
  change stabilize (lowerSpecialOrthogonal (southTotalStandardFiber Q)) =
    (southSection (southTotalBase Q))⁻¹ * Q.1 at hstab
  rw [hstab]
  simp

/-- Explicit product trivialization of `SO(7) → S⁶` over the south patch. -/
public def southPatchTrivialization : SouthTotal ≃ₜ (SouthPatch × SO6) where
  toFun := southTrivializationForward
  invFun := southTrivializationInverse
  left_inv := southTrivializationInverse_forward
  right_inv := southTrivializationForward_inverse
  continuous_toFun := continuous_southTrivializationForward
  continuous_invFun := continuous_southTrivializationInverse

@[simp] public theorem southPatchTrivialization_fst (Q : SouthTotal) :
    (southPatchTrivialization Q).1 = southTotalBase Q :=
  rfl

@[simp] public theorem southPatchTrivialization_symm_base (p : SouthPatch × SO6) :
    southTotalBase (southPatchTrivialization.symm p) = p.1 := by
  exact congr_arg Prod.fst (southPatchTrivialization.apply_symm_apply p)

@[simp] public theorem coe_southTotalBase (Q : SouthTotal) :
    (southTotalBase Q : Sphere6) = firstColumn Q.1 :=
  rfl

@[simp] public theorem firstColumn_southPatchTrivialization_symm
    (p : SouthPatch × SO6) :
    firstColumn (southPatchTrivialization.symm p).1 = p.1.1 := by
  exact congr_arg Subtype.val (southPatchTrivialization_symm_base p)

end SphereSixComplex.SpecialOrthogonalSevenStiefel
