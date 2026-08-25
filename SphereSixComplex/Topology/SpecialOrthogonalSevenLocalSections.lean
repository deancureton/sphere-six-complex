module

public import SphereSixComplex.Topology.SpecialOrthogonalSevenStiefel

/-!
# Local sections of `SO(7) → S⁶`

This file constructs two explicit local sections of the first-column projection
`SO(7) → S⁶`.  Each section is a product of two Householder reflections, hence is
orientation-preserving.  Their domains are the complements of the two poles and cover the sphere.

These sections are the geometric input for local trivializations of the Stiefel bundle
`SO(6) → SO(7) → S⁶`.
-/

@[expose] public section

noncomputable section

open ContinuousMap Matrix Set Topology
open scoped Classical MatrixGroups RealInnerProductSpace Topology

namespace SphereSixComplex.SpecialOrthogonalSevenStiefel

public abbrev V7 := Fin 7 → ℝ

/-- The rank-one Householder reflection in the hyperplane perpendicular to `v`. -/
public def householder (v : V7) : Matrix (Fin 7) (Fin 7) ℝ :=
  1 - (2 / dotProduct v v) • Matrix.vecMulVec v v

public theorem dot_self_ne_zero {v : V7} (hv : v ≠ 0) : dotProduct v v ≠ 0 := by
  intro h
  exact hv (dotProduct_self_eq_zero.mp h)

public theorem vecMulVec_mul_self (v : V7) :
    Matrix.vecMulVec v v * Matrix.vecMulVec v v =
      dotProduct v v • Matrix.vecMulVec v v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [dotProduct]
  calc
    ∑ k, v i * v k * (v k * v j) =
        ∑ k, (v i * v j) * (v k * v k) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (v i * v j) * ∑ k, v k * v k := by rw [Finset.mul_sum]
    _ = (∑ k, v k * v k) * (v i * v j) := by ring

public theorem householder_transpose (v : V7) : (householder v)ᵀ = householder v := by
  rw [householder, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_vecMulVec]

public theorem householder_mul_self {v : V7} (hv : v ≠ 0) :
    householder v * householder v = 1 := by
  let d : ℝ := dotProduct v v
  let c : ℝ := 2 / d
  let P : Matrix (Fin 7) (Fin 7) ℝ := Matrix.vecMulVec v v
  have hd : d ≠ 0 := dot_self_ne_zero hv
  have hP : P * P = d • P := vecMulVec_mul_self v
  change (1 - c • P) * (1 - c • P) = 1
  rw [sub_mul, mul_sub, mul_sub]
  simp only [one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  dsimp [c]
  field_simp
  ring

public theorem householder_orthogonal {v : V7} (hv : v ≠ 0) :
    (householder v)ᵀ * householder v = 1 := by
  rw [householder_transpose]
  exact householder_mul_self hv

public theorem householder_det {v : V7} (hv : v ≠ 0) :
    (householder v).det = -1 := by
  have hd : dotProduct v v ≠ 0 := dot_self_ne_zero hv
  rw [householder, sub_eq_add_neg]
  rw [← neg_smul]
  change (1 + ((-(2 / dotProduct v v)) • Matrix.vecMulVec v v)).det = -1
  rw [← Matrix.smul_vecMulVec,
    Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  rw [dotProduct_smul]
  simp only [smul_eq_mul]
  change 1 + -(2 / dotProduct v v) * dotProduct v v = -1
  field_simp
  ring

/-- Householder reflection, continuously parametrized by a nonzero vector. -/
public def householderNonzero (v : {v : V7 // v ≠ 0}) : Matrix (Fin 7) (Fin 7) ℝ :=
  householder v.1

public theorem continuous_householderNonzero : Continuous householderNonzero := by
  apply continuous_matrix
  intro i j
  unfold householderNonzero householder
  dsimp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply]
  have hv : Continuous (fun a : {v : V7 // v ≠ 0} ↦ (a.1 : V7)) := continuous_subtype_val
  have hdot : Continuous (fun a : {v : V7 // v ≠ 0} ↦ dotProduct a.1 a.1) :=
    hv.dotProduct hv
  have hi : Continuous (fun a : {v : V7 // v ≠ 0} ↦ a.1 i) :=
    (continuous_apply i).comp hv
  have hj : Continuous (fun a : {v : V7 // v ≠ 0} ↦ a.1 j) :=
    (continuous_apply j).comp hv
  exact continuous_const.sub
    ((continuous_const.div hdot (fun a ↦ dot_self_ne_zero a.2)).mul (hi.mul hj))

/-- The raw function coordinates of a point on the Euclidean sphere. -/
public def rawSphere (x : Sphere6) : V7 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 7 ↦ ℝ)) x.1

public theorem toLp_rawSphere (x : Sphere6) :
    WithLp.toLp 2 (rawSphere x) = x.1 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 7 ↦ ℝ)).symm_apply_apply x.1

public theorem rawSphere_dot_self (x : Sphere6) :
    dotProduct (rawSphere x) (rawSphere x) = 1 := by
  have hnorm : ‖x.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2
  calc
    dotProduct (rawSphere x) (rawSphere x) =
        inner ℝ (WithLp.toLp 2 (rawSphere x)) (WithLp.toLp 2 (rawSphere x)) := by
      symm
      rw [EuclideanSpace.inner_toLp_toLp]
      congr 1
    _ = inner ℝ x.1 x.1 := by rw [toLp_rawSphere]
    _ = ‖x.1‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = 1 := by rw [hnorm]; norm_num

public theorem continuous_rawSphere : Continuous rawSphere :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 7 ↦ ℝ)).continuous.comp
    continuous_subtype_val

/-- Coordinate basis vectors in the raw function model. -/
public def basisVec (j : Fin 7) : V7 := fun i ↦ if i = j then 1 else 0

@[simp] public theorem basisVec_apply_self (j : Fin 7) : basisVec j j = 1 := by
  simp [basisVec]

public theorem basisVec_eq_single (j : Fin 7) : basisVec j = Pi.single j 1 := by
  ext i
  simp [basisVec, Pi.single_apply, eq_comm]

@[simp] public theorem basisVec_dot (j : Fin 7) (v : V7) :
    dotProduct (basisVec j) v = v j := by
  rw [basisVec_eq_single]
  exact single_one_dotProduct j v

@[simp] public theorem dot_basisVec (v : V7) (j : Fin 7) :
    dotProduct v (basisVec j) = v j := by
  rw [basisVec_eq_single]
  exact dotProduct_single_one v j

@[simp] public theorem basisVec_dot_self (j : Fin 7) :
    dotProduct (basisVec j) (basisVec j) = 1 := by
  rw [basisVec_dot]
  simp [basisVec]

public theorem basisVec_ne_zero (j : Fin 7) : basisVec j ≠ 0 := by
  intro h
  have := congr_fun h j
  simp [basisVec] at this

/-- The sphere with the antipode of the first basis vector removed. -/
public def northSet : Set Sphere6 :=
  {x | rawSphere x ≠ -basisVec 0}

/-- The sphere with the first basis vector removed. -/
public def southSet : Set Sphere6 :=
  {x | rawSphere x ≠ basisVec 0}

public theorem isOpen_northSet : IsOpen northSet := by
  have hclosed : IsClosed (rawSphere ⁻¹' ({-basisVec 0} : Set V7)) :=
    isClosed_singleton.preimage continuous_rawSphere
  change IsOpen ((rawSphere ⁻¹' ({-basisVec 0} : Set V7))ᶜ)
  exact hclosed.isOpen_compl

public theorem isOpen_southSet : IsOpen southSet := by
  have hclosed : IsClosed (rawSphere ⁻¹' ({basisVec 0} : Set V7)) :=
    isClosed_singleton.preimage continuous_rawSphere
  change IsOpen ((rawSphere ⁻¹' ({basisVec 0} : Set V7))ᶜ)
  exact hclosed.isOpen_compl

public abbrev NorthPatch := ↑northSet
public abbrev SouthPatch := ↑southSet

public def northNormal (x : NorthPatch) : {v : V7 // v ≠ 0} :=
  ⟨basisVec 0 + rawSphere x.1, by
    intro h
    apply x.2
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using h⟩

public def southNormal (x : SouthPatch) : {v : V7 // v ≠ 0} :=
  ⟨basisVec 0 - rawSphere x.1, sub_ne_zero.mpr (Ne.symm x.2)⟩

public theorem continuous_northNormal : Continuous northNormal :=
  continuous_induced_rng.mpr
    (continuous_const.add (continuous_rawSphere.comp continuous_subtype_val))

public theorem continuous_southNormal : Continuous southNormal :=
  continuous_induced_rng.mpr
    (continuous_const.sub (continuous_rawSphere.comp continuous_subtype_val))

public theorem householder_mulVec (v : V7) (w : V7) :
    householder v *ᵥ w =
      w - (2 / dotProduct v v * dotProduct v w) • v := by
  ext i
  simp only [householder, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.sub_apply, Pi.smul_apply, op_smul_eq_smul, smul_eq_mul]
  ring

public theorem householder_mulVec_self {v : V7} (hv : v ≠ 0) :
    householder v *ᵥ v = -v := by
  rw [householder_mulVec]
  have hd := dot_self_ne_zero hv
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

public theorem north_householder_basisVec_zero (x : NorthPatch) :
    householder (northNormal x).1 *ᵥ basisVec 0 = -rawSphere x.1 := by
  rw [householder_mulVec]
  have hunit := rawSphere_dot_self x.1
  have hd := dot_self_ne_zero (northNormal x).2
  ext i
  simp only [northNormal, add_dotProduct, dotProduct_add,
    basisVec_dot, dot_basisVec, hunit, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul, basisVec_apply_self]
  simp only [northNormal, add_dotProduct, dotProduct_add,
    basisVec_dot, dot_basisVec, hunit, basisVec_apply_self] at hd
  field_simp [hd]
  ring

public theorem south_householder_basisVec_zero (x : SouthPatch) :
    householder (southNormal x).1 *ᵥ basisVec 0 = rawSphere x.1 := by
  rw [householder_mulVec]
  have hunit := rawSphere_dot_self x.1
  have hd := dot_self_ne_zero (southNormal x).2
  ext i
  simp only [southNormal, sub_dotProduct, dotProduct_sub,
    basisVec_dot, dot_basisVec, hunit, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    basisVec_apply_self]
  simp only [southNormal, sub_dotProduct, dotProduct_sub,
    basisVec_dot, dot_basisVec, hunit, basisVec_apply_self] at hd
  field_simp [hd]
  ring

public theorem householder_basisVec_zero_self :
    householder (basisVec 0) *ᵥ basisVec 0 = -basisVec 0 :=
  householder_mulVec_self (basisVec_ne_zero 0)

public theorem householder_basisVec_one_fixes_zero :
    householder (basisVec 1) *ᵥ basisVec 0 = basisVec 0 := by
  rw [householder_mulVec]
  ext i
  simp [basisVec]

/-- Orientation-preserving north-patch lift, a product of two reflections. -/
public def northMatrix (x : NorthPatch) : Matrix (Fin 7) (Fin 7) ℝ :=
  householder (northNormal x).1 * householder (basisVec 0)

/-- Orientation-preserving south-patch lift, a product of two reflections. -/
public def southMatrix (x : SouthPatch) : Matrix (Fin 7) (Fin 7) ℝ :=
  householder (southNormal x).1 * householder (basisVec 1)

public theorem northMatrix_col_zero (x : NorthPatch) :
    Matrix.col (northMatrix x) 0 = rawSphere x.1 := by
  rw [← Matrix.mulVec_single_one]
  rw [← basisVec_eq_single]
  rw [northMatrix]
  rw [← Matrix.mulVec_mulVec]
  rw [householder_basisVec_zero_self]
  rw [Matrix.mulVec_neg, north_householder_basisVec_zero]
  simp

public theorem southMatrix_col_zero (x : SouthPatch) :
    Matrix.col (southMatrix x) 0 = rawSphere x.1 := by
  rw [← Matrix.mulVec_single_one]
  rw [← basisVec_eq_single]
  rw [southMatrix]
  rw [← Matrix.mulVec_mulVec]
  rw [householder_basisVec_one_fixes_zero,
    south_householder_basisVec_zero]

public theorem northMatrix_orthogonal (x : NorthPatch) :
    (northMatrix x)ᵀ * northMatrix x = 1 := by
  rw [northMatrix, Matrix.transpose_mul]
  calc
    (householder (basisVec 0))ᵀ * (householder (northNormal x).1)ᵀ *
          (householder (northNormal x).1 * householder (basisVec 0)) =
        (householder (basisVec 0))ᵀ *
          ((householder (northNormal x).1)ᵀ * householder (northNormal x).1) *
            householder (basisVec 0) := by simp only [Matrix.mul_assoc]
    _ = (householder (basisVec 0))ᵀ * 1 * householder (basisVec 0) := by
      rw [householder_orthogonal (northNormal x).2]
    _ = 1 := by simpa using householder_orthogonal (basisVec_ne_zero 0)

public theorem southMatrix_orthogonal (x : SouthPatch) :
    (southMatrix x)ᵀ * southMatrix x = 1 := by
  rw [southMatrix, Matrix.transpose_mul]
  calc
    (householder (basisVec 1))ᵀ * (householder (southNormal x).1)ᵀ *
          (householder (southNormal x).1 * householder (basisVec 1)) =
        (householder (basisVec 1))ᵀ *
          ((householder (southNormal x).1)ᵀ * householder (southNormal x).1) *
            householder (basisVec 1) := by simp only [Matrix.mul_assoc]
    _ = (householder (basisVec 1))ᵀ * 1 * householder (basisVec 1) := by
      rw [householder_orthogonal (southNormal x).2]
    _ = 1 := by simpa using householder_orthogonal (basisVec_ne_zero 1)

public theorem northMatrix_det (x : NorthPatch) : (northMatrix x).det = 1 := by
  rw [northMatrix, Matrix.det_mul, householder_det (northNormal x).2,
    householder_det (basisVec_ne_zero 0)]
  norm_num

public theorem southMatrix_det (x : SouthPatch) : (southMatrix x).det = 1 := by
  rw [southMatrix, Matrix.det_mul, householder_det (southNormal x).2,
    householder_det (basisVec_ne_zero 1)]
  norm_num

public theorem continuous_northMatrix : Continuous northMatrix :=
  (continuous_householderNonzero.comp continuous_northNormal).mul continuous_const

public theorem continuous_southMatrix : Continuous southMatrix :=
  (continuous_householderNonzero.comp continuous_southNormal).mul continuous_const

public theorem northMatrix_mem (x : NorthPatch) : northMatrix x ∈ SO7 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨by
    rw [Matrix.mem_orthogonalGroup_iff']
    exact northMatrix_orthogonal x, northMatrix_det x⟩

public theorem southMatrix_mem (x : SouthPatch) : southMatrix x ∈ SO7 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨by
    rw [Matrix.mem_orthogonalGroup_iff']
    exact southMatrix_orthogonal x, southMatrix_det x⟩

/-- A continuous local section over the complement of the south pole. -/
public def northSection (x : NorthPatch) : SO7 :=
  ⟨northMatrix x, northMatrix_mem x⟩

/-- A continuous local section over the complement of the north pole. -/
public def southSection (x : SouthPatch) : SO7 :=
  ⟨southMatrix x, southMatrix_mem x⟩

public theorem continuous_northSection : Continuous northSection :=
  continuous_induced_rng.mpr continuous_northMatrix

public theorem continuous_southSection : Continuous southSection :=
  continuous_induced_rng.mpr continuous_southMatrix

public def northSectionMap : C(NorthPatch, SO7) :=
  ⟨northSection, continuous_northSection⟩

public def southSectionMap : C(SouthPatch, SO7) :=
  ⟨southSection, continuous_southSection⟩

public def northPatchInclusion : C(NorthPatch, Sphere6) :=
  ⟨Subtype.val, continuous_subtype_val⟩

public def southPatchInclusion : C(SouthPatch, Sphere6) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] public theorem firstColumn_northSection (x : NorthPatch) :
    firstColumn (northSection x) = x.1 := by
  apply Subtype.ext
  change WithLp.toLp 2 (Matrix.col (northMatrix x) 0) = x.1.1
  rw [northMatrix_col_zero, toLp_rawSphere]

@[simp] public theorem firstColumn_southSection (x : SouthPatch) :
    firstColumn (southSection x) = x.1 := by
  apply Subtype.ext
  change WithLp.toLp 2 (Matrix.col (southMatrix x) 0) = x.1.1
  rw [southMatrix_col_zero, toLp_rawSphere]

public theorem firstColumnMap_comp_northSectionMap :
    firstColumnMap.comp northSectionMap = northPatchInclusion := by
  apply ContinuousMap.ext
  intro x
  exact firstColumn_northSection x

public theorem firstColumnMap_comp_southSectionMap :
    firstColumnMap.comp southSectionMap = southPatchInclusion := by
  apply ContinuousMap.ext
  intro x
  exact firstColumn_southSection x

/-- The two local-section domains cover the entire six-sphere. -/
public theorem northSet_union_southSet : northSet ∪ southSet = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true, northSet, southSet,
    Set.mem_ofPred_eq]
  by_contra h
  push Not at h
  have heq : basisVec 0 = -basisVec 0 := h.2.symm.trans h.1
  have hzero := congr_fun heq 0
  norm_num [basisVec] at hzero

end SphereSixComplex.SpecialOrthogonalSevenStiefel
