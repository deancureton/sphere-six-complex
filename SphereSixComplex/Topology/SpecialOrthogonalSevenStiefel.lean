module

public import SphereSixComplex.Topology.StableFiveSphereCubeBoundaryCollapse
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# The standard fiber of `SO(7) → S⁶`

This file constructs the first-column projection from `SO(7)` to the unit six-sphere and the
standard block inclusion `SO(6) → SO(7)`.  It identifies the fiber over the first standard basis
vector explicitly with `SO(6)` by extracting the lower-right block.

This is the point-set foundation for the Stiefel fibration route to `π₅(SO(7)) = 0`.  No
fibration or long exact sequence is asserted here.
-/

@[expose] public section

noncomputable section

open ContinuousMap Matrix Set Topology
open scoped Classical MatrixGroups RealInnerProductSpace Topology

namespace SphereSixComplex.SpecialOrthogonalSevenStiefel

set_option maxRecDepth 100000

public abbrev SO7 := StableSpecialOrthogonalSeven
public abbrev SO6 := Matrix.specialOrthogonalGroup (Fin 6) ℝ
public abbrev Sphere6 := ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1)

/-- The first column, regarded as a Euclidean vector. -/
public def firstColumnVector (Q : SO7) : EuclideanSpace ℝ (Fin 7) :=
  WithLp.toLp 2 (Matrix.col (Q : Matrix (Fin 7) (Fin 7) ℝ) 0)

public theorem firstColumnVector_inner_self (Q : SO7) :
    inner ℝ (firstColumnVector Q) (firstColumnVector Q) = 1 := by
  change inner ℝ
    (WithLp.toLp 2 ((Q : Matrix (Fin 7) (Fin 7) ℝ)ᵀ 0))
    (WithLp.toLp 2 ((Q : Matrix (Fin 7) (Fin 7) ℝ)ᵀ 0)) = 1
  rw [inner_matrix_col_col]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.one_apply_eq] using
    congr_fun (congr_fun ((Matrix.mem_orthogonalGroup_iff' (Fin 7) ℝ).mp Q.property.1) 0) 0

public theorem firstColumnVector_norm (Q : SO7) : ‖firstColumnVector Q‖ = 1 := by
  have hsquare : ‖firstColumnVector Q‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, firstColumnVector_inner_self]
  nlinarith [norm_nonneg (firstColumnVector Q)]

/-- Every special orthogonal matrix has a unit first column. -/
public def firstColumn (Q : SO7) : Sphere6 :=
  ⟨firstColumnVector Q, by
    rw [Metric.mem_sphere, dist_zero_right, firstColumnVector_norm]⟩

public theorem continuous_firstColumnVector : Continuous firstColumnVector := by
  unfold firstColumnVector
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 7 ↦ ℝ)).symm.continuous.comp
    (continuous_pi fun i ↦
      (continuous_apply_apply i 0).comp continuous_subtype_val)

public theorem continuous_firstColumn : Continuous firstColumn :=
  continuous_induced_rng.mpr continuous_firstColumnVector

/-- The homogeneous-space projection `SO(7) → S⁶`. -/
public def firstColumnMap : C(SO7, Sphere6) :=
  ⟨firstColumn, continuous_firstColumn⟩

/-- The block inclusion of six-dimensional matrices fixing the first coordinate. -/
public def stabilizeMatrix (Q : SO6) : Matrix (Fin 7) (Fin 7) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
      (Q : Matrix (Fin 6) (Fin 6) ℝ))

public theorem stabilizeMatrix_transpose_mul_self (Q : SO6) :
    (stabilizeMatrix Q)ᵀ * stabilizeMatrix Q = 1 := by
  unfold stabilizeMatrix
  rw [Matrix.transpose_reindex]
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [(Matrix.mem_orthogonalGroup_iff' (Fin 6) ℝ).mp Q.property.1]
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

public theorem stabilizeMatrix_det (Q : SO6) : (stabilizeMatrix Q).det = 1 := by
  rw [stabilizeMatrix, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simpa using Q.property.2

public theorem stabilizeMatrix_mem (Q : SO6) : stabilizeMatrix Q ∈ SO7 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff']
    exact stabilizeMatrix_transpose_mul_self Q
  · exact stabilizeMatrix_det Q

/-- The standard block inclusion `SO(6) → SO(7)`. -/
public def stabilize (Q : SO6) : SO7 :=
  ⟨stabilizeMatrix Q, stabilizeMatrix_mem Q⟩

public theorem continuous_stabilizeMatrix : Continuous stabilizeMatrix := by
  unfold stabilizeMatrix
  fun_prop

public theorem continuous_stabilize : Continuous stabilize :=
  continuous_induced_rng.mpr continuous_stabilizeMatrix

public def stabilizeMap : C(SO6, SO7) :=
  ⟨stabilize, continuous_stabilize⟩

public theorem stabilizeMatrix_col_zero (Q : SO6) :
    Matrix.col (stabilizeMatrix Q) 0 =
      Matrix.col (1 : Matrix (Fin 7) (Fin 7) ℝ) 0 := by
  have hzero : (@finSumFinEquiv 1 6).symm (0 : Fin 7) = Sum.inl 0 := by
    rfl
  funext i
  change Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
      (Q : Matrix (Fin 6) (Fin 6) ℝ) ((@finSumFinEquiv 1 6).symm i)
      ((@finSumFinEquiv 1 6).symm 0) =
    (1 : Matrix (Fin 7) (Fin 7) ℝ) i 0
  rw [hzero]
  obtain ⟨i, rfl⟩ := (@finSumFinEquiv 1 6).surjective i
  rw [(@finSumFinEquiv 1 6).symm_apply_apply]
  rcases i with i | i
  · fin_cases i
    simp [Matrix.one_apply, finSumFinEquiv]
  · have hne : (@finSumFinEquiv 1 6) (Sum.inr i) ≠ (0 : Fin 7) := by
      intro heq
      have hval := congr_arg Fin.val heq
      simp [finSumFinEquiv] at hval
    simp [hne]

@[simp] public theorem firstColumn_stabilize (Q : SO6) :
    firstColumn (stabilize Q) = firstColumn (1 : SO7) := by
  apply Subtype.ext
  exact congr_arg (WithLp.toLp 2) (stabilizeMatrix_col_zero Q)

/-- The point-set fiber over the standard first column. -/
public abbrev StandardFiber :=
  {Q : SO7 // firstColumn Q = firstColumn (1 : SO7)}

/-- The block inclusion lands in the point-set fiber of the first-column map. -/
public def stabilizeFiber (Q : SO6) : StandardFiber :=
  ⟨stabilize Q, firstColumn_stabilize Q⟩

public theorem continuous_stabilizeFiber : Continuous stabilizeFiber :=
  continuous_induced_rng.mpr continuous_stabilize

public theorem stabilizeMatrix_injective : Function.Injective stabilizeMatrix := by
  intro Q R h
  apply Subtype.ext
  have h' := congr_arg
    (fun M : Matrix (Fin 7) (Fin 7) ℝ ↦
      Matrix.toBlocks₂₂ (Matrix.reindex (@finSumFinEquiv 1 6).symm
        (@finSumFinEquiv 1 6).symm M)) h
  simpa [stabilizeMatrix] using h'

public theorem stabilizeFiber_injective : Function.Injective stabilizeFiber := by
  intro Q R h
  exact stabilizeMatrix_injective (congr_arg (fun z : StandardFiber ↦
    ((z.1 : SO7) : Matrix (Fin 7) (Fin 7) ℝ)) h)

public theorem fiber_column_eq (Q : StandardFiber) :
    Matrix.col (Q.1 : Matrix (Fin 7) (Fin 7) ℝ) 0 =
      Matrix.col (1 : Matrix (Fin 7) (Fin 7) ℝ) 0 := by
  have h := congr_arg Subtype.val Q.2
  change WithLp.toLp 2 (Matrix.col (Q.1 : Matrix (Fin 7) (Fin 7) ℝ) 0) =
    WithLp.toLp 2 (Matrix.col (1 : Matrix (Fin 7) (Fin 7) ℝ) 0) at h
  exact WithLp.toLp_injective 2 h

public theorem row_zero_eq_of_column_zero_eq (Q : SO7)
    (hcol : Matrix.col (Q : Matrix (Fin 7) (Fin 7) ℝ) 0 =
      Matrix.col (1 : Matrix (Fin 7) (Fin 7) ℝ) 0) :
    Matrix.row (Q : Matrix (Fin 7) (Fin 7) ℝ) 0 =
      Matrix.row (1 : Matrix (Fin 7) (Fin 7) ℝ) 0 := by
  funext j
  have horth := congr_fun (congr_fun
    ((Matrix.mem_orthogonalGroup_iff' (Fin 7) ℝ).mp Q.property.1) 0) j
  rw [Matrix.mul_apply] at horth
  simp only [Matrix.transpose_apply] at horth
  have hcol_apply : ∀ i : Fin 7,
      (Q : Matrix (Fin 7) (Fin 7) ℝ) i 0 =
        (1 : Matrix (Fin 7) (Fin 7) ℝ) i 0 := congr_fun hcol
  simp_rw [hcol_apply] at horth
  simpa [Matrix.one_apply] using horth

public theorem fiber_row_eq (Q : StandardFiber) :
    Matrix.row (Q.1 : Matrix (Fin 7) (Fin 7) ℝ) 0 =
      Matrix.row (1 : Matrix (Fin 7) (Fin 7) ℝ) 0 :=
  row_zero_eq_of_column_zero_eq Q.1 (fiber_column_eq Q)

/-- Move the distinguished coordinate to a `Fin 1 ⊕ Fin 6` block decomposition. -/
public def splitMatrix (Q : SO7) : Matrix (Fin 1 ⊕ Fin 6) (Fin 1 ⊕ Fin 6) ℝ :=
  Matrix.reindex (@finSumFinEquiv 1 6).symm (@finSumFinEquiv 1 6).symm
    (Q : Matrix (Fin 7) (Fin 7) ℝ)

/-- The lower-right six-dimensional block. -/
public def lowerBlock (Q : SO7) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.toBlocks₂₂ (splitMatrix Q)

public theorem continuous_lowerBlock : Continuous lowerBlock := by
  apply continuous_matrix
  intro i j
  change Continuous (fun Q : SO7 ↦
    (Q : Matrix (Fin 7) (Fin 7) ℝ)
      ((@finSumFinEquiv 1 6) (Sum.inr i))
      ((@finSumFinEquiv 1 6) (Sum.inr j)))
  exact (continuous_apply_apply _ _).comp continuous_subtype_val

public theorem splitMatrix_fiber_blockDiagonal (Q : StandardFiber) :
    splitMatrix Q.1 = Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
      (lowerBlock Q.1) := by
  rw [Matrix.ext_iff_blocks]
  refine ⟨?_, ?_, ?_, rfl⟩
  · ext i j
    fin_cases i
    fin_cases j
    have h := congr_fun (fiber_column_eq Q) 0
    change (Q.1 : Matrix (Fin 7) (Fin 7) ℝ) 0 0 = 1
    simpa [Matrix.one_apply] using h
  · ext i j
    fin_cases i
    have h := congr_fun (fiber_row_eq Q) ((@finSumFinEquiv 1 6) (Sum.inr j))
    change (Q.1 : Matrix (Fin 7) (Fin 7) ℝ) 0
      ((@finSumFinEquiv 1 6) (Sum.inr j)) = 0
    have hne : (0 : Fin 7) ≠ (@finSumFinEquiv 1 6) (Sum.inr j) := by
      intro heq
      have hval := congr_arg Fin.val heq
      simp [finSumFinEquiv] at hval
      omega
    simpa [Matrix.one_apply, hne] using h
  · ext i j
    fin_cases j
    have h := congr_fun (fiber_column_eq Q) ((@finSumFinEquiv 1 6) (Sum.inr i))
    change (Q.1 : Matrix (Fin 7) (Fin 7) ℝ)
      ((@finSumFinEquiv 1 6) (Sum.inr i)) 0 = 0
    have hne : (@finSumFinEquiv 1 6) (Sum.inr i) ≠ (0 : Fin 7) := by
      intro heq
      have hval := congr_arg Fin.val heq
      simp [finSumFinEquiv] at hval
    simpa [Matrix.one_apply, hne] using h

public theorem splitMatrix_transpose_mul_self (Q : SO7) :
    (splitMatrix Q)ᵀ * splitMatrix Q = 1 := by
  unfold splitMatrix
  rw [Matrix.transpose_reindex]
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [(Matrix.mem_orthogonalGroup_iff' (Fin 7) ℝ).mp Q.property.1]
  exact Matrix.submatrix_one_equiv _

public theorem lowerBlock_transpose_mul_self (Q : StandardFiber) :
    (lowerBlock Q.1)ᵀ * lowerBlock Q.1 = 1 := by
  have h := splitMatrix_transpose_mul_self Q.1
  rw [splitMatrix_fiber_blockDiagonal Q] at h
  have h₂₂ := congr_arg Matrix.toBlocks₂₂ h
  apply Matrix.ext
  intro i j
  have hij := congr_fun (congr_fun h₂₂ i) j
  simpa [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.toBlocks₂₂,
    Matrix.one_apply] using hij

public theorem lowerBlock_det (Q : StandardFiber) : (lowerBlock Q.1).det = 1 := by
  have hQdet : ((Q.1 : SO7) : Matrix (Fin 7) (Fin 7) ℝ).det = 1 :=
    Q.1.property.2
  have hdet : (splitMatrix Q.1).det = 1 := by
    simpa only [splitMatrix, Matrix.det_reindex_self] using hQdet
  rw [splitMatrix_fiber_blockDiagonal Q, Matrix.det_fromBlocks_zero₂₁] at hdet
  simpa only [Matrix.det_one, one_mul] using hdet

public theorem lowerBlock_mem (Q : StandardFiber) : lowerBlock Q.1 ∈ SO6 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff']
    exact lowerBlock_transpose_mul_self Q
  · exact lowerBlock_det Q

/-- Inverse of the block inclusion on the standard fiber. -/
public def lowerSpecialOrthogonal (Q : StandardFiber) : SO6 :=
  ⟨lowerBlock Q.1, lowerBlock_mem Q⟩

public theorem continuous_lowerSpecialOrthogonal :
    Continuous lowerSpecialOrthogonal :=
  continuous_induced_rng.mpr (continuous_lowerBlock.comp continuous_subtype_val)

public theorem stabilizeMatrix_lowerBlock (Q : StandardFiber) :
    stabilizeMatrix (lowerSpecialOrthogonal Q) =
      (Q.1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  change Matrix.reindex (@finSumFinEquiv 1 6) (@finSumFinEquiv 1 6)
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (lowerBlock Q.1)) =
    (Q.1 : Matrix (Fin 7) (Fin 7) ℝ)
  rw [← splitMatrix_fiber_blockDiagonal Q]
  change (Matrix.reindex (@finSumFinEquiv 1 6) (@finSumFinEquiv 1 6))
      ((Matrix.reindex (@finSumFinEquiv 1 6) (@finSumFinEquiv 1 6)).symm
        (Q.1 : Matrix (Fin 7) (Fin 7) ℝ)) = _
  exact (Matrix.reindex (@finSumFinEquiv 1 6) (@finSumFinEquiv 1 6)).apply_symm_apply _

@[simp] public theorem lowerSpecialOrthogonal_stabilizeFiber (Q : SO6) :
    lowerSpecialOrthogonal (stabilizeFiber Q) = Q := by
  exact stabilizeFiber_injective
    (Subtype.ext (Subtype.ext (stabilizeMatrix_lowerBlock (stabilizeFiber Q))))

@[simp] public theorem stabilizeFiber_lowerSpecialOrthogonal (Q : StandardFiber) :
    stabilizeFiber (lowerSpecialOrthogonal Q) = Q := by
  exact Subtype.ext (Subtype.ext (stabilizeMatrix_lowerBlock Q))

/-- The standard fiber of `SO(7) → S⁶` is homeomorphic to `SO(6)`. -/
public def standardFiberHomeomorphSO6 : StandardFiber ≃ₜ SO6 where
  toFun := lowerSpecialOrthogonal
  invFun := stabilizeFiber
  left_inv := stabilizeFiber_lowerSpecialOrthogonal
  right_inv := lowerSpecialOrthogonal_stabilizeFiber
  continuous_toFun := continuous_lowerSpecialOrthogonal
  continuous_invFun := continuous_stabilizeFiber

/-- Point-set characterization of the image of the standard block inclusion. -/
public theorem mem_range_stabilize_iff (Q : SO7) :
    Q ∈ Set.range stabilize ↔ firstColumn Q = firstColumn (1 : SO7) := by
  constructor
  · rintro ⟨R, rfl⟩
    exact firstColumn_stabilize R
  · intro hQ
    let Q' : StandardFiber := ⟨Q, hQ⟩
    refine ⟨lowerSpecialOrthogonal Q', ?_⟩
    exact congr_arg Subtype.val (stabilizeFiber_lowerSpecialOrthogonal Q')

end SphereSixComplex.SpecialOrthogonalSevenStiefel
