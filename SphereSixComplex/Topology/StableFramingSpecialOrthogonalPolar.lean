module

public import SphereSixComplex.Topology.StableFramingGeneralLinearDeterminantNormalization
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Polar reduction of rank-seven clutching maps

This file completes the comparison of `SL₇(ℝ)` with its maximal compact subgroup `SO(7)`.
For `A ∈ SL₇(ℝ)`, put `P = AᵀA` and use the explicit polar deformation

`H(A,t) = A P⁻ᵗ/²`.

The continuous functional calculus proves joint continuity in `A` and `t`.  Positivity of `P`
shows that every power is invertible, while a spectral determinant calculation shows that the
whole path has determinant one.  At `t = 1` its value is special orthogonal, and the path fixes
`SO(7)` pointwise.  Thus it gives an actual homotopy equivalence `SL₇(ℝ) ≃ SO(7)`, not merely a
pointwise polar decomposition.
-/

@[expose] public section

noncomputable section

open ContinuousMap Matrix Set Topology
open scoped Classical MatrixGroups MatrixOrder Matrix.Norms.L2Operator Topology

namespace SphereSixComplex

set_option maxRecDepth 100000

public abbrev StableSpecialOrthogonalSeven := Matrix.specialOrthogonalGroup (Fin 7) ℝ

public abbrev StableSevenRealMatrix := Matrix (Fin 7) (Fin 7) ℝ

/-- The positive-definite Gram matrix `AᵀA`. -/
public noncomputable def stablePolarGram
    (A : StableSpecialLinearSeven) : StableSevenRealMatrix :=
  (A : StableSevenRealMatrix)ᵀ * (A : StableSevenRealMatrix)

public theorem stableSpecialLinearSeven_coe_isUnit
    (A : StableSpecialLinearSeven) : IsUnit (A : StableSevenRealMatrix) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp

public theorem stablePolarGram_posDef
    (A : StableSpecialLinearSeven) : (stablePolarGram A).PosDef := by
  rw [stablePolarGram]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self (A : StableSevenRealMatrix)
      (Matrix.mulVec_injective_iff_isUnit.mpr
        (stableSpecialLinearSeven_coe_isUnit A))

public theorem stablePolarGram_isStrictlyPositive
    (A : StableSpecialLinearSeven) : IsStrictlyPositive (stablePolarGram A) :=
  (stablePolarGram_posDef A).isStrictlyPositive

/-- The functional-calculus factor `(AᵀA)⁻ᵗ/²`. -/
public noncomputable def stablePolarScale
    (A : StableSpecialLinearSeven) (t : ℝ) : StableSevenRealMatrix :=
  CFC.rpow (stablePolarGram A) (-t / 2)

/-- The matrix-valued polar path `A(AᵀA)⁻ᵗ/²`. -/
public noncomputable def stablePolarPath
    (A : StableSpecialLinearSeven) (t : ℝ) : StableSevenRealMatrix :=
  (A : StableSevenRealMatrix) * stablePolarScale A t

public theorem stablePolarScale_isUnit
    (A : StableSpecialLinearSeven) (t : ℝ) : IsUnit (stablePolarScale A t) := by
  exact (stablePolarGram_posDef A).isUnit.cfcRpow (-t / 2)
    (stablePolarGram_posDef A).posSemidef.nonneg

public theorem stablePolarPath_isUnit
    (A : StableSpecialLinearSeven) (t : ℝ) : IsUnit (stablePolarPath A t) :=
  (stableSpecialLinearSeven_coe_isUnit A).mul (stablePolarScale_isUnit A t)

public theorem continuous_stablePolarGram : Continuous stablePolarGram := by
  unfold stablePolarGram
  fun_prop

public theorem continuous_stablePolarScale_fixed (t : ℝ) :
    Continuous (fun A : StableSpecialLinearSeven ↦ stablePolarScale A t) := by
  rw [← continuousOn_univ]
  exact (CFC.continuousOn_rpow (-t / 2)).comp continuous_stablePolarGram.continuousOn
    (fun A _ ↦ stablePolarGram_isStrictlyPositive A)

/-- On a positive-definite matrix, functional-calculus real powers are exponentials of logs. -/
public theorem cfc_rpow_eq_exp_smul_log
    {P : StableSevenRealMatrix} (hP : P.PosDef) (r : ℝ) :
    CFC.rpow P r = NormedSpace.exp (r • CFC.log P) := by
  have hpos : ∀ x ∈ spectrum ℝ P, 0 < x :=
    fun _ hx ↦ hP.isStrictlyPositive.spectrum_pos hx
  have hlog : ContinuousOn Real.log (spectrum ℝ P) :=
    continuousOn_id.log (fun x hx ↦ (hpos x hx).ne')
  have hf : ContinuousOn (fun x : ℝ ↦ r * Real.log x) (spectrum ℝ P) :=
    continuousOn_const.mul hlog
  change P ^ r = NormedSpace.exp (r • CFC.log P)
  rw [CFC.rpow_eq_cfc_real hP.posSemidef.nonneg]
  calc
    cfc (fun x : ℝ ↦ x ^ r) P = cfc (fun x : ℝ ↦ Real.exp (r * Real.log x)) P := by
      apply cfc_congr
      intro x hx
      change x ^ r = Real.exp (r * Real.log x)
      rw [Real.rpow_def_of_pos (hpos x hx)]
      congr 1
      ring
    _ = cfc Real.exp (cfc (fun x : ℝ ↦ r * Real.log x) P) := by
      exact cfc_comp' Real.exp (fun x : ℝ ↦ r * Real.log x) P
        (by fun_prop) hf hP.isHermitian
    _ = cfc Real.exp (r • CFC.log P) := by
      rw [cfc_const_mul r Real.log P hlog]
      rfl
    _ = NormedSpace.exp (r • CFC.log P) := by
      exact CFC.real_exp_eq_normedSpace_exp (by cfc_tac)

public theorem continuous_stablePolarLogGram :
    Continuous (fun A : StableSpecialLinearSeven ↦ CFC.log (stablePolarGram A)) := by
  rw [← continuousOn_univ]
  exact CFC.continuousOn_log.comp continuous_stablePolarGram.continuousOn
    (fun A _ ↦ ⟨(stablePolarGram_posDef A).isHermitian,
      (stablePolarGram_posDef A).isUnit⟩)

/-- The polar scale is jointly continuous in the matrix and real exponent. -/
public theorem continuous_stablePolarScale :
    Continuous (fun p : StableSpecialLinearSeven × ℝ ↦ stablePolarScale p.1 p.2) := by
  let _ : NormedAlgebra ℚ StableSevenRealMatrix :=
    .restrictScalars ℚ ℝ StableSevenRealMatrix
  have hexp : Continuous (fun p : StableSpecialLinearSeven × ℝ ↦
      NormedSpace.exp ((-p.2 / 2) • CFC.log (stablePolarGram p.1))) := by
    apply NormedSpace.exp_continuous.comp
    have hs : Continuous (fun p : StableSpecialLinearSeven × ℝ ↦ -p.2 / 2) := by
      fun_prop
    exact hs.smul (continuous_stablePolarLogGram.comp continuous_fst)
  apply hexp.congr
  intro p
  exact (cfc_rpow_eq_exp_smul_log (stablePolarGram_posDef p.1) (-p.2 / 2)).symm

public theorem continuous_stablePolarPath :
    Continuous (fun p : StableSpecialLinearSeven × ℝ ↦ stablePolarPath p.1 p.2) := by
  unfold stablePolarPath
  exact (continuous_subtype_val.comp continuous_fst).mul continuous_stablePolarScale

public theorem continuous_stablePolarPath_fixed (t : ℝ) :
    Continuous (fun A : StableSpecialLinearSeven ↦ stablePolarPath A t) := by
  unfold stablePolarPath
  exact continuous_subtype_val.mul (continuous_stablePolarScale_fixed t)

@[simp] public theorem stablePolarPath_zero (A : StableSpecialLinearSeven) :
    stablePolarPath A 0 = (A : StableSevenRealMatrix) := by
  simp [stablePolarPath, stablePolarScale, CFC.rpow_zero,
    (stablePolarGram_posDef A).posSemidef.nonneg]

public theorem stablePolarGram_det (A : StableSpecialLinearSeven) :
    (stablePolarGram A).det = 1 := by
  simp [stablePolarGram, Matrix.det_mul]

/-- Spectral determinant formula for a real power of a positive-definite seven-matrix. -/
public theorem det_cfc_rpow_of_posDef
    {P : StableSevenRealMatrix} (hP : P.PosDef) (r : ℝ) :
    (CFC.rpow P r).det = P.det ^ r := by
  change (P ^ r).det = P.det ^ r
  rw [CFC.rpow_eq_cfc_real hP.posSemidef.nonneg, hP.isHermitian.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Matrix.det_map, Matrix.det_diagonal,
    Function.comp_apply, hP.isHermitian.det_eq_prod_eigenvalues]
  exact Real.finsetProd_rpow Finset.univ _
    (fun i _ ↦ (hP.eigenvalues_pos i).le) r

@[simp] public theorem stablePolarScale_det
    (A : StableSpecialLinearSeven) (t : ℝ) : (stablePolarScale A t).det = 1 := by
  rw [stablePolarScale, det_cfc_rpow_of_posDef (stablePolarGram_posDef A),
    stablePolarGram_det]
  exact Real.one_rpow _

@[simp] public theorem stablePolarPath_det
    (A : StableSpecialLinearSeven) (t : ℝ) : (stablePolarPath A t).det = 1 := by
  simp [stablePolarPath, Matrix.det_mul]

/-- The polar path, regarded as a path entirely inside `SL₇(ℝ)`. -/
public noncomputable def stablePolarSpecialLinearPath
    (A : StableSpecialLinearSeven) (t : ℝ) : StableSpecialLinearSeven :=
  ⟨stablePolarPath A t, stablePolarPath_det A t⟩

public theorem continuous_stablePolarSpecialLinearPath :
    Continuous (fun p : StableSpecialLinearSeven × ℝ ↦
      stablePolarSpecialLinearPath p.1 p.2) := by
  apply continuous_induced_rng.mpr
  exact continuous_stablePolarPath

public theorem stablePolarScale_transpose
    (A : StableSpecialLinearSeven) (t : ℝ) :
    (stablePolarScale A t)ᵀ = stablePolarScale A t := by
  have hnonneg : (0 : StableSevenRealMatrix) ≤ stablePolarScale A t := CFC.rpow_nonneg
  have h := hnonneg.posSemidef.isHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

public theorem stablePolarScale_one_sandwich (A : StableSpecialLinearSeven) :
    stablePolarScale A 1 * stablePolarGram A * stablePolarScale A 1 = 1 := by
  have hnonneg := (stablePolarGram_posDef A).posSemidef.nonneg
  have hunit := (stablePolarGram_posDef A).isUnit
  change (stablePolarGram A) ^ (-1 / 2 : ℝ) * stablePolarGram A *
    (stablePolarGram A) ^ (-1 / 2 : ℝ) = 1
  calc
    _ = (stablePolarGram A) ^ (-1 / 2 : ℝ) * (stablePolarGram A) ^ (1 : ℝ) *
        (stablePolarGram A) ^ (-1 / 2 : ℝ) := by
      congr 2
      exact (CFC.rpow_one (stablePolarGram A) hnonneg).symm
    _ = (stablePolarGram A) ^ ((-1 / 2 : ℝ) + 1) *
        (stablePolarGram A) ^ (-1 / 2 : ℝ) := by
      rw [CFC.rpow_add hunit]
    _ = (stablePolarGram A) ^ (((-1 / 2 : ℝ) + 1) + (-1 / 2 : ℝ)) := by
      exact (CFC.rpow_add (a := stablePolarGram A) (x := (-1 / 2 : ℝ) + 1)
        (y := -1 / 2) hunit).symm
    _ = 1 := by
      norm_num [CFC.rpow_zero (stablePolarGram A) hnonneg]

public theorem stablePolarPath_one_orthogonal (A : StableSpecialLinearSeven) :
    stablePolarPath A 1 ∈ Matrix.orthogonalGroup (Fin 7) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  rw [stablePolarPath, Matrix.transpose_mul, stablePolarScale_transpose]
  simpa only [Matrix.mul_assoc, stablePolarGram] using stablePolarScale_one_sandwich A

public theorem stablePolarPath_one_mem_specialOrthogonal
    (A : StableSpecialLinearSeven) :
    stablePolarPath A 1 ∈ StableSpecialOrthogonalSeven := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨stablePolarPath_one_orthogonal A, stablePolarPath_det A 1⟩

/-- The polar retraction `SL₇(ℝ) → SO(7)`. -/
public noncomputable def specialOrthogonalSevenProjection :
    C(StableSpecialLinearSeven, StableSpecialOrthogonalSeven) where
  toFun A := ⟨stablePolarPath A 1, stablePolarPath_one_mem_specialOrthogonal A⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_stablePolarPath_fixed 1

/-- The tautological inclusion `SO(7) → SL₇(ℝ)`. -/
public def specialOrthogonalSevenInclusion :
    C(StableSpecialOrthogonalSeven, StableSpecialLinearSeven) where
  toFun Q := ⟨Q, Q.property.2⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val

@[simp] public theorem specialOrthogonalSevenInclusion_coe
    (Q : StableSpecialOrthogonalSeven) :
    ((specialOrthogonalSevenInclusion Q : StableSpecialLinearSeven) :
      StableSevenRealMatrix) = (Q : StableSevenRealMatrix) :=
  rfl

public theorem stablePolarGram_specialOrthogonalSevenInclusion
    (Q : StableSpecialOrthogonalSeven) :
    stablePolarGram (specialOrthogonalSevenInclusion Q) = 1 := by
  rw [stablePolarGram, specialOrthogonalSevenInclusion_coe]
  exact (Matrix.mem_orthogonalGroup_iff' (Fin 7) ℝ).mp Q.property.1

/-- The polar retraction is a left inverse to the inclusion of `SO(7)`. -/
@[simp] public theorem specialOrthogonalSevenProjection_inclusion
    (Q : StableSpecialOrthogonalSeven) :
    specialOrthogonalSevenProjection (specialOrthogonalSevenInclusion Q) = Q := by
  apply Subtype.ext
  change stablePolarPath (specialOrthogonalSevenInclusion Q) 1 =
    (Q : StableSevenRealMatrix)
  rw [stablePolarPath, stablePolarScale,
    stablePolarGram_specialOrthogonalSevenInclusion]
  rw [specialOrthogonalSevenInclusion_coe]
  simp

/-- The entire polar path fixes `SO(7)` pointwise. -/
@[simp] public theorem stablePolarSpecialLinearPath_inclusion
    (Q : StableSpecialOrthogonalSeven) (t : ℝ) :
    stablePolarSpecialLinearPath (specialOrthogonalSevenInclusion Q) t =
      specialOrthogonalSevenInclusion Q := by
  apply Subtype.ext
  simp [stablePolarSpecialLinearPath, stablePolarPath, stablePolarScale,
    stablePolarGram_specialOrthogonalSevenInclusion]

/-- The strong polar deformation from the identity of `SL₇(ℝ)` to the `SO(7)` projection. -/
public noncomputable def specialLinearSevenPolarDeformation :
    (ContinuousMap.id StableSpecialLinearSeven).Homotopy
      (specialOrthogonalSevenInclusion.comp specialOrthogonalSevenProjection) where
  toFun z := stablePolarSpecialLinearPath z.2 z.1
  continuous_toFun := continuous_stablePolarSpecialLinearPath.comp
    (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
  map_zero_left A := by
    apply Subtype.ext
    exact stablePolarPath_zero A
  map_one_left A := by
    rfl

/-- The polar deformation fixes the embedded copy of `SO(7)` at every time. -/
@[simp] public theorem specialLinearSevenPolarDeformation_inclusion
    (t : unitInterval) (Q : StableSpecialOrthogonalSeven) :
    specialLinearSevenPolarDeformation
      (t, specialOrthogonalSevenInclusion Q) = specialOrthogonalSevenInclusion Q :=
  stablePolarSpecialLinearPath_inclusion Q t

@[simp] public theorem specialOrthogonalSevenProjection_comp_inclusion :
    specialOrthogonalSevenProjection.comp specialOrthogonalSevenInclusion =
      ContinuousMap.id StableSpecialOrthogonalSeven := by
  apply ContinuousMap.ext
  exact specialOrthogonalSevenProjection_inclusion

/-- Polar decomposition gives the homotopy equivalence `SL₇(ℝ) ≃ SO(7)`. -/
public noncomputable def specialLinearSevenHomotopyEquivSpecialOrthogonalSeven :
    StableSpecialLinearSeven ≃ₕ StableSpecialOrthogonalSeven where
  toFun := specialOrthogonalSevenProjection
  invFun := specialOrthogonalSevenInclusion
  left_inv := ⟨specialLinearSevenPolarDeformation.symm⟩
  right_inv := by
    rw [specialOrthogonalSevenProjection_comp_inclusion]

/-- Representative-level `π₅(SO(7)) = 0`. -/
public def SpecialOrthogonalSevenFiveSphereNullhomotopyVanishing : Prop :=
  ∀ f : C(StableClutchingEquatorFiveSphere, StableSpecialOrthogonalSeven),
    f.Nullhomotopic

/-- The polar equivalence transports representative-level `π₅(SO(7))` vanishing to the
existing `SL₇` obligation. -/
public theorem specialLinearSevenFiveSphereNullhomotopyVanishing_of_specialOrthogonal
    (hSO : SpecialOrthogonalSevenFiveSphereNullhomotopyVanishing) :
    SpecialLinearSevenFiveSphereNullhomotopyVanishing := by
  intro f
  have hprojection : (specialOrthogonalSevenProjection.comp f).Nullhomotopic :=
    hSO (specialOrthogonalSevenProjection.comp f)
  have hf : f.Nullhomotopic :=
    (nullhomotopic_comp_homotopyEquiv_iff
      specialLinearSevenHomotopyEquivSpecialOrthogonalSeven f).mp hprojection
  exact hf.comp_right specialLinearSevenInclusion

/-- The compact-group computation implies the existing `GL₇` clutching-map obligation. -/
public theorem topologicalGLSevenFiveSphereNullhomotopyVanishing_of_specialOrthogonal
    (hSO : SpecialOrthogonalSevenFiveSphereNullhomotopyVanishing) :
    TopologicalGLSevenFiveSphereNullhomotopyVanishing :=
  topologicalGLSevenFiveSphereNullhomotopyVanishing_of_specialLinear
    (specialLinearSevenFiveSphereNullhomotopyVanishing_of_specialOrthogonal hSO)

/-- Buffered radial geometry and representative-level `π₅(SO(7)) = 0` imply the original
rank-seven hemispherical clutching-extension theorem. -/
public theorem
    homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_buffered_and_specialOrthogonal
    (hgeometry : HomotopySixSphereBufferedRadialRankSevenClutchingPresentation)
    (hSO : SpecialOrthogonalSevenFiveSphereNullhomotopyVanishing) :
    HomotopySixSphereHemisphericalRankSevenClutchingVanishing :=
  homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_buffered_and_specialLinear
    hgeometry (specialLinearSevenFiveSphereNullhomotopyVanishing_of_specialOrthogonal hSO)

end SphereSixComplex
