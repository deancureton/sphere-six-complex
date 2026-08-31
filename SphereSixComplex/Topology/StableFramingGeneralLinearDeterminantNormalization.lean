module

public import SphereSixComplex.Topology.StableFramingSmoothClutchingNullhomotopy
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Determinant normalization for rank-seven clutching maps

This file starts the comparison of the clutching target `GL₇(ℝ)` with its connected
determinant-one subgroup.  It first records the elementary homotopy bookkeeping independently of
the matrix construction.  The matrix normalization below separates the two components of
`GL₇(ℝ)`, moves the negative component by a fixed orientation-reversing scalar, and continuously
rescales one coordinate so that the determinant is exactly one.  A later comparison can then
retract `SL₇(ℝ)` to the compact group `SO(7)`.
-/

@[expose] public section

noncomputable section

open ContinuousMap Matrix Set Topology
open scoped Classical MatrixGroups Topology

namespace SphereSixComplex

set_option maxRecDepth 10000

private abbrev StableFiveSphere := StableClutchingEquatorFiveSphere
private abbrev StableGLSeven := StableGeneralLinearSeven
private abbrev StableSevenMatrix := Matrix (Fin 7) (Fin 7) ℝ

/-- The matrix special linear group used after determinant normalization. -/
public abbrev StableSpecialLinearSeven := Matrix.SpecialLinearGroup (Fin 7) ℝ

/-- Nullhomotopy is invariant under replacing a map by an ordinarily homotopic map. -/
public theorem nullhomotopic_iff_of_homotopic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) :
    f.Nullhomotopic ↔ g.Nullhomotopic := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, h.symm.trans hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, h.trans hy⟩

/-- Postcomposition with a homotopy equivalence detects nullhomotopy. -/
public theorem nullhomotopic_comp_homotopyEquiv_iff
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₕ Z) (f : C(X, Y)) :
    (e.toFun.comp f).Nullhomotopic ↔ f.Nullhomotopic := by
  constructor
  · intro h
    have hback : (e.invFun.comp (e.toFun.comp f)).Nullhomotopic :=
      h.comp_right e.invFun
    have heq : (e.invFun.comp (e.toFun.comp f)).Homotopic f := by
      simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
        e.left_inv.comp (.refl f)
    exact (nullhomotopic_iff_of_homotopic heq).mp hback
  · exact fun h => h.comp_right e.toFun

/-- Put one unit in the first diagonal coordinate and ones elsewhere. -/
private def firstCoordinateUnit (u : ℝˣ) : (Fin 7 → ℝ)ˣ where
  val i := if i = 0 then u else 1
  inv i := if i = 0 then ↑u⁻¹ else 1
  val_inv := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  inv_val := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]

/-- The invertible diagonal matrix which scales only the first coordinate. -/
private def firstCoordinateDiagonal (u : ℝˣ) : StableGLSeven :=
  Units.map (Matrix.diagonalRingHom (Fin 7) ℝ) (firstCoordinateUnit u)

private theorem continuous_firstCoordinateUnit :
    Continuous firstCoordinateUnit := by
  rw [Units.continuous_iff]
  constructor
  · apply continuous_pi
    intro i
    by_cases hi : i = 0
    · simpa [firstCoordinateUnit, hi] using
        (Units.continuous_val : Continuous ((↑) : ℝˣ → ℝ))
    · simpa [firstCoordinateUnit, hi] using
        (continuous_const : Continuous (fun _ : ℝˣ ↦ (1 : ℝ)))
  · apply continuous_pi
    intro i
    by_cases hi : i = 0
    · simpa [firstCoordinateUnit, hi] using
        (Units.continuous_coe_inv : Continuous (fun u : ℝˣ ↦ (↑u⁻¹ : ℝ)))
    · simpa [firstCoordinateUnit, hi] using
        (continuous_const : Continuous (fun _ : ℝˣ ↦ (1 : ℝ)))

private theorem continuous_firstCoordinateDiagonal :
    Continuous firstCoordinateDiagonal := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous (fun u : ℝˣ ↦ Matrix.diagonal (firstCoordinateUnit u).val)
    exact (Units.continuous_val.comp continuous_firstCoordinateUnit).matrix_diagonal
  · change Continuous (fun u : ℝˣ ↦ Matrix.diagonal (firstCoordinateUnit u).inv)
    exact (Units.continuous_coe_inv.comp continuous_firstCoordinateUnit).matrix_diagonal

@[simp] private theorem det_firstCoordinateDiagonal (u : ℝˣ) :
    Matrix.GeneralLinearGroup.det (firstCoordinateDiagonal u) = u := by
  apply Units.ext
  simp [firstCoordinateDiagonal, firstCoordinateUnit, Matrix.det_diagonal,
    Matrix.GeneralLinearGroup.det]

@[simp] private theorem firstCoordinateDiagonal_one :
    firstCoordinateDiagonal (1 : ℝˣ) = 1 := by
  apply Units.ext
  simp [firstCoordinateDiagonal, firstCoordinateUnit]

private theorem stableFiveSphere_preconnected : PreconnectedSpace StableFiveSphere := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 6)) :=
    Module.one_lt_rank_of_one_lt_finrank (by
      rw [finrank_euclideanSpace_fin]
      norm_num)
  apply isPreconnected_iff_preconnectedSpace.mp
  exact isPreconnected_sphere (E := EuclideanSpace ℝ (Fin 6)) hrank 0 1

private theorem stableFiveSphere_nonempty : Nonempty StableFiveSphere := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 6)) :=
    Module.one_lt_rank_of_one_lt_finrank (by
      rw [finrank_euclideanSpace_fin]
      norm_num)
  exact (isConnected_sphere (E := EuclideanSpace ℝ (Fin 6))
    hrank 0 zero_le_one).nonempty.to_subtype

/-- The determinant of a continuous `GL₇`-valued map on `S⁵` has one sign. -/
private theorem det_mul_pos_of_continuousMap
    (g : C(StableFiveSphere, StableGLSeven)) (u v : StableFiveSphere) :
    0 < ((Matrix.GeneralLinearGroup.det (g u) : ℝ) *
      (Matrix.GeneralLinearGroup.det (g v) : ℝ)) := by
  let _ : PreconnectedSpace StableFiveSphere := stableFiveSphere_preconnected
  let d : StableFiveSphere → ℝ := fun w ↦ (Matrix.GeneralLinearGroup.det (g w) : ℝ)
  have hd : Continuous d :=
    Units.continuous_val.comp (Matrix.GeneralLinearGroup.continuous_det.comp g.continuous)
  have hne (w : StableFiveSphere) : d w ≠ 0 := (g w).det_ne_zero
  have same_pos (hu : 0 < d u) : 0 < d v := by
    by_contra hv
    have hvneg : d v < 0 := lt_of_le_of_ne (le_of_not_gt hv) (hne v)
    obtain ⟨w, hw⟩ := mem_range_of_exists_le_of_exists_ge (c := (0 : ℝ)) hd
      ⟨v, hvneg.le⟩ ⟨u, hu.le⟩
    exact hne w hw
  by_cases hu : 0 < d u
  · exact mul_pos hu (same_pos hu)
  · have huneg : d u < 0 := lt_of_le_of_ne (le_of_not_gt hu) (hne u)
    have hvneg : d v < 0 := by
      by_contra hv
      have hvpos : 0 < d v := lt_of_le_of_ne (le_of_not_gt hv) (hne v).symm
      obtain ⟨w, hw⟩ := mem_range_of_exists_le_of_exists_ge (c := (0 : ℝ)) hd
        ⟨u, huneg.le⟩ ⟨v, hvpos.le⟩
      exact hne w hw
    exact mul_pos_of_neg_of_neg huneg hvneg

private noncomputable def stableFiveSphereBase : StableFiveSphere :=
  Classical.choice stableFiveSphere_nonempty

/-- The fixed scalar which moves a family into the positive-determinant component. -/
private def orientationFactor (g : C(StableFiveSphere, StableGLSeven)) : StableGLSeven :=
  if 0 < (Matrix.GeneralLinearGroup.det (g stableFiveSphereBase) : ℝ) then 1 else -1

private def orientContinuousMap
    (g : C(StableFiveSphere, StableGLSeven)) : C(StableFiveSphere, StableGLSeven) where
  toFun u := orientationFactor g * g u
  continuous_toFun := continuous_const.mul g.continuous

private theorem orientContinuousMap_det_pos
    (g : C(StableFiveSphere, StableGLSeven)) (u : StableFiveSphere) :
    0 < (Matrix.GeneralLinearGroup.det (orientContinuousMap g u) : ℝ) := by
  have hsame := det_mul_pos_of_continuousMap g stableFiveSphereBase u
  by_cases hbase : 0 < (Matrix.GeneralLinearGroup.det (g stableFiveSphereBase) : ℝ)
  · have hu : 0 < (Matrix.GeneralLinearGroup.det (g u) : ℝ) :=
      pos_of_mul_pos_right hsame hbase.le
    have hfactor : orientationFactor g = 1 := by
      have hbase' : 0 < Matrix.det (g stableFiveSphereBase : StableSevenMatrix) := by
        simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hbase
      simp [orientationFactor, hbase']
    change 0 < (Matrix.GeneralLinearGroup.det (orientationFactor g * g u) : ℝ)
    rw [hfactor, one_mul]
    exact hu
  · have hbaseNeg : (Matrix.GeneralLinearGroup.det (g stableFiveSphereBase) : ℝ) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hbase) (g stableFiveSphereBase).det_ne_zero
    have huNeg : (Matrix.GeneralLinearGroup.det (g u) : ℝ) < 0 :=
      neg_of_mul_pos_right hsame hbaseNeg.le
    have hfactor : orientationFactor g = -1 := by
      have hbase' : ¬0 < Matrix.det (g stableFiveSphereBase : StableSevenMatrix) := by
        simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hbase
      simp [orientationFactor, hbase']
    change 0 < (Matrix.GeneralLinearGroup.det (orientationFactor g * g u) : ℝ)
    rw [hfactor, neg_one_mul]
    have hneg : (-g u : StableGLSeven) = (-1 : StableGLSeven) * g u := by simp
    have hscalar : (-1 : StableGLSeven) =
        Matrix.GeneralLinearGroup.scalar (Fin 7) (-1 : ℝˣ) := by
      apply Units.ext
      ext i j
      change (-(1 : StableSevenMatrix)) i j = (Matrix.scalar (Fin 7) (-1 : ℝ)) i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, hij]
    have hdetNegOne :
        Matrix.GeneralLinearGroup.det (-1 : StableGLSeven) = (-1 : ℝˣ) := by
      rw [hscalar, Matrix.GeneralLinearGroup.det_scalar]
      apply Units.ext
      norm_num
    rw [hneg, map_mul, hdetNegOne]
    change 0 < (-1 : ℝ) * (Matrix.GeneralLinearGroup.det (g u) : ℝ)
    simpa only [neg_one_mul] using (neg_pos.mpr huNeg)

/-- Normalize a positive-determinant family by changing only its first row. -/
private def specialLinearRepresentative
    (g : C(StableFiveSphere, StableGLSeven)) : C(StableFiveSphere, StableSpecialLinearSeven) where
  toFun u :=
    ⟨((firstCoordinateDiagonal (Matrix.GeneralLinearGroup.det (g u))⁻¹ * g u :
        StableGLSeven) : StableSevenMatrix), by
      have hdet : Matrix.GeneralLinearGroup.det
          (firstCoordinateDiagonal (Matrix.GeneralLinearGroup.det (g u))⁻¹ * g u) = 1 := by
        rw [map_mul, det_firstCoordinateDiagonal, inv_mul_cancel]
      simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
        congrArg (fun x : ℝˣ ↦ (x : ℝ)) hdet⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Units.continuous_val.comp
      ((continuous_firstCoordinateDiagonal.comp
        (continuous_inv.comp (Matrix.GeneralLinearGroup.continuous_det.comp g.continuous))).mul
          g.continuous)

private def determinantInterpolationValue
    (g : C(StableFiveSphere, StableGLSeven)) (z : unitInterval × StableFiveSphere) : ℝ :=
  (1 - (z.1 : ℝ)) + (z.1 : ℝ) *
    ((Matrix.GeneralLinearGroup.det (g z.2) : ℝ)⁻¹)

private theorem determinantInterpolationValue_pos
    (g : C(StableFiveSphere, StableGLSeven))
    (hg : ∀ u, 0 < (Matrix.GeneralLinearGroup.det (g u) : ℝ))
    (z : unitInterval × StableFiveSphere) : 0 < determinantInterpolationValue g z := by
  have hdinv : 0 < ((Matrix.GeneralLinearGroup.det (g z.2) : ℝ)⁻¹) :=
    inv_pos.mpr (hg z.2)
  by_cases ht : (z.1 : ℝ) = 0
  · simp [determinantInterpolationValue, ht]
  · have htpos : 0 < (z.1 : ℝ) := lt_of_le_of_ne z.1.property.1 (Ne.symm ht)
    have hone : 0 ≤ 1 - (z.1 : ℝ) := sub_nonneg.mpr z.1.property.2
    exact add_pos_of_nonneg_of_pos hone (mul_pos htpos hdinv)

private def determinantInterpolationUnit
    (g : C(StableFiveSphere, StableGLSeven))
    (hg : ∀ u, 0 < (Matrix.GeneralLinearGroup.det (g u) : ℝ))
    (z : unitInterval × StableFiveSphere) : ℝˣ :=
  Units.mk0 (determinantInterpolationValue g z)
    (determinantInterpolationValue_pos g hg z).ne'

private theorem continuous_determinantInterpolationUnit
    (g : C(StableFiveSphere, StableGLSeven))
    (hg : ∀ u, 0 < (Matrix.GeneralLinearGroup.det (g u) : ℝ)) :
    Continuous (determinantInterpolationUnit g hg) := by
  have hd : Continuous (fun z : unitInterval × StableFiveSphere ↦
      (Matrix.GeneralLinearGroup.det (g z.2) : ℝ)) :=
    Units.continuous_val.comp
      (Matrix.GeneralLinearGroup.continuous_det.comp (g.continuous.comp continuous_snd))
  have hv : Continuous (determinantInterpolationValue g) := by
    exact (continuous_const.sub continuous_subtype_val.fst').add
      (continuous_subtype_val.fst'.mul (hd.inv₀ fun z ↦ (g z.2).det_ne_zero))
  rw [Units.continuous_iff]
  exact ⟨hv, hv.inv₀ fun z ↦ (determinantInterpolationValue_pos g hg z).ne'⟩

/-- The continuous inclusion `SL₇(ℝ) → GL₇(ℝ)`. -/
public def specialLinearSevenInclusion :
    C(StableSpecialLinearSeven, StableGeneralLinearSeven) :=
  ⟨Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.continuous_toGL⟩

/-- Positive-determinant `GL₇` families are homotopic to the inclusion of an `SL₇` family. -/
private def homotopy_specialLinearRepresentative
    (g : C(StableFiveSphere, StableGLSeven))
    (hg : ∀ u, 0 < (Matrix.GeneralLinearGroup.det (g u) : ℝ)) :
    g.Homotopy (specialLinearSevenInclusion.comp (specialLinearRepresentative g)) where
  toFun z := firstCoordinateDiagonal (determinantInterpolationUnit g hg z) * g z.2
  continuous_toFun := (continuous_firstCoordinateDiagonal.comp
    (continuous_determinantInterpolationUnit g hg)).mul (g.continuous.comp continuous_snd)
  map_zero_left u := by
    change firstCoordinateDiagonal (determinantInterpolationUnit g hg (0, u)) * g u = g u
    have hu : determinantInterpolationUnit g hg (0, u) = 1 := by
      apply Units.ext
      simp [determinantInterpolationUnit, determinantInterpolationValue]
    rw [hu, firstCoordinateDiagonal_one, one_mul]
  map_one_left u := by
    have hu : determinantInterpolationUnit g hg (1, u) =
        (Matrix.GeneralLinearGroup.det (g u))⁻¹ := by
      apply Units.ext
      simp [determinantInterpolationUnit, determinantInterpolationValue]
    rw [hu]
    apply Units.ext
    rfl

/-- The exact reduced input after removing the determinant component and radial scale. -/
public def SpecialLinearSevenFiveSphereNullhomotopyVanishing : Prop :=
  ∀ f : C(StableClutchingEquatorFiveSphere, StableSpecialLinearSeven),
    (specialLinearSevenInclusion.comp f).Nullhomotopic

/-- Representative-level `π₅(SL₇(ℝ)) = 0` implies the required
representative-level `π₅(GL₇(ℝ)) = 0`. -/
public theorem topologicalGLSevenFiveSphereNullhomotopyVanishing_of_specialLinear
    (hSL : SpecialLinearSevenFiveSphereNullhomotopyVanishing) :
    TopologicalGLSevenFiveSphereNullhomotopyVanishing := by
  intro g
  let gpos : C(StableFiveSphere, StableGLSeven) := orientContinuousMap g
  have hgpos : ∀ u, 0 < (Matrix.GeneralLinearGroup.det (gpos u) : ℝ) :=
    orientContinuousMap_det_pos g
  let f : C(StableFiveSphere, StableSpecialLinearSeven) := specialLinearRepresentative gpos
  have hnorm : gpos.Homotopic (specialLinearSevenInclusion.comp f) :=
    ⟨homotopy_specialLinearRepresentative gpos hgpos⟩
  obtain ⟨base, hbase⟩ := hSL f
  have hgplusNull : gpos.Nullhomotopic := ⟨base, hnorm.trans hbase⟩
  let undo : C(StableGLSeven, StableGLSeven) :=
    ⟨fun A ↦ (orientationFactor g)⁻¹ * A, continuous_const.mul continuous_id⟩
  have hundone := hgplusNull.comp_right undo
  have heq : undo.comp gpos = g := by
    ext u
    simp [undo, gpos, orientContinuousMap]
  rw [heq] at hundone
  exact hundone

/-- Buffered radial presentation existence and the `SL₇` representative computation imply the
original exact hemispherical clutching-extension theorem. -/
public theorem
    homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_buffered_and_specialLinear
    (hgeometry : HomotopySixSphereBufferedRadialRankSevenClutchingPresentation)
    (hSL : SpecialLinearSevenFiveSphereNullhomotopyVanishing) :
    HomotopySixSphereHemisphericalRankSevenClutchingVanishing :=
  homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_buffered_and_topological_piFive
    hgeometry (topologicalGLSevenFiveSphereNullhomotopyVanishing_of_specialLinear hSL)

end SphereSixComplex
