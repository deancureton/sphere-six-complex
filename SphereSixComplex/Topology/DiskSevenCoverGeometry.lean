module

public import SphereSixComplex.Topology.SingularExcision
public import SphereSixComplex.Topology.CollarHomotopyExtension
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Geometry of the concrete two-member cover of the seven-disk

This file records explicit radial geometry for `diskSevenExcisionCover`.  The true member is the
open disk.  The false member is the disk with its centre removed, and radially deformation
retracts onto the boundary.  Their intersection is the punctured open disk.
-/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousMap Function Metric Set Topology

namespace SphereSixComplex

/-- The true member is definitionally the complement of the disk boundary, hence is homeomorphic
to the standard open seven-ball. -/
public noncomputable def diskSevenCoverTrueHomeomorphBall :
    (diskSevenExcisionCover true : Set (TopCat.disk.{0} 7)) ≃ₜ
      (TopCat.ball.{0} 7 : Type) := by
  change CollapseComplement (TopCat.diskBoundaryInclusion.{0} 7) ≃ₜ _
  exact diskSevenComplementBoundaryHomeomorphBall

set_option linter.style.haveILetI false in
/-- The true cover member is contractible. -/
public theorem diskSevenCoverTrue_contractibleSpace :
    ContractibleSpace (diskSevenExcisionCover true : Set (TopCat.disk.{0} 7)) := by
  letI : ContractibleSpace
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 7)) 1) :=
    Metric.contractibleSpace_ball (by norm_num)
  letI : ContractibleSpace (TopCat.ball.{0} 7 : Type) := by
    change ContractibleSpace
      (ULift (Metric.ball (0 : EuclideanSpace ℝ (Fin 7)) 1))
    exact (Homeomorph.ulift :
      ULift (Metric.ball (0 : EuclideanSpace ℝ (Fin 7)) 1) ≃ₜ
        Metric.ball (0 : EuclideanSpace ℝ (Fin 7)) 1).contractibleSpace
  exact diskSevenCoverTrueHomeomorphBall.contractibleSpace

/-- The ambient Euclidean vector underlying a point of the seven-disk. -/
public def diskSevenVector (x : TopCat.disk.{0} 7) :
    EuclideanSpace ℝ (Fin 7) :=
  x.down.1

@[simp]
public theorem diskSevenVector_center :
    diskSevenVector diskSevenCenter = 0 := by
  rfl

/-- A point in the false cover member has a nonzero underlying vector. -/
public theorem diskSevenVector_ne_zero_of_mem_false
    (x : diskSevenExcisionCover false) : diskSevenVector x.1 ≠ 0 := by
  intro hx
  have hxc : x.1 = diskSevenCenter := by
    apply ULift.ext
    apply Subtype.ext
    exact hx
  have hxmem : x.1 ≠ diskSevenCenter := by
    simpa [diskSevenExcisionCover] using x.2
  exact hxmem hxc

/-- A point in the false member has strictly positive radius. -/
public theorem diskSevenNorm_pos_of_mem_false
    (x : diskSevenExcisionCover false) : 0 < ‖diskSevenVector x.1‖ :=
  norm_pos_iff.mpr (diskSevenVector_ne_zero_of_mem_false x)

/-- Radial normalization from the punctured disk to its boundary sphere. -/
public def diskSevenFalseRadialRetractionFunction
    (x : diskSevenExcisionCover false) : TopCat.sphere.{0} 6 :=
  ULift.up ⟨‖diskSevenVector x.1‖⁻¹ • diskSevenVector x.1, by
    have hn := diskSevenNorm_pos_of_mem_false x
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm]
    exact inv_mul_cancel₀ hn.ne'⟩

/-- Radial normalization is continuous on the disk with its centre removed. -/
public theorem continuous_diskSevenFalseRadialRetractionFunction :
    Continuous diskSevenFalseRadialRetractionFunction := by
  unfold diskSevenFalseRadialRetractionFunction
  apply continuous_uliftUp.comp
  apply Continuous.subtype_mk
  have hv : Continuous (fun x : diskSevenExcisionCover false ↦
      diskSevenVector x.1) :=
    (continuous_subtype_val.comp continuous_uliftDown).comp
      continuous_subtype_val
  exact (hv.norm.inv₀ (fun x ↦
    (diskSevenNorm_pos_of_mem_false x).ne')).smul hv

/-- Radial normalization as a morphism of topological spaces. -/
public noncomputable def diskSevenFalseRadialRetraction :
    TopCat.of (diskSevenExcisionCover false) ⟶ TopCat.sphere.{0} 6 :=
  TopCat.ofHom
    ⟨diskSevenFalseRadialRetractionFunction,
      continuous_diskSevenFalseRadialRetractionFunction⟩

@[simp]
public theorem diskSevenFalseRadialRetraction_down (x : diskSevenExcisionCover false) :
    (diskSevenFalseRadialRetraction x).down.1 =
      ‖diskSevenVector x.1‖⁻¹ • diskSevenVector x.1 :=
  rfl

@[simp]
public theorem diskBoundaryToDiskSevenExcisionCoverFalse_vector
    (x : TopCat.sphere.{0} 6) :
    diskSevenVector (diskBoundaryToDiskSevenExcisionCoverFalse x).1 = x.down.1 :=
  rfl

/-- Radial normalization is a left inverse to the boundary inclusion into the false member. -/
public theorem diskBoundaryToDiskSevenExcisionCoverFalse_comp_radialRetraction :
    diskBoundaryToDiskSevenExcisionCoverFalse ≫
        diskSevenFalseRadialRetraction =
      𝟙 (TopCat.sphere.{0} 6) := by
  ext x
  apply ULift.ext
  apply Subtype.ext
  change ‖x.down.1‖⁻¹ • x.down.1 = x.down.1
  have hx : ‖x.down.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.down.2
  simp [hx]

/-- Every disk point has radius at most one. -/
public theorem diskSevenNorm_le_one (x : TopCat.disk.{0} 7) :
    ‖diskSevenVector x‖ ≤ 1 := by
  simpa only [diskSevenVector, Metric.mem_closedBall, dist_zero_right] using x.down.2

/-- The radial homotopy interpolates between normalization and the original radius. -/
public def diskSevenFalseRadialScale (t : unitInterval)
    (x : diskSevenExcisionCover false) : ℝ :=
  (t : ℝ) + (1 - (t : ℝ)) * ‖diskSevenVector x.1‖⁻¹

/-- The radial scaling factor is always positive. -/
public theorem diskSevenFalseRadialScale_pos (t : unitInterval)
    (x : diskSevenExcisionCover false) :
    0 < diskSevenFalseRadialScale t x := by
  have hinv : 0 < ‖diskSevenVector x.1‖⁻¹ :=
    inv_pos.mpr (diskSevenNorm_pos_of_mem_false x)
  by_cases ht : (t : ℝ) = 0
  · simp [diskSevenFalseRadialScale, ht, hinv]
  · exact add_pos_of_pos_of_nonneg
      (lt_of_le_of_ne t.2.1 (Ne.symm ht))
      (mul_nonneg (sub_nonneg.mpr t.2.2) hinv.le)

/-- Radial interpolation stays in the closed unit disk. -/
public theorem norm_diskSevenFalseRadialScale_smul_le_one
    (t : unitInterval) (x : diskSevenExcisionCover false) :
    ‖diskSevenFalseRadialScale t x • diskSevenVector x.1‖ ≤ 1 := by
  have hn := diskSevenNorm_pos_of_mem_false x
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (diskSevenFalseRadialScale_pos t x)]
  change (((t : ℝ) + (1 - (t : ℝ)) * ‖diskSevenVector x.1‖⁻¹) *
    ‖diskSevenVector x.1‖) ≤ 1
  rw [add_mul, mul_assoc, inv_mul_cancel₀ hn.ne', mul_one]
  calc
    (t : ℝ) * ‖diskSevenVector x.1‖ + (1 - (t : ℝ)) ≤
        (t : ℝ) * 1 + (1 - (t : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (diskSevenNorm_le_one x.1) t.2.1) le_rfl
    _ = 1 := by ring

/-- The explicit radial homotopy on the disk with its centre removed. -/
public def diskSevenFalseRadialHomotopyFunction
    (p : unitInterval × diskSevenExcisionCover false) :
    diskSevenExcisionCover false :=
  ⟨ULift.up ⟨diskSevenFalseRadialScale p.1 p.2 • diskSevenVector p.2.1,
      by simpa only [Metric.mem_closedBall, dist_zero_right] using
        norm_diskSevenFalseRadialScale_smul_le_one p.1 p.2⟩, by
    change (ULift.up ⟨diskSevenFalseRadialScale p.1 p.2 •
      diskSevenVector p.2.1, _⟩ : TopCat.disk.{0} 7) ≠ diskSevenCenter
    intro h
    have hv := congrArg diskSevenVector h
    change diskSevenFalseRadialScale p.1 p.2 •
      diskSevenVector p.2.1 = diskSevenVector diskSevenCenter at hv
    rw [diskSevenVector_center] at hv
    exact (smul_ne_zero (ne_of_gt (diskSevenFalseRadialScale_pos p.1 p.2))
      (diskSevenVector_ne_zero_of_mem_false p.2)) hv⟩

/-- The radial homotopy is jointly continuous in time and the punctured-disk point. -/
public theorem continuous_diskSevenFalseRadialHomotopyFunction :
    Continuous diskSevenFalseRadialHomotopyFunction := by
  unfold diskSevenFalseRadialHomotopyFunction
  apply Continuous.subtype_mk
  apply continuous_uliftUp.comp
  apply Continuous.subtype_mk
  have hv₀ : Continuous (fun x : diskSevenExcisionCover false ↦
      diskSevenVector x.1) :=
    (continuous_subtype_val.comp continuous_uliftDown).comp
      continuous_subtype_val
  have hv : Continuous (fun p : unitInterval × diskSevenExcisionCover false ↦
      diskSevenVector p.2.1) := hv₀.comp continuous_snd
  have ht : Continuous (fun p : unitInterval ×
      diskSevenExcisionCover false ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hninv : Continuous (fun p : unitInterval ×
      diskSevenExcisionCover false ↦ ‖diskSevenVector p.2.1‖⁻¹) :=
    hv.norm.inv₀ (fun p ↦ (diskSevenNorm_pos_of_mem_false p.2).ne')
  exact (ht.add ((continuous_const.sub ht).mul hninv)).smul hv

@[simp]
public theorem diskSevenFalseRadialHomotopyFunction_vector
    (t : unitInterval) (x : diskSevenExcisionCover false) :
    diskSevenVector (diskSevenFalseRadialHomotopyFunction (t, x)).1 =
      diskSevenFalseRadialScale t x • diskSevenVector x.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- At time zero the radial homotopy is radial normalization. -/
@[simp]
public theorem diskSevenFalseRadialHomotopyFunction_zero
    (x : diskSevenExcisionCover false) :
    diskSevenFalseRadialHomotopyFunction (0, x) =
      diskBoundaryToDiskSevenExcisionCoverFalse
        (diskSevenFalseRadialRetraction x) := by
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  change diskSevenVector (diskSevenFalseRadialHomotopyFunction (0, x)).1 =
    diskSevenVector (diskBoundaryToDiskSevenExcisionCoverFalse
      (diskSevenFalseRadialRetraction x)).1
  rw [diskSevenFalseRadialHomotopyFunction_vector,
    diskBoundaryToDiskSevenExcisionCoverFalse_vector,
    diskSevenFalseRadialRetraction_down]
  simp [diskSevenFalseRadialScale]

/-- At time one the radial homotopy is the identity. -/
@[simp]
public theorem diskSevenFalseRadialHomotopyFunction_one
    (x : diskSevenExcisionCover false) :
    diskSevenFalseRadialHomotopyFunction (1, x) = x := by
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  simp [diskSevenFalseRadialHomotopyFunction, diskSevenFalseRadialScale,
    diskSevenVector]

/-- The radial homotopy from boundary normalization to the identity of the false member. -/
public noncomputable def diskSevenFalseRadialHomotopy :
    TopCat.Homotopy
      (diskSevenFalseRadialRetraction ≫
        diskBoundaryToDiskSevenExcisionCoverFalse)
      (𝟙 (TopCat.of (diskSevenExcisionCover false))) where
  toFun := diskSevenFalseRadialHomotopyFunction
  continuous_toFun := continuous_diskSevenFalseRadialHomotopyFunction
  map_zero_left := diskSevenFalseRadialHomotopyFunction_zero
  map_one_left := diskSevenFalseRadialHomotopyFunction_one

@[simp]
public theorem diskSevenFalseRadialHomotopy_vector
    (t : unitInterval) (x : diskSevenExcisionCover false) :
    diskSevenVector (diskSevenFalseRadialHomotopy (t, x)).1 =
      diskSevenFalseRadialScale t x • diskSevenVector x.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The radial homotopy fixes boundary points pointwise. -/
public theorem diskSevenFalseRadialHomotopy_fixed
    (t : unitInterval) (x : TopCat.sphere.{0} 6) :
    diskSevenFalseRadialHomotopy
      (t, diskBoundaryToDiskSevenExcisionCoverFalse x) =
      diskBoundaryToDiskSevenExcisionCoverFalse x := by
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  have hx : ‖x.down.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.down.2
  change diskSevenVector
      (diskSevenFalseRadialHomotopy
        (t, diskBoundaryToDiskSevenExcisionCoverFalse x)).1 =
    diskSevenVector (diskBoundaryToDiskSevenExcisionCoverFalse x).1
  rw [diskSevenFalseRadialHomotopy_vector,
    diskBoundaryToDiskSevenExcisionCoverFalse_vector]
  have hnorm : ‖diskSevenVector
      (diskBoundaryToDiskSevenExcisionCoverFalse x).1‖ = 1 := by
    rw [diskBoundaryToDiskSevenExcisionCoverFalse_vector]
    exact hx
  simp [diskSevenFalseRadialScale, hnorm]

/-- The boundary is a strong deformation retract of the false cover member. -/
public noncomputable def diskSevenFalseStrongDeformationRetract :
    TopCat.StrongDeformationRetractData
      diskBoundaryToDiskSevenExcisionCoverFalse where
  retraction := diskSevenFalseRadialRetraction
  retract := diskBoundaryToDiskSevenExcisionCoverFalse_comp_radialRetraction
  homotopy := diskSevenFalseRadialHomotopy
  fixed := diskSevenFalseRadialHomotopy_fixed

/-- The boundary inclusion into the false member is an explicit homotopy equivalence. -/
public noncomputable def diskBoundaryToDiskSevenExcisionCoverFalseHomotopyEquiv :
    (TopCat.sphere.{0} 6 : Type) ≃ₕ
      (diskSevenExcisionCover false : Set (TopCat.disk.{0} 7)) :=
  strongDeformationRetractHomotopyEquiv
    diskSevenFalseStrongDeformationRetract

/-- The intersection of the two concrete cover members. -/
public abbrev DiskSevenCoverIntersection : Type :=
  (diskSevenExcisionCover true ∩ diskSevenExcisionCover false :
    Set (TopCat.disk.{0} 7))

/-- Radius strictly below one characterizes membership in the true cover member. -/
public theorem mem_diskSevenExcisionCover_true_of_norm_lt_one
    (x : TopCat.disk.{0} 7) (hx : ‖diskSevenVector x‖ < 1) :
    x ∈ diskSevenExcisionCover true := by
  change x ∉ Set.range (TopCat.diskBoundaryInclusion.{0} 7)
  rintro ⟨y, rfl⟩
  have hy : ‖y.down.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.down.2
  apply hx.ne
  change ‖y.down.1‖ = 1
  exact hy

/-- Intersection points, being in the open disk, have radius strictly below one. -/
public theorem diskSevenNorm_lt_one_of_mem_intersection
    (x : DiskSevenCoverIntersection) : ‖diskSevenVector x.1‖ < 1 := by
  have hx := x.2.1
  change x.1 ∉ Set.range (TopCat.diskBoundaryInclusion.{0} 7) at hx
  exact lt_of_le_of_ne (diskSevenNorm_le_one x.1) (fun h ↦ hx
    ⟨ULift.up ⟨diskSevenVector x.1, by
      simpa only [Metric.mem_sphere, dist_zero_right] using h⟩, by
        apply ULift.ext
        apply Subtype.ext
        rfl⟩)

/-- Forgetting the true-member condition, as a function to the false member. -/
public def diskSevenIntersectionToFalseFunction
    (x : DiskSevenCoverIntersection) : diskSevenExcisionCover false :=
  ⟨x.1, x.2.2⟩

/-- Forgetting the true-member condition includes the intersection in the false member. -/
public noncomputable def diskSevenIntersectionToFalse :
    TopCat.of DiskSevenCoverIntersection ⟶
      TopCat.of (diskSevenExcisionCover false) :=
  TopCat.ofHom ⟨diskSevenIntersectionToFalseFunction,
    continuous_subtype_val.subtype_mk _⟩

@[simp]
public theorem diskSevenIntersectionToFalseFunction_vector
    (x : DiskSevenCoverIntersection) :
    diskSevenVector (diskSevenIntersectionToFalseFunction x).1 =
      diskSevenVector x.1 :=
  rfl

/-- Halving the vector of a false-member point keeps it in the closed disk. -/
public theorem norm_half_diskSevenVector_le_one
    (x : diskSevenExcisionCover false) :
    ‖(2 : ℝ)⁻¹ • diskSevenVector x.1‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs]
  have habs : |(2 : ℝ)⁻¹| = (2 : ℝ)⁻¹ := abs_of_pos (by positivity)
  rw [habs]
  calc
    (2 : ℝ)⁻¹ * ‖diskSevenVector x.1‖ ≤ (2 : ℝ)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (diskSevenNorm_le_one x.1) (by positivity)
    _ ≤ 1 := by norm_num

/-- Halving the vector of a false-member point puts it strictly inside the disk. -/
public theorem norm_half_diskSevenVector_lt_one
    (x : diskSevenExcisionCover false) :
    ‖(2 : ℝ)⁻¹ • diskSevenVector x.1‖ < 1 := by
  rw [norm_smul, Real.norm_eq_abs]
  have habs : |(2 : ℝ)⁻¹| = (2 : ℝ)⁻¹ := abs_of_pos (by positivity)
  rw [habs]
  calc
    (2 : ℝ)⁻¹ * ‖diskSevenVector x.1‖ ≤ (2 : ℝ)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (diskSevenNorm_le_one x.1) (by positivity)
    _ < 1 := by norm_num

/-- The closed-disk point obtained by radially halving a false-member point. -/
public def diskSevenFalseHalfDiskPoint
    (x : diskSevenExcisionCover false) : TopCat.disk.{0} 7 :=
  ULift.up ⟨(2 : ℝ)⁻¹ • diskSevenVector x.1, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_half_diskSevenVector_le_one x⟩

@[simp]
public theorem diskSevenFalseHalfDiskPoint_vector
    (x : diskSevenExcisionCover false) :
    diskSevenVector (diskSevenFalseHalfDiskPoint x) =
      (2 : ℝ)⁻¹ • diskSevenVector x.1 :=
  rfl

/-- Radially halve a false-member point; the result lies in the punctured open disk. -/
public def diskSevenFalseToIntersectionHalfFunction
    (x : diskSevenExcisionCover false) : DiskSevenCoverIntersection :=
  ⟨diskSevenFalseHalfDiskPoint x, ⟨by
    apply mem_diskSevenExcisionCover_true_of_norm_lt_one
    rw [diskSevenFalseHalfDiskPoint_vector]
    exact norm_half_diskSevenVector_lt_one x
  , by
    change diskSevenFalseHalfDiskPoint x ≠ diskSevenCenter
    intro h
    have hv := congrArg diskSevenVector h
    rw [diskSevenFalseHalfDiskPoint_vector, diskSevenVector_center] at hv
    exact (smul_ne_zero (by norm_num) (diskSevenVector_ne_zero_of_mem_false x)) hv⟩⟩

/-- Radial halving is continuous. -/
public theorem continuous_diskSevenFalseToIntersectionHalfFunction :
    Continuous diskSevenFalseToIntersectionHalfFunction := by
  unfold diskSevenFalseToIntersectionHalfFunction diskSevenFalseHalfDiskPoint
  apply Continuous.subtype_mk
  apply continuous_uliftUp.comp
  apply Continuous.subtype_mk
  have hv : Continuous (fun x : diskSevenExcisionCover false ↦
      diskSevenVector x.1) :=
    (continuous_subtype_val.comp continuous_uliftDown).comp
      continuous_subtype_val
  have hc : Continuous (fun _ : diskSevenExcisionCover false ↦ (2 : ℝ)⁻¹) :=
    continuous_const
  exact hc.smul hv

/-- Radial halving as a topological map from the false member to the intersection. -/
public noncomputable def diskSevenFalseToIntersectionHalf :
    TopCat.of (diskSevenExcisionCover false) ⟶
      TopCat.of DiskSevenCoverIntersection :=
  TopCat.ofHom ⟨diskSevenFalseToIntersectionHalfFunction,
    continuous_diskSevenFalseToIntersectionHalfFunction⟩

/-- Scaling coefficient from one half at time zero to one at time one. -/
public def diskSevenHalfToIdentityScale (t : unitInterval) : ℝ :=
  (1 + (t : ℝ)) / 2

public theorem diskSevenHalfToIdentityScale_pos (t : unitInterval) :
    0 < diskSevenHalfToIdentityScale t := by
  dsimp [diskSevenHalfToIdentityScale]
  linarith [t.2.1]

public theorem diskSevenHalfToIdentityScale_le_one (t : unitInterval) :
    diskSevenHalfToIdentityScale t ≤ 1 := by
  dsimp [diskSevenHalfToIdentityScale]
  linarith [t.2.2]

/-- The half-radius-to-identity homotopy on the false member. -/
public def diskSevenFalseHalfHomotopyFunction
    (p : unitInterval × diskSevenExcisionCover false) :
    diskSevenExcisionCover false :=
  ⟨ULift.up ⟨diskSevenHalfToIdentityScale p.1 • diskSevenVector p.2.1, by
      have hnorm : ‖diskSevenHalfToIdentityScale p.1 • diskSevenVector p.2.1‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (diskSevenHalfToIdentityScale_pos p.1)]
        exact (mul_le_mul_of_nonneg_right
          (diskSevenHalfToIdentityScale_le_one p.1)
          (norm_nonneg _)).trans (by simpa using diskSevenNorm_le_one p.2.1)
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm⟩, by
    change (ULift.up ⟨diskSevenHalfToIdentityScale p.1 •
      diskSevenVector p.2.1, _⟩ : TopCat.disk.{0} 7) ≠ diskSevenCenter
    intro h
    have hv := congrArg diskSevenVector h
    change diskSevenHalfToIdentityScale p.1 • diskSevenVector p.2.1 =
      diskSevenVector diskSevenCenter at hv
    rw [diskSevenVector_center] at hv
    exact (smul_ne_zero (ne_of_gt (diskSevenHalfToIdentityScale_pos p.1))
      (diskSevenVector_ne_zero_of_mem_false p.2)) hv⟩

public theorem continuous_diskSevenFalseHalfHomotopyFunction :
    Continuous diskSevenFalseHalfHomotopyFunction := by
  unfold diskSevenFalseHalfHomotopyFunction
  apply Continuous.subtype_mk
  apply continuous_uliftUp.comp
  apply Continuous.subtype_mk
  have ht : Continuous (fun p : unitInterval × diskSevenExcisionCover false ↦
      diskSevenHalfToIdentityScale p.1) := by
    unfold diskSevenHalfToIdentityScale
    fun_prop
  have hv₀ : Continuous (fun x : diskSevenExcisionCover false ↦
      diskSevenVector x.1) :=
    (continuous_subtype_val.comp continuous_uliftDown).comp
      continuous_subtype_val
  exact ht.smul (hv₀.comp continuous_snd)

@[simp]
public theorem diskSevenFalseHalfHomotopyFunction_vector
    (t : unitInterval) (x : diskSevenExcisionCover false) :
    diskSevenVector (diskSevenFalseHalfHomotopyFunction (t, x)).1 =
      diskSevenHalfToIdentityScale t • diskSevenVector x.1 :=
  rfl

@[simp]
public theorem diskSevenFalseToIntersectionHalfFunction_vector
    (x : diskSevenExcisionCover false) :
    diskSevenVector (diskSevenFalseToIntersectionHalfFunction x).1 =
      (2 : ℝ)⁻¹ • diskSevenVector x.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On the false member, halving followed by inclusion is homotopic to the identity. -/
public noncomputable def diskSevenFalseHalfHomotopy :
    TopCat.Homotopy
      (diskSevenFalseToIntersectionHalf ≫ diskSevenIntersectionToFalse)
      (𝟙 (TopCat.of (diskSevenExcisionCover false))) where
  toFun := diskSevenFalseHalfHomotopyFunction
  continuous_toFun := continuous_diskSevenFalseHalfHomotopyFunction
  map_zero_left x := by
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    change diskSevenVector (diskSevenFalseHalfHomotopyFunction (0, x)).1 =
      diskSevenVector (diskSevenIntersectionToFalseFunction
        (diskSevenFalseToIntersectionHalfFunction x)).1
    rw [diskSevenFalseHalfHomotopyFunction_vector,
      diskSevenIntersectionToFalseFunction_vector,
      diskSevenFalseToIntersectionHalfFunction_vector]
    simp [diskSevenHalfToIdentityScale]
  map_one_left x := by
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    simp [diskSevenFalseHalfHomotopyFunction,
      diskSevenHalfToIdentityScale, diskSevenVector]

/-- Restrict the same radial homotopy to the punctured open disk. -/
public def diskSevenIntersectionHalfHomotopyFunction
    (p : unitInterval × DiskSevenCoverIntersection) :
    DiskSevenCoverIntersection :=
  ⟨(diskSevenFalseHalfHomotopyFunction
      (p.1, diskSevenIntersectionToFalseFunction p.2)).1, ⟨by
    apply mem_diskSevenExcisionCover_true_of_norm_lt_one
    rw [diskSevenFalseHalfHomotopyFunction_vector,
      diskSevenIntersectionToFalseFunction_vector, norm_smul, Real.norm_eq_abs,
      abs_of_pos (diskSevenHalfToIdentityScale_pos p.1)]
    calc
      diskSevenHalfToIdentityScale p.1 * ‖diskSevenVector p.2.1‖ ≤
          1 * ‖diskSevenVector p.2.1‖ :=
        mul_le_mul_of_nonneg_right (diskSevenHalfToIdentityScale_le_one p.1)
          (norm_nonneg _)
      _ < 1 := by simpa using diskSevenNorm_lt_one_of_mem_intersection p.2
  , by
    exact (diskSevenFalseHalfHomotopyFunction
      (p.1, diskSevenIntersectionToFalseFunction p.2)).2⟩⟩

public theorem continuous_diskSevenIntersectionHalfHomotopyFunction :
    Continuous diskSevenIntersectionHalfHomotopyFunction := by
  unfold diskSevenIntersectionHalfHomotopyFunction
  apply Continuous.subtype_mk
  apply continuous_subtype_val.comp
  apply continuous_diskSevenFalseHalfHomotopyFunction.comp
  have hi : Continuous diskSevenIntersectionToFalseFunction :=
    continuous_subtype_val.subtype_mk _
  exact continuous_fst.prodMk (hi.comp continuous_snd)

@[simp]
public theorem diskSevenIntersectionHalfHomotopyFunction_vector
    (t : unitInterval) (x : DiskSevenCoverIntersection) :
    diskSevenVector (diskSevenIntersectionHalfHomotopyFunction (t, x)).1 =
      diskSevenHalfToIdentityScale t • diskSevenVector x.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On the intersection, inclusion followed by radial halving is homotopic to the identity. -/
public noncomputable def diskSevenIntersectionHalfHomotopy :
    TopCat.Homotopy
      (diskSevenIntersectionToFalse ≫ diskSevenFalseToIntersectionHalf)
      (𝟙 (TopCat.of DiskSevenCoverIntersection)) where
  toFun := diskSevenIntersectionHalfHomotopyFunction
  continuous_toFun := continuous_diskSevenIntersectionHalfHomotopyFunction
  map_zero_left x := by
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    change diskSevenVector
        (diskSevenIntersectionHalfHomotopyFunction (0, x)).1 =
      diskSevenVector (diskSevenFalseToIntersectionHalfFunction
        (diskSevenIntersectionToFalseFunction x)).1
    rw [diskSevenIntersectionHalfHomotopyFunction_vector,
      diskSevenFalseToIntersectionHalfFunction_vector,
      diskSevenIntersectionToFalseFunction_vector]
    simp [diskSevenHalfToIdentityScale]
  map_one_left x := by
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    change diskSevenVector
        (diskSevenIntersectionHalfHomotopyFunction (1, x)).1 =
      diskSevenVector x.1
    rw [diskSevenIntersectionHalfHomotopyFunction_vector]
    simp [diskSevenHalfToIdentityScale]

/-- Radial halving and inclusion give a homotopy equivalence between the punctured closed and
punctured open disks. -/
public noncomputable def diskSevenFalseIntersectionHomotopyEquiv :
    (diskSevenExcisionCover false : Set (TopCat.disk.{0} 7)) ≃ₕ
      DiskSevenCoverIntersection where
  toFun := diskSevenFalseToIntersectionHalf.hom
  invFun := diskSevenIntersectionToFalse.hom
  left_inv := ⟨diskSevenFalseHalfHomotopy⟩
  right_inv := ⟨diskSevenIntersectionHalfHomotopy⟩

/-- The punctured open disk, i.e. the cover intersection, is homotopy equivalent to the standard
six-sphere. -/
public noncomputable def diskSevenCoverIntersectionHomotopyEquivSphereSix :
    DiskSevenCoverIntersection ≃ₕ (TopCat.sphere.{0} 6 : Type) :=
  (diskBoundaryToDiskSevenExcisionCoverFalseHomotopyEquiv.trans
    diskSevenFalseIntersectionHomotopyEquiv).symm

/-- The forward map of the intersection-sphere equivalence is exactly radial normalization after
forgetting the open-disk condition. -/
@[simp]
public theorem diskSevenCoverIntersectionHomotopyEquivSphereSix_apply
    (x : DiskSevenCoverIntersection) :
    diskSevenCoverIntersectionHomotopyEquivSphereSix x =
      diskSevenFalseRadialRetraction (diskSevenIntersectionToFalse x) :=
  rfl

/-- The inverse map first includes the boundary in the punctured closed disk and then halves its
radius, landing in the punctured interior. -/
@[simp]
public theorem diskSevenCoverIntersectionHomotopyEquivSphereSix_symm_apply
    (x : TopCat.sphere.{0} 6) :
    diskSevenCoverIntersectionHomotopyEquivSphereSix.symm x =
      diskSevenFalseToIntersectionHalf
        (diskBoundaryToDiskSevenExcisionCoverFalse x) :=
  rfl

end SphereSixComplex
