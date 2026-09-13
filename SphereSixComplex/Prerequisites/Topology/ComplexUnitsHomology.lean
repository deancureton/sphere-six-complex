module

public import SphereSixComplex.Prerequisites.Topology.AdjunctionCollarEquiv
public import SphereSixComplex.Prerequisites.Topology.StandardTorusHomology
public import Mathlib.Topology.Algebra.GroupWithZero
public import SphereSixComplex.Prerequisites.Topology.UnitCircleExponential
public section
open Set Topology ContinuousMap
open SphereSixComplex
noncomputable section

def Complex.unitsHomotopyEquivCircle : ℂˣ ≃ₕ Circle := by
  let e : ℂˣ ≃ₜ {z : ℂ | ‖z‖ ∈ Ioi (0 : ℝ)} :=
    (unitsHomeomorphNeZero : ℂˣ ≃ₜ {z : ℂ | z ≠ 0}).trans
      (Homeomorph.setCongr (by ext z; change (z ≠ 0) ↔ 0 < ‖z‖; exact norm_pos_iff.symm))
  exact (e.trans (Homeomorph.prodUnique _ Unit).symm).toHomotopyEquiv.trans
    ((normPreimageProdHomotopyEquiv ℂ Unit (Ioi 0) (Subset.refl _)
      (convex_Ioi 0) ⟨1, by norm_num⟩).trans
      (Homeomorph.prodUnique Circle Unit).toHomotopyEquiv)

@[simp] theorem Complex.unitsHomotopyEquivCircle_toUnits (z : Circle) :
    Complex.unitsHomotopyEquivCircle (Circle.toUnits z) = z := by
  apply Subtype.ext
  change ‖(z : ℂ)‖⁻¹ • (z : ℂ) = (z : ℂ)
  simp [Circle.norm_coe]

def Complex.unitsHomologyOneEquiv : IntegralSingularHomology 1 ℂˣ ≃+ ℤ :=
  (integralSingularHomologyEquivOfHomotopyEquiv 1 Complex.unitsHomotopyEquivCircle).trans
    ((integralSingularHomologyEquiv 1 (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)).symm.trans
      (AddEquiv.ofBijective StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        ⟨StandardTorusHomology.unitCircleHomologyWinding_injective,
          StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_surjective⟩))

theorem Complex.unitsHomologyOneEquiv_toUnits
    (x : IntegralSingularHomology 1 UnitAddCircle) :
    Complex.unitsHomologyOneEquiv (integralSingularHomologyMap 1 CircleExponential.toUnits x) =
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding x := by
  change StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
    (integralSingularHomologyMap 1
      ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm,
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous⟩
      (integralSingularHomologyMap 1 Complex.unitsHomotopyEquivCircle.toFun
        (integralSingularHomologyMap 1 CircleExponential.toUnits x))) = _
  rw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
  have he :
      (⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm,
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous⟩ : C(Circle, UnitAddCircle)).comp
        (Complex.unitsHomotopyEquivCircle.toFun.comp CircleExponential.toUnits) =
      ContinuousMap.id UnitAddCircle := by
    ext z
    change (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
      (Complex.unitsHomotopyEquivCircle (Circle.toUnits (AddCircle.toCircle z))) = z
    rw [Complex.unitsHomotopyEquivCircle_toUnits,
      ← AddCircle.homeomorphCircle_apply one_ne_zero z]
    exact (AddCircle.homeomorphCircle one_ne_zero).symm_apply_apply z
  rw [ContinuousMap.comp_assoc, he, integralSingularHomologyMap_id_wang]

theorem Circle.subsingleton_homology (n : ℕ) (hn : 1 < n) :
    Subsingleton (IntegralSingularHomology n Circle) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl (StandardTorusHomology.StdTorus 0)) k
  let _ := StandardTorusHomology.subsingleton_homology_stdTorusZero (k + 1) (by omega)
  let _ := StandardTorusHomology.subsingleton_homology_stdTorusZero k (by omega)
  have hzero (x : IntegralSingularHomology (k + 1)
      (CircleMappingTorus (Homeomorph.refl (StandardTorusHomology.StdTorus 0)))) : x = 0 := by
    obtain ⟨y, hy⟩ := (P.exact_inclusion_boundary x).mp (Subsingleton.elim _ _)
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa [hy0] using hy.symm
  let _ : Subsingleton (IntegralSingularHomology (k + 1)
      (CircleMappingTorus (Homeomorph.refl (StandardTorusHomology.StdTorus 0)))) :=
    ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  let e := (StandardTorusHomology.stdTorusMappingTorusHomeomorph 0).trans
    (StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph.trans
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero))
  exact ⟨fun x y => (integralSingularHomologyEquiv (k + 1) e).symm.injective (Subsingleton.elim _ _)⟩
