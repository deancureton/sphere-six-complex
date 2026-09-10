module

public import SphereSixComplex.Prerequisites.Topology.CellularDiscreteHomologyZero

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace SphereSixComplex

public theorem cwBoundaryOne_coordinate (x : CWCharacteristicBoundarySphere 1) :
    x.1 0 = -1 ∨ x.1 0 = 1 := by
  have he : x.1 = fun _ ↦ x.1 0 := by funext i; fin_cases i; rfl
  have hx := x.property
  rw [Metric.mem_sphere, dist_zero_right, he, pi_norm_const, Real.norm_eq_abs] at hx
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hx with h | h
  · exact Or.inr h
  · exact Or.inl h

public def cwBoundaryOneLeft : CWCharacteristicBoundarySphere 1 :=
  ⟨fun _ ↦ -1, by simp [pi_norm_const]⟩

public def cwBoundaryOneRight : CWCharacteristicBoundarySphere 1 :=
  ⟨fun _ ↦ 1, by simp [pi_norm_const]⟩

public theorem cwBoundaryOneLeft_ne_right : cwBoundaryOneLeft ≠ cwBoundaryOneRight := by
  intro h
  have he := congrArg (fun x : CWCharacteristicBoundarySphere 1 ↦ x.1 0) h
  norm_num [cwBoundaryOneLeft, cwBoundaryOneRight] at he

public theorem cwBoundaryOne_eq_left_or_right (x : CWCharacteristicBoundarySphere 1) :
    x = cwBoundaryOneLeft ∨ x = cwBoundaryOneRight := by
  rcases cwBoundaryOne_coordinate x with h | h
  · left; apply Subtype.ext; funext i; fin_cases i; exact h
  · right; apply Subtype.ext; funext i; fin_cases i; exact h

public instance : Finite (CWCharacteristicBoundarySphere 1) := by
  apply Finite.of_injective (fun x : CWCharacteristicBoundarySphere 1 ↦ decide (x = cwBoundaryOneRight))
  intro x y h
  rcases cwBoundaryOne_eq_left_or_right x with rfl | rfl <;>
    rcases cwBoundaryOne_eq_left_or_right y with rfl | rfl
  all_goals first | rfl | simp [cwBoundaryOneLeft_ne_right] at h

public def cwOrientedIntervalPath : TopCat.I ⟶ TopCat.of (CWCharacteristicClosedBall 1) :=
  TopCat.ofHom ⟨fun t ↦ ⟨fun _ ↦ 2 * (TopCat.I.homeomorph t : ℝ) - 1, by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_const, Real.norm_eq_abs, abs_le]
    have ht0 := (TopCat.I.homeomorph t).property.1
    have ht1 := (TopCat.I.homeomorph t).property.2
    constructor <;> linarith⟩, by fun_prop⟩

public theorem cwOrientedIntervalPath_left : cwOrientedIntervalPath 0 =
    cwCharacteristicBoundaryInclusion 1 cwBoundaryOneLeft := by
  apply Subtype.ext
  funext i
  change 2 * (0 : ℝ) - 1 = -1
  norm_num

public theorem cwOrientedIntervalPath_right : cwOrientedIntervalPath 1 =
    cwCharacteristicBoundaryInclusion 1 cwBoundaryOneRight := by
  apply Subtype.ext
  funext i
  change 2 * (1 : ℝ) - 1 = 1
  norm_num

public def cwOrientedIntervalClass : AddCommGrpCat.of ℤ ⟶
    (CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion 1)).homology 1 :=
  cwRelativePathClass (cwCharacteristicBoundaryInclusion 1) cwOrientedIntervalPath
    cwBoundaryOneLeft cwBoundaryOneRight cwOrientedIntervalPath_left cwOrientedIntervalPath_right

public def cwIntervalOrientationEvaluation :
    (CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion 1)).homology 1 ⟶
      AddCommGrpCat.of ℤ :=
  cwRelativeIntegralSingularBoundary (cwCharacteristicBoundaryInclusion 1) 0 ≫
    cwDiscreteHomologyZeroWeight (TopCat.of (CWCharacteristicBoundarySphere 1))
      (fun x ↦ if x = cwBoundaryOneRight then 1 else 0)

public theorem cwOrientedIntervalClass_evaluation :
    cwOrientedIntervalClass ≫ cwIntervalOrientationEvaluation = 𝟙 (AddCommGrpCat.of ℤ) := by
  rw [cwOrientedIntervalClass, cwIntervalOrientationEvaluation, cwRelativePathClass_boundary_weight]
  simp [cwBoundaryOneLeft_ne_right]

public def normalizedIntervalDiskOrientation (T : IntegralCWCellularHomologyFoundation) :
    (CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion 1)).homology 1 ≃+ ℤ :=
  cyclicEvaluationEquiv (T.diskOrientation 1) cwIntervalOrientationEvaluation.hom
    (cwOrientedIntervalClass.hom 1) (by
      exact ConcreteCategory.congr_hom cwOrientedIntervalClass_evaluation 1)

public theorem normalizedIntervalDiskOrientation_symm_one
    (T : IntegralCWCellularHomologyFoundation) :
    (normalizedIntervalDiskOrientation T).symm 1 = cwOrientedIntervalClass.hom 1 := by
  apply (normalizedIntervalDiskOrientation T).injective
  rw [AddEquiv.apply_symm_apply]
  exact (ConcreteCategory.congr_hom cwOrientedIntervalClass_evaluation 1).symm

public theorem normalizedIntervalDiskOrientation_boundary
    (T : IntegralCWCellularHomologyFoundation) :
    (cwRelativeIntegralSingularBoundary (cwCharacteristicBoundaryInclusion 1) 0).hom
      ((normalizedIntervalDiskOrientation T).symm 1) =
        (cwIntegralPointClass (TopCat.of (CWCharacteristicBoundarySphere 1))
          cwBoundaryOneRight).hom 1 -
        (cwIntegralPointClass (TopCat.of (CWCharacteristicBoundarySphere 1))
          cwBoundaryOneLeft).hom 1 := by
  rw [normalizedIntervalDiskOrientation_symm_one]
  exact ConcreteCategory.congr_hom
    (cwRelativePathClass_boundary_pointClasses (cwCharacteristicBoundaryInclusion 1)
      cwOrientedIntervalPath cwBoundaryOneLeft cwBoundaryOneRight
      cwOrientedIntervalPath_left cwOrientedIntervalPath_right) 1

end SphereSixComplex
