module

public import SphereSixComplex.Topology.CellularIntervalOrientation
public import SphereSixComplex.Topology.ConnectedMayerVietorisDegreeZero

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace SphereSixComplex

public instance : IsEmpty (CWCharacteristicBoundarySphere 0) := ⟨by
  intro x
  have hx := x.property
  have he : x.1 = 0 := Subsingleton.elim _ _
  rw [Metric.mem_sphere, he, dist_self] at hx
  norm_num at hx⟩

public theorem cwCharacteristicBoundaryInclusion_zero_chainMap :
    cwIntegralSingularChainMapObj (cwCharacteristicBoundaryInclusion 0) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (SSet.chainComplexMap (TopCat.toSSet.map (cwCharacteristicBoundaryInclusion 0))
    (AddCommGrpCat.of ℤ)).f n = 0
  apply SSet.chainComplex_hom_ext
  intro x
  exact isEmptyElim (TopCat.toSSetObjEquiv _ _ x (stdSimplex.vertex 0))

public instance : IsIso (cwRelativeIntegralSingularChainProjection
    (cwCharacteristicBoundaryInclusion 0)) := by
  have h (f : CWIntegralSingularChainComplexObj
      (TopCat.of (CWCharacteristicBoundarySphere 0)) ⟶ CWIntegralSingularChainComplexObj
      (TopCat.of (CWCharacteristicClosedBall 0))) [HasCokernel f]
      (hf : f = 0) : IsIso (cokernel.π f) := by
    subst f
    infer_instance
  exact h _ cwCharacteristicBoundaryInclusion_zero_chainMap

public def cwPointDiskPoint : CWCharacteristicClosedBall 0 :=
  ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

public instance : Nonempty (CWCharacteristicClosedBall 0) := ⟨cwPointDiskPoint⟩

public def normalizedPointDiskOrientation :
    (CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion 0)).homology 0 ≃+ ℤ :=
  ((asIso (HomologicalComplex.homologyMap (cwRelativeIntegralSingularChainProjection
    (cwCharacteristicBoundaryInclusion 0)) 0)).symm).addCommGroupIsoToAddEquiv |>.trans
      (pathConnectedIntegralHomologyZeroEquivInteger (CWCharacteristicClosedBall 0))

public def cwOrientedPointClass : AddCommGrpCat.of ℤ ⟶
    (CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion 0)).homology 0 :=
  cwIntegralPointClass (TopCat.of (CWCharacteristicClosedBall 0)) cwPointDiskPoint ≫
    HomologicalComplex.homologyMap (cwRelativeIntegralSingularChainProjection
      (cwCharacteristicBoundaryInclusion 0)) 0

public theorem cwOrientedPointClass_augmentation :
    cwIntegralPointClass (TopCat.of (CWCharacteristicClosedBall 0)) cwPointDiskPoint ≫
      (TopCat.of (CWCharacteristicClosedBall 0)).singularHomology₀ε (AddCommGrpCat.of ℤ) =
        𝟙 (AddCommGrpCat.of ℤ) := by
  exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
    (TopCat.toSSet.obj (TopCat.of (CWCharacteristicClosedBall 0))) (AddCommGrpCat.of ℤ)
      (TopCat.toSSetObj₀Equiv.symm cwPointDiskPoint)

public theorem normalizedPointDiskOrientation_class :
    normalizedPointDiskOrientation (cwOrientedPointClass.hom 1) = 1 := by
  let e := (asIso (HomologicalComplex.homologyMap
    (cwRelativeIntegralSingularChainProjection (cwCharacteristicBoundaryInclusion 0)) 0)).addCommGroupIsoToAddEquiv
  let o := pathConnectedIntegralHomologyZeroEquivInteger (CWCharacteristicClosedBall 0)
  change o (e.symm (e ((cwIntegralPointClass
    (TopCat.of (CWCharacteristicClosedBall 0)) cwPointDiskPoint).hom 1))) = 1
  rw [e.symm_apply_apply]
  exact ConcreteCategory.congr_hom cwOrientedPointClass_augmentation 1

public theorem normalizedPointDiskOrientation_symm_one :
    normalizedPointDiskOrientation.symm 1 = cwOrientedPointClass.hom 1 := by
  apply normalizedPointDiskOrientation.injective
  rw [AddEquiv.apply_symm_apply, normalizedPointDiskOrientation_class]

end SphereSixComplex
