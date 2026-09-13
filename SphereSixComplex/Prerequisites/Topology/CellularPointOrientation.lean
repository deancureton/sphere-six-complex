module

public import SphereSixComplex.Prerequisites.Topology.CellularIntervalOrientation
public import SphereSixComplex.Prerequisites.Topology.ConnectedMayerVietorisDegreeZero

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
  have h (f : cwIntegralSingularChainComplexObj
      (TopCat.of (CWCharacteristicBoundarySphere 0)) ⟶ cwIntegralSingularChainComplexObj
      (TopCat.of (CWCharacteristicClosedBall 0))) [HasCokernel f]
      (hf : f = 0) : IsIso (cokernel.π f) := by
    subst f
    infer_instance
  exact h _ cwCharacteristicBoundaryInclusion_zero_chainMap

public def cwPointDiskPoint : CWCharacteristicClosedBall 0 :=
  ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

public instance : Nonempty (CWCharacteristicClosedBall 0) := ⟨cwPointDiskPoint⟩

public def normalizedPointDiskOrientation :
    (cwRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion 0)).homology 0
      ≃+ ℤ :=
  ((asIso (HomologicalComplex.homologyMap (cwRelativeIntegralSingularChainProjection
    (cwCharacteristicBoundaryInclusion 0)) 0)).symm).addCommGroupIsoToAddEquiv |>.trans
      (pathConnectedIntegralHomologyZeroEquivInteger (CWCharacteristicClosedBall 0))

end SphereSixComplex
