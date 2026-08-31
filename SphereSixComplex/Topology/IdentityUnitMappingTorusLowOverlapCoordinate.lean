module

public import SphereSixComplex.Topology.IdentityUnitMappingTorusPositiveBoundary

/-!
# The low-overlap coordinate of the positive point mapping-torus boundary

The chain-level calibration of the positive cylinder boundary is read in the ordered overlap
basis.  Its low coordinate is the canonical point class in degree-zero homology, hence has
augmentation `+1`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex.Topology.IdentityUnitMappingTorusLowOverlapCoordinate

open IdentityUnitMappingTorusPositiveBoundary
open SphereSixComplex.BinaryOpenCover
open SphereSixComplex.MappingTorusBaseCircleWangBoundaryNaturality
open SphereSixComplex.MappingTorusDegreeOneCoverComparison
open SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality

/-- The canonical degree-zero homology class represented by the unique point of `Unit`. -/
public noncomputable def pointH0Class : IntegralSingularHomology 0 Unit :=
  zeroChainHomologyClass (IntegralChains Unit) (pointChain ())

private theorem zeroChainHomologyClass_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (c : Chains X 0) :
    integralSingularHomologyMap 0 f
        (zeroChainHomologyClass (IntegralChains X) c) =
      zeroChainHomologyClass (IntegralChains Y) ((singularChainMap f).f 0 c) := by
  have h :
      ((IntegralChains X).liftCycles (AddCommGrpCat.asHom c) 0 (by simp) (by simp) ≫
          (IntegralChains X).homologyπ 0) ≫
          HomologicalComplex.homologyMap (singularChainMap f) 0 =
        (IntegralChains Y).liftCycles
            (AddCommGrpCat.asHom ((singularChainMap f).f 0 c)) 0 (by simp) (by simp) ≫
          (IntegralChains Y).homologyπ 0 := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
    congr 2
    apply AddCommGrpCat.int_hom_ext
    simp
  exact ConcreteCategory.congr_hom h 1

private theorem pointH0Class_map
    {X : Type} [TopologicalSpace X] (f : C(Unit, X)) :
    integralSingularHomologyMap 0 f pointH0Class =
      zeroChainHomologyClass (IntegralChains X) (pointChain (f ())) := by
  rw [pointH0Class, zeroChainHomologyClass_naturality]
  simp only [pointChain, singularChainMap_simplex]
  rfl

private theorem zeroChainHomologyClass_sub
    {X : Type} [TopologicalSpace X] (c d : Chains X 0) :
    zeroChainHomologyClass (IntegralChains X) (c - d) =
      zeroChainHomologyClass (IntegralChains X) c -
        zeroChainHomologyClass (IntegralChains X) d := by
  change
    (((IntegralChains X).liftCycles (AddCommGrpCat.asHom (c - d)) 0 (by simp) (by simp) ≫
        (IntegralChains X).homologyπ 0) 1) =
      (((IntegralChains X).liftCycles (AddCommGrpCat.asHom c) 0 (by simp) (by simp) ≫
          (IntegralChains X).homologyπ 0) 1) -
        (((IntegralChains X).liftCycles (AddCommGrpCat.asHom d) 0 (by simp) (by simp) ≫
          (IntegralChains X).homologyπ 0) 1)
  have hLift :
      (IntegralChains X).liftCycles (AddCommGrpCat.asHom c) 0 (by simp) (by simp) -
          (IntegralChains X).liftCycles (AddCommGrpCat.asHom d) 0 (by simp) (by simp) =
        (IntegralChains X).liftCycles (AddCommGrpCat.asHom (c - d)) 0 (by simp) (by simp) := by
    rw [← cancel_mono ((IntegralChains X).iCycles 0),
      CategoryTheory.Preadditive.sub_comp]
    simp only [HomologicalComplex.liftCycles_i]
    apply AddCommGrpCat.int_hom_ext
    simp
  have hComp := congrArg (fun f ↦ f ≫ (IntegralChains X).homologyπ 0) hLift
  rw [CategoryTheory.Preadditive.sub_comp] at hComp
  have hEval := ConcreteCategory.congr_hom hComp (1 : ℤ)
  symm
  simpa only [AddCommGrpCat.comp_apply, AddCommGrpCat.hom_sub,
    AddMonoidHom.sub_apply] using hEval

private theorem opensIntersectionHomologyIso_hom_apply
    {X : TopCat} (U V : Opens X) (n : ℕ)
    (x : IntegralSingularHomology n ((U : Set X) ∩ (V : Set X) : Set X)) :
    ConcreteCategory.hom (opensIntersectionHomologyIso U V n).hom x = x := by
  have hhom :
      (TopCat.isoOfHomeo (opensIntersectionHomeomorph U V)).hom =
        𝟙 (TopCat.of ((U : Set X) ∩ (V : Set X) : Set X)) := by
    ext y
    rfl
  have hmap := congrArg (integralHomologyFunctor n).map hhom
  rw [(integralHomologyFunctor n).map_id] at hmap
  exact DFunLike.congr_fun (congrArg ConcreteCategory.hom hmap) x

private theorem positiveBoundaryCalibration_legacy_coordinates :
    zeroChainHomologyClass
        (openSingularChains (pointVertexOpen ⊓ pointEdgeOpen))
        (pointChain positiveBoundaryCalibration.low -
          pointChain positiveBoundaryCalibration.high) =
      overlapEquiv (fun _ : Unit ↦ Homeomorph.refl Unit) 0
        ((fun _ : Unit ↦ pointH0Class), fun _ : Unit ↦ -pointH0Class) := by
  change zeroChainHomologyClass (IntegralChains _)
      (pointChain positiveBoundaryCalibration.low -
        pointChain positiveBoundaryCalibration.high) = _
  rw [overlapEquiv]
  change _ = overlapLegSum (fun _ : Unit ↦ Homeomorph.refl Unit) 0 _
  rw [overlapLegSum_apply]
  simp only [Fintype.sum_unique]
  rw [map_neg, pointH0Class_map, pointH0Class_map]
  rw [zeroChainHomologyClass_sub]
  have hlow : positiveBoundaryCalibration.low =
      overlapPt (fun _ : Unit ↦ Homeomorph.refl Unit)
        uQuarter_mem_overlapBand () () := by
    apply Subtype.ext
    rw [positiveBoundaryCalibration.low_coe]
    rfl
  have hhigh : positiveBoundaryCalibration.high =
      overlapPt (fun _ : Unit ↦ Homeomorph.refl Unit)
        uThreeQuarters_mem_overlapBand () () := by
    apply Subtype.ext
    rw [positiveBoundaryCalibration.high_coe]
    rfl
  rw [hlow, hhigh, sub_eq_add_neg]
  rfl

/-- The ordered low-overlap reader sends the calibrated ordinary boundary to the canonical
degree-zero point class. -/
public theorem positiveBoundaryCalibration_lowOverlapRead :
    lowOverlapRead (Homeomorph.refl Unit) 0
        (zeroChainHomologyClass
          (openSingularChains (pointVertexOpen ⊓ pointEdgeOpen))
          (pointChain positiveBoundaryCalibration.low -
            pointChain positiveBoundaryCalibration.high)) =
      pointH0Class := by
  have hread := lowOverlapRead_opensIntersectionHomologyIso_overlapEquiv
    (Homeomorph.refl Unit) 0 pointH0Class (-pointH0Class)
  have hhom := opensIntersectionHomologyIso_hom_apply
    pointVertexOpen pointEdgeOpen 0
    (overlapEquiv (fun _ : Unit ↦ Homeomorph.refl Unit) 0
      ((fun _ : Unit ↦ pointH0Class), fun _ : Unit ↦ -pointH0Class))
  rw [hhom] at hread
  rw [positiveBoundaryCalibration_legacy_coordinates]
  exact hread

/-- In the canonical augmentation basis, the low-overlap coordinate of the calibrated positive
boundary is exactly `+1`. -/
public theorem positiveBoundaryCalibration_lowOverlapRead_integer :
    pathConnectedIntegralHomologyZeroEquivInteger Unit
        (lowOverlapRead (Homeomorph.refl Unit) 0
          (zeroChainHomologyClass
            (openSingularChains (pointVertexOpen ⊓ pointEdgeOpen))
            (pointChain positiveBoundaryCalibration.low -
              pointChain positiveBoundaryCalibration.high))) = 1 := by
  rw [positiveBoundaryCalibration_lowOverlapRead]
  change ConcreteCategory.hom
      ((TopCat.of Unit).singularHomology₀ε (AddCommGrpCat.of ℤ)) pointH0Class = 1
  unfold pointH0Class zeroChainHomologyClass
  change (((IntegralChains Unit).liftCycles
      (AddCommGrpCat.asHom (pointChain ())) 0 (by simp) (by simp) ≫
        (IntegralChains Unit).homologyπ 0 ≫
          (TopCat.toSSet.obj (TopCat.of Unit)).homology₀ε (AddCommGrpCat.of ℤ)) 1) = 1
  have hpoint : AddCommGrpCat.asHom (pointChain ()) =
      (TopCat.toSSet.obj (TopCat.of Unit)).ιChainComplex
        (R := AddCommGrpCat.of ℤ)
        (simplexIndex Unit 0 (ContinuousMap.const (Simplex 0) ())) := by
    apply AddCommGrpCat.int_hom_ext
    simp [pointChain, simplexChain]
  rw [hpoint]
  rw [(TopCat.toSSet.obj (TopCat.of Unit)).liftCycles_ιChainComplex_homologyπ_homology₀ε]
  rfl

end SphereSixComplex.Topology.IdentityUnitMappingTorusLowOverlapCoordinate

end

end
