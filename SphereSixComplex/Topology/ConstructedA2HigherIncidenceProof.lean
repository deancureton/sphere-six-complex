module

public import SphereSixComplex.Topology.ConstructedA2CharacteristicSweeps
public import SphereSixComplex.Topology.CylinderSweepPrismComparison

@[expose] public section
noncomputable section
open Set Topology Matrix CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def constructedA2PositiveDiskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.of (CWCharacteristicClosedBall 2) ⟶ TopCat.of (ActualLocalCuspCentralOrbitQuotient W) :=
  TopCat.ofHom ⟨fun b ↦ constructedA2CorrectedPositiveTwoOrbit W b.1,
    (constructedA2CorrectedPositiveTwoOrbit_continuousOn W).domRestrict⟩

public def constructedA2PositiveDiskPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cylinderBaseInclusion (cwBallBoundarySet 2))
      (constructedA2TwoSkeletonInclusion W) where
  left := TopCat.ofHom ⟨fun b ↦ ⟨constructedA2CorrectedPositiveTwoOrbit W b.1.1,
    Or.inl (Or.inl (constructedA2CorrectedPositiveTwoOrbit_mapsTo_oneSkeleton W b.2))⟩,
    ((constructedA2PositiveDiskMap W).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  right := constructedA2PositiveDiskMap W
  comm := rfl

public def constructedA2PositiveDiskReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    TopCat.Homotopy (constructedA2PositiveDiskPair W).right
      (constructedA2PositiveDiskPair W).right :=
  TopCat.Homotopy.comp (constructedA2CircleSweepHomotopy W i).symm
    (TopCat.Homotopy.refl (constructedA2PositiveDiskMap W))

public def constructedA2PositiveDiskBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    TopCat.Homotopy (constructedA2PositiveDiskPair W).left
      (constructedA2PositiveDiskPair W).left where
  toFun := constructedA2PositiveNestedBoundaryReverseSweep W i
  continuous_toFun := (constructedA2PositiveNestedBoundaryReverseSweep W i).continuous
  map_zero_left p := (constructedA2PositiveNestedBoundaryReverseSweep W i).map_zero_left p
  map_one_left p := (constructedA2PositiveNestedBoundaryReverseSweep W i).map_one_left p

public instance constructedA2BaseBoundary_mono (n : ℕ) :
    Mono (cylinderBaseInclusion (cwBallBoundarySet n)) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

public def constructedA2PositiveDiskRelativeReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  cwRelativeSingularHomotopy (f := constructedA2PositiveDiskPair W)
    (g := constructedA2PositiveDiskPair W)
    (constructedA2PositiveDiskBoundaryReverseSweep W i)
    (constructedA2PositiveDiskReverseSweep W i) (by ext p; rfl)

public def constructedA2ThreeLowerCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    CWTopologicalPairMap (cylinderLowerSideInclusion (cwBallBoundarySet 2))
      (constructedA2TwoSkeletonInclusion W) where
  left := cylinderLowerSideToBoundary (cwBallBoundarySet 2) ≫
    (constructedA2ThreeCylinderPair W i).left
  right := (constructedA2ThreeCylinderPair W i).right
  comm := rfl

public instance constructedA2TwoSkeletonInclusion_mono
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Mono (constructedA2TwoSkeletonInclusion W) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

public theorem constructedA2PositiveRelativeReverseSweep_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    closedPrismHomology (constructedA2PositiveDiskRelativeReverseSweep W i) 1 ≫
      cwRelativeIntegralSingularBoundary (constructedA2TwoSkeletonInclusion W) 2 = 0 := by
  let A := cwRelativeIntegralSingularShortComplex (cylinderBaseInclusion (cwBallBoundarySet 2))
  let B := cwRelativeIntegralSingularShortComplex (constructedA2TwoSkeletonInclusion W)
  let H₁ := (constructedA2PositiveDiskBoundaryReverseSweep W i).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)
  let H₂ := (constructedA2PositiveDiskReverseSweep W i).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)
  let H₃ := constructedA2PositiveDiskRelativeReverseSweep W i
  apply closedPrism_relative_boundary_eq_zero A B
    (cwRelativeIntegralSingularShortComplex_shortExact _)
    (cwRelativeIntegralSingularShortComplex_shortExact _) H₁ H₂ H₃
  · intro p q
    exact topologicalPrism_naturality (constructedA2PositiveDiskBoundaryReverseSweep W i)
      (constructedA2PositiveDiskReverseSweep W i)
      (cylinderBaseInclusion (cwBallBoundarySet 2)) (constructedA2TwoSkeletonInclusion W)
      (by ext p; rfl) (AddCommGrpCat.of ℤ) p q
  · intro p q
    exact cwRelativeSingularHomotopy_projection
      (f := constructedA2PositiveDiskPair W) (g := constructedA2PositiveDiskPair W)
      (constructedA2PositiveDiskBoundaryReverseSweep W i)
      (constructedA2PositiveDiskReverseSweep W i) (by ext p; rfl) p q
  · exact constructedA2PositiveNestedBoundaryReverseSweep_homology_zero W i

public theorem constructedA2PositiveReverseSweep_eq_reversedCylinder
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (p : unitInterval × CWCharacteristicClosedBall 2) :
    constructedA2PositiveDiskReverseSweep W i p =
      cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 2))
        (constructedA2ThreeCylinderPair W i).right p := by
  change constructedA2CircleSweepHomotopy W i (unitInterval.symm p.1,
      constructedA2CorrectedPositiveTwoOrbit W p.2.1) = _
  change _ = (constructedA2ThreeCylinderPair W i).right
    (cylinderVerticalScale p.1 1, p.2)
  rw [constructedA2ThreeCylinderPair_apply]
  congr 1
  apply Prod.ext
  · apply Subtype.ext
    change 1 - (p.1 : ℝ) = (1 - (p.1 : ℝ)) * 1
    ring
  · rfl

public theorem constructedA2PositiveReverseSweep_prism
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) (p q : ℕ) :
    ((constructedA2PositiveDiskReverseSweep W i).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom p q =
    ((cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 2))
      (constructedA2ThreeCylinderPair W i).right).singularChainComplexFunctorObjMap
        (AddCommGrpCat.of ℤ)).hom p q := by
  have h := topologicalPrism_naturality (constructedA2PositiveDiskReverseSweep W i)
    (cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 2))
      (constructedA2ThreeCylinderPair W i).right) (𝟙 _) (𝟙 _) (by
        ext x : 1
        exact (constructedA2PositiveReverseSweep_eq_reversedCylinder W i (x.2.down, x.1)).symm)
    (AddCommGrpCat.of ℤ) p q
  change (cwIntegralSingularChainMapObj (𝟙 _)).f p ≫ _ =
    _ ≫ (cwIntegralSingularChainMapObj (𝟙 _)).f q at h
  rw [cwIntegralSingularChainMapObj_id, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.id_f, HomologicalComplex.id_f, Category.id_comp, Category.comp_id] at h
  exact h.symm

public theorem constructedA2ThreePrism_relative_compatibility
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) (p q : ℕ) :
    (cwRelativeIntegralSingularChainMapOfPair
      (cylinderTopLowerPair (X := TopCat.of (CWCharacteristicClosedBall 2))
        (cwBallBoundarySet 2))).f p ≫
      (cylinderRelativeContraction (cwBallBoundarySet 2)).hom p q ≫
        (cwRelativeIntegralSingularChainMapOfPair (constructedA2ThreeLowerCylinderPair W i)).f q =
      (constructedA2PositiveDiskRelativeReverseSweep W i).hom p q := by
  apply cylinderRelativeContraction_sweep_relative
  have h := cwRelativeSingularHomotopy_projection
    (f := constructedA2PositiveDiskPair W) (g := constructedA2PositiveDiskPair W)
    (constructedA2PositiveDiskBoundaryReverseSweep W i)
    (constructedA2PositiveDiskReverseSweep W i) (by ext p; rfl) p q
  rw [constructedA2PositiveReverseSweep_prism] at h
  exact h

public theorem constructedA2ThreeCylinderPair_relative_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainMapOfPair (constructedA2ThreeCylinderPair W i)) 3 ≫
        cwRelativeIntegralSingularBoundary (constructedA2TwoSkeletonInclusion W) 2 = 0 := by
  let S := cylinderRelativeTriple (cwBallBoundarySet 2)
  let K := CWRelativeIntegralSingularChainComplex (cylinderBaseInclusion (cwBallBoundarySet 2))
  let L := CWRelativeIntegralSingularChainComplex (constructedA2TwoSkeletonInclusion W)
  let f : K ⟶ S.X₁ := cylinderTopFaceRelativeChains (cwBallBoundarySet 2)
  let g : S.X₃ ⟶ L := cwRelativeIntegralSingularChainMapOfPair (constructedA2ThreeCylinderPair W i)
  have ht : f ≫ S.f = cwRelativeIntegralSingularChainMapOfPair
      (cylinderTopLowerPair (X := TopCat.of (CWCharacteristicClosedBall 2)) (cwBallBoundarySet 2)) := by
    dsimp only [f, S, cylinderRelativeTriple]
    rw [cwRelativeTripleShortComplex_f]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp
      (cylinderTopFacePairMap (cwBallBoundarySet 2)) _).symm
  have hg : S.g ≫ g = cwRelativeIntegralSingularChainMapOfPair
      (constructedA2ThreeLowerCylinderPair W i) := by
    dsimp only [S, cylinderRelativeTriple, g]
    rw [cwRelativeTripleShortComplex_g]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp _
      (constructedA2ThreeCylinderPair W i)).symm
  apply mappedContractingPrism_boundary_eq_zero S (cylinderRelativeContraction _) K L f g
    (constructedA2PositiveDiskRelativeReverseSweep W i) 1
  · have ht' := congrArg (fun k ↦ k.f 2) ht
    have hg' := congrArg (fun k ↦ k.f 3) hg
    change f.f 2 ≫ S.f.f 2 = _ at ht'
    change S.g.f 3 ≫ g.f 3 = _ at hg'
    erw [← Category.assoc, ← Category.assoc, ← Category.assoc, ht', Category.assoc,
      Category.assoc, hg']
    exact constructedA2ThreePrism_relative_compatibility W i 2 3
  · exact cylinderTopPrismClass_surjective (cwBallBoundarySet 2) 1
  · exact constructedA2PositiveRelativeReverseSweep_boundary_zero W i

public theorem constructedA2ThreeCharacteristicPair_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (constructedA2ThreeCharacteristicPair W i).left) 2 = 0 := by
  let e := cwCharacteristicCylinderRelativeIso 2
  have hg : cwRelativeIntegralSingularChainMapOfPair (constructedA2ThreeCylinderPair W i) =
      e.hom ≫ cwRelativeIntegralSingularChainMapOfPair (constructedA2ThreeCharacteristicPair W i) :=
    cwRelativeIntegralSingularChainMapOfPair_comp _ _
  have hr : HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainMapOfPair (constructedA2ThreeCharacteristicPair W i)) 3 ≫
        cwRelativeIntegralSingularBoundary (constructedA2TwoSkeletonInclusion W) 2 = 0 := by
    apply (cancel_epi (HomologicalComplex.homologyMap e.hom 3)).mp
    have h := constructedA2ThreeCylinderPair_relative_boundary_zero W i
    erw [hg, HomologicalComplex.homologyMap_comp, Category.assoc] at h
    simpa using h
  let := cwCharacteristicBoundary_isIso 2 (by decide)
  apply (cancel_epi (cwRelativeIntegralSingularBoundary (cwCharacteristicBoundaryInclusion 3) 2)).mp
  rw [cwRelativeIntegralSingularBoundary_natural, hr, comp_zero]

public theorem constructedA2ThreeCell_attachingDegree_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) (i : Fin 2) (j : Fin 4) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 2 i j = 0 :=
  constructedA2ThreeCell_attachingDegree_zero_of_boundary W T i
    (constructedA2ThreeCharacteristicPair_boundary_zero W i) j

public def constructedA2ThreeDiskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.of (CWCharacteristicClosedBall 3) ⟶ TopCat.of (ActualLocalCuspCentralOrbitQuotient W) :=
  TopCat.ofHom ⟨fun b ↦ constructedA2CorrectedThreeOrbit W 0 b.1,
    (constructedA2CorrectedThreeOrbit_continuousOn W 0).domRestrict⟩

public def constructedA2ThreeDiskPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cylinderBaseInclusion (cwBallBoundarySet 3))
      (constructedA2ThreeSkeletonInclusion W) where
  left := TopCat.ofHom ⟨fun b ↦ ⟨constructedA2CorrectedThreeOrbit W 0 b.1.1,
    Or.inl (constructedA2CorrectedThreeOrbit_mapsTo_twoSkeleton W 0 b.2)⟩,
    ((constructedA2ThreeDiskMap W).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  right := constructedA2ThreeDiskMap W
  comm := rfl

public def constructedA2ThreeDiskReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.Homotopy (constructedA2ThreeDiskPair W).right
      (constructedA2ThreeDiskPair W).right :=
  TopCat.Homotopy.comp (constructedA2CircleSweepHomotopy W 1).symm
    (TopCat.Homotopy.refl (constructedA2ThreeDiskMap W))

public def constructedA2ThreeDiskBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.Homotopy (constructedA2ThreeDiskPair W).left
      (constructedA2ThreeDiskPair W).left where
  toFun := constructedA2ThreeNestedBoundaryReverseSweep W
  continuous_toFun := (constructedA2ThreeNestedBoundaryReverseSweep W).continuous
  map_zero_left p := (constructedA2ThreeNestedBoundaryReverseSweep W).map_zero_left p
  map_one_left p := (constructedA2ThreeNestedBoundaryReverseSweep W).map_one_left p

public def constructedA2ThreeDiskRelativeReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  cwRelativeSingularHomotopy (f := constructedA2ThreeDiskPair W)
    (g := constructedA2ThreeDiskPair W)
    (constructedA2ThreeDiskBoundaryReverseSweep W)
    (constructedA2ThreeDiskReverseSweep W) (by ext p; rfl)

public def constructedA2FourLowerCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cylinderLowerSideInclusion (cwBallBoundarySet 3))
      (constructedA2ThreeSkeletonInclusion W) where
  left := cylinderLowerSideToBoundary (cwBallBoundarySet 3) ≫
    (constructedA2FourCylinderPair W).left
  right := (constructedA2FourCylinderPair W).right
  comm := rfl

public instance constructedA2ThreeSkeletonInclusion_mono
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Mono (constructedA2ThreeSkeletonInclusion W) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

public theorem constructedA2ThreeRelativeReverseSweep_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    closedPrismHomology (constructedA2ThreeDiskRelativeReverseSweep W) 2 ≫
      cwRelativeIntegralSingularBoundary (constructedA2ThreeSkeletonInclusion W) 3 = 0 := by
  let A := cwRelativeIntegralSingularShortComplex (cylinderBaseInclusion (cwBallBoundarySet 3))
  let B := cwRelativeIntegralSingularShortComplex (constructedA2ThreeSkeletonInclusion W)
  let H₁ := (constructedA2ThreeDiskBoundaryReverseSweep W).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)
  let H₂ := (constructedA2ThreeDiskReverseSweep W).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)
  let H₃ := constructedA2ThreeDiskRelativeReverseSweep W
  apply closedPrism_relative_boundary_eq_zero A B
    (cwRelativeIntegralSingularShortComplex_shortExact _)
    (cwRelativeIntegralSingularShortComplex_shortExact _) H₁ H₂ H₃
  · intro p q
    exact topologicalPrism_naturality (constructedA2ThreeDiskBoundaryReverseSweep W)
      (constructedA2ThreeDiskReverseSweep W)
      (cylinderBaseInclusion (cwBallBoundarySet 3)) (constructedA2ThreeSkeletonInclusion W)
      (by ext p; rfl) (AddCommGrpCat.of ℤ) p q
  · intro p q
    exact cwRelativeSingularHomotopy_projection
      (f := constructedA2ThreeDiskPair W) (g := constructedA2ThreeDiskPair W)
      (constructedA2ThreeDiskBoundaryReverseSweep W)
      (constructedA2ThreeDiskReverseSweep W) (by ext p; rfl) p q
  · exact constructedA2ThreeNestedBoundaryReverseSweep_homology_zero W
      (constructedA2ThreeCharacteristicPair_boundary_zero W 0)

public theorem constructedA2ThreeReverseSweep_eq_reversedCylinder
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : unitInterval × CWCharacteristicClosedBall 3) :
    constructedA2ThreeDiskReverseSweep W p =
      cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 3))
        (constructedA2FourCylinderPair W).right p := by
  change constructedA2CircleSweepHomotopy W 1 (unitInterval.symm p.1,
      constructedA2CorrectedThreeOrbit W 0 p.2.1) = _
  change _ = (constructedA2FourCylinderPair W).right
    (cylinderVerticalScale p.1 1, p.2)
  rw [constructedA2FourCylinderPair_apply]
  congr 1
  apply Prod.ext
  · apply Subtype.ext
    change 1 - (p.1 : ℝ) = (1 - (p.1 : ℝ)) * 1
    ring
  · rfl

public theorem constructedA2ThreeReverseSweep_prism
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p q : ℕ) :
    ((constructedA2ThreeDiskReverseSweep W).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom p q =
    ((cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 3))
      (constructedA2FourCylinderPair W).right).singularChainComplexFunctorObjMap
        (AddCommGrpCat.of ℤ)).hom p q := by
  have h := topologicalPrism_naturality (constructedA2ThreeDiskReverseSweep W)
    (cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 3))
      (constructedA2FourCylinderPair W).right) (𝟙 _) (𝟙 _) (by
        ext x : 1
        exact (constructedA2ThreeReverseSweep_eq_reversedCylinder W (x.2.down, x.1)).symm)
    (AddCommGrpCat.of ℤ) p q
  change (cwIntegralSingularChainMapObj (𝟙 _)).f p ≫ _ =
    _ ≫ (cwIntegralSingularChainMapObj (𝟙 _)).f q at h
  rw [cwIntegralSingularChainMapObj_id, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.id_f, HomologicalComplex.id_f, Category.id_comp, Category.comp_id] at h
  exact h.symm

public theorem constructedA2FourPrism_relative_compatibility
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p q : ℕ) :
    (cwRelativeIntegralSingularChainMapOfPair
      (cylinderTopLowerPair (X := TopCat.of (CWCharacteristicClosedBall 3))
        (cwBallBoundarySet 3))).f p ≫
      (cylinderRelativeContraction (cwBallBoundarySet 3)).hom p q ≫
        (cwRelativeIntegralSingularChainMapOfPair (constructedA2FourLowerCylinderPair W)).f q =
      (constructedA2ThreeDiskRelativeReverseSweep W).hom p q := by
  apply cylinderRelativeContraction_sweep_relative
  have h := cwRelativeSingularHomotopy_projection
    (f := constructedA2ThreeDiskPair W) (g := constructedA2ThreeDiskPair W)
    (constructedA2ThreeDiskBoundaryReverseSweep W)
    (constructedA2ThreeDiskReverseSweep W) (by ext p; rfl) p q
  rw [constructedA2ThreeReverseSweep_prism] at h
  exact h

public theorem constructedA2FourCylinderPair_relative_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainMapOfPair (constructedA2FourCylinderPair W)) 4 ≫
        cwRelativeIntegralSingularBoundary (constructedA2ThreeSkeletonInclusion W) 3 = 0 := by
  let S := cylinderRelativeTriple (cwBallBoundarySet 3)
  let K := CWRelativeIntegralSingularChainComplex (cylinderBaseInclusion (cwBallBoundarySet 3))
  let L := CWRelativeIntegralSingularChainComplex (constructedA2ThreeSkeletonInclusion W)
  let f : K ⟶ S.X₁ := cylinderTopFaceRelativeChains (cwBallBoundarySet 3)
  let g : S.X₃ ⟶ L := cwRelativeIntegralSingularChainMapOfPair (constructedA2FourCylinderPair W)
  have ht : f ≫ S.f = cwRelativeIntegralSingularChainMapOfPair
      (cylinderTopLowerPair (X := TopCat.of (CWCharacteristicClosedBall 3)) (cwBallBoundarySet 3)) := by
    dsimp only [f, S, cylinderRelativeTriple]
    rw [cwRelativeTripleShortComplex_f]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp
      (cylinderTopFacePairMap (cwBallBoundarySet 3)) _).symm
  have hg : S.g ≫ g = cwRelativeIntegralSingularChainMapOfPair
      (constructedA2FourLowerCylinderPair W) := by
    dsimp only [S, cylinderRelativeTriple, g]
    rw [cwRelativeTripleShortComplex_g]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp _
      (constructedA2FourCylinderPair W)).symm
  apply mappedContractingPrism_boundary_eq_zero S (cylinderRelativeContraction _) K L f g
    (constructedA2ThreeDiskRelativeReverseSweep W) 2
  · have ht' := congrArg (fun k ↦ k.f 3) ht
    have hg' := congrArg (fun k ↦ k.f 4) hg
    change f.f 3 ≫ S.f.f 3 = _ at ht'
    change S.g.f 4 ≫ g.f 4 = _ at hg'
    erw [← Category.assoc, ← Category.assoc, ← Category.assoc, ht', Category.assoc,
      Category.assoc, hg']
    exact constructedA2FourPrism_relative_compatibility W 3 4
  · exact cylinderTopPrismClass_surjective (cwBallBoundarySet 3) 2
  · exact constructedA2ThreeRelativeReverseSweep_boundary_zero W

public theorem constructedA2FourCharacteristicPair_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (constructedA2FourCharacteristicPair W).left) 3 = 0 := by
  let e := cwCharacteristicCylinderRelativeIso 3
  have hg : cwRelativeIntegralSingularChainMapOfPair (constructedA2FourCylinderPair W) =
      e.hom ≫ cwRelativeIntegralSingularChainMapOfPair (constructedA2FourCharacteristicPair W) :=
    cwRelativeIntegralSingularChainMapOfPair_comp _ _
  have hr : HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainMapOfPair (constructedA2FourCharacteristicPair W)) 4 ≫
        cwRelativeIntegralSingularBoundary (constructedA2ThreeSkeletonInclusion W) 3 = 0 := by
    apply (cancel_epi (HomologicalComplex.homologyMap e.hom 4)).mp
    have h := constructedA2FourCylinderPair_relative_boundary_zero W
    erw [hg, HomologicalComplex.homologyMap_comp, Category.assoc] at h
    simpa using h
  let := cwCharacteristicBoundary_isIso 3 (by decide)
  apply (cancel_epi (cwRelativeIntegralSingularBoundary (cwCharacteristicBoundaryInclusion 4) 3)).mp
  rw [cwRelativeIntegralSingularBoundary_natural, hr, comp_zero]

public theorem constructedA2FourCell_attachingDegree_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) (j : Fin 2) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 3 (0 : Fin 1) j = 0 :=
  constructedA2FourCell_attachingDegree_zero_of_boundary W T
    (constructedA2FourCharacteristicPair_boundary_zero W) j

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
