module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CharacteristicSweeps
public import SphereSixComplex.Prerequisites.Topology.CylinderSweepPrismComparison

@[expose] public section
noncomputable section
open Set Topology Matrix CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def positiveDiskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.of (CWCharacteristicClosedBall 2) ⟶ TopCat.of (ActualLocalCuspCentralOrbitQuotient W) :=
  TopCat.ofHom ⟨fun b ↦ correctedPositiveTwoOrbit W b.1,
    (continuousOn_correctedPositiveTwoOrbit W).domRestrict⟩

public def positiveDiskPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cylinderBaseInclusion (cwBallBoundarySet 2))
      (twoSkeletonInclusion W) where
  left := TopCat.ofHom ⟨fun b ↦ ⟨correctedPositiveTwoOrbit W b.1.1,
    Or.inl (Or.inl (correctedPositiveTwoOrbit_mapsTo_oneSkeleton W b.2))⟩,
    ((positiveDiskMap W).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  right := positiveDiskMap W
  comm := rfl

public def positiveDiskReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    TopCat.Homotopy (positiveDiskPair W).right
      (positiveDiskPair W).right :=
  TopCat.Homotopy.comp (circleSweepHomotopy W i).symm
    (TopCat.Homotopy.refl (positiveDiskMap W))

public def positiveDiskBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    TopCat.Homotopy (positiveDiskPair W).left
      (positiveDiskPair W).left where
  toFun := positiveNestedBoundaryReverseSweep W i
  continuous_toFun := (positiveNestedBoundaryReverseSweep W i).continuous
  map_zero_left p := (positiveNestedBoundaryReverseSweep W i).map_zero_left p
  map_one_left p := (positiveNestedBoundaryReverseSweep W i).map_one_left p

public def positiveDiskRelativeReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  cwRelativeSingularHomotopy (f := positiveDiskPair W)
    (g := positiveDiskPair W)
    (positiveDiskBoundaryReverseSweep W i)
    (positiveDiskReverseSweep W i) (by ext p; rfl)

public def threeLowerCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    CWTopologicalPairMap (cylinderLowerSideInclusion (cwBallBoundarySet 2))
      (twoSkeletonInclusion W) where
  left := cylinderLowerSideToBoundary (cwBallBoundarySet 2) ≫
    (threeCylinderPair W i).left
  right := (threeCylinderPair W i).right
  comm := rfl

public instance twoSkeletonInclusion_mono
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Mono (twoSkeletonInclusion W) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

public theorem positiveRelativeReverseSweep_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    closedPrismHomology (positiveDiskRelativeReverseSweep W i) 1 ≫
      cwRelativeIntegralSingularBoundary (twoSkeletonInclusion W) 2 = 0 := by
  let A := cwRelativeIntegralSingularShortComplex (cylinderBaseInclusion (cwBallBoundarySet 2))
  let B := cwRelativeIntegralSingularShortComplex (twoSkeletonInclusion W)
  let H₁ := (positiveDiskBoundaryReverseSweep W i).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)
  let H₂ := (positiveDiskReverseSweep W i).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)
  let H₃ := positiveDiskRelativeReverseSweep W i
  apply closedPrism_relative_boundary_eq_zero A B
    (cwRelativeIntegralSingularShortComplex_shortExact _)
    (cwRelativeIntegralSingularShortComplex_shortExact _) H₁ H₂ H₃
  · intro p q
    exact topologicalPrism_naturality (positiveDiskBoundaryReverseSweep W i)
      (positiveDiskReverseSweep W i)
      (cylinderBaseInclusion (cwBallBoundarySet 2)) (twoSkeletonInclusion W)
      (by ext p; rfl) (AddCommGrpCat.of ℤ) p q
  · intro p q
    exact cwRelativeSingularHomotopy_projection
      (f := positiveDiskPair W) (g := positiveDiskPair W)
      (positiveDiskBoundaryReverseSweep W i)
      (positiveDiskReverseSweep W i) (by ext p; rfl) p q
  · exact positiveNestedBoundaryReverseSweep_homology_zero W i

public theorem positiveReverseSweep_eq_reversedCylinder
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (p : unitInterval × CWCharacteristicClosedBall 2) :
    positiveDiskReverseSweep W i p =
      cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 2))
        (threeCylinderPair W i).right p := by
  change circleSweepHomotopy W i (unitInterval.symm p.1,
      correctedPositiveTwoOrbit W p.2.1) = _
  change _ = (threeCylinderPair W i).right
    (cylinderVerticalScale p.1 1, p.2)
  rw [threeCylinderPair_apply]
  congr 1
  apply Prod.ext
  · apply Subtype.ext
    change 1 - (p.1 : ℝ) = (1 - (p.1 : ℝ)) * 1
    ring
  · rfl

public theorem positiveReverseSweep_prism
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) (p q : ℕ) :
    ((positiveDiskReverseSweep W i).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom p q =
    ((cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 2))
      (threeCylinderPair W i).right).singularChainComplexFunctorObjMap
        (AddCommGrpCat.of ℤ)).hom p q := by
  have h := topologicalPrism_naturality (positiveDiskReverseSweep W i)
    (cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 2))
      (threeCylinderPair W i).right) (𝟙 _) (𝟙 _) (by
        ext x : 1
        exact (positiveReverseSweep_eq_reversedCylinder W i (x.2.down, x.1)).symm)
    (AddCommGrpCat.of ℤ) p q
  change (cwIntegralSingularChainMapObj (𝟙 _)).f p ≫ _ =
    _ ≫ (cwIntegralSingularChainMapObj (𝟙 _)).f q at h
  rw [cwIntegralSingularChainMapObj_id, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.id_f, HomologicalComplex.id_f, Category.id_comp, Category.comp_id] at h
  exact h.symm

public theorem threePrism_relative_compatibility
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) (p q : ℕ) :
    (cwRelativeIntegralSingularChainMapOfPair
      (cylinderTopLowerPair (X := TopCat.of (CWCharacteristicClosedBall 2))
        (cwBallBoundarySet 2))).f p ≫
      (cylinderRelativeContraction (cwBallBoundarySet 2)).hom p q ≫
        (cwRelativeIntegralSingularChainMapOfPair (threeLowerCylinderPair W i)).f q =
      (positiveDiskRelativeReverseSweep W i).hom p q := by
  apply cylinderRelativeContraction_sweep_relative
  have h := cwRelativeSingularHomotopy_projection
    (f := positiveDiskPair W) (g := positiveDiskPair W)
    (positiveDiskBoundaryReverseSweep W i)
    (positiveDiskReverseSweep W i) (by ext p; rfl) p q
  rw [positiveReverseSweep_prism] at h
  exact h

public theorem threeCylinderPair_relative_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainMapOfPair (threeCylinderPair W i)) 3 ≫
        cwRelativeIntegralSingularBoundary (twoSkeletonInclusion W) 2 = 0 := by
  let S := cylinderRelativeTriple (cwBallBoundarySet 2)
  let K := cwRelativeIntegralSingularChainComplex (cylinderBaseInclusion (cwBallBoundarySet 2))
  let L := cwRelativeIntegralSingularChainComplex (twoSkeletonInclusion W)
  let f : K ⟶ S.X₁ := cylinderTopFaceRelativeChains (cwBallBoundarySet 2)
  let g : S.X₃ ⟶ L := cwRelativeIntegralSingularChainMapOfPair (threeCylinderPair W i)
  have ht : f ≫ S.f = cwRelativeIntegralSingularChainMapOfPair
      (cylinderTopLowerPair (X := TopCat.of (CWCharacteristicClosedBall 2)) (cwBallBoundarySet 2)) := by
    dsimp only [f, S, cylinderRelativeTriple]
    rw [cwRelativeTripleShortComplex_f]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp
      (cylinderTopFacePairMap (cwBallBoundarySet 2)) _).symm
  have hg : S.g ≫ g = cwRelativeIntegralSingularChainMapOfPair
      (threeLowerCylinderPair W i) := by
    dsimp only [S, cylinderRelativeTriple, g]
    rw [cwRelativeTripleShortComplex_g]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp _
      (threeCylinderPair W i)).symm
  apply mappedContractingPrism_boundary_eq_zero S (cylinderRelativeContraction _) K L f g
    (positiveDiskRelativeReverseSweep W i) 1
  · have ht' := congrArg (fun k ↦ k.f 2) ht
    have hg' := congrArg (fun k ↦ k.f 3) hg
    change f.f 2 ≫ S.f.f 2 = _ at ht'
    change S.g.f 3 ≫ g.f 3 = _ at hg'
    erw [← Category.assoc, ← Category.assoc, ← Category.assoc, ht', Category.assoc,
      Category.assoc, hg']
    exact threePrism_relative_compatibility W i 2 3
  · exact cylinderTopPrismClass_surjective (cwBallBoundarySet 2) 1
  · exact positiveRelativeReverseSweep_boundary_zero W i

public theorem threeCharacteristicPair_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (threeCharacteristicPair W i).left) 2 = 0 := by
  let e := cwCharacteristicCylinderRelativeIso 2
  have hg : cwRelativeIntegralSingularChainMapOfPair (threeCylinderPair W i) =
      e.hom ≫ cwRelativeIntegralSingularChainMapOfPair (threeCharacteristicPair W i) :=
    cwRelativeIntegralSingularChainMapOfPair_comp _ _
  have hr : HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainMapOfPair (threeCharacteristicPair W i)) 3 ≫
        cwRelativeIntegralSingularBoundary (twoSkeletonInclusion W) 2 = 0 := by
    apply (cancel_epi (HomologicalComplex.homologyMap e.hom 3)).mp
    have h := threeCylinderPair_relative_boundary_zero W i
    erw [hg, HomologicalComplex.homologyMap_comp, Category.assoc] at h
    simpa using h
  let := cwCharacteristicBoundary_isIso 2 (by decide)
  apply (cancel_epi (cwRelativeIntegralSingularBoundary (cwCharacteristicBoundaryInclusion 3) 2)).mp
  rw [cwRelativeIntegralSingularBoundary_natural, hr, comp_zero]

public theorem threeCell_attachingDegree_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (i : Fin 2) (j : Fin 4) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 2 i j = 0 :=
  threeCell_attachingDegree_zero_of_boundary W T i
    (threeCharacteristicPair_boundary_zero W i) j

public def threeDiskMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.of (CWCharacteristicClosedBall 3) ⟶ TopCat.of (ActualLocalCuspCentralOrbitQuotient W) :=
  TopCat.ofHom ⟨fun b ↦ correctedThreeOrbit W 0 b.1,
    (continuousOn_correctedThreeOrbit W 0).domRestrict⟩

public def threeDiskPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cylinderBaseInclusion (cwBallBoundarySet 3))
      (threeSkeletonInclusion W) where
  left := TopCat.ofHom ⟨fun b ↦ ⟨correctedThreeOrbit W 0 b.1.1,
    Or.inl (correctedThreeOrbit_mapsTo_twoSkeleton W 0 b.2)⟩,
    ((threeDiskMap W).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  right := threeDiskMap W
  comm := rfl

public def threeDiskReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.Homotopy (threeDiskPair W).right
      (threeDiskPair W).right :=
  TopCat.Homotopy.comp (circleSweepHomotopy W 1).symm
    (TopCat.Homotopy.refl (threeDiskMap W))

public def threeDiskBoundaryReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopCat.Homotopy (threeDiskPair W).left
      (threeDiskPair W).left where
  toFun := threeNestedBoundaryReverseSweep W
  continuous_toFun := (threeNestedBoundaryReverseSweep W).continuous
  map_zero_left p := (threeNestedBoundaryReverseSweep W).map_zero_left p
  map_one_left p := (threeNestedBoundaryReverseSweep W).map_one_left p

public def threeDiskRelativeReverseSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  cwRelativeSingularHomotopy (f := threeDiskPair W)
    (g := threeDiskPair W)
    (threeDiskBoundaryReverseSweep W)
    (threeDiskReverseSweep W) (by ext p; rfl)

public def fourLowerCylinderPair
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CWTopologicalPairMap (cylinderLowerSideInclusion (cwBallBoundarySet 3))
      (threeSkeletonInclusion W) where
  left := cylinderLowerSideToBoundary (cwBallBoundarySet 3) ≫
    (fourCylinderPair W).left
  right := (fourCylinderPair W).right
  comm := rfl

public instance threeSkeletonInclusion_mono
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Mono (threeSkeletonInclusion W) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

public theorem threeRelativeReverseSweep_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    closedPrismHomology (threeDiskRelativeReverseSweep W) 2 ≫
      cwRelativeIntegralSingularBoundary (threeSkeletonInclusion W) 3 = 0 := by
  let A := cwRelativeIntegralSingularShortComplex (cylinderBaseInclusion (cwBallBoundarySet 3))
  let B := cwRelativeIntegralSingularShortComplex (threeSkeletonInclusion W)
  let H₁ := (threeDiskBoundaryReverseSweep W).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)
  let H₂ := (threeDiskReverseSweep W).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)
  let H₃ := threeDiskRelativeReverseSweep W
  apply closedPrism_relative_boundary_eq_zero A B
    (cwRelativeIntegralSingularShortComplex_shortExact _)
    (cwRelativeIntegralSingularShortComplex_shortExact _) H₁ H₂ H₃
  · intro p q
    exact topologicalPrism_naturality (threeDiskBoundaryReverseSweep W)
      (threeDiskReverseSweep W)
      (cylinderBaseInclusion (cwBallBoundarySet 3)) (threeSkeletonInclusion W)
      (by ext p; rfl) (AddCommGrpCat.of ℤ) p q
  · intro p q
    exact cwRelativeSingularHomotopy_projection
      (f := threeDiskPair W) (g := threeDiskPair W)
      (threeDiskBoundaryReverseSweep W)
      (threeDiskReverseSweep W) (by ext p; rfl) p q
  · exact threeNestedBoundaryReverseSweep_homology_zero W
      (threeCharacteristicPair_boundary_zero W 0)

public theorem threeReverseSweep_eq_reversedCylinder
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : unitInterval × CWCharacteristicClosedBall 3) :
    threeDiskReverseSweep W p =
      cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 3))
        (fourCylinderPair W).right p := by
  change circleSweepHomotopy W 1 (unitInterval.symm p.1,
      correctedThreeOrbit W 0 p.2.1) = _
  change _ = (fourCylinderPair W).right
    (cylinderVerticalScale p.1 1, p.2)
  rw [fourCylinderPair_apply]
  congr 1
  apply Prod.ext
  · apply Subtype.ext
    change 1 - (p.1 : ℝ) = (1 - (p.1 : ℝ)) * 1
    ring
  · rfl

public theorem threeReverseSweep_prism
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p q : ℕ) :
    ((threeDiskReverseSweep W).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)).hom p q =
    ((cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 3))
      (fourCylinderPair W).right).singularChainComplexFunctorObjMap
        (AddCommGrpCat.of ℤ)).hom p q := by
  have h := topologicalPrism_naturality (threeDiskReverseSweep W)
    (cylinderReversedSweep (X := TopCat.of (CWCharacteristicClosedBall 3))
      (fourCylinderPair W).right) (𝟙 _) (𝟙 _) (by
        ext x : 1
        exact (threeReverseSweep_eq_reversedCylinder W (x.2.down, x.1)).symm)
    (AddCommGrpCat.of ℤ) p q
  change (cwIntegralSingularChainMapObj (𝟙 _)).f p ≫ _ =
    _ ≫ (cwIntegralSingularChainMapObj (𝟙 _)).f q at h
  rw [cwIntegralSingularChainMapObj_id, cwIntegralSingularChainMapObj_id,
    HomologicalComplex.id_f, HomologicalComplex.id_f, Category.id_comp, Category.comp_id] at h
  exact h.symm

public theorem fourPrism_relative_compatibility
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p q : ℕ) :
    (cwRelativeIntegralSingularChainMapOfPair
      (cylinderTopLowerPair (X := TopCat.of (CWCharacteristicClosedBall 3))
        (cwBallBoundarySet 3))).f p ≫
      (cylinderRelativeContraction (cwBallBoundarySet 3)).hom p q ≫
        (cwRelativeIntegralSingularChainMapOfPair (fourLowerCylinderPair W)).f q =
      (threeDiskRelativeReverseSweep W).hom p q := by
  apply cylinderRelativeContraction_sweep_relative
  have h := cwRelativeSingularHomotopy_projection
    (f := threeDiskPair W) (g := threeDiskPair W)
    (threeDiskBoundaryReverseSweep W)
    (threeDiskReverseSweep W) (by ext p; rfl) p q
  rw [threeReverseSweep_prism] at h
  exact h

public theorem fourCylinderPair_relative_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainMapOfPair (fourCylinderPair W)) 4 ≫
        cwRelativeIntegralSingularBoundary (threeSkeletonInclusion W) 3 = 0 := by
  let S := cylinderRelativeTriple (cwBallBoundarySet 3)
  let K := cwRelativeIntegralSingularChainComplex (cylinderBaseInclusion (cwBallBoundarySet 3))
  let L := cwRelativeIntegralSingularChainComplex (threeSkeletonInclusion W)
  let f : K ⟶ S.X₁ := cylinderTopFaceRelativeChains (cwBallBoundarySet 3)
  let g : S.X₃ ⟶ L := cwRelativeIntegralSingularChainMapOfPair (fourCylinderPair W)
  have ht : f ≫ S.f = cwRelativeIntegralSingularChainMapOfPair
      (cylinderTopLowerPair (X := TopCat.of (CWCharacteristicClosedBall 3)) (cwBallBoundarySet 3)) := by
    dsimp only [f, S, cylinderRelativeTriple]
    rw [cwRelativeTripleShortComplex_f]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp
      (cylinderTopFacePairMap (cwBallBoundarySet 3)) _).symm
  have hg : S.g ≫ g = cwRelativeIntegralSingularChainMapOfPair
      (fourLowerCylinderPair W) := by
    dsimp only [S, cylinderRelativeTriple, g]
    rw [cwRelativeTripleShortComplex_g]
    exact (cwRelativeIntegralSingularChainMapOfPair_comp _
      (fourCylinderPair W)).symm
  apply mappedContractingPrism_boundary_eq_zero S (cylinderRelativeContraction _) K L f g
    (threeDiskRelativeReverseSweep W) 2
  · have ht' := congrArg (fun k ↦ k.f 3) ht
    have hg' := congrArg (fun k ↦ k.f 4) hg
    change f.f 3 ≫ S.f.f 3 = _ at ht'
    change S.g.f 4 ≫ g.f 4 = _ at hg'
    erw [← Category.assoc, ← Category.assoc, ← Category.assoc, ht', Category.assoc,
      Category.assoc, hg']
    exact fourPrism_relative_compatibility W 3 4
  · exact cylinderTopPrismClass_surjective (cwBallBoundarySet 3) 2
  · exact threeRelativeReverseSweep_boundary_zero W

public theorem fourCharacteristicPair_boundary_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    HomologicalComplex.homologyMap
      (cwIntegralSingularChainMapObj (fourCharacteristicPair W).left) 3 = 0 := by
  let e := cwCharacteristicCylinderRelativeIso 3
  have hg : cwRelativeIntegralSingularChainMapOfPair (fourCylinderPair W) =
      e.hom ≫ cwRelativeIntegralSingularChainMapOfPair (fourCharacteristicPair W) :=
    cwRelativeIntegralSingularChainMapOfPair_comp _ _
  have hr : HomologicalComplex.homologyMap
      (cwRelativeIntegralSingularChainMapOfPair (fourCharacteristicPair W)) 4 ≫
        cwRelativeIntegralSingularBoundary (threeSkeletonInclusion W) 3 = 0 := by
    apply (cancel_epi (HomologicalComplex.homologyMap e.hom 4)).mp
    have h := fourCylinderPair_relative_boundary_zero W
    erw [hg, HomologicalComplex.homologyMap_comp, Category.assoc] at h
    simpa using h
  let := cwCharacteristicBoundary_isIso 3 (by decide)
  apply (cancel_epi (cwRelativeIntegralSingularBoundary (cwCharacteristicBoundaryInclusion 4) 3)).mp
  rw [cwRelativeIntegralSingularBoundary_natural, hr, comp_zero]

public theorem fourCell_attachingDegree_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (j : Fin 2) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 3 (0 : Fin 1) j = 0 :=
  fourCell_attachingDegree_zero_of_boundary W T
    (fourCharacteristicPair_boundary_zero W) j

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
