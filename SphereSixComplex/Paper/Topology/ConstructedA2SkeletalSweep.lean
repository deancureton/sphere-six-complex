module

public import SphereSixComplex.Paper.Topology.ConstructedA2CompactActionFiltration
public import SphereSixComplex.Paper.Topology.ConstructedA2CircleSweepPrism
public import SphereSixComplex.Prerequisites.Topology.CharacteristicCylinderHomeomorph
public import SphereSixComplex.Prerequisites.Topology.ClosedPrismHomology
public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveBoundaryLoop

@[expose] public section
noncomputable section
open Set Topology CategoryTheory
namespace SphereSixComplex

public def restrictedClosedHomotopy {X : Type} [TopologicalSpace X]
    (H : TopCat.Homotopy (𝟙 (TopCat.of X)) (𝟙 (TopCat.of X)))
    {A B : Set X} (hAB : A ⊆ B)
    (hH : ∀ t : unitInterval, ∀ x : A, H (t, x.1) ∈ B) :
    TopCat.Homotopy (TopCat.ofHom ⟨Set.inclusion hAB, continuous_inclusion hAB⟩)
      (TopCat.ofHom ⟨Set.inclusion hAB, continuous_inclusion hAB⟩) where
  toFun p := ⟨H (p.1, p.2.1), hH p.1 p.2⟩
  continuous_toFun := (H.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left p := by apply Subtype.ext; exact H.map_zero_left _
  map_one_left p := by apply Subtype.ext; exact H.map_one_left _

end SphereSixComplex

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

public theorem constructedA2CircleSweep_one_to_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (t : unitInterval) (x : constructedCentralOneSkeleton W) :
    constructedA2CircleSweepHomotopy W i (t, x.1) ∈ constructedA2CorrectedTwoSkeleton W :=
  Or.inl (constructedA2CentralCompactOrbitMap_oneSkeleton W _ x.2)

public theorem constructedA2CircleSweep_two_to_three
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (t : unitInterval) (x : constructedA2CorrectedTwoSkeleton W) :
    constructedA2CircleSweepHomotopy W i (t, x.1) ∈ constructedA2CorrectedThreeSkeleton W := by
  rcases x with ⟨x, hx | hx⟩
  · exact Or.inl (Or.inl (constructedA2CentralCompactOrbitMap_boundaryTwoSkeleton W _ hx))
  · obtain ⟨b, hb, rfl⟩ := hx
    rw [constructedA2CircleSweepHomotopy_positiveCell]
    apply Or.inr
    refine Set.mem_iUnion.mpr ⟨i, Fin.append b ![2 * (t : ℝ) - 1], ?_, rfl⟩
    rw [← cwCharacteristicCylinderHomeomorph_apply 2 t ⟨b, hb⟩]
    exact (cwCharacteristicCylinderHomeomorph 2 (t, ⟨b, hb⟩)).2

public def constructedA2OneSkeletalSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  restrictedClosedHomotopy (constructedA2CircleSweepHomotopy W i)
    (show constructedCentralOneSkeleton W ⊆ constructedA2CorrectedTwoSkeleton W from
      fun _ hx ↦ Or.inl (Or.inl hx)) (constructedA2CircleSweep_one_to_two W i)

public def constructedA2TwoSkeletalSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  restrictedClosedHomotopy (constructedA2CircleSweepHomotopy W i)
    (show constructedA2CorrectedTwoSkeleton W ⊆ constructedA2CorrectedThreeSkeleton W from
      fun _ hx ↦ Or.inl hx) (constructedA2CircleSweep_two_to_three W i)

public theorem constructedA2OneSkeletalSweep_hexagon_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    closedPrismHomology ((constructedA2OneSkeletalSweep W i).singularChainComplexFunctorObjMap
      (AddCommGrpCat.of ℤ)) 0
      (SphereSixComplex.StandardCircleHomologyLiftDegree.loopHomologyClass
        (constructedA2OneSkeletonHexagonLoop W)) = 0 := by
  rw [constructedA2OneSkeletonHexagonLoop_homology_zero]
  exact (closedPrismHomology ((constructedA2OneSkeletalSweep W i).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of ℤ)) 0).hom.map_zero

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
