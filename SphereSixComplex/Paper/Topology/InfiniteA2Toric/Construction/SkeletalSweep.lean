module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CompactActionFiltration
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CircleSweepPrism
public import SphereSixComplex.Prerequisites.Topology.CharacteristicCylinderHomeomorph
public import SphereSixComplex.Prerequisites.Topology.ClosedPrismHomology
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveBoundaryLoop

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

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem circleSweep_one_to_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (t : unitInterval) (x : constructedCentralOneSkeleton W) :
    circleSweepHomotopy W i (t, x.1) ∈ correctedTwoSkeleton W :=
  Or.inl (centralCompactOrbitMap_oneSkeleton W _ x.2)

public theorem circleSweep_two_to_three
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (t : unitInterval) (x : correctedTwoSkeleton W) :
    circleSweepHomotopy W i (t, x.1) ∈ correctedThreeSkeleton W := by
  rcases x with ⟨x, hx | hx⟩
  · exact Or.inl (Or.inl (centralCompactOrbitMap_boundaryTwoSkeleton W _ hx))
  · obtain ⟨b, hb, rfl⟩ := hx
    rw [circleSweepHomotopy_positiveCell]
    apply Or.inr
    refine Set.mem_iUnion.mpr ⟨i, Fin.append b ![2 * (t : ℝ) - 1], ?_, rfl⟩
    rw [← cwCharacteristicCylinderHomeomorph_apply 2 t ⟨b, hb⟩]
    exact (cwCharacteristicCylinderHomeomorph 2 (t, ⟨b, hb⟩)).2

public def oneSkeletalSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  restrictedClosedHomotopy (circleSweepHomotopy W i)
    (show constructedCentralOneSkeleton W ⊆ correctedTwoSkeleton W from
      fun _ hx ↦ Or.inl (Or.inl hx)) (circleSweep_one_to_two W i)

public def twoSkeletalSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :=
  restrictedClosedHomotopy (circleSweepHomotopy W i)
    (show correctedTwoSkeleton W ⊆ correctedThreeSkeleton W from
      fun _ hx ↦ Or.inl hx) (circleSweep_two_to_three W i)


end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
