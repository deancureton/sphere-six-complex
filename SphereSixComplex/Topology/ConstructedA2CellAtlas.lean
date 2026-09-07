module

public import SphereSixComplex.Topology.StandardA2PhaseCellRegularity
public import SphereSixComplex.Topology.PaperCuspCentralFiberCWTypes

@[expose] public section
noncomputable section
open Set Matrix Topology
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def constructedCentralCellMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (n : ℕ) → SphereSixComplex.cuspWCellIndex n →
      PartialEquiv (Fin n → ℝ) (ActualLocalCuspCentralOrbitQuotient W)
  | 0 => constructedCentralZeroCell W
  | 1 => constructedCentralOneCell W
  | 2 => ![constructedA2CorrectedPositiveTwoCell W, constructedCentralPhaseTwoCell W 0,
      constructedCentralPhaseTwoCell W 1, constructedCentralPhaseTwoCell W 2]
  | 3 => constructedA2CorrectedThreeCell W
  | 4 => fun _ ↦ constructedA2CorrectedFourCell W
  | _ + 5 => fun i ↦ i.elim

public theorem constructedCentralCellMap_source_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (i : SphereSixComplex.cuspWCellIndex n) :
    (constructedCentralCellMap W n i).source = Metric.ball 0 1 := by
  rcases n with (_ | _ | _ | _ | _ | n)
  · exact constructedCentralZeroCell_source_eq W i
  · exact constructedCentralOneCell_source_eq W i
  · change Fin 4 at i
    fin_cases i
    · exact constructedA2CorrectedPositiveTwoCell_source_eq W
    · exact constructedCentralPhaseTwoCell_source_eq W 0
    · exact constructedCentralPhaseTwoCell_source_eq W 1
    · exact constructedCentralPhaseTwoCell_source_eq W 2
  · exact constructedA2CorrectedThreeCell_source_eq W i
  · exact constructedA2CorrectedFourCell_source_eq W
  · exact i.elim

public theorem constructedCentralCellMap_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (i : SphereSixComplex.cuspWCellIndex n) :
    ContinuousOn (constructedCentralCellMap W n i) (Metric.closedBall 0 1) := by
  rcases n with (_ | _ | _ | _ | _ | n)
  · exact constructedCentralZeroCell_continuousOn W i
  · exact constructedCentralOneCell_continuousOn W i
  · change Fin 4 at i
    fin_cases i
    · exact constructedA2CorrectedPositiveTwoCell_continuousOn W
    · exact constructedCentralPhaseTwoCell_continuousOn W 0
    · exact constructedCentralPhaseTwoCell_continuousOn W 1
    · exact constructedCentralPhaseTwoCell_continuousOn W 2
  · exact constructedA2CorrectedThreeCell_continuousOn W i
  · exact constructedA2CorrectedFourCell_continuousOn W
  · exact i.elim

public theorem constructedCentralCellMap_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (i : SphereSixComplex.cuspWCellIndex n) :
    ContinuousOn (constructedCentralCellMap W n i).symm (constructedCentralCellMap W n i).target := by
  rcases n with (_ | _ | _ | _ | _ | n)
  · exact constructedCentralZeroCell_continuousOn_symm W i
  · exact constructedCentralOneCell_continuousOn_symm W i
  · change Fin 4 at i
    fin_cases i
    · exact constructedA2CorrectedPositiveTwoCell_continuousOn_symm W
    · exact constructedCentralPhaseTwoCell_continuousOn_symm W 0
    · exact constructedCentralPhaseTwoCell_continuousOn_symm W 1
    · exact constructedCentralPhaseTwoCell_continuousOn_symm W 2
  · exact constructedA2CorrectedThreeCell_continuousOn_symm W i
  · exact constructedA2CorrectedFourCell_continuousOn_symm W
  · exact i.elim

public def constructedCentralCellSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) :=
  ⋃ (m < n) (j : SphereSixComplex.cuspWCellIndex m),
    constructedCentralCellMap W m j '' Metric.closedBall 0 1

public theorem constructedCentralOneSkeleton_subset_cellSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) {n : ℕ} (hn : 1 < n) :
    constructedCentralOneSkeleton W ⊆ constructedCentralCellSkeleton W n := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by omega,
      Set.mem_iUnion.mpr ⟨i, hi⟩⟩⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨hn,
      Set.mem_iUnion.mpr ⟨i, hi⟩⟩⟩

public theorem constructedCentralBoundaryTwoSkeleton_subset_cellSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) {n : ℕ} (hn : 2 < n) :
    constructedCentralBoundaryTwoSkeleton W ⊆ constructedCentralCellSkeleton W n := by
  intro x hx
  rcases hx with hx | hx
  · exact constructedCentralOneSkeleton_subset_cellSkeleton W (by omega) hx
  · obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨2, Set.mem_iUnion.mpr ⟨hn, ?_⟩⟩
    fin_cases i
    · exact Set.mem_iUnion.mpr ⟨(1 : Fin 4), y, Metric.ball_subset_closedBall hy, rfl⟩
    · exact Set.mem_iUnion.mpr ⟨(2 : Fin 4), y, Metric.ball_subset_closedBall hy, rfl⟩
    · exact Set.mem_iUnion.mpr ⟨(3 : Fin 4), y, Metric.ball_subset_closedBall hy, rfl⟩

public theorem constructedA2CorrectedTwoSkeleton_subset_cellSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) {n : ℕ} (hn : 2 < n) :
    constructedA2CorrectedTwoSkeleton W ⊆ constructedCentralCellSkeleton W n := by
  intro x hx
  rcases hx with hx | hx
  · exact constructedCentralBoundaryTwoSkeleton_subset_cellSkeleton W hn hx
  · exact Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨hn,
      Set.mem_iUnion.mpr ⟨(0 : Fin 4), hx⟩⟩⟩

public theorem constructedA2CorrectedThreeSkeleton_subset_cellSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) {n : ℕ} (hn : 3 < n) :
    constructedA2CorrectedThreeSkeleton W ⊆ constructedCentralCellSkeleton W n := by
  intro x hx
  rcases hx with hx | hx
  · exact constructedA2CorrectedTwoSkeleton_subset_cellSkeleton W (by omega) hx
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨3, Set.mem_iUnion.mpr ⟨hn,
      Set.mem_iUnion.mpr ⟨i, hi⟩⟩⟩

public theorem constructedCentralCellMap_mapsTo
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (i : SphereSixComplex.cuspWCellIndex n) :
    MapsTo (constructedCentralCellMap W n i) (Metric.sphere 0 1)
      (constructedCentralCellSkeleton W n) := by
  rcases n with (_ | _ | _ | _ | _ | n)
  · intro x hx
    have : x = 0 := Subsingleton.elim _ _
    rw [this, Metric.mem_sphere, dist_self] at hx
    norm_num at hx
  · intro x hx
    have h := constructedCentralOneCell_mapsTo_zeroCells W i hx
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by decide, h⟩⟩
  · apply Set.MapsTo.mono_right _ (constructedCentralOneSkeleton_subset_cellSkeleton W (by decide))
    change Fin 4 at i
    fin_cases i
    · exact constructedA2CorrectedPositiveTwoCell_mapsTo_oneSkeleton W
    · exact constructedCentralPhaseTwoCell_mapsTo_oneSkeleton W 0
    · exact constructedCentralPhaseTwoCell_mapsTo_oneSkeleton W 1
    · exact constructedCentralPhaseTwoCell_mapsTo_oneSkeleton W 2
  · exact (constructedA2CorrectedThreeOrbit_mapsTo_twoSkeleton W i).mono_right
      (constructedA2CorrectedTwoSkeleton_subset_cellSkeleton W (by decide))
  · exact (constructedA2CorrectedFourOrbit_mapsTo_threeSkeleton W).mono_right
      (constructedA2CorrectedThreeSkeleton_subset_cellSkeleton W (by decide))
  · exact i.elim

public theorem constructedCentralCellMap_union_eq
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (⋃ n, ⋃ i, constructedCentralCellMap W n i '' Metric.closedBall 0 1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ constructedCentralBoundaryTwoSkeleton W ∪
      constructedA2CorrectedFourOrbit W '' Metric.closedBall 0 1 := by
    rw [constructedA2BoundaryTwoSkeleton_union_closedFour W]
    trivial
  rcases hx with hx | hx
  · have hs := constructedCentralBoundaryTwoSkeleton_subset_cellSkeleton W (n := 5) (by decide) hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hs
    obtain ⟨_, hi⟩ := Set.mem_iUnion.mp hm
    exact Set.mem_iUnion.mpr ⟨m, hi⟩
  · exact Set.mem_iUnion.mpr ⟨4, Set.mem_iUnion.mpr ⟨(0 : Fin 1), hx⟩⟩

private theorem constructedCentralCellMap_disjoint_0
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 2) (m : ℕ) (j : SphereSixComplex.cuspWCellIndex m)
    (hij : (⟨0, i⟩ : Σ n, SphereSixComplex.cuspWCellIndex n) ≠ ⟨m, j⟩) :
    Disjoint (constructedCentralCellMap W 0 i '' Metric.ball 0 1)
      (constructedCentralCellMap W m j '' Metric.ball 0 1) := by
  have hp : constructedA2CorrectedPositiveTwoCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPositiveTwoOrbit_mem_singleton W hx
  have ht (i : Fin 2) : constructedA2CorrectedThreeCell W i '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 1 _ hx
  have hf : constructedA2CorrectedFourCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 2 _ hx
  have hz (i : Fin 2) : Disjoint
      (constructedCentralZeroCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) :=
    (constructedCentralZeroCell_singleton_disjoint W i).mono_left
      (Set.image_mono Metric.ball_subset_closedBall)
  rcases m with (_ | _ | _ | _ | _ | m)
  all_goals try exact j.elim
  all_goals first | change Fin 1 at j | change Fin 2 at j | change Fin 3 at j | change Fin 4 at j
  all_goals fin_cases i <;> fin_cases j
  all_goals dsimp only [constructedCentralCellMap, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first
    | exact (hij rfl).elim
    | exact (constructedCentralZeroCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralOneCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedA2CorrectedThreeOrbit_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact constructedCentralZeroCell_oneCell_disjoint W _ _
    | exact (constructedCentralZeroCell_oneCell_disjoint W _ _).symm
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _).symm
    | exact constructedA2CorrectedPositiveTwo_three_disjoint W _
    | exact (constructedA2CorrectedPositiveTwo_three_disjoint W _).symm
    | exact constructedA2CorrectedPositiveTwo_four_disjoint W
    | exact (constructedA2CorrectedPositiveTwo_four_disjoint W).symm
    | exact constructedA2CorrectedThree_four_disjoint W _
    | exact (constructedA2CorrectedThree_four_disjoint W _).symm
    | exact (hz _).mono_right hp
    | exact ((hz _).mono_right hp).symm
    | exact (hz _).mono_right (ht _)
    | exact ((hz _).mono_right (ht _)).symm
    | exact (hz _).mono_right hf

private theorem constructedCentralCellMap_disjoint_1
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (m : ℕ) (j : SphereSixComplex.cuspWCellIndex m)
    (hij : (⟨1, i⟩ : Σ n, SphereSixComplex.cuspWCellIndex n) ≠ ⟨m, j⟩) :
    Disjoint (constructedCentralCellMap W 1 i '' Metric.ball 0 1)
      (constructedCentralCellMap W m j '' Metric.ball 0 1) := by
  have hp : constructedA2CorrectedPositiveTwoCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPositiveTwoOrbit_mem_singleton W hx
  have ht (i : Fin 2) : constructedA2CorrectedThreeCell W i '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 1 _ hx
  have hf : constructedA2CorrectedFourCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 2 _ hx
  have hz (i : Fin 2) : Disjoint
      (constructedCentralZeroCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) :=
    (constructedCentralZeroCell_singleton_disjoint W i).mono_left
      (Set.image_mono Metric.ball_subset_closedBall)
  rcases m with (_ | _ | _ | _ | _ | m)
  all_goals try exact j.elim
  all_goals first | change Fin 1 at j | change Fin 2 at j | change Fin 3 at j | change Fin 4 at j
  all_goals fin_cases i <;> fin_cases j
  all_goals dsimp only [constructedCentralCellMap, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first
    | exact (hij rfl).elim
    | exact (constructedCentralZeroCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralOneCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedA2CorrectedThreeOrbit_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact constructedCentralZeroCell_oneCell_disjoint W _ _
    | exact (constructedCentralZeroCell_oneCell_disjoint W _ _).symm
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _).symm
    | exact constructedA2CorrectedPositiveTwo_three_disjoint W _
    | exact (constructedA2CorrectedPositiveTwo_three_disjoint W _).symm
    | exact constructedA2CorrectedPositiveTwo_four_disjoint W
    | exact (constructedA2CorrectedPositiveTwo_four_disjoint W).symm
    | exact constructedA2CorrectedThree_four_disjoint W _
    | exact (constructedA2CorrectedThree_four_disjoint W _).symm
    | exact (hz _).mono_right hp
    | exact ((hz _).mono_right hp).symm
    | exact (hz _).mono_right (ht _)
    | exact ((hz _).mono_right (ht _)).symm
    | exact (hz _).mono_right hf
    | exact ((hz _).mono_right hf).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right hp
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right hp).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right (ht _)
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right (ht _)).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right hf

private theorem constructedCentralCellMap_disjoint_2_0
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 4) (hi : i = 0) (m : ℕ) (j : SphereSixComplex.cuspWCellIndex m)
    (hij : (⟨2, i⟩ : Σ n, SphereSixComplex.cuspWCellIndex n) ≠ ⟨m, j⟩) :
    Disjoint (constructedCentralCellMap W 2 i '' Metric.ball 0 1)
      (constructedCentralCellMap W m j '' Metric.ball 0 1) := by
  have hp : constructedA2CorrectedPositiveTwoCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPositiveTwoOrbit_mem_singleton W hx
  have ht (i : Fin 2) : constructedA2CorrectedThreeCell W i '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 1 _ hx
  have hf : constructedA2CorrectedFourCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 2 _ hx
  have hz (i : Fin 2) : Disjoint
      (constructedCentralZeroCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) :=
    (constructedCentralZeroCell_singleton_disjoint W i).mono_left
      (Set.image_mono Metric.ball_subset_closedBall)
  subst i
  rcases m with (_ | _ | _ | _ | _ | m)
  all_goals try exact j.elim
  all_goals first | change Fin 1 at j | change Fin 2 at j | change Fin 3 at j | change Fin 4 at j
  all_goals fin_cases j
  all_goals dsimp only [constructedCentralCellMap, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first
    | exact (hij rfl).elim
    | exact (constructedCentralZeroCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralOneCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedA2CorrectedThreeOrbit_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact constructedCentralZeroCell_oneCell_disjoint W _ _
    | exact (constructedCentralZeroCell_oneCell_disjoint W _ _).symm
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _).symm
    | exact constructedA2CorrectedPositiveTwo_three_disjoint W _
    | exact (constructedA2CorrectedPositiveTwo_three_disjoint W _).symm
    | exact constructedA2CorrectedPositiveTwo_four_disjoint W
    | exact (constructedA2CorrectedPositiveTwo_four_disjoint W).symm
    | exact constructedA2CorrectedThree_four_disjoint W _
    | exact (constructedA2CorrectedThree_four_disjoint W _).symm
    | exact (hz _).mono_right hp
    | exact ((hz _).mono_right hp).symm
    | exact (hz _).mono_right (ht _)
    | exact ((hz _).mono_right (ht _)).symm
    | exact (hz _).mono_right hf
    | exact ((hz _).mono_right hf).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right hp
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right hp).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right (ht _)
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right (ht _)).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right hf
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right hf).symm
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hp
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hp
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hp
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hp).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hp).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hp).symm

private theorem constructedCentralCellMap_disjoint_2_1
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 4) (hi : i = 1) (m : ℕ) (j : SphereSixComplex.cuspWCellIndex m)
    (hij : (⟨2, i⟩ : Σ n, SphereSixComplex.cuspWCellIndex n) ≠ ⟨m, j⟩) :
    Disjoint (constructedCentralCellMap W 2 i '' Metric.ball 0 1)
      (constructedCentralCellMap W m j '' Metric.ball 0 1) := by
  have hp : constructedA2CorrectedPositiveTwoCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPositiveTwoOrbit_mem_singleton W hx
  have ht (i : Fin 2) : constructedA2CorrectedThreeCell W i '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 1 _ hx
  have hf : constructedA2CorrectedFourCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 2 _ hx
  have hz (i : Fin 2) : Disjoint
      (constructedCentralZeroCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) :=
    (constructedCentralZeroCell_singleton_disjoint W i).mono_left
      (Set.image_mono Metric.ball_subset_closedBall)
  subst i
  rcases m with (_ | _ | _ | _ | _ | m)
  all_goals try exact j.elim
  all_goals first | change Fin 1 at j | change Fin 2 at j | change Fin 3 at j | change Fin 4 at j
  all_goals fin_cases j
  all_goals dsimp only [constructedCentralCellMap, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first
    | exact (hij rfl).elim
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hp
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right (ht _)
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hf


private theorem constructedCentralCellMap_disjoint_2_2
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 4) (hi : i = 2) (m : ℕ) (j : SphereSixComplex.cuspWCellIndex m)
    (hij : (⟨2, i⟩ : Σ n, SphereSixComplex.cuspWCellIndex n) ≠ ⟨m, j⟩) :
    Disjoint (constructedCentralCellMap W 2 i '' Metric.ball 0 1)
      (constructedCentralCellMap W m j '' Metric.ball 0 1) := by
  have hp : constructedA2CorrectedPositiveTwoCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPositiveTwoOrbit_mem_singleton W hx
  have ht (i : Fin 2) : constructedA2CorrectedThreeCell W i '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 1 _ hx
  have hf : constructedA2CorrectedFourCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 2 _ hx
  have hz (i : Fin 2) : Disjoint
      (constructedCentralZeroCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) :=
    (constructedCentralZeroCell_singleton_disjoint W i).mono_left
      (Set.image_mono Metric.ball_subset_closedBall)
  subst i
  rcases m with (_ | _ | _ | _ | _ | m)
  all_goals try exact j.elim
  all_goals first | change Fin 1 at j | change Fin 2 at j | change Fin 3 at j | change Fin 4 at j
  all_goals fin_cases j
  all_goals dsimp only [constructedCentralCellMap, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first
    | exact (hij rfl).elim
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hp
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right (ht _)
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hf


private theorem constructedCentralCellMap_disjoint_2_3
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 4) (hi : i = 3) (m : ℕ) (j : SphereSixComplex.cuspWCellIndex m)
    (hij : (⟨2, i⟩ : Σ n, SphereSixComplex.cuspWCellIndex n) ≠ ⟨m, j⟩) :
    Disjoint (constructedCentralCellMap W 2 i '' Metric.ball 0 1)
      (constructedCentralCellMap W m j '' Metric.ball 0 1) := by
  have hp : constructedA2CorrectedPositiveTwoCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPositiveTwoOrbit_mem_singleton W hx
  have ht (i : Fin 2) : constructedA2CorrectedThreeCell W i '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 1 _ hx
  have hf : constructedA2CorrectedFourCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 2 _ hx
  have hz (i : Fin 2) : Disjoint
      (constructedCentralZeroCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) :=
    (constructedCentralZeroCell_singleton_disjoint W i).mono_left
      (Set.image_mono Metric.ball_subset_closedBall)
  subst i
  rcases m with (_ | _ | _ | _ | _ | m)
  all_goals try exact j.elim
  all_goals first | change Fin 1 at j | change Fin 2 at j | change Fin 3 at j | change Fin 4 at j
  all_goals fin_cases j
  all_goals dsimp only [constructedCentralCellMap, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first
    | exact (hij rfl).elim
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hp
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right (ht _)
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hf


private theorem constructedCentralCellMap_disjoint_2
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 4) (m : ℕ) (j : SphereSixComplex.cuspWCellIndex m)
    (hij : (⟨2, i⟩ : Σ n, SphereSixComplex.cuspWCellIndex n) ≠ ⟨m, j⟩) :
    Disjoint (constructedCentralCellMap W 2 i '' Metric.ball 0 1)
      (constructedCentralCellMap W m j '' Metric.ball 0 1) := by
  fin_cases i
  · exact constructedCentralCellMap_disjoint_2_0 W _ rfl m j hij
  · exact constructedCentralCellMap_disjoint_2_1 W _ rfl m j hij
  · exact constructedCentralCellMap_disjoint_2_2 W _ rfl m j hij
  · exact constructedCentralCellMap_disjoint_2_3 W _ rfl m j hij

private theorem constructedCentralCellMap_disjoint_3
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 2) (m : ℕ) (j : SphereSixComplex.cuspWCellIndex m)
    (hij : (⟨3, i⟩ : Σ n, SphereSixComplex.cuspWCellIndex n) ≠ ⟨m, j⟩) :
    Disjoint (constructedCentralCellMap W 3 i '' Metric.ball 0 1)
      (constructedCentralCellMap W m j '' Metric.ball 0 1) := by
  have hp : constructedA2CorrectedPositiveTwoCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPositiveTwoOrbit_mem_singleton W hx
  have ht (i : Fin 2) : constructedA2CorrectedThreeCell W i '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 1 _ hx
  have hf : constructedA2CorrectedFourCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 2 _ hx
  have hz (i : Fin 2) : Disjoint
      (constructedCentralZeroCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) :=
    (constructedCentralZeroCell_singleton_disjoint W i).mono_left
      (Set.image_mono Metric.ball_subset_closedBall)
  rcases m with (_ | _ | _ | _ | _ | m)
  all_goals try exact j.elim
  all_goals first | change Fin 1 at j | change Fin 2 at j | change Fin 3 at j | change Fin 4 at j
  all_goals fin_cases i <;> fin_cases j
  all_goals dsimp only [constructedCentralCellMap, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first
    | exact (hij rfl).elim
    | exact (constructedCentralZeroCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralOneCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedA2CorrectedThreeOrbit_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact constructedCentralZeroCell_oneCell_disjoint W _ _
    | exact (constructedCentralZeroCell_oneCell_disjoint W _ _).symm
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _).symm
    | exact constructedA2CorrectedPositiveTwo_three_disjoint W _
    | exact (constructedA2CorrectedPositiveTwo_three_disjoint W _).symm
    | exact constructedA2CorrectedPositiveTwo_four_disjoint W
    | exact (constructedA2CorrectedPositiveTwo_four_disjoint W).symm
    | exact constructedA2CorrectedThree_four_disjoint W _
    | exact (constructedA2CorrectedThree_four_disjoint W _).symm
    | exact (hz _).mono_right hp
    | exact ((hz _).mono_right hp).symm
    | exact (hz _).mono_right (ht _)
    | exact ((hz _).mono_right (ht _)).symm
    | exact (hz _).mono_right hf
    | exact ((hz _).mono_right hf).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right hp
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right hp).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right (ht _)
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right (ht _)).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right hf
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right hf).symm
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hp
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hp
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hp
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hp).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hp).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hp).symm
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right (ht _)
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right (ht _)
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right (ht _)
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right (ht _)).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right (ht _)).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right (ht _)).symm

private theorem constructedCentralCellMap_disjoint_4
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 1) (m : ℕ) (j : SphereSixComplex.cuspWCellIndex m)
    (hij : (⟨4, i⟩ : Σ n, SphereSixComplex.cuspWCellIndex n) ≠ ⟨m, j⟩) :
    Disjoint (constructedCentralCellMap W 4 i '' Metric.ball 0 1)
      (constructedCentralCellMap W m j '' Metric.ball 0 1) := by
  have hp : constructedA2CorrectedPositiveTwoCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPositiveTwoOrbit_mem_singleton W hx
  have ht (i : Fin 2) : constructedA2CorrectedThreeCell W i '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 1 _ hx
  have hf : constructedA2CorrectedFourCell W '' Metric.ball 0 1 ⊆
      constructedA2ActualSingletonStratum W := by
    rintro z ⟨x, hx, rfl⟩
    exact constructedA2CorrectedPhaseOrbit_mem_singleton W 2 _ hx
  have hz (i : Fin 2) : Disjoint
      (constructedCentralZeroCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) :=
    (constructedCentralZeroCell_singleton_disjoint W i).mono_left
      (Set.image_mono Metric.ball_subset_closedBall)
  rcases m with (_ | _ | _ | _ | _ | m)
  all_goals try exact j.elim
  all_goals first | change Fin 1 at j | change Fin 2 at j | change Fin 3 at j | change Fin 4 at j
  all_goals (fin_cases i; fin_cases j)
  all_goals dsimp only [constructedCentralCellMap, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first
    | exact (hij rfl).elim
    | exact (constructedCentralZeroCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralOneCell_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (0 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (1 : Fin 3)) (Set.mem_univ (2 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (0 : Fin 3)) (by decide)
    | exact (constructedCentralPhaseTwoCell_pairwiseDisjoint W) (Set.mem_univ (2 : Fin 3)) (Set.mem_univ (1 : Fin 3)) (by decide)
    | exact (constructedA2CorrectedThreeOrbit_pairwiseDisjoint W) (Set.mem_univ _) (Set.mem_univ _) (by decide)
    | exact constructedCentralZeroCell_oneCell_disjoint W _ _
    | exact (constructedCentralZeroCell_oneCell_disjoint W _ _).symm
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact (constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 0 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 1 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact ((constructedCentralPhaseTwoCell_zeroCell_disjoint W 2 _).mono_right (Set.image_mono Metric.ball_subset_closedBall)).symm
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _
    | exact constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 0 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 1 _).symm
    | exact (constructedCentralPhaseTwoCell_oneCell_disjoint W 2 _).symm
    | exact constructedA2CorrectedPositiveTwo_three_disjoint W _
    | exact (constructedA2CorrectedPositiveTwo_three_disjoint W _).symm
    | exact constructedA2CorrectedPositiveTwo_four_disjoint W
    | exact (constructedA2CorrectedPositiveTwo_four_disjoint W).symm
    | exact constructedA2CorrectedThree_four_disjoint W _
    | exact (constructedA2CorrectedThree_four_disjoint W _).symm
    | exact (hz _).mono_right hp
    | exact ((hz _).mono_right hp).symm
    | exact (hz _).mono_right (ht _)
    | exact ((hz _).mono_right (ht _)).symm
    | exact (hz _).mono_right hf
    | exact ((hz _).mono_right hf).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right hp
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right hp).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right (ht _)
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right (ht _)).symm
    | exact (constructedCentralOneCell_singleton_disjoint W _).mono_right hf
    | exact ((constructedCentralOneCell_singleton_disjoint W _).mono_right hf).symm
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hp
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hp
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hp
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hp).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hp).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hp).symm
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right (ht _)
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right (ht _)
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right (ht _)
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right (ht _)).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right (ht _)).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right (ht _)).symm
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hf
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hf
    | exact (constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hf
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 0).mono_right hf).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 1).mono_right hf).symm
    | exact ((constructedCentralPhaseTwoCell_singleton_disjoint W 2).mono_right hf).symm

public theorem constructedCentralCellMap_pairwiseDisjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Set.univ : Set (Σ n, SphereSixComplex.cuspWCellIndex n)).PairwiseDisjoint
      (fun ni ↦ constructedCentralCellMap W ni.1 ni.2 '' Metric.ball 0 1) := by
  rintro ⟨n, i⟩ _ ⟨m, j⟩ _ hij
  rcases n with (_ | _ | _ | _ | _ | n)
  · exact constructedCentralCellMap_disjoint_0 W i m j hij
  · exact constructedCentralCellMap_disjoint_1 W i m j hij
  · exact constructedCentralCellMap_disjoint_2 W i m j hij
  · exact constructedCentralCellMap_disjoint_3 W i m j hij
  · exact constructedCentralCellMap_disjoint_4 W i m j hij
  · exact i.elim

public def constructedCentralCellAtlas
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    SphereSixComplex.StandardA2ToricCentralFiberCellAtlas
      (ActualLocalCuspCentralOrbitQuotient W) where
  cellMap := constructedCentralCellMap W
  source_eq := constructedCentralCellMap_source_eq W
  continuousOn := constructedCentralCellMap_continuousOn W
  continuousOn_symm := constructedCentralCellMap_continuousOn_symm W
  pairwiseDisjoint := constructedCentralCellMap_pairwiseDisjoint W
  mapsTo := constructedCentralCellMap_mapsTo W
  union_eq := constructedCentralCellMap_union_eq W

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
