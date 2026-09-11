module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepCharacteristicPairs
public import SphereSixComplex.Prerequisites.Topology.RelativeSingularHomotopy

@[expose] public section
noncomputable section
open Set Topology CategoryTheory
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open InfiniteA2Toric InfiniteA2Toric
open InfiniteA2Toric.Construction CuspFilling CuspPeriodExpansion
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def phaseSweepOneSkeletonInclusion
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (phaseSweepCellAtlas W).cwComplex
    TopCat.of (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2) ⟶
      TopCat.of (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 3) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  exact integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 2

public theorem phaseSweepCompactAction_zeroSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (k : Fin 2 → Circle) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    ∀ x : IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 1,
      constructedA2CentralCompactOrbitMap W k x.1 = x.1 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  intro x
  have hx := x.2
  change x.1 ∈ (Topology.RelCWComplex.skeletonLT
    (Set.univ : Set (ActualLocalCuspCentralOrbitQuotient W)) (1 : ℕ∞) : Set _) at hx
  simp only [Topology.RelCWComplex.coe_skeletonLT] at hx
  change x.1 ∈ (∅ : Set _) ∪ ⋃ (m : ℕ) (_ : m < (1 : ℕ∞)) (j : CuspWCellIndex m),
    phaseSweepCellMap W m j '' Metric.closedBall 0 1 at hx
  rcases hx with hx | hx
  · exact False.elim hx
  · obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hm, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, b, hb, he⟩ := Set.mem_iUnion.mp hx
    have hmNat : m < 1 := by exact_mod_cast hm
    have hm0 : m = 0 := by omega
    subst m
    rw [← he]
    exact constructedA2CentralCompactOrbitMap_zeroCell W k j b

public def phaseSweepSkeletalBasePair
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (phaseSweepCellAtlas W).cwComplex
    CWTopologicalPairMap (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 1)
      (phaseSweepOneSkeletonInclusion W) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  exact
    { left := integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 1
      right := phaseSweepOneSkeletonInclusion W
      comm := rfl }

public theorem phaseSweepCompactAction_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (k : Fin 2 → Circle) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    ∀ x : IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2,
      constructedA2CentralCompactOrbitMap W k x.1 ∈
        (phaseSweepCellAtlas W).skeletalSet 3 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  intro x
  have hx := x.2
  change x.1 ∈ (Topology.RelCWComplex.skeletonLT
    (Set.univ : Set (ActualLocalCuspCentralOrbitQuotient W)) (2 : ℕ∞) : Set _) at hx
  simp only [Topology.RelCWComplex.coe_skeletonLT] at hx
  change x.1 ∈ (∅ : Set _) ∪ ⋃ (m : ℕ) (_ : m < (2 : ℕ∞)) (j : CuspWCellIndex m),
    phaseSweepCellMap W m j '' Metric.closedBall 0 1 at hx
  have hxold : x.1 ∈ constructedCentralOneSkeleton W := by
    rcases hx with hx | hx
    · exact False.elim hx
    · obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hm, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, b, hb, he⟩ := Set.mem_iUnion.mp hx
      have hmNat : m < 2 := by exact_mod_cast hm
      have hm' : m = 0 ∨ m = 1 := by omega
      rcases hm' with rfl | rfl
      · exact Or.inl (Set.mem_iUnion.mpr ⟨j, b, hb, he⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨j, b, hb, he⟩)
  have hy := constructedA2CentralCompactOrbitMap_oneSkeleton W k hxold
  have hy' := constructedCentralBoundaryTwoSkeleton_subset_cellSkeleton W (by decide : 3 ≤ 3) hy
  change _ ∈ (Topology.RelCWComplex.skeletonLT
    (Set.univ : Set (ActualLocalCuspCentralOrbitQuotient W)) (3 : ℕ∞) :
      Set (ActualLocalCuspCentralOrbitQuotient W))
  simp only [Topology.RelCWComplex.coe_skeletonLT]
  change _ ∈ (∅ : Set _) ∪ ⋃ (m : ℕ) (_ : m < (3 : ℕ∞)) (j : CuspWCellIndex m),
    phaseSweepCellMap W m j '' Metric.closedBall 0 1
  simp only [phaseSweepCellMap_closedImage]
  apply Or.inr
  obtain ⟨m, hy'⟩ := Set.mem_iUnion.mp hy'
  obtain ⟨hm, hy'⟩ := Set.mem_iUnion.mp hy'
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy'
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨by exact_mod_cast hm,
    Set.mem_iUnion.mpr ⟨j, hj⟩⟩⟩

public def phaseSweepSkeletalHomotopy
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :
    TopCat.Homotopy (phaseSweepSkeletalBasePair W).right
      (phaseSweepSkeletalBasePair W).right where
  toFun p := ⟨constructedA2CircleSweepHomotopy W i (p.1, p.2.1),
    phaseSweepCompactAction_oneSkeleton W (constructedA2CircleSweepParameter i p.1) p.2⟩
  continuous_toFun := ((constructedA2CircleSweepHomotopy W i).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext ((constructedA2CircleSweepHomotopy W i).map_zero_left x.1)
  map_one_left x := Subtype.ext ((constructedA2CircleSweepHomotopy W i).map_one_left x.1)

public def phaseSweepSkeletalRelativeHomotopy
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 2) :=
  cwRelativeSingularHomotopy (f := phaseSweepSkeletalBasePair W)
    (g := phaseSweepSkeletalBasePair W)
    (TopCat.Homotopy.refl (phaseSweepSkeletalBasePair W).left)
    (phaseSweepSkeletalHomotopy W i) (by
      ext p : 1
      apply Subtype.ext
      exact phaseSweepCompactAction_zeroSkeleton W (constructedA2CircleSweepParameter i p.2.down) p.1)

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
