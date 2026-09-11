module

public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberCWTypes

@[expose] public section
noncomputable section
open Set Topology CategoryTheory
namespace SphereSixComplex
namespace StandardA2ToricCentralFiberCellAtlas
variable {X : Type} [TopologicalSpace X]

public def rechart (A : StandardA2ToricCentralFiberCellAtlas X)
    (f : (n : ℕ) → CuspWCellIndex n → PartialEquiv (Fin n → ℝ) X)
    (hs : ∀ n i, (f n i).source = Metric.ball 0 1)
    (hc : ∀ n i, ContinuousOn (f n i) (Metric.closedBall 0 1))
    (hi : ∀ n i, ContinuousOn (f n i).symm (f n i).target)
    (ho : ∀ n i, f n i '' Metric.ball 0 1 = A.cellMap n i '' Metric.ball 0 1)
    (hcl : ∀ n i, f n i '' Metric.closedBall 0 1 = A.cellMap n i '' Metric.closedBall 0 1)
    (hb : ∀ n i, MapsTo (f n i) (Metric.sphere 0 1)
      (⋃ (m < n) (j : CuspWCellIndex m), A.cellMap m j '' Metric.closedBall 0 1)) :
    StandardA2ToricCentralFiberCellAtlas X where
  cellMap := f
  source_eq := hs
  continuousOn := hc
  continuousOn_symm := hi
  pairwiseDisjoint := by
    intro a ha b hb hab
    change Disjoint (f a.1 a.2 '' Metric.ball 0 1) (f b.1 b.2 '' Metric.ball 0 1)
    rw [ho, ho]
    exact A.pairwiseDisjoint ha hb hab
  mapsTo := by simpa only [hcl] using hb
  union_eq := by simpa only [hcl] using A.union_eq

public def skeletalSet [T2Space X] (A : StandardA2ToricCentralFiberCellAtlas X) (k : ℕ∞) : Set X := by
  let _ := A.cwComplex
  exact (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) k : Set X)

public theorem skeleton_eq_of_closedCell_eq [T2Space X]
    (A B : StandardA2ToricCentralFiberCellAtlas X)
    (h : ∀ n i, A.cellMap n i '' Metric.closedBall 0 1 =
      B.cellMap n i '' Metric.closedBall 0 1) (k : ℕ∞) :
    A.skeletalSet k = B.skeletalSet k := by
  ext x
  simp only [skeletalSet, Topology.RelCWComplex.coe_skeletonLT]
  change x ∈ (∅ : Set X) ∪ ⋃ (m : ℕ) (_ : m < k) (i : CuspWCellIndex m),
      A.cellMap m i '' Metric.closedBall 0 1 ↔
    x ∈ (∅ : Set X) ∪ ⋃ (m : ℕ) (_ : m < k) (i : CuspWCellIndex m),
      B.cellMap m i '' Metric.closedBall 0 1
  simp only [h]




end StandardA2ToricCentralFiberCellAtlas


end SphereSixComplex
