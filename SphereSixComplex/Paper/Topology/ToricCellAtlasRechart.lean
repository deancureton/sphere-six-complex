module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.CentralFiber.CellularModel

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric
open Set Topology CategoryTheory
namespace SphereSixComplex
namespace Geometry.InfiniteA2Toric.CentralFiber.CellAtlas
variable {X : Type} [TopologicalSpace X]

public def rechart (A : CentralFiber.CellAtlas X)
    (f : (n : ℕ) → CentralFiber.Cell n → PartialEquiv (Fin n → ℝ) X)
    (hs : ∀ n i, (f n i).source = Metric.ball 0 1)
    (hc : ∀ n i, ContinuousOn (f n i) (Metric.closedBall 0 1))
    (hi : ∀ n i, ContinuousOn (f n i).symm (f n i).target)
    (ho : ∀ n i, f n i '' Metric.ball 0 1 = A.cellMap n i '' Metric.ball 0 1)
    (hcl : ∀ n i, f n i '' Metric.closedBall 0 1 = A.cellMap n i '' Metric.closedBall 0 1)
    (hb : ∀ n i, MapsTo (f n i) (Metric.sphere 0 1)
      (⋃ (m < n) (j : CentralFiber.Cell m), A.cellMap m j '' Metric.closedBall 0 1)) :
    CentralFiber.CellAtlas X where
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

public def skeletalSet [T2Space X] (A : CentralFiber.CellAtlas X) (k : ℕ∞) : Set X := by
  let _ := A.cwComplex
  exact (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) k : Set X)

public theorem skeleton_eq_of_closedCell_eq [T2Space X]
    (A B : CentralFiber.CellAtlas X)
    (h : ∀ n i, A.cellMap n i '' Metric.closedBall 0 1 =
      B.cellMap n i '' Metric.closedBall 0 1) (k : ℕ∞) :
    A.skeletalSet k = B.skeletalSet k := by
  ext x
  simp only [skeletalSet, Topology.RelCWComplex.coe_skeletonLT]
  change x ∈ (∅ : Set X) ∪ ⋃ (m : ℕ) (_ : m < k) (i : CentralFiber.Cell m),
      A.cellMap m i '' Metric.closedBall 0 1 ↔
    x ∈ (∅ : Set X) ∪ ⋃ (m : ℕ) (_ : m < k) (i : CentralFiber.Cell m),
      B.cellMap m i '' Metric.closedBall 0 1
  simp only [h]




end Geometry.InfiniteA2Toric.CentralFiber.CellAtlas


end SphereSixComplex
