module

public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberCWTypes
public import SphereSixComplex.Prerequisites.Topology.CellularHomologyClassicalBoundary

@[expose] public section
noncomputable section
open Set Topology CategoryTheory
namespace SphereSixComplex
namespace StandardA2ToricCentralFiberCellAtlas
variable {X : Type} [TopologicalSpace X]

public def rechart (A : StandardA2ToricCentralFiberCellAtlas X)
    (f : (n : ℕ) → cuspWCellIndex n → PartialEquiv (Fin n → ℝ) X)
    (hs : ∀ n i, (f n i).source = Metric.ball 0 1)
    (hc : ∀ n i, ContinuousOn (f n i) (Metric.closedBall 0 1))
    (hi : ∀ n i, ContinuousOn (f n i).symm (f n i).target)
    (ho : ∀ n i, f n i '' Metric.ball 0 1 = A.cellMap n i '' Metric.ball 0 1)
    (hcl : ∀ n i, f n i '' Metric.closedBall 0 1 = A.cellMap n i '' Metric.closedBall 0 1)
    (hb : ∀ n i, MapsTo (f n i) (Metric.sphere 0 1)
      (⋃ (m < n) (j : cuspWCellIndex m), A.cellMap m j '' Metric.closedBall 0 1)) :
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
  change x ∈ (∅ : Set X) ∪ ⋃ (m : ℕ) (_ : m < k) (i : cuspWCellIndex m),
      A.cellMap m i '' Metric.closedBall 0 1 ↔
    x ∈ (∅ : Set X) ∪ ⋃ (m : ℕ) (_ : m < k) (i : cuspWCellIndex m),
      B.cellMap m i '' Metric.closedBall 0 1
  simp only [h]

public def skeletalInclusion [T2Space X] (A : StandardA2ToricCentralFiberCellAtlas X) (n : ℕ) :
    TopCat.of (A.skeletalSet n) ⟶ TopCat.of (A.skeletalSet (n + 1)) := by
  let _ := A.cwComplex
  exact integralCWSkeletonInclusion X n

public def relativeChains [T2Space X] (A : StandardA2ToricCentralFiberCellAtlas X) (n : ℕ) :=
  CWRelativeIntegralSingularChainComplex (A.skeletalInclusion n)

public def relativeChainsIsoOfClosedCellEq [T2Space X]
    (A B : StandardA2ToricCentralFiberCellAtlas X)
    (h : ∀ n i, A.cellMap n i '' Metric.closedBall 0 1 =
      B.cellMap n i '' Metric.closedBall 0 1) (n : ℕ) :
    A.relativeChains n ≅ B.relativeChains n := by
  let e₀ : TopCat.of (A.skeletalSet n) ≅ TopCat.of (B.skeletalSet n) :=
    TopCat.isoOfHomeo (Homeomorph.setCongr (skeleton_eq_of_closedCell_eq A B h n))
  let e₁ : TopCat.of (A.skeletalSet (n + 1)) ≅ TopCat.of (B.skeletalSet (n + 1)) :=
    TopCat.isoOfHomeo (Homeomorph.setCongr (skeleton_eq_of_closedCell_eq A B h (n + 1)))
  let F := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  apply CategoryTheory.Limits.cokernel.mapIso
    (cwIntegralSingularChainMapObj (A.skeletalInclusion n))
    (cwIntegralSingularChainMapObj (B.skeletalInclusion n))
    (F.mapIso e₀) (F.mapIso e₁)
  change F.map (A.skeletalInclusion n) ≫ F.map e₁.hom =
    F.map e₀.hom ≫ F.map (B.skeletalInclusion n)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

end StandardA2ToricCentralFiberCellAtlas

public theorem characteristicClass_has_integral_retraction
    (T : CellularHomology.IntegralComparison)
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (c : Topology.CWComplex.cell (Set.univ : Set X) n)
    {G : Type} [AddCommGroup G] (e : IntegralCWRelativeCellObject X n ≃+ G) :
    ∃ r : G →+ ℤ, r (e (ConcreteCategory.hom
      ((CWRelativeIntegralSingularChainComplex (cwCharacteristicBoundaryInclusion n)).homologyMap
        (integralCWCharacteristicPairMap X n c).relativeChainMap n)
          ((T.diskOrientation n).symm 1))) = 1 := by
  classical
  refine ⟨(Finsupp.applyAddHom c).comp ((T.cellBasis X n).symm.toAddMonoidHom.comp
    e.symm.toAddMonoidHom), ?_⟩
  rw [← T.cellBasis_single]
  simp

end SphereSixComplex
