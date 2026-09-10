module

public import SphereSixComplex.Prerequisites.Topology.CellularPathComparison
public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicTopology

namespace SphereSixComplex
open StandardCircleHomologyLiftDegree Hurewicz.Chains

public abbrev cwPathMorphism {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) : TopCat.I ⟶ TopCat.of X :=
  TopCat.ofHom ⟨fun t ↦ p t.down, p.continuous.comp continuous_uliftDown⟩

public theorem cwPathMorphism_source {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) : cwPathMorphism p 0 = x := p.source

public theorem cwPathMorphism_target {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) : cwPathMorphism p 1 = y := p.target

public theorem cwIntegralPathChain_path {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) :
    (cwIntegralPathChain (cwPathMorphism p)).hom 1 = pathChain p := by
  rfl

public theorem cwIntegralPathDifferenceClass_eq_loop {X : Type} [TopologicalSpace X]
    {x y : X} (p q : Path x y) :
    (cwIntegralPathDifferenceClass (cwPathMorphism p)
      (cwPathMorphism q) ((cwPathMorphism_source p).trans (cwPathMorphism_source q).symm)
      ((cwPathMorphism_target p).trans (cwPathMorphism_target q).symm)).hom 1 = loopHomologyClass (p.trans q.symm) := by
  apply (AddCommGrpCat.mono_iff_injective ((integralChains X).homologyι 1)).mp
    (inferInstance : Mono ((integralChains X).homologyι 1))
  rw [homologyι_loopHomologyClass, pathOpchainClass_trans, pathOpchainClass_symm]
  change (cwIntegralPathDifferenceClass _ _ _ _ ≫ (integralChains X).homologyι 1).hom 1 = _
  unfold cwIntegralPathDifferenceClass
  erw [Category.assoc, HomologicalComplex.homology_π_ι,
    ← Category.assoc, HomologicalComplex.liftCycles_i]
  change (opchainClass X) ((cwIntegralPathChain (cwPathMorphism p)).hom 1 -
    (cwIntegralPathChain (cwPathMorphism q)).hom 1) = _
  rw [cwIntegralPathChain_path, cwIntegralPathChain_path]
  exact ((opchainClass X).map_sub _ _).trans (sub_eq_add_neg _ _)

public theorem normalized_cellBasis_loop_edges
    (T : CellularHomology.IntegralComparison) (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (e f : Topology.CWComplex.cell (Set.univ : Set X) 1)
    (h₀ : (integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneLeft =
      (integralCWCharacteristicPairMap X 1 f).boundaryMap cwBoundaryOneLeft)
    (h₁ : (integralCWCharacteristicPairMap X 1 e).boundaryMap cwBoundaryOneRight =
      (integralCWCharacteristicPairMap X 1 f).boundaryMap cwBoundaryOneRight)
    {x y : IntegralCWSkeletonLT X 2} (p q : Path x y)
    (hp : cwPathMorphism p = cwCellularEdgePath X e)
    (hq : cwPathMorphism q = cwCellularEdgePath X f) :
    (T.normalized.cellBasis X 1).symm
      ((HomologicalComplex.homologyMap
        (cwRelativeIntegralSingularChainProjection (integralCWSkeletonInclusion X 1)) 1).hom
        (loopHomologyClass (p.trans q.symm))) = Finsupp.single e 1 - Finsupp.single f 1 := by
  have h := normalized_cellBasis_edgeDifference T X e f h₀ h₁
  have he := cwIntegralPathDifferenceClass_eq_loop p q
  simp only [hp, hq] at he
  rw [← he]
  exact h

end SphereSixComplex
