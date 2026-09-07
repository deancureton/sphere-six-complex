module

public import SphereSixComplex.Topology.CellularHomologyClassicalBoundary
public import SphereSixComplex.Topology.StandardSpherePositiveHomology

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex.IntegralCWCellularHomologyFoundation

public theorem attachingDegree_zero_of_contractible_boundary_factor
    (T : IntegralCWCellularHomologyFoundation)
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    {Z : Type} [TopologicalSpace Z] [ContractibleSpace Z]
    (n : ℕ) (hn : n ≠ 0)
    (e : Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set X) n)
    (u : TopCat.of (CWCharacteristicBoundarySphere (n + 1)) ⟶ TopCat.of Z)
    (v : TopCat.of Z ⟶ TopCat.of (IntegralCWSkeletonLT X (n + 1)))
    (h : (T.characteristicPair X (n + 1) e).boundaryMap = u ≫ v) :
    T.attachingDegree X n e e' = 0 := by
  let _ : Subsingleton ((CWIntegralSingularChainComplexObj (TopCat.of Z)).homology n) :=
    subsingleton_integralSingularHomology_of_contractible (X := Z) n hn
  rw [T.attachingDegree_eq_homologicalAttachingMapDegree]
  unfold homologicalAttachingMapDegree
  rw [h, cwIntegralSingularChainMapObj_comp, HomologicalComplex.homologyMap_comp]
  have hz : HomologicalComplex.homologyMap (cwIntegralSingularChainMapObj u) n = 0 := by
    ext x
    exact Subsingleton.elim _ _
  rw [hz, zero_comp, zero_comp]
  simp

public theorem attachingDegree_zero_of_boundary_mem_embedded_contractible
    (T : IntegralCWCellularHomologyFoundation)
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    {Z : Type} [TopologicalSpace Z] [ContractibleSpace Z]
    (n : ℕ) (hn : n ≠ 0)
    (e : Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set X) n)
    (v : TopCat.of Z ⟶ TopCat.of (IntegralCWSkeletonLT X (n + 1)))
    (hv : Topology.IsEmbedding v)
    (hr : ∀ x, (T.characteristicPair X (n + 1) e).boundaryMap x ∈ Set.range v) :
    T.attachingDegree X n e e' = 0 := by
  let u := fun x ↦ (hr x).choose
  have hu : ∀ x, v (u x) = (T.characteristicPair X (n + 1) e).boundaryMap x :=
    fun x ↦ (hr x).choose_spec
  have hucont : Continuous u := hv.isInducing.continuous_iff.mpr (by
    have he : (fun x ↦ v (u x)) = (T.characteristicPair X (n + 1) e).boundaryMap :=
      funext hu
    change Continuous (fun x ↦ v (u x))
    rw [he]
    exact (T.characteristicPair X (n + 1) e).boundaryMap.hom.continuous)
  exact T.attachingDegree_zero_of_contractible_boundary_factor X n hn e e'
    (TopCat.ofHom ⟨u, hucont⟩) v (by ext x; exact congrArg Subtype.val (hu x).symm)

end SphereSixComplex.IntegralCWCellularHomologyFoundation
