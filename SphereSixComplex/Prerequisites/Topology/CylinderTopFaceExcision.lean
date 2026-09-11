module

public import SphereSixComplex.Prerequisites.Topology.CylinderRelativeSmallChains
public import SphereSixComplex.Prerequisites.Topology.CylinderTopRelativeEquivalence

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex

private def relativePairIso {A X B Y : TopCat} {i : A ⟶ X} {j : B ⟶ Y}
    (f : CWTopologicalPairMap i j) (g : CWTopologicalPairMap j i)
    (hf : f.right ≫ g.right = 𝟙 _) (hg : g.right ≫ f.right = 𝟙 _) :
    cwRelativeIntegralSingularChainComplex i ≅ cwRelativeIntegralSingularChainComplex j where
  hom := cwRelativeIntegralSingularChainMapOfPair f
  inv := cwRelativeIntegralSingularChainMapOfPair g
  hom_inv_id := by
    apply Cofork.IsColimit.hom_ext (cokernelIsCokernel (cwIntegralSingularChainMapObj i))
    change cwRelativeIntegralSingularChainProjection _ ≫ (_ ≫ _) =
      cwRelativeIntegralSingularChainProjection _ ≫ 𝟙 _
    rw [← Category.assoc, cwRelativeIntegralSingularChainProjection_natural,
      Category.assoc, cwRelativeIntegralSingularChainProjection_natural, ← Category.assoc,
      ← cwIntegralSingularChainMapObj_comp, hf, cwIntegralSingularChainMapObj_id,
      Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply Cofork.IsColimit.hom_ext (cokernelIsCokernel (cwIntegralSingularChainMapObj j))
    change cwRelativeIntegralSingularChainProjection _ ≫ (_ ≫ _) =
      cwRelativeIntegralSingularChainProjection _ ≫ 𝟙 _
    rw [← Category.assoc, cwRelativeIntegralSingularChainProjection_natural,
      Category.assoc, cwRelativeIntegralSingularChainProjection_natural, ← Category.assoc,
      ← cwIntegralSingularChainMapObj_comp, hg, cwIntegralSingularChainMapObj_id,
      Category.id_comp, Category.comp_id]

public def cylinderUpperIntersectionPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap (cylinderUpperSideInclusion A)
      (subsetIntersectionInclusion (TopCat.of (cylinderBoundary A))
        (cylinderUpperNeighborhood A) {p | p.1 ∈ cylinderLowerSide A}) where
  left := TopCat.ofHom ⟨fun p ↦ ⟨p.1.1, p.1.2, p.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  right := 𝟙 _
  comm := rfl

public def cylinderIntersectionUpperPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap
      (subsetIntersectionInclusion (TopCat.of (cylinderBoundary A))
        (cylinderUpperNeighborhood A) {p | p.1 ∈ cylinderLowerSide A})
      (cylinderUpperSideInclusion A) where
  left := TopCat.ofHom ⟨fun p ↦ ⟨⟨p.1, p.2.1⟩, p.2.2⟩,
    (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  right := 𝟙 _
  comm := rfl

public def cylinderLowerAmbientPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap
      (topologicalSubsetInclusion (TopCat.of (cylinderBoundary A))
        {p | p.1 ∈ cylinderLowerSide A}) (cylinderLowerSideToBoundary A) where
  left := TopCat.ofHom ⟨fun p ↦ ⟨p.1.1, p.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  right := 𝟙 _
  comm := rfl

public def cylinderAmbientLowerPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap (cylinderLowerSideToBoundary A)
      (topologicalSubsetInclusion (TopCat.of (cylinderBoundary A))
        {p | p.1 ∈ cylinderLowerSide A}) where
  left := TopCat.ofHom ⟨fun p ↦ ⟨⟨p.1, cylinderLowerSide_subset_boundary A p.2⟩, p.2⟩,
    (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  right := 𝟙 _
  comm := rfl

public def cylinderUpperBoundaryPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap (cylinderUpperSideInclusion A) (cylinderLowerSideToBoundary A) where
  left := TopCat.ofHom ⟨fun p ↦ ⟨p.1.1.1, p.2⟩,
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩
  right := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  comm := rfl

public def cylinderUpperExcisionChains {X : Type} [TopologicalSpace X] (A : Set X) :
    cwRelativeIntegralSingularChainComplex
      (subsetIntersectionInclusion (TopCat.of (cylinderBoundary A))
        (cylinderUpperNeighborhood A) {p | p.1 ∈ cylinderLowerSide A}) ⟶
    cwRelativeIntegralSingularChainComplex
      (topologicalSubsetInclusion (TopCat.of (cylinderBoundary A))
        {p | p.1 ∈ cylinderLowerSide A}) := cylinderUpperRelativeExcisionMap A

public theorem cylinderUpperExcisionChains_quasiIso {X : Type} [TopologicalSpace X]
    (A : Set X) : QuasiIso (cylinderUpperExcisionChains A) :=
  cylinderUpperRelativeExcisionMap_quasiIso A

public theorem cylinderUpperBoundaryPair_factorization {X : Type} [TopologicalSpace X]
    (A : Set X) :
    cwRelativeIntegralSingularChainMapOfPair (cylinderUpperBoundaryPair A) =
      cwRelativeIntegralSingularChainMapOfPair (cylinderUpperIntersectionPair A) ≫
        cylinderUpperExcisionChains A ≫
          cwRelativeIntegralSingularChainMapOfPair (cylinderLowerAmbientPair A) := by
  apply Cofork.IsColimit.hom_ext
    (cokernelIsCokernel (cwIntegralSingularChainMapObj (cylinderUpperSideInclusion A)))
  change cwRelativeIntegralSingularChainProjection _ ≫ _ =
    cwRelativeIntegralSingularChainProjection _ ≫ (_ ≫ _ ≫ _)
  dsimp only [cwRelativeIntegralSingularChainComplex, relativeIntegralSingularChainComplex]
  erw [cwRelativeIntegralSingularChainProjection_natural, ← Category.assoc,
    ← Category.assoc, cwRelativeIntegralSingularChainProjection_natural (cylinderUpperIntersectionPair A)]
  change _ = ((cwIntegralSingularChainMapObj (𝟙 _) ≫ _) ≫ _) ≫ _
  erw [cwIntegralSingularChainMapObj_id, Category.id_comp]
  erw [singularSubsetRelativeExcisionMap_projection (TopCat.of (cylinderBoundary A))
    (cylinderUpperNeighborhood A) {p | p.1 ∈ cylinderLowerSide A}]
  erw [Category.assoc, cwRelativeIntegralSingularChainProjection_natural (cylinderLowerAmbientPair A)]
  change _ = _ ≫ cwIntegralSingularChainMapObj (𝟙 _) ≫ _
  erw [cwIntegralSingularChainMapObj_id, Category.id_comp]
  rfl

public theorem cylinderUpperBoundaryPair_quasiIso {X : Type} [TopologicalSpace X]
    (A : Set X) :
    QuasiIso (cwRelativeIntegralSingularChainMapOfPair (cylinderUpperBoundaryPair A)) := by
  let e := relativePairIso (cylinderUpperIntersectionPair A)
    (cylinderIntersectionUpperPair A) (Category.id_comp _) (Category.id_comp _)
  let f := relativePairIso (cylinderLowerAmbientPair A)
    (cylinderAmbientLowerPair A) (Category.id_comp _) (Category.id_comp _)
  let : IsIso (cwRelativeIntegralSingularChainMapOfPair
      (cylinderUpperIntersectionPair A)) := e.isIso_hom
  let : IsIso (cwRelativeIntegralSingularChainMapOfPair
      (cylinderLowerAmbientPair A)) := f.isIso_hom
  let := cylinderUpperExcisionChains_quasiIso A
  let : QuasiIso (cylinderUpperExcisionChains A ≫
      cwRelativeIntegralSingularChainMapOfPair (cylinderLowerAmbientPair A)) :=
    quasiIso_comp (cylinderUpperExcisionChains A) f.hom
  exact (cylinderUpperBoundaryPair_factorization A).symm ▸
    quasiIso_comp e.hom (cylinderUpperExcisionChains A ≫ f.hom)

public theorem cylinderTopFaceRelativeChains_quasiIso {X : Type} [TopologicalSpace X]
    (A : Set X) : QuasiIso (cylinderTopFaceRelativeChains A) := by
  let : QuasiIso (cwRelativeIntegralSingularChainMapOfPair (cylinderTopUpperPair A)) :=
    (cylinderTopUpperRelativeEquivalence A).quasiIso_hom
  let := cylinderUpperBoundaryPair_quasiIso A
  have h : cylinderTopFaceRelativeChains A =
      cwRelativeIntegralSingularChainMapOfPair (cylinderTopUpperPair A) ≫
        cwRelativeIntegralSingularChainMapOfPair (cylinderUpperBoundaryPair A) :=
    cwRelativeIntegralSingularChainMapOfPair_comp
      (cylinderTopUpperPair A) (cylinderUpperBoundaryPair A)
  exact h.symm ▸ quasiIso_comp
    (cwRelativeIntegralSingularChainMapOfPair (cylinderTopUpperPair A))
    (cwRelativeIntegralSingularChainMapOfPair (cylinderUpperBoundaryPair A))


end SphereSixComplex
