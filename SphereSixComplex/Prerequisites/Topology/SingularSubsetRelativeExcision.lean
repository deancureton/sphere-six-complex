module

public import SphereSixComplex.Prerequisites.Topology.SingularSubsetRanges
public import SphereSixComplex.Prerequisites.Topology.SingularRelativeSmallChains

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
namespace SphereSixComplex

public def binarySubsetCover (X : TopCat) (U V : Set X) : Bool → Set X
  | false => U
  | true => V

public theorem binarySubsetCover_small_eq (X : TopCat) (U V : Set X) :
    coverSmallSingularSubcomplex X (binarySubsetCover X U V) =
      singularSubsetRange X U ⊔ singularSubsetRange X V := by
  ext n x
  rw [mem_coverSmallSingularSubcomplex_iff]
  change (∃ b, x ∈ (singularSubsetRange X (binarySubsetCover X U V b)).obj n) ↔
    x ∈ (singularSubsetRange X U).obj n ∨ x ∈ (singularSubsetRange X V).obj n
  constructor
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩

public def subsetIntersectionInclusion (X : TopCat) (U V : Set X) :
    TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨Set.inclusion inter_subset_left, continuous_inclusion _⟩

public def singularIntersectionCorestrictionIso (X : TopCat) (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)) ≅
      (singularSubsetRange X U ⊓ singularSubsetRange X V).toSSet :=
  asIso (singularSubsetCorestriction X (U ∩ V)) ≪≫
    SSet.Subcomplex.eqToIso (singularSubsetRange_inter X U V)

public theorem singularIntersectionCorestrictionIso_natural (X : TopCat) (U V : Set X) :
    TopCat.toSSet.map (subsetIntersectionInclusion X U V) ≫ singularSubsetCorestriction X U =
      (singularIntersectionCorestrictionIso X U V).hom ≫
        SSet.Subcomplex.homOfLE (inf_le_left : singularSubsetRange X U ⊓ singularSubsetRange X V ≤ _) := by
  apply (cancel_mono (singularSubsetRange X U).ι).mp
  ext n x
  rfl

public def singularIntersectionRelativeIso (X : TopCat) (U V : Set X) :
    relativeIntegralSingularChainComplex (subsetIntersectionInclusion X U V) ≅
      cokernel (BinaryOpenCover.integralSimplicialChains.map
        (SSet.Subcomplex.homOfLE
          (inf_le_left : singularSubsetRange X U ⊓ singularSubsetRange X V ≤ _))) := by
  let F := BinaryOpenCover.integralSimplicialChains
  refine cokernel.mapIso _ _ (F.mapIso (singularIntersectionCorestrictionIso X U V))
    (F.mapIso (@asIso _ _ _ _ (singularSubsetCorestriction X U)
      (singularSubsetCorestriction_isIso X U))) ?_
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (singularIntersectionCorestrictionIso_natural X U V)).trans (F.map_comp _ _))

public def singularUnionSmallIso (X : TopCat) (U V : Set X) :
    (coverSmallSingularSubcomplex X (binarySubsetCover X U V)).toSSet ≅
      (singularSubsetRange X U ⊔ singularSubsetRange X V).toSSet :=
  SSet.Subcomplex.eqToIso (binarySubsetCover_small_eq X U V)

public theorem singularUnionSmallIso_natural (X : TopCat) (U V : Set X) :
    coverMemberToSmallSingularSet X (binarySubsetCover X U V) true ≫
      (singularUnionSmallIso X U V).hom =
    singularSubsetCorestriction X V ≫
      SSet.Subcomplex.homOfLE (le_sup_right : singularSubsetRange X V ≤
        singularSubsetRange X U ⊔ singularSubsetRange X V) := by
  ext n x
  rfl

public def singularUnionSmallRelativeIso (X : TopCat) (U V : Set X) :
    (coverSmallRelativeShortComplex X (binarySubsetCover X U V) true).X₃ ≅
      cokernel (BinaryOpenCover.integralSimplicialChains.map
        (SSet.Subcomplex.homOfLE (le_sup_right : singularSubsetRange X V ≤
          singularSubsetRange X U ⊔ singularSubsetRange X V))) := by
  let F := BinaryOpenCover.integralSimplicialChains
  refine cokernel.mapIso _ _
    (F.mapIso (@asIso _ _ _ _ (singularSubsetCorestriction X V)
      (singularSubsetCorestriction_isIso X V)))
    (F.mapIso (singularUnionSmallIso X U V)) ?_
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (singularUnionSmallIso_natural X U V)).trans (F.map_comp _ _))

public def singularSubsetSmallRelativeExcisionIso (X : TopCat) (U V : Set X) :
    relativeIntegralSingularChainComplex (subsetIntersectionInclusion X U V) ≅
      (coverSmallRelativeShortComplex X (binarySubsetCover X U V) true).X₃ :=
  singularIntersectionRelativeIso X U V ≪≫
    simplicialSubcomplexRelativeExcisionIso (singularSubsetRange X U) (singularSubsetRange X V) ≪≫
    (singularUnionSmallRelativeIso X U V).symm

public def singularSubsetRelativeExcisionMap (X : TopCat) (U V : Set X) :
    relativeIntegralSingularChainComplex (subsetIntersectionInclusion X U V) ⟶
      relativeIntegralSingularChainComplex (topologicalSubsetInclusion X V) :=
  (singularSubsetSmallRelativeExcisionIso X U V).hom ≫
    coverSmallRelativeComparison X (binarySubsetCover X U V) true

public theorem singularSubsetRelativeExcisionMap_quasiIso (X : TopCat) (U V : Set X)
    {κ : Type} (W : κ → Set X) (r : κ → Bool)
    (h : ∀ j, W j ⊆ binarySubsetCover X U V (r j))
    (hWopen : ∀ j, IsOpen (W j)) (hWcover : ⋃ j, W j = Set.univ) :
    QuasiIso (singularSubsetRelativeExcisionMap X U V) := by
  let : QuasiIso (coverSmallRelativeComparison X (binarySubsetCover X U V) true) :=
    coverSmallRelativeComparison_quasiIso_of_open_refinement X
    (binarySubsetCover X U V) true W r h hWopen hWcover
  dsimp [singularSubsetRelativeExcisionMap]
  exact quasiIso_comp
    (singularSubsetSmallRelativeExcisionIso X U V).hom
    (coverSmallRelativeComparison X (binarySubsetCover X U V) true)

public theorem singularSubsetRelativeExcisionMap_projection (X : TopCat) (U V : Set X) :
    relativeIntegralSingularChainProjection (subsetIntersectionInclusion X U V) ≫
      singularSubsetRelativeExcisionMap X U V =
    integralSingularChainMapObj (topologicalSubsetInclusion X U) ≫
      relativeIntegralSingularChainProjection (topologicalSubsetInclusion X V) := by
  dsimp +instances only [relativeIntegralSingularChainProjection, singularSubsetRelativeExcisionMap,
    singularSubsetSmallRelativeExcisionIso, singularIntersectionRelativeIso,
    singularUnionSmallRelativeIso, simplicialSubcomplexRelativeExcisionIso,
    simplicialSubcomplexRelativeExcisionMap, coverSmallRelativeComparison,
    Iso.trans, Iso.symm, cokernel.mapIso, asIso, Functor.mapIso,
    relativeIntegralSingularChainComplex, coverSmallRelativeShortComplex, binarySubsetCover]
  dsimp +instances only [cokernel.map]
  simp +instances only [Category.assoc, cokernel.π_desc_assoc]
  erw [Category.assoc, cokernel.π_desc_assoc, Category.assoc,
    cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc]
  let F := BinaryOpenCover.integralSimplicialChains
  change F.map (singularSubsetCorestriction X U) ≫ F.map _ ≫ F.map _ ≫
    F.map (coverSmallSingularSubcomplex X (binarySubsetCover X U V)).ι ≫ _ =
      F.map (TopCat.toSSet.map (topologicalSubsetInclusion X U)) ≫ _
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2

end SphereSixComplex
