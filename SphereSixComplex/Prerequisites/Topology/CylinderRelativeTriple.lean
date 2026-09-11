module

public import SphereSixComplex.Prerequisites.Topology.RelativeTripleShortExact
public import SphereSixComplex.Prerequisites.Topology.CylinderLowerSideContraction

@[expose] public section
noncomputable section
open Set Topology CategoryTheory
namespace SphereSixComplex

public def cylinderBoundary {X : Type} (A : Set X) : Set (unitInterval × X) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ A}

public theorem cylinderLowerSide_subset_boundary {X : Type} (A : Set X) :
    cylinderLowerSide A ⊆ cylinderBoundary A := by
  rintro p (h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

public def cylinderLowerSideToBoundary {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of (cylinderLowerSide A) ⟶ TopCat.of (cylinderBoundary A) :=
  TopCat.ofHom ⟨Set.inclusion (cylinderLowerSide_subset_boundary A), continuous_inclusion _⟩

public def cylinderBoundaryInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of (cylinderBoundary A) ⟶ TopCat.of (unitInterval × X) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

public instance cylinderBoundaryInclusion_mono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (cylinderBoundaryInclusion A) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

public def cylinderRelativeTriple {X : Type} [TopologicalSpace X] (A : Set X) :=
  cwRelativeTripleShortComplex (cylinderLowerSideToBoundary A) (cylinderBoundaryInclusion A)

public theorem cylinderRelativeTriple_shortExact {X : Type} [TopologicalSpace X] (A : Set X) :
    (cylinderRelativeTriple A).ShortExact :=
  cwRelativeTripleShortComplex_shortExact _ _

public def cylinderTopFaceMap {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of X ⟶ TopCat.of (cylinderBoundary A) :=
  TopCat.ofHom ⟨fun x ↦ ⟨(1, x), Or.inr (Or.inl rfl)⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

public def cylinderTopEdgeMap {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of (cylinderLowerSide A) :=
  TopCat.ofHom ⟨fun x ↦ ⟨(1, x.1), Or.inr x.2⟩,
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩

public def cylinderTopFacePairMap {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ TopCat.of X)
      (cylinderLowerSideToBoundary A) where
  left := cylinderTopEdgeMap A
  right := cylinderTopFaceMap A
  comm := rfl

public def cylinderTopFaceRelativeChains {X : Type} [TopologicalSpace X] (A : Set X) :=
  cwRelativeIntegralSingularChainMapOfPair (cylinderTopFacePairMap A)


end SphereSixComplex
