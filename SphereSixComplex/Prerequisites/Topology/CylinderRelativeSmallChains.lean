module

public import SphereSixComplex.Prerequisites.Topology.CylinderUpperNeighborhood
public import SphereSixComplex.Prerequisites.Topology.SingularSubsetRelativeExcision

@[expose] public section
noncomputable section
open Set CategoryTheory
namespace SphereSixComplex

public def cylinderRelativeCover {X : Type} (A : Set X) : Bool → Set (cylinderBoundary A)
  | false => cylinderUpperNeighborhood A
  | true => {p | p.1 ∈ cylinderLowerSide A}

public def cylinderRelativeOpenRefinement {X : Type} (A : Set X) : Bool → Set (cylinderBoundary A)
  | false => cylinderUpperNeighborhood A
  | true => cylinderBottomNeighborhood A

public theorem cylinderRelativeOpenRefinement_le {X : Type} (A : Set X) (b : Bool) :
    cylinderRelativeOpenRefinement A b ⊆ cylinderRelativeCover A b := by
  cases b
  · exact Set.Subset.refl _
  · exact cylinderBottomNeighborhood_subset_lowerSide A

public theorem cylinderRelativeOpenRefinement_isOpen {X : Type} [TopologicalSpace X]
    (A : Set X) (b : Bool) : IsOpen (cylinderRelativeOpenRefinement A b) := by
  cases b
  · exact cylinderUpperNeighborhood_isOpen A
  · exact cylinderBottomNeighborhood_isOpen A

public theorem cylinderRelativeOpenRefinement_iUnion {X : Type} (A : Set X) :
    ⋃ b, cylinderRelativeOpenRefinement A b = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hp : p ∈ cylinderUpperNeighborhood A ∪ cylinderBottomNeighborhood A := by
    rw [cylinderBoundary_open_cover A]
    trivial
  rcases hp with hp | hp
  · exact Set.mem_iUnion.mpr ⟨false, hp⟩
  · exact Set.mem_iUnion.mpr ⟨true, hp⟩


public def cylinderUpperRelativeExcisionMap {X : Type} [TopologicalSpace X] (A : Set X) :=
  singularSubsetRelativeExcisionMap (TopCat.of (cylinderBoundary A))
    (cylinderUpperNeighborhood A) {p | p.1 ∈ cylinderLowerSide A}

public theorem cylinderUpperRelativeExcisionMap_quasiIso {X : Type} [TopologicalSpace X]
    (A : Set X) : QuasiIso (cylinderUpperRelativeExcisionMap A) :=
  singularSubsetRelativeExcisionMap_quasiIso (TopCat.of (cylinderBoundary A))
    (cylinderUpperNeighborhood A) {p | p.1 ∈ cylinderLowerSide A}
    (cylinderRelativeOpenRefinement A) id (cylinderRelativeOpenRefinement_le A)
    (cylinderRelativeOpenRefinement_isOpen A) (cylinderRelativeOpenRefinement_iUnion A)

end SphereSixComplex
