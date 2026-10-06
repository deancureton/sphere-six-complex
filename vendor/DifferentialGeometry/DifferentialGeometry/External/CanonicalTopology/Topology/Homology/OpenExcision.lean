module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ExcisionQuotient

@[expose] public section

/-! # Excision for the original integral relative singular homology -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- For two original open subspaces covering X, the SAME original pair
inclusion (B,B ∩ A) → (X,A) is a quasi-isomorphism of relative complexes.
This is proved by the exact quotient identification and actual subdivision. -/
theorem integralRelativeChainMap_openExcision (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ) :
    QuasiIso (integralRelativeChainMap (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)) := by
  have hU : ∀ i, IsOpen (twoSetCover A B i) := by
    intro i
    cases i with
    | false => exact hA
    | true => exact hB
  have hc : ∀ x, ∃ i, x ∈ twoSetCover A B i := by
    intro x
    have hx : x ∈ A ∪ B := hcover.symm ▸ mem_univ x
    rcases hx with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  let := integralSmallRelativeComparison_quasiIso (twoSetCover A B) false hU hc
  rw [← integralExcisionSmallMap_comparison]
  infer_instance

/-- The excision isomorphism is induced by the SAME actual relative pair
map, in every degree of the original integral singular homology. -/
def integralRelativeOpenExcisionIso (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ) :
    integralRelativeHomology n (subspaceIntersection A B) ≅ integralRelativeHomology n A := by
  letI := integralRelativeChainMap_openExcision A B hA hB hcover
  exact asIso (HomologicalComplex.homologyMap
    (integralRelativeChainMap (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)) n)

/-- Its homomorphism is the original relative homology map, exactly. -/
theorem integralRelativeOpenExcisionIso_hom (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ) :
    (integralRelativeOpenExcisionIso n A B hA hB hcover).hom.hom =
      integralRelativeHomologyMap n (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B) := rfl

end DifferentialGeometry.Topology
