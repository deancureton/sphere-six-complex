module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OpenExcision

@[expose] public section

/-! # Actual integral local homology and open-neighborhood excision -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Local homology is the ORIGINAL relative singular homology of
(X, X minus the specified point). -/
abbrev integralLocalHomology (n : ℕ) (x : X) : ModuleCat.{u} ℤ :=
  integralRelativeHomology n ({x}ᶜ : Set X)

omit [TopologicalSpace X] in
/-- Removing the SAME point in an original subspace is exactly the
preimage of the ambient point complement. -/
theorem subspaceIntersection_point_complement (x : X) (U : Set X) (hx : x ∈ U) :
    subspaceIntersection ({x}ᶜ : Set X) U = ({(⟨x, hx⟩ : U)}ᶜ : Set U) := by
  ext y
  simp [subspaceIntersection, Subtype.ext_iff]

/-- The original neighborhood inclusion is a map of the SAME punctured pairs. -/
theorem neighborhoodPointComplement_mapsTo (x : X) (U : Set X) (hx : x ∈ U) :
    MapsTo (singularSubspaceInclusion U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ({x}ᶜ : Set X) := by
  rw [← subspaceIntersection_point_complement x U hx]
  exact subspaceIntersection_mapsTo _ _

/-- Open-neighborhood excision applies to the ORIGINAL punctured pair
map at the SAME point, with no manifold or local-homology conclusion assumed. -/
theorem integralLocalChainMap_quasiIso [T1Space X] (x : X) (U : Set X)
    (hU : IsOpen U) (hx : x ∈ U) :
    QuasiIso (integralRelativeChainMap (singularSubspaceInclusion U)
      (neighborhoodPointComplement_mapsTo x U hx)) := by
  have hc : ({x}ᶜ : Set X) ∪ U = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y = x
    · exact Or.inr (hy.symm ▸ hx)
    · exact Or.inl hy
  have h := integralRelativeChainMap_openExcision ({x}ᶜ : Set X) U isClosed_singleton.isOpen_compl hU hc
  have H : ∀ hf : MapsTo (singularSubspaceInclusion U) (subspaceIntersection ({x}ᶜ : Set X) U) ({x}ᶜ : Set X),
      QuasiIso (integralRelativeChainMap (singularSubspaceInclusion U) hf) := fun _ => h
  rw [subspaceIntersection_point_complement x U hx] at H
  exact H _

/-- The induced original pair map identifies actual neighborhood local
homology with actual ambient local homology, in EVERY degree. -/
def integralLocalHomologyNeighborhoodIso [T1Space X] (n : ℕ) (x : X) (U : Set X)
    (hU : IsOpen U) (hx : x ∈ U) :
    integralLocalHomology n (⟨x, hx⟩ : U) ≅ integralLocalHomology n x := by
  letI := integralLocalChainMap_quasiIso x U hU hx
  exact asIso (HomologicalComplex.homologyMap
    (integralRelativeChainMap (singularSubspaceInclusion U) (neighborhoodPointComplement_mapsTo x U hx)) n)

end DifferentialGeometry.Topology
