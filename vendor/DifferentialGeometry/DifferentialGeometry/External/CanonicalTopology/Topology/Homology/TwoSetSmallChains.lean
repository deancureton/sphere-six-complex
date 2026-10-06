module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallRelative
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubspaceCarriers

@[expose] public section

/-! # The actual two-set small complex and its quotient square -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The specified two original subspaces, in the order A, B. -/
abbrev twoSetCover (A B : Set X) : Bool → Set X := fun b => if b then B else A

/-- Small chains for this pair are exactly sums of original A- and B-carried chains. -/
theorem integralSingularTwoSetSmallChains_eq (n : ℕ) (A B : Set X) :
    integralSingularSmallChains n (twoSetCover A B) =
      integralSingularChainsIn n A ⊔ integralSingularChainsIn n B := by
  simp [integralSingularSmallChains, twoSetCover, iSup_bool_eq, sup_comm]

/-- Every actual small chain for the pair decomposes into actual chains
on A and B through their SAME original inclusions. -/
theorem integralSingularTwoSetSmallChains_decompose (n : ℕ) (A B : Set X)
    (c : integralSingularSmallChains n (twoSetCover A B)) :
    ∃ a : (integralSingularChains A).X n, ∃ b : (integralSingularChains B).X n,
      (integralSingularChainMap (singularSubspaceInclusion A)).f n a +
        (integralSingularChainMap (singularSubspaceInclusion B)).f n b = c.val := by
  have hc := (integralSingularTwoSetSmallChains_eq n A B).le c.property
  rw [Submodule.mem_sup] at hc
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  rw [integralSingularChainsIn_eq_range] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨a', b', hab⟩

/-- The original map of pairs (B, B ∩ A) → (X,A). -/
theorem subspaceIntersection_mapsTo (A B : Set X) :
    MapsTo (singularSubspaceInclusion B) (subspaceIntersection A B) A := fun _ h => h

/-- The SAME original pair square factors through the two-set small complex. -/
theorem integralSingularTwoSetSmall_square (A B : Set X) :
    integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection A B)) ≫
      integralSingularChainToSmall (twoSetCover A B) true =
        integralSingularChainMap (singularPairRestriction (singularSubspaceInclusion B)
          (subspaceIntersection_mapsTo A B)) ≫ integralSingularChainToSmall (twoSetCover A B) false := by
  apply (cancel_mono (integralSingularSmallInclusion (twoSetCover A B))).mp
  exact integralSingularChainMap_pair_square (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)

end DifferentialGeometry.Topology
