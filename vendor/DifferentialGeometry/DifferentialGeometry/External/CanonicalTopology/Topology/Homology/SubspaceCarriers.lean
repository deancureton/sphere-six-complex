module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierMaps
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainSupport

@[expose] public section

/-! # Exact carriers of chains in an original subspace -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The SAME intersection, viewed as a subset of the original subspace B. -/
def subspaceIntersection (A B : Set X) : Set B := {b | b.val ∈ A}

/-- An original chain on B is carried by A inside B exactly when its
SAME original ambient inclusion is carried by A. -/
theorem integralSingularChainsIn_subspace_iff (n : ℕ) (A B : Set X)
    (c : (integralSingularChains B).X n) :
    c ∈ integralSingularChainsIn n (subspaceIntersection A B) ↔
      (integralSingularChainMap (singularSubspaceInclusion B)).f n c ∈ integralSingularChainsIn n A := by
  constructor
  · intro hc
    exact integralSingularChainsIn_map n (singularSubspaceInclusion B) (fun _ h => h) hc
  · intro hc
    have hB : (integralSingularChainMap (singularSubspaceInclusion B)).f n c ∈
        integralSingularChainsIn n B := by
      rw [integralSingularChainsIn_eq_range]
      exact ⟨c, rfl⟩
    have hAB : (integralSingularChainMap (singularSubspaceInclusion B)).f n c ∈
        integralSingularChainsIn n (A ∩ B) := by
      rw [integralSingularChainsIn_inter]
      exact ⟨hc, hB⟩
    let b := integralSingularChainRestriction n (A ∩ B)
      ⟨(integralSingularChainMap (singularSubspaceInclusion B)).f n c, hAB⟩
    let f : C(↥(A ∩ B), subspaceIntersection A B) :=
      ⟨fun x => ⟨⟨x.val, x.property.2⟩, x.property.1⟩,
        (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
    rw [integralSingularChainsIn_eq_range]
    refine ⟨(integralSingularChainMap f).f n b, ?_⟩
    apply integralSingularChainInclusion_injective n B
    have he : integralSingularChainMap f ≫
        integralSingularChainMap (singularSubspaceInclusion (subspaceIntersection A B)) ≫
          integralSingularChainMap (singularSubspaceInclusion B) =
            integralSingularChainMap (singularSubspaceInclusion (A ∩ B)) := by
      rw [← integralSingularChainMap_comp, ← integralSingularChainMap_comp]
      rfl
    have h := congrArg (fun k : integralSingularChains ↥(A ∩ B) ⟶ integralSingularChains X => k.f n b) he
    exact h.trans (integralSingularChainRestriction_inclusion n (A ∩ B) _)

end DifferentialGeometry.Topology
