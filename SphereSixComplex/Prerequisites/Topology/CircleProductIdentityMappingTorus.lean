module

public import SphereSixComplex.Prerequisites.Topology.IdentityMappingTorus
public import SphereSixComplex.Prerequisites.Topology.StandardTorusHomology

/-!
# The product as the mapping torus of the identity

The real-line quotient model identifies `S¹ × X` with the mapping torus of the identity of `X`.
Transporting the constructed Mayer--Vietoris Wang sequence through this homeomorphism gives a
canonical product Wang boundary, with no arbitrary choice of an automorphism of `Hₖ(X)`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.CircleProductIdentityMappingTorus

open CyclicAngularFundamentalDomain
open StandardTorusHomology

variable {X : Type} [TopologicalSpace X]

/-- The canonical product Wang boundary, transported from the constructed Mayer--Vietoris
boundary for the mapping torus of the identity. -/
public noncomputable def canonicalProductWangBoundary (k : ℕ) :
    IntegralSingularHomology (k + 1) (UnitAddCircle × X) →+
    IntegralSingularHomology k X :=
  (circleMappingTorusWangPresentationOfCover (Homeomorph.refl X) k).boundary.comp
    (integralSingularHomologyMap (k + 1)
      (circleProductIdentityMappingTorusHomeomorph (X := X) :
        C(UnitAddCircle × X, CircleMappingTorus (Homeomorph.refl X))))

private theorem canonical_inclusion_naturality (k : ℕ)
    (x : IntegralSingularHomology (k + 1) X) :
    integralSingularHomologyMap (k + 1)
        (circleProductIdentityMappingTorusHomeomorph (X := X) :
          C(UnitAddCircle × X, CircleMappingTorus (Homeomorph.refl X)))
        (integralSingularHomologyMap (k + 1) (productFiberInclusion (X := X)) x) =
      (circleMappingTorusWangPresentationOfCover
        (Homeomorph.refl X) k).inclusion x := by
  rw [integralSingularHomologyMap_comp_wang,
    circleProductIdentityMappingTorusHomeomorph_comp_productFiberInclusion]
  rfl


public theorem canonicalProductWangBoundary_surjective (k : ℕ) :
    Function.Surjective (canonicalProductWangBoundary (X := X) k) := by
  let P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl X) k
  have hlow : P.lowDifference = 0 := circleMonodromyDifference_refl (F := X) k
  have hboundary : Function.Surjective P.boundary := by
    intro y
    exact (P.exact_boundary_lowDifference y).mp (by rw [hlow]; rfl)
  intro y
  obtain ⟨z, hz⟩ := hboundary y
  let eH := integralSingularHomologyEquiv (k + 1)
    (circleProductIdentityMappingTorusHomeomorph (X := X))
  refine ⟨eH.symm z, ?_⟩
  simp only [canonicalProductWangBoundary, AddMonoidHom.comp_apply]
  change P.boundary (eH (eH.symm z)) = y
  rw [eH.apply_symm_apply, hz]

public theorem canonicalProductWang_exact (k : ℕ) :
    Function.Exact
      (integralSingularHomologyMap (k + 1) (productFiberInclusion (X := X)))
      (canonicalProductWangBoundary (X := X) k) := by
  let P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl X) k
  let eH := integralSingularHomologyEquiv (k + 1)
    (circleProductIdentityMappingTorusHomeomorph (X := X))
  intro z
  simp only [canonicalProductWangBoundary, AddMonoidHom.comp_apply]
  change P.boundary (eH z) = 0 ↔ _
  rw [P.exact_inclusion_boundary (eH z)]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, eH.injective ?_⟩
    calc
      eH (integralSingularHomologyMap (k + 1) productFiberInclusion x) =
          P.inclusion x := canonical_inclusion_naturality k x
      _ = eH z := hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    calc
      P.inclusion x =
          eH (integralSingularHomologyMap (k + 1) productFiberInclusion x) :=
        (canonical_inclusion_naturality k x).symm
      _ = eH z := congrArg eH hx


end SphereSixComplex.Topology.CircleProductIdentityMappingTorus

end

end
