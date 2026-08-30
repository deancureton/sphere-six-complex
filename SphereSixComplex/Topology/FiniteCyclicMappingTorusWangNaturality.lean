module

public import SphereSixComplex.Topology.NormalizedAffineMappingTorusCover
public import SphereSixComplex.Topology.CircleProductIdentityMappingTorus

/-!
# Naturality of the Wang sequence for finite cyclic mapping-torus covers

The boundary below is intrinsic: it mentions only the actual fibre-inclusion homology maps and
the actual Wang boundary from the Mayer--Vietoris construction.  No coordinate basis or elliptic
data occurs in its statement.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.FiniteCyclicMappingTorusWangNaturality

open NormalizedAffineMappingTorusCover
open CircleProductIdentityMappingTorus

/-- Inclusion of the fibre in the product model, over the additive-circle origin. -/
public def circleProductFiberInclusion {X : Type} [TopologicalSpace X] :
    C(X, UnitAddCircle × X) :=
  productFiberInclusion

/-- The oriented Wang short exact sequence of the trivial mapping torus `S¹ × X` in total
degree `k + 1`. -/
public structure CircleProductWangPresentation
    (X : Type) [TopologicalSpace X] (k : ℕ) where
  boundary : IntegralSingularHomology (k + 1) (UnitAddCircle × X) →+
    IntegralSingularHomology k X
  inclusion_injective : Function.Injective
    (integralSingularHomologyMap (k + 1) (circleProductFiberInclusion (X := X)))
  exact_inclusion_boundary : Function.Exact
    (integralSingularHomologyMap (k + 1) (circleProductFiberInclusion (X := X))) boundary
  boundary_surjective : Function.Surjective boundary

/-- The product presentation transported from the constructed Mayer--Vietoris Wang sequence of
the identity mapping torus. -/
public noncomputable def canonicalCircleProductWangPresentation
    (X : Type) [TopologicalSpace X] (k : ℕ) : CircleProductWangPresentation X k where
  boundary := canonicalProductWangBoundary k
  inclusion_injective := canonicalProductFiberInclusion_injective k
  exact_inclusion_boundary := canonicalProductWang_exact k
  boundary_surjective := canonicalProductWangBoundary_surjective k

/-- The natural commutative Wang diagram for the normalized `m`-fold cyclic cover.

The first square identifies the map on the upper coinvariant edge with the fibre identity.  The
second identifies the lower invariant edge with the standard cyclic norm. -/
public structure FiniteCyclicCoverWangNaturality
    {X : Type} [TopologicalSpace X] (k m : ℕ) [NeZero m]
    (phi : X ≃ₜ X) (hpow : phi ^ m = 1) where
  fibre_square : ∀ x : IntegralSingularHomology (k + 1) X,
    integralSingularHomologyMap (k + 1)
        (normalizedAffineCoverToCircleMappingTorus phi hpow)
        (integralSingularHomologyMap (k + 1)
          (circleProductFiberInclusion (X := X)) x) =
      (circleMappingTorusWangPresentationOfCover phi k).inclusion x
  boundary_square : ∀ z : IntegralSingularHomology (k + 1) (UnitAddCircle × X),
    (circleMappingTorusWangPresentationOfCover phi k).boundary
        (integralSingularHomologyMap (k + 1)
          (normalizedAffineCoverToCircleMappingTorus phi hpow) z) =
      ∑ i ∈ Finset.range m,
        integralSingularHomologyMap k ((phi ^ i : X ≃ₜ X) : C(X, X))
          (canonicalProductWangBoundary k z)

end SphereSixComplex.Topology.FiniteCyclicMappingTorusWangNaturality

end

end
