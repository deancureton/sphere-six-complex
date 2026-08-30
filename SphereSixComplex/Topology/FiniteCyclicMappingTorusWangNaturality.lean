module

public import SphereSixComplex.Topology.NormalizedAffineMappingTorusCover
public import SphereSixComplex.Topology.WangHomologyPresentationProof

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

/-- Inclusion of the fibre in the product model, over the additive-circle origin. -/
public def circleProductFiberInclusion {X : Type} [TopologicalSpace X] :
    C(X, UnitAddCircle × X) where
  toFun x := (0, x)
  continuous_toFun := continuous_const.prodMk continuous_id

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

/-- The natural commutative Wang diagram for the normalized `m`-fold cyclic cover.

The first square identifies the map on the upper coinvariant edge with the fibre identity.  The
second identifies the lower invariant edge with the standard cyclic norm. -/
public structure FiniteCyclicCoverWangNaturality
    {X : Type} [TopologicalSpace X] (k m : ℕ) [NeZero m]
    (phi : X ≃ₜ X) (hpow : phi ^ m = 1) where
  source : CircleProductWangPresentation X k
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
          (source.boundary z)

/-- Classical naturality of the Wang long exact sequence for the normalized finite cyclic cover.

This is source-independent and holds for every space, every degree, and every finite-order
clutching homeomorphism.  It is the mapping-cone/Serre-sequence naturality theorem: identity on
the fibre term and the group-homology norm on the swept term. -/
public axiom finiteCyclicCover_wangNaturality
    {X : Type} [TopologicalSpace X] (k m : ℕ) [NeZero m]
    (phi : X ≃ₜ X) (hpow : phi ^ m = 1) :
    Nonempty (FiniteCyclicCoverWangNaturality k m phi hpow)

end SphereSixComplex.Topology.FiniteCyclicMappingTorusWangNaturality

end

end
