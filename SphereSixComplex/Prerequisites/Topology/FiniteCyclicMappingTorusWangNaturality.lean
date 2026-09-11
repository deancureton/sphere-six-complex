module

public import SphereSixComplex.Prerequisites.Topology.NormalizedAffineMappingTorusCover
public import SphereSixComplex.Prerequisites.Topology.CircleProductIdentityMappingTorus

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




end SphereSixComplex.Topology.FiniteCyclicMappingTorusWangNaturality

end

end
