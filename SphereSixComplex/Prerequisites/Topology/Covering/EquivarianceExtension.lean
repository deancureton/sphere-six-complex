module

public import Mathlib.Topology.Covering.Quotient

namespace SphereSixComplex.Topology

universe u v w x y z

/-- Equivariance of a lift between quotient covers is determined at one point. -/
public theorem quotientCover_equivariant_of_eq_at
    {G : Type u} {H : Type v} {E : Type w} {E' : Type x}
    {B : Type y} {N : Type z}
    [Group G] [Group H] [TopologicalSpace E] [TopologicalSpace E']
    [TopologicalSpace B] [TopologicalSpace N] [MulAction G E] [MulAction H E']
    [PreconnectedSpace E]
    (p : E → B) (q : E' → N)
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    (φ : G →* H) (L : C(E, E')) (b : B → N)
    (commutes : ∀ z, b (p z) = q (L z))
    (e₀ : E) (atBase : ∀ g, L (g • e₀) = φ g • L e₀) :
    ∀ g z, L (g • z) = φ g • L z := by
  intro g z
  have hleft : Continuous (fun z : E ↦ L (g • z)) :=
    L.continuous.comp (hp.continuous_const_smul g)
  have hright : Continuous (fun z : E ↦ φ g • L z) :=
    (hq.continuous_const_smul (φ g)).comp L.continuous
  have hcomp :
      q ∘ (fun z : E ↦ L (g • z)) =
        q ∘ (fun z : E ↦ φ g • L z) := by
    funext z
    exact (commutes (g • z)).symm.trans <|
      (congrArg b (hp.map_smul g)).trans <|
        (commutes z).trans (hq.map_smul (φ g)).symm
  have hfun := hq.isCoveringMap.eq_of_comp_eq hleft hright hcomp e₀ (atBase g)
  exact congrFun hfun z

end SphereSixComplex.Topology
