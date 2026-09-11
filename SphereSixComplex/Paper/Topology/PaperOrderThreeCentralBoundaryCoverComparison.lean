module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticFillingDeckTransport
public import SphereSixComplex.Paper.Topology.EstablishedEquivariantUniversalCover
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeCommonGaugeGeometry
public import SphereSixComplex.Prerequisites.Topology.EstablishedAffineVanKampen

/-!
# The order-three boundary cover comparison

The central universal cover is the based-path universal cover.  Consequently its transported
deck action reverses the deck element represented by a loop.  The physical inverse meridian
therefore maps to the inverse first free lift, while a local translation by `a` maps to the
global affine translation by `-a`.

This file isolates the remaining point-set input: a continuous lift of the literal order-three
collar chart with those equivariance formulas.  Once such a lift is supplied, uniqueness of
lifts proves that its two marked deck transformations and the canonical lift-induced ones differ
by one common conjugator.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology


/-- Simultaneous conjugacy is transitive. -/
public theorem SimultaneouslyConjugate.trans
    {G : Type*} [Group G] {left middle right : G × G}
    (h₁ : SimultaneouslyConjugate left middle)
    (h₂ : SimultaneouslyConjugate middle right) :
    SimultaneouslyConjugate left right := by
  obtain ⟨c₁, hfirst₁, hsecond₁⟩ := h₁
  obtain ⟨c₂, hfirst₂, hsecond₂⟩ := h₂
  refine ⟨c₁ * c₂, ?_, ?_⟩
  · rw [hfirst₁, hfirst₂]
    group
  · rw [hsecond₁, hsecond₂]
    group

end SphereSixComplex.Topology

end

end
