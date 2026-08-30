module

public import SphereSixComplex.Topology.PaperMultipleFiberHOneTopologyCore

open Topology

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
namespace EstablishedAffineCyclicQuotientHomology

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

variable {m : ℕ} [NeZero m]
variable {p : SphereSixComplex.Periods.Parameters}
variable {D : RadialEllipticActionData m (AdditiveTorus p)}

public theorem centralFiberCoverProjection_surjective
    (D : RadialEllipticActionData m (AdditiveTorus p)) :
    Function.Surjective (RadialEllipticActionData.centralFiberCoverProjection D) := by
  rintro ⟨x, hx⟩
  change x ∈ Quotient.mk _ '' D.centralSlice at hx
  obtain ⟨q, hq, rfl⟩ := hx
  refine ⟨⟨q, ?_⟩, rfl⟩
  exact ⟨q, hq, rfl⟩

public theorem centralFiberCoverProjection_isOpenQuotientMap
    (D : RadialEllipticActionData m (AdditiveTorus p)) :
    IsOpenQuotientMap (RadialEllipticActionData.centralFiberCoverProjection D) := by
  let action := D.actionData.diagonalAction
  let _ := action
  let _ : ContinuousConstSMul (FiniteCyclic m) D.Product :=
    ⟨D.representation_continuous⟩
  have hfull : IsOpenMap
      (Quotient.mk _ : D.Product → D.FillingQuotient) := by
    change IsOpenMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic m) D.Product))
    exact MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  have hopen : IsOpenMap
      (RadialEllipticActionData.centralFiberCoverProjection D) := by
    intro U hU
    rw [isOpen_induced_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    rw [isOpen_induced_iff]
    refine ⟨Quotient.mk _ '' V, hfull V hV, ?_⟩
    ext b
    constructor
    · rintro ⟨q, hq, hqb⟩
      exact ⟨⟨q, by rw [hqb]; exact b.2⟩, hq, Subtype.ext hqb⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : D.Product), ha, rfl⟩
  exact IsOpenQuotientMap.mk (centralFiberCoverProjection_surjective D)
    (RadialEllipticActionData.centralFiberCoverProjection D).continuous hopen

public theorem complexTwoReducedCentralFiberProjection_isQuotientMap
    (D : RadialEllipticActionData m (AdditiveTorus p)) :
    IsQuotientMap (complexTwoReducedCentralFiberProjection (D := D)) := by
  have htorus : IsQuotientMap (torusProjection p) :=
    isQuotientMap_quotient_mk'
  have hsource : IsQuotientMap
      ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm) :=
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm.isQuotientMap
  have hcentral : IsQuotientMap
      (RadialEllipticActionData.centralFiberCoverProjection D) :=
    (centralFiberCoverProjection_isOpenQuotientMap D).isQuotientMap
  change IsQuotientMap
    ((RadialEllipticActionData.centralFiberCoverProjection D) ∘
      ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm ∘
        torusProjection p))
  exact hcentral.comp (hsource.comp htorus)

end EstablishedAffineCyclicQuotientHomology
end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
