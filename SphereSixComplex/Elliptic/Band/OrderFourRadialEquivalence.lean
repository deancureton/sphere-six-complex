module

public import SphereSixComplex.Regular.Cover.FamilyTransport

/-! # The order-four lifted affine radial equivalence -/

open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

namespace SphereSixComplex.Geometry.AnalyticData

variable (A : AnalyticData)

/-- The order-four affine disc lift includes into the order-four affine half-plane lift by a
full-deck equivariant homotopy equivalence on the genuine regular cover. -/
public theorem exists_orderFourAffineRadialEquiv
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3) :
    ∃ E : EquivariantHomotopyEquivData
        (A.orderFourAffineDiscLiftAction r) A.orderFourAffineHalfPlaneLiftAction,
      (E.toFun : (A.orderFourAffineDiscLiftCarrier r).carrier →
        A.orderFourAffineHalfPlaneLiftCarrier.carrier) =
          A.orderFourAffineDiscLiftInclusion hr :=
  ⟨familyEquivOfBaseEquiv (A.orderFourAffineDiscLiftCarrier_subset_halfPlane hr)
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    (A.orderFourBaseRadialEquiv (half_pos hr0) (half_lt_self hr0) hr) (fun _ ↦ rfl), rfl⟩

end SphereSixComplex.Geometry.AnalyticData
