module

public import SphereSixComplex.Regular.Cover.FamilyTransport

/-! # Lifted affine radial equivalences -/

open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

namespace SphereSixComplex.Geometry.AnalyticData

variable (A : AnalyticData)

/-- The inclusion of the order-three affine disc lift into the order-three affine half-plane
lift is a deck-equivariant homotopy equivalence on the regular torus family. -/
public theorem exists_orderThreeAffineRadialEquiv {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 2 / 3) :
    ∃ E : EquivariantHomotopyEquivData
        (A.orderThreeAffineDiscLiftAction r) A.orderThreeAffineHalfPlaneLiftAction,
      (E.toFun : (A.orderThreeAffineDiscLiftCarrier r).carrier →
        A.orderThreeAffineHalfPlaneLiftCarrier.carrier) =
          A.orderThreeAffineDiscLiftInclusion hr :=
  ⟨familyEquivOfBaseEquiv (A.orderThreeAffineDiscLiftCarrier_subset_halfPlane hr)
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    (A.orderThreeBaseRadialEquiv (half_pos hr0) (half_lt_self hr0) hr) (fun _ ↦ rfl), rfl⟩

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
