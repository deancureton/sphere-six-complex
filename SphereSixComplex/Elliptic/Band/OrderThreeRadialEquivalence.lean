module

public import SphereSixComplex.Regular.Cover.FamilyTransport

/-! # The order-three lifted affine radial equivalence -/

open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

namespace SphereSixComplex.Geometry.AnalyticData

variable (A : AnalyticData) {r : ℝ}

/-- The inclusion of the order-three affine disc lift into the order-three affine half-plane
lift is a deck-equivariant homotopy equivalence on the regular torus family. -/
public theorem exists_orderThreeAffineRadialEquiv (hr0 : 0 < r) (hr : r ≤ 2 / 3) :
    ∃ E : EquivariantHomotopyEquivData
        (A.orderThreeAffineDiscLiftAction r) A.orderThreeAffineHalfPlaneLiftAction,
      (E.toFun : (A.orderThreeAffineDiscLiftCarrier r).carrier →
        A.orderThreeAffineHalfPlaneLiftCarrier.carrier) =
          A.orderThreeAffineDiscLiftInclusion hr :=
  ⟨familyEquivOfBaseEquiv (A.orderThreeAffineDiscLiftCarrier_subset_halfPlane hr)
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    (A.orderThreeBaseRadialEquiv (half_pos hr0) (half_lt_self hr0) hr) (fun _ ↦ rfl), rfl⟩

end SphereSixComplex.Geometry.AnalyticData
