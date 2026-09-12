module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRegularLiftCarriers

/-!
# The order-four affine overlap quotient identification

The orbit quotient of the order-four affine disc lift is identified with its open image in the
actual central family, and that image is computed to be the exact affine coordinate disc region.
Reducing along the fixed central-region quotient homeomorphism then shows that the order-four
overlap quotient identification exists exactly when the actual order-four star overlap is, on the
nose, an affine coordinate disc region.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open GlobalTorusFamily TorusFamily
open EquivariantQuotientHomeomorph
open SphereSixComplex.OpenUnionHomotopy

variable (A : AnalyticData)

/-- The order-four lifted disc quotient mapped into the actual central family. -/
public noncomputable def orderFourAffineDiscLiftQuotientToCentralFamily (r : ℝ) :
    Quotient (orbitRelOf (A.orderFourAffineDiscLiftAction r)) → A.CentralFamily :=
  restrictedOrbitQuotientInclusion (regularFamilyDeckAction A.periods)
    (A.orderFourAffineDiscLiftCarrier r)

/-- The disc lift quotient is exactly the affine coordinate disc region of the central family. -/
public theorem range_orderFourAffineDiscLiftQuotientToCentralFamily (r : ℝ) :
    Set.range (A.orderFourAffineDiscLiftQuotientToCentralFamily r) =
      {q : A.CentralFamily | ‖(A.centralFamilyCoordinate q).1 - 1‖ < r} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.inductionOn with
    | _ x => exact x.2
  · intro hq
    induction q using Quotient.inductionOn with
    | _ q =>
      refine ⟨Quotient.mk _ ⟨q, ?_⟩, rfl⟩
      exact hq

/-- The disc lift quotient inclusion is compatible with the two central-family inclusions. -/
public theorem orderFourAffineHalfPlaneLiftQuotientToCentralFamily_discInclusion
    {r : ℝ} (hr : r ≤ 1 - 1 / 3)
    (q : Quotient (orbitRelOf (A.orderFourAffineDiscLiftAction r))) :
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.orderFourAffineDiscLiftQuotientInclusion hr q) =
      A.orderFourAffineDiscLiftQuotientToCentralFamily r q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- Undoing the half-plane range homeomorphism returns the underlying central-family point. -/
public theorem orderFourAffineHalfPlaneLiftQuotientToCentralFamily_homeomorphRange_symm
    (w : Set.range A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily) :
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.orderFourAffineHalfPlaneLiftQuotientHomeomorphRange.symm w) =
      (w : A.CentralFamily) := by
  have h := Topology.IsEmbedding.toHomeomorph_apply_coe
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.isEmbedding
    (A.orderFourAffineHalfPlaneLiftQuotientHomeomorphRange.symm w)
  exact h.symm.trans (congrArg Subtype.val
    (A.orderFourAffineHalfPlaneLiftQuotientHomeomorphRange.apply_symm_apply w))

/-- The fixed central-region quotient homeomorphism is the identity in central-family
coordinates. -/
public theorem orderFourAffineHalfPlaneLiftQuotientToCentralFamily_centralRegionQuotient
    (x : A.ellipticCentralImage)
    (hx : (1 : ℝ) / 3 < A.ellipticCentralHeight x) :
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.affineOrderFourCentralRegionQuotientHomeomorph ⟨x.1, ⟨x, hx, rfl⟩⟩) =
      A.ellipticCentralImageHomeomorph x := by
  have h1 : (centralHeightUpperRegionHomeomorph A A.ellipticCentralHeight
      (1 / 3 : ℝ)).symm ⟨x.1, ⟨x, hx, rfl⟩⟩ = ⟨x, hx⟩ := by
    rw [Homeomorph.symm_apply_eq]
    rfl
  simp only [affineOrderFourCentralRegionQuotientHomeomorph,
    Homeomorph.trans_apply,
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_homeomorphRange_symm, h1]
  rfl








end SphereSixComplex.Geometry.AnalyticData

end
