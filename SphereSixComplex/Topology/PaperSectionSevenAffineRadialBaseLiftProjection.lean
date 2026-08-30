module

public import SphereSixComplex.Topology.PaperSectionSevenAffinePrincipalGaugeStripLiftComparison

/-!
# Projection formulas for the affine radial base lifts

The inverse lifted radial maps project to the explicit normalization maps on the punctured
affine coordinate line.  These formulas identify the common base map needed for uniqueness of
the principal-gauge and marked-strip lifts.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

universe u v

variable {E : Type u} {Z : Type v} [TopologicalSpace E] [TopologicalSpace Z]
variable {small big : Set Z} {hsmall : small ⊆ big}

/-- The endpoint of the lifted reverse deformation projects to the normalization of the base
coordinate. -/
public theorem CoveringPreimageDeformationData.ambientLift_one_projects_normalize
    (D : CoveringPreimageDeformationData small big hsmall)
    (p : E → Z) (cov : IsCoveringMap p)
    (e : coveringRegionPreimage p big) :
    p (D.ambientLift p cov (1, e)) =
      (D.normalize (CoveringPreimageDeformationData.bigCoordinate p cov e)).1 := by
  rw [D.ambientLift_projects p cov 1 e]
  change (D.homotopy.symm
    (1, CoveringPreimageDeformationData.bigCoordinate p cov e)).1 = _
  rw [ContinuousMap.Homotopy.symm_apply]
  norm_num
  rfl

end SphereSixComplex

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex

/-- The order-three lifted radial inverse lies over the explicit order-three normalization. -/
public theorem orderThreeBaseRadialEquiv_invFun_regularCoordinate
    (A : PaperAnalyticData) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (hr : r ≤ 2 / 3)
    (e : A.orderThreeAffineHalfPlaneBaseLift) :
    A.regularCoordinate
        ((A.orderThreeBaseRadialEquiv hs hsr hr).invFun e).1 =
      ((orderThreeCoordinateDeformation hs hsr hr).normalize
        ⟨A.regularCoordinate e.1, e.2⟩).1 := by
  exact (orderThreeCoordinateDeformation hs hsr hr).ambientLift_one_projects_normalize
    A.regularCoordinate A.regularCoordinate_isCoveringMap e

/-- The order-four lifted radial inverse lies over the explicit order-four normalization. -/
public theorem orderFourBaseRadialEquiv_invFun_regularCoordinate
    (A : PaperAnalyticData) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (hr : r ≤ 1 - 1 / 3)
    (e : A.orderFourAffineHalfPlaneBaseLift) :
    A.regularCoordinate
        ((A.orderFourBaseRadialEquiv hs hsr hr).invFun e).1 =
      ((orderFourCoordinateDeformation hs hsr hr).normalize
        ⟨A.regularCoordinate e.1, e.2⟩).1 := by
  exact (orderFourCoordinateDeformation hs hsr hr).ambientLift_one_projects_normalize
    A.regularCoordinate A.regularCoordinate_isCoveringMap e

end SphereSixComplex.Geometry.PaperAnalyticData

end
