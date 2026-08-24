module

public import SphereSixComplex.Topology.EstablishedAffineVanKampen
public import SphereSixComplex.Topology.PaperSectionSevenFinalDegreeZero
public import Mathlib.Analysis.Convex.Contractible

/-!
# Candidate universal covers of the actual filling pieces

The additive cusp collar cover and the Cayley vector-bundle covers of the elliptic fillings are
simply connected.  The elliptic maps below are the actual composites to the finite affine
quotients.  Constructing the quotient-cover squares additionally requires the combined affine
deck groups and their actions on these sources.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

open Geometry Geometry.ComplexTorus Geometry.CuspPuncturedCollarBridge
open Geometry.EllipticLocalCoordinates Geometry.EllipticVaryingFamilyQuotient

/-- The normalized additive cover of the actual cusp collar is simply connected. -/
public theorem additiveCuspRadiusCover_simplyConnected {r : ℝ} (hr : 0 < r) :
    SimplyConnectedSpace (additiveCuspRadiusCover r) := by
  let _ : ContractibleSpace (additiveCuspRadiusCover r) :=
    (additiveCuspRadiusCover_convex r hr).contractibleSpace
      (additiveCuspRadiusCover_nonempty r hr)
  infer_instance

namespace Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The vector-bundle cover composed with the order-three affine filling quotient. -/
public noncomputable def orderThreeActualFillingCoverProjection (r : ℝ) :
    C(ComplexDiscBall r × ComplexTwoSpace, A.OrderThreeVaryingFilling r) where
  toFun p := Quotient.mk _ (A.orderThreeFillingCoverMap r p)
  continuous_toFun := continuous_quot_mk.comp (A.orderThreeFillingCoverMap_continuous r)

/-- The vector-bundle cover composed with the order-four affine filling quotient. -/
public noncomputable def orderFourActualFillingCoverProjection (r : ℝ) :
    C(ComplexDiscBall r × ComplexTwoSpace, A.OrderFourVaryingFilling r) where
  toFun p := Quotient.mk _ (A.orderFourFillingCoverMap r p)
  continuous_toFun := continuous_quot_mk.comp (A.orderFourFillingCoverMap_continuous r)

/-- The actual order-three filling projection from the vector-bundle cover is onto. -/
public theorem orderThreeActualFillingCoverProjection_surjective (r : ℝ) :
    Function.Surjective (A.orderThreeActualFillingCoverProjection r) :=
  Quotient.mk_surjective.comp (A.orderThreeFillingCoverMap_surjective r)

/-- The actual order-four filling projection from the vector-bundle cover is onto. -/
public theorem orderFourActualFillingCoverProjection_surjective (r : ℝ) :
    Function.Surjective (A.orderFourActualFillingCoverProjection r) :=
  Quotient.mk_surjective.comp (A.orderFourFillingCoverMap_surjective r)

/-- The candidate total space of the actual order-three filling cover is simply connected. -/
public theorem orderThreeFillingCoverSource_simplyConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := by
  let _ : ContractibleSpace (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).contractibleSpace (Metric.nonempty_ball.mpr hr)
  let _ : ContractibleSpace (ComplexDiscBall r) :=
    (complexDiscBallHomeomorph hr1).contractibleSpace
  infer_instance

/-- The candidate total space of the actual order-four filling cover is simply connected. -/
public theorem orderFourFillingCoverSource_simplyConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) :=
  orderThreeFillingCoverSource_simplyConnected hr hr1

end Geometry.PaperAnalyticData

end SphereSixComplex

end
