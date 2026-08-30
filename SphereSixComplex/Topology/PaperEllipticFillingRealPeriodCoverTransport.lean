module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourRadialFillingLift

/-!
# Real-period transport on the elliptic filling covers

These homeomorphisms identify the moving vector-bundle covers used by the analytic fillings with
the corresponding fixed real-period products.  The first coordinate is unchanged, so the radial
ball condition is preserved exactly.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial

variable (A : PaperAnalyticData) (r : ℝ)

/-- Fixed real-period coordinates on the order-three vector-bundle filling cover. -/
public def orderThreeFillingCoverRealPeriodHomeomorph :
    ComplexDiscBall r × ComplexTwoSpace ≃ₜ ComplexDiscBall r × ComplexTwoSpace where
  toFun p :=
    (p.1, (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne
      (orderThreeCayleyHomeomorph.symm p.1.1, p.2)).2)
  invFun p :=
    (p.1, (fixedToMovingCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne
      (orderThreeCayleyHomeomorph.symm p.1.1, p.2)).2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · have h := congrArg Prod.snd (fixedToMovingCover_movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (orderThreeCayleyHomeomorph.symm p.1.1, p.2))
      exact h
  right_inv p := by
    apply Prod.ext
    · rfl
    · have h := congrArg Prod.snd (movingToFixedCover_fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (orderThreeCayleyHomeomorph.symm p.1.1, p.2))
      exact h
  continuous_toFun := by
    let v : ComplexDiscBall r × ComplexTwoSpace → UpperHalfPlane × ComplexTwoSpace :=
      fun p ↦ (orderThreeCayleyHomeomorph.symm p.1.1, p.2)
    have hv : Continuous v :=
      (orderThreeCayleyHomeomorph.symm.continuous.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
    exact continuous_fst.prodMk
      (continuous_snd.comp ((movingToFixedCover_continuous A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).comp hv))
  continuous_invFun := by
    let v : ComplexDiscBall r × ComplexTwoSpace → UpperHalfPlane × ComplexTwoSpace :=
      fun p ↦ (orderThreeCayleyHomeomorph.symm p.1.1, p.2)
    have hv : Continuous v :=
      (orderThreeCayleyHomeomorph.symm.continuous.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
    exact continuous_fst.prodMk
      (continuous_snd.comp ((fixedToMovingCover_continuous A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).comp hv))

/-- Fixed real-period coordinates on the order-four vector-bundle filling cover. -/
public def orderFourFillingCoverRealPeriodHomeomorph :
    ComplexDiscBall r × ComplexTwoSpace ≃ₜ ComplexDiscBall r × ComplexTwoSpace where
  toFun p :=
    (p.1, (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo
      (orderFourCayleyHomeomorph.symm p.1.1, p.2)).2)
  invFun p :=
    (p.1, (fixedToMovingCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo
      (orderFourCayleyHomeomorph.symm p.1.1, p.2)).2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · have h := congrArg Prod.snd (fixedToMovingCover_movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (orderFourCayleyHomeomorph.symm p.1.1, p.2))
      exact h
  right_inv p := by
    apply Prod.ext
    · rfl
    · have h := congrArg Prod.snd (movingToFixedCover_fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (orderFourCayleyHomeomorph.symm p.1.1, p.2))
      exact h
  continuous_toFun := by
    let v : ComplexDiscBall r × ComplexTwoSpace → UpperHalfPlane × ComplexTwoSpace :=
      fun p ↦ (orderFourCayleyHomeomorph.symm p.1.1, p.2)
    have hv : Continuous v :=
      (orderFourCayleyHomeomorph.symm.continuous.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
    exact continuous_fst.prodMk
      (continuous_snd.comp ((movingToFixedCover_continuous A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).comp hv))
  continuous_invFun := by
    let v : ComplexDiscBall r × ComplexTwoSpace → UpperHalfPlane × ComplexTwoSpace :=
      fun p ↦ (orderFourCayleyHomeomorph.symm p.1.1, p.2)
    have hv : Continuous v :=
      (orderFourCayleyHomeomorph.symm.continuous.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
    exact continuous_fst.prodMk
      (continuous_snd.comp ((fixedToMovingCover_continuous A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).comp hv))

/-- The order-three cover map becomes the ordinary central torus projection in fixed real-period
coordinates. -/
public theorem orderThreeFillingProductMap_coverMap_eq_fixed
    (p : ComplexDiscBall r × ComplexTwoSpace) :
    orderThreeFillingProductMap A r (A.orderThreeFillingCoverMap r p) =
      (p.1.1, Quotient.mk _ (A.orderThreeFillingCoverRealPeriodHomeomorph r p).2) := by
  rw [orderThreeFillingProductMap, orderThreeFillingCoverMap.eq_def,
    orderThreeRealPeriodProductHomeomorph_mk,
    orderThreeCayleyHomeomorph.apply_symm_apply]
  rfl

/-- The order-four cover map becomes the ordinary central torus projection in fixed real-period
coordinates. -/
public theorem orderFourFillingProductMap_coverMap_eq_fixed
    (p : ComplexDiscBall r × ComplexTwoSpace) :
    orderFourFillingProductMap A r (A.orderFourFillingCoverMap r p) =
      (p.1.1, Quotient.mk _ (A.orderFourFillingCoverRealPeriodHomeomorph r p).2) := by
  rw [orderFourFillingProductMap, orderFourFillingCoverMap.eq_def,
    orderFourRealPeriodProductHomeomorph_mk,
    orderFourCayleyHomeomorph.apply_symm_apply]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData
