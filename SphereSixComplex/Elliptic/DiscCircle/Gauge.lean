module

public import SphereSixComplex.Elliptic.LogarithmicGauge.Homeomorph

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.EllipticLogarithmicGauge

open SphereSixComplex.LatticeData SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph

variable {U : TriangleUniformization} (F : PeriodFunctions U)

public theorem orderThreePrincipalGauge_zero_of_exp
    (z : UpperHalfPlane) (l : ℂ)
    (hl : Complex.exp l = (orderThreeCayleyHomeomorph z : ℂ)) :
    orderThreePrincipalGaugeEquiv F (Quotient.mk _ (z, 0)) =
      Quotient.mk _ (z, logarithmicGaugeScalar l •
        periodVector (parameterMap F z).1 epsilon) := by
  have hw : (orderThreeCayleyHomeomorph z : ℂ) ≠ 0 := by
    rw [← hl]
    exact Complex.exp_ne_zero l
  have he : Complex.exp (Complex.log (orderThreeCayleyHomeomorph z)) =
      Complex.exp l := by
    rw [Complex.exp_log hw, hl]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have h := logarithmicGaugeMap_mk_eq_of_branch_change F
    orderThreeCayleyHomeomorph epsilon
    (fun _ ↦ l) (fun w ↦ Complex.log w) z 0 k (by rw [hk]; ring)
  rw [orderThreePrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply]
  change familyTranslationMap F
    (logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
      (fun w ↦ Complex.log w)) (Quotient.mk _ (z, 0)) = _
  rw [h]
  simp only [familyTranslationMap_mk, familyTranslationCover.eq_def,
    logarithmicGaugeSection.eq_def, add_zero]

public theorem orderFourPrincipalGauge_zero_of_exp
    (z : UpperHalfPlane) (l : ℂ)
    (hl : Complex.exp l = (orderFourCayleyHomeomorph z : ℂ)) :
    orderFourPrincipalGaugeEquiv F (Quotient.mk _ (z, 0)) =
      Quotient.mk _ (z, logarithmicGaugeScalar l •
        periodVector (parameterMap F z).1 (-epsilon')) := by
  have hw : (orderFourCayleyHomeomorph z : ℂ) ≠ 0 := by
    rw [← hl]
    exact Complex.exp_ne_zero l
  have he : Complex.exp (Complex.log (orderFourCayleyHomeomorph z)) =
      Complex.exp l := by
    rw [Complex.exp_log hw, hl]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have h := logarithmicGaugeMap_mk_eq_of_branch_change F
    orderFourCayleyHomeomorph (-epsilon')
    (fun _ ↦ l) (fun w ↦ Complex.log w) z 0 k (by rw [hk]; ring)
  rw [orderFourPrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply]
  change familyTranslationMap F
    (logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
      (fun w ↦ Complex.log w)) (Quotient.mk _ (z, 0)) = _
  rw [h]
  simp only [familyTranslationMap_mk, familyTranslationCover.eq_def,
    logarithmicGaugeSection.eq_def, add_zero]

end SphereSixComplex.Geometry.EllipticLogarithmicGauge
