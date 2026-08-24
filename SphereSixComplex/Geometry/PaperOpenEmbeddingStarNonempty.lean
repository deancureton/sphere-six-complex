module

public import SphereSixComplex.Geometry.PaperOpenEmbeddingStar

/-!
# Nonempty collars in the concrete four-piece star

The cusp and elliptic punctured carriers contain explicit points.  Their quotient classes supply
the nonempty collar hypotheses needed by the four-piece gluing construction.
-/

namespace SphereSixComplex.Geometry

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open TorusFamily AnalyticTorusFamily CuspPuncturedCollarBridge
open EllipticLocalCoordinates EllipticCayleyHomeomorph EllipticWholeFiberCompactCover
open EllipticVaryingFamilyQuotient EllipticPuncturedCollarGaugeHomeomorph
open EquivariantQuotientHomeomorph

noncomputable section

private def puncturedDiscPoint (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : ComplexUnitDisc :=
  ⟨((r / 2 : ℝ) : ℂ), by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith⟩

private theorem puncturedDiscPoint_norm (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖(puncturedDiscPoint r hr hr1 : ℂ)‖ = r / 2 := by
  rw [puncturedDiscPoint, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- A positive order-three punctured collar contains a point of Cayley radius `r / 2`. -/
public theorem orderThreeAffinePuncturedCarrier_nonempty
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Nonempty (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := by
  let w := puncturedDiscPoint r hr hr1
  let q : TotalSpace (parameterMap A.periods) :=
    Quotient.mk _ (orderThreeCayleyHomeomorph.symm w, 0)
  refine ⟨⟨q, ?_⟩⟩
  change 0 < orderThreeFamilyRadius A.periods q ∧ orderThreeFamilyRadius A.periods q < r
  dsimp only [q]
  rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk,
    orderThreeCayleyHomeomorph.apply_symm_apply, puncturedDiscPoint_norm r hr hr1]
  exact ⟨half_pos hr, half_lt_self hr⟩

/-- A positive order-four punctured collar contains a point of Cayley radius `r / 2`. -/
public theorem orderFourAffinePuncturedCarrier_nonempty
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Nonempty (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := by
  let w := puncturedDiscPoint r hr hr1
  let q : TotalSpace (parameterMap A.periods) :=
    Quotient.mk _ (orderFourCayleyHomeomorph.symm w, 0)
  refine ⟨⟨q, ?_⟩⟩
  change 0 < orderFourFamilyRadius A.periods q ∧ orderFourFamilyRadius A.periods q < r
  dsimp only [q]
  rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk,
    orderFourCayleyHomeomorph.apply_symm_apply, puncturedDiscPoint_norm r hr hr1]
  exact ⟨half_pos hr, half_lt_self hr⟩

/-- Each of the cusp, order-three, and order-four common collar sources is nonempty. -/
public theorem starCollarSourceType_nonempty (i : Fin 3) :
    Nonempty (A.starCollarSourceType i) := by
  fin_cases i
  · exact ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty A.starCuspWitness).some⟩
  · exact ⟨Quotient.mk _
      (A.orderThreeAffinePuncturedCarrier_nonempty A.starSeparation.orderThree.radius
        A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one).some⟩
  · exact ⟨Quotient.mk _
      (A.orderFourAffinePuncturedCarrier_nonempty A.starSeparation.orderFour.radius
        A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one).some⟩

/-- The collar sources in the packaged open-embedding star are nonempty. -/
public theorem openEmbeddingStarData_collarSource_nonempty :
    ∀ i, Nonempty (A.openEmbeddingStarData.collarSource i) := fun i ↦ by
  change Nonempty (A.starCollarSourceType i)
  exact A.starCollarSourceType_nonempty i

/-- All three central collar images in the packaged star are nonempty. -/
public theorem openEmbeddingStarData_centralCollar_nonempty :
    ∀ i, Nonempty (A.openEmbeddingStarData.centralCollar i) := fun i ↦ by
  exact ⟨A.openEmbeddingStarData.centralCollarPoint i
    (A.openEmbeddingStarData_collarSource_nonempty i).some⟩

/-- All three filling collar images in the packaged star are nonempty. -/
public theorem openEmbeddingStarData_fillingCollar_nonempty :
    ∀ i, Nonempty (A.openEmbeddingStarData.fillingCollar i) := fun i ↦ by
  exact ⟨A.openEmbeddingStarData.fillingCollarPoint i
    (A.openEmbeddingStarData_collarSource_nonempty i).some⟩

/-- The concrete four-piece gluing datum satisfies its central-collar nonemptiness premise. -/
public theorem fourPieceStarGluingData_nonemptyCentralCollar :
    ∀ i, Nonempty
      (A.openEmbeddingStarData.toFourPieceStarGluingData.centralCollar i) :=
  A.openEmbeddingStarData_centralCollar_nonempty

end PaperAnalyticData

/-- The three collar sources for supplied paper analytic data are nonempty. -/
public theorem paperStarCollarSourceType_nonempty (A : PaperAnalyticData) :
    ∀ i, Nonempty (A.starCollarSourceType i) :=
  A.starCollarSourceType_nonempty

/-- The central collars of a supplied paper open-embedding star are nonempty. -/
public theorem paperOpenEmbeddingStarData_centralCollar_nonempty (A : PaperAnalyticData) :
    ∀ i, Nonempty (A.openEmbeddingStarData.centralCollar i) :=
  A.openEmbeddingStarData_centralCollar_nonempty

/-- The filling collars of a supplied paper open-embedding star are nonempty. -/
public theorem paperOpenEmbeddingStarData_fillingCollar_nonempty (A : PaperAnalyticData) :
    ∀ i, Nonempty (A.openEmbeddingStarData.fillingCollar i) :=
  A.openEmbeddingStarData_fillingCollar_nonempty

/-- A supplied paper four-piece gluing datum has nonempty central collars. -/
public theorem paperFourPieceStarGluingData_nonemptyCentralCollar (A : PaperAnalyticData) :
    ∀ i, Nonempty
      (A.openEmbeddingStarData.toFourPieceStarGluingData.centralCollar i) :=
  A.fourPieceStarGluingData_nonemptyCentralCollar

end

end SphereSixComplex.Geometry
