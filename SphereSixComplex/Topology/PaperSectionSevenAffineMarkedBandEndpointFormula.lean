module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandHomotopyReduction

/-!
# Endpoints of the marked affine band contractions

This module unfolds the central-fibre end of the two remaining marked side contractions.  The
marked projection followed by the inverse radial equivalence is represented upstairs by the
literal fixed-product point whose disc coordinate is the elliptic centre and whose torus
coordinate is the marked real-period coordinate.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

namespace RadialEllipticActionData

variable {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] [AddCommGroup T]

/-- Inserting a point of the canonical central-fibre cover into the filling quotient gives the
literal orbit class of the corresponding fixed-product point at the disc centre. -/
public theorem centralInclusion_coverProjection_sourceHomeomorph_symm
    (D : RadialEllipticActionData m T) (x : T) :
    PaperEllipticFillingRadialRetraction.RadialEllipticActionData.centralInclusion D
        (centralFiberCoverProjection D ((centralFiberCoverSourceHomeomorph D).symm x)) =
      Quotient.mk _ (D.actionData.center, x) :=
  rfl

end RadialEllipticActionData

end SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

namespace SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

namespace EquivariantRadialProductIdentification

open SphereSixComplex.Geometry
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

variable {m : ℕ} [NeZero m] {X T : Type} [TopologicalSpace X] [TopologicalSpace T]
    [AddCommGroup T] {sourceAction : MulAction (FiniteCyclic m) X}
    {D : RadialEllipticActionData m T}

/-- On an orbit representative, the transported radial retraction forgets exactly the disc
coordinate and returns the canonical central-fibre cover class of the product-chart coordinate. -/
public theorem centralRetraction_quotientHomeomorph_mk
    (e : EquivariantRadialProductIdentification sourceAction D) (x : X) :
    D.centralRetraction (e.quotientHomeomorph (Quotient.mk _ x)) =
      RadialEllipticActionData.centralFiberCoverProjection D
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm
          (e.toHomeomorph x).2) := by
  apply Subtype.ext
  rw [e.quotientHomeomorph_mk]
  change D.quotientRetract (Quotient.mk _ (e.toHomeomorph x)) = _
  rw [D.quotientRetract_mk]
  apply congrArg (Quotient.mk _)
  apply Prod.ext
  · exact D.center_eq.symm
  · rfl

end EquivariantRadialProductIdentification

end SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels
open SphereSixComplex.Geometry.GlobalTorusFamily

variable {A : PaperAnalyticData}

/-- The order-three marked band point, inserted into the fixed-product filling quotient before
transport back to the actual varying filling. -/
public noncomputable def sectionSevenAffineOrderThreeMarkedFixedCentralPoint
    (A : PaperAnalyticData) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      (orderThreeRadialActionData A.periods).FillingQuotient) :=
  (orderThreeRadialActionData A.periods).centralInclusion.comp
    (sectionSevenAffineBandOrderThreeMarkedProjection A)

/-- The order-four analogue of `sectionSevenAffineOrderThreeMarkedFixedCentralPoint`. -/
public noncomputable def sectionSevenAffineOrderFourMarkedFixedCentralPoint
    (A : PaperAnalyticData) :
    C((A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
        A.sectionSevenActualAffineSplit.allocation.orderFourSide :
          Set A.SectionSevenEllipticInterior),
      (orderFourRadialActionData A.periods).FillingQuotient) :=
  (orderFourRadialActionData A.periods).centralInclusion.comp
    (sectionSevenAffineBandOrderFourMarkedProjection A)

/-- Pointwise, the order-three endpoint is the orbit class at the disc centre with the marked
band fibre coordinate. -/
public theorem sectionSevenAffineOrderThreeMarkedFixedCentralPoint_apply
    (A : PaperAnalyticData)
    (x : (A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
      A.sectionSevenActualAffineSplit.allocation.orderFourSide :
        Set A.SectionSevenEllipticInterior)) :
    sectionSevenAffineOrderThreeMarkedFixedCentralPoint A x =
      Quotient.mk _ ((orderThreeRadialActionData A.periods).actionData.center,
        sectionSevenAffineBandFiberCoordinate A x) := by
  exact RadialEllipticActionData.centralInclusion_coverProjection_sourceHomeomorph_symm
    (orderThreeRadialActionData A.periods) (sectionSevenAffineBandFiberCoordinate A x)

/-- Pointwise, the order-four endpoint is the orbit class at its disc centre with the marked
band coordinate transported to the order-four fixed torus. -/
public theorem sectionSevenAffineOrderFourMarkedFixedCentralPoint_apply
    (A : PaperAnalyticData)
    (x : (A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
      A.sectionSevenActualAffineSplit.allocation.orderFourSide :
        Set A.SectionSevenEllipticInterior)) :
    sectionSevenAffineOrderFourMarkedFixedCentralPoint A x =
      Quotient.mk _ ((orderFourRadialActionData A.periods).actionData.center,
        A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
          (sectionSevenAffineBandFiberCoordinate A x)) := by
  exact RadialEllipticActionData.centralInclusion_coverProjection_sourceHomeomorph_symm
    (orderFourRadialActionData A.periods)
      (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
        (sectionSevenAffineBandFiberCoordinate A x))

/-- Before transport through the open filling image, the inverse of the selected order-three
radial equivalence is exactly the inverse product-quotient homeomorphism applied to the explicit
fixed central point. -/
public theorem orderThreeSelectedFilling_invFun_markedProjection
    (A : PaperAnalyticData) :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).invFun.comp
        (sectionSevenAffineBandOrderThreeMarkedProjection A) =
      (⟨(orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification
          |>.quotientHomeomorph.symm,
        (orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification
          |>.quotientHomeomorph.symm.continuous⟩ :
        C((orderThreeRadialActionData A.periods).FillingQuotient,
          A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)).comp
        (sectionSevenAffineOrderThreeMarkedFixedCentralPoint A) := by
  rfl

/-- The analogous formula for the selected order-four filling equivalence. -/
public theorem orderFourSelectedFilling_invFun_markedProjection
    (A : PaperAnalyticData) :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).invFun.comp
        (sectionSevenAffineBandOrderFourMarkedProjection A) =
      (⟨(orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification
          |>.quotientHomeomorph.symm,
        (orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification
          |>.quotientHomeomorph.symm.continuous⟩ :
        C((orderFourRadialActionData A.periods).FillingQuotient,
          A.OrderFourVaryingFilling A.starSeparation.orderFour.radius)).comp
        (sectionSevenAffineOrderFourMarkedFixedCentralPoint A) := by
  rfl

/-- The explicit order-three affine radial equivalence between an affine disc region and the
whole order-three central half-plane region.  Unlike selecting a witness from the proposition
`discRegionInclusion_isHomotopyEquivalence`, its inverse retains the real-period formula. -/
public noncomputable def orderThreeAffineDiscCentralHomotopyEquiv
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 2 / 3) :
    ↥(A.sectionSevenAffineOrderThreeDiscRegion r) ≃ₕ
      ↥A.sectionSevenAffineOrderThreeCentralRegion :=
  (A.sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r).toHomotopyEquiv |>.trans
    ((A.orderThreeAffineRadialLiftEquiv (s := r / 2) (by linarith) (by linarith) hr)
      |>.quotientHomotopyEquiv
        (A.orderThreeAffineDiscLiftAction_continuous r)
        A.orderThreeAffineHalfPlaneLiftAction_continuous) |>.trans
    A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph.symm.toHomotopyEquiv

/-- The forward map of the explicit order-three equivalence is the literal region inclusion. -/
public theorem orderThreeAffineDiscCentralHomotopyEquiv_toFun
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 2 / 3) :
    (A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).toFun =
      regionInclusion (A.discRegion_subset_centralRegion hr) := by
  apply ContinuousMap.ext
  intro x
  apply A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph.injective
  change A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph
      (A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph.symm
        ((A.orderThreeAffineRadialLiftEquiv (s := r / 2)
          (by linarith) (by linarith) hr).quotientToFun
            (A.sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r x))) = _
  rw [A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph.apply_symm_apply]
  apply A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.injective
  rw [A.quotientToFun_eq_orderThreeAffineDiscLiftQuotientInclusion hr
    (A.orderThreeAffineRadialLiftEquiv (s := r / 2) (by linarith) (by linarith) hr) rfl,
    A.toCentralFamily_orderThreeAffineDiscLiftQuotientInclusion hr,
    A.toCentralFamily_sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r,
    A.toCentralFamily_sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph]
  rfl

/-- The explicit affine radial inverse deforms the identity of the whole order-three central
region to the inclusion of a smaller affine disc, without forgetting its period-coordinate
formula. -/
public theorem orderThreeAffineDiscCentral_inverse_deformation
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 2 / 3) :
    (ContinuousMap.id ↥A.sectionSevenAffineOrderThreeCentralRegion).Homotopic
      ((regionInclusion (A.discRegion_subset_centralRegion hr)).comp
        (A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).invFun) := by
  rw [← A.orderThreeAffineDiscCentralHomotopyEquiv_toFun hr0 hr]
  exact (A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).right_inv.symm

/-- A named explicit order-four affine radial equivalence. -/
public noncomputable def orderFourAffineRadialEquivChoice
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3) :=
  familyEquivOfBaseEquiv (A.orderFourAffineDiscLiftCarrier_subset_halfPlane hr)
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    (A.orderFourBaseRadialEquiv (half_pos hr0) (half_lt_self hr0) hr) (fun _ ↦ rfl)

public theorem orderFourAffineRadialEquivChoice_toFun
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3) :
    ((A.orderFourAffineRadialEquivChoice hr0 hr).toFun :
      (A.orderFourAffineDiscLiftCarrier r).carrier →
        A.orderFourAffineHalfPlaneLiftCarrier.carrier) =
      A.orderFourAffineDiscLiftInclusion hr :=
  rfl

/-- The selected order-four radial inverse is the flat transport used in the explicit
`familyEquivOfBaseEquiv` construction. -/
public theorem orderFourAffineRadialEquivChoice_invFun
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3)
    (y : A.orderFourAffineHalfPlaneLiftCarrier.carrier) :
    ((A.orderFourAffineRadialEquivChoice hr0 hr).invFun y).1 =
      A.regularFlatTransport
        (((A.orderFourBaseRadialEquiv (half_pos hr0) (half_lt_self hr0) hr).invFun
            (⟨regularTotalSpaceBase A.periods y.1, y.2⟩ :
              A.orderFourAffineHalfPlaneBaseLift)).1,
          y.1) :=
  rfl

/-- The explicit order-four affine radial equivalence between a disc region and the whole
order-four central half-plane region. -/
public noncomputable def orderFourAffineDiscCentralHomotopyEquiv
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3) :
    ↥(A.sectionSevenAffineOrderFourDiscRegion r) ≃ₕ
      ↥A.sectionSevenAffineOrderFourCentralRegion :=
  (A.sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph r).toHomotopyEquiv |>.trans
    ((A.orderFourAffineRadialEquivChoice hr0 hr).quotientHomotopyEquiv
      (A.orderFourAffineDiscLiftAction_continuous r)
      A.orderFourAffineHalfPlaneLiftAction_continuous) |>.trans
    A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph.symm.toHomotopyEquiv

/-- The forward map of the explicit order-four equivalence is the literal region inclusion. -/
public theorem orderFourAffineDiscCentralHomotopyEquiv_toFun
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3) :
    (A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).toFun =
      regionInclusion (A.orderFourDiscRegion_subset_centralRegion hr) := by
  apply ContinuousMap.ext
  intro u
  apply A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph.injective
  change A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph
      (A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph.symm
        ((A.orderFourAffineRadialEquivChoice hr0 hr).quotientToFun
          (A.sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph r u))) = _
  rw [A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph.apply_symm_apply]
  apply A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.injective
  have hmem : u.1 ∈ A.sectionSevenEllipticCentralImage :=
    A.mem_centralImage_of_mem_centralHeightLowerRegion
      (fun z ↦ ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖) r u.2
  have hheight : (1 : ℝ) / 3 <
      A.sectionSevenEllipticCentralHeight ⟨u.1, hmem⟩ := by
    obtain ⟨y, hy, hyu⟩ := A.orderFourDiscRegion_subset_centralRegion hr u.2
    have hxy : y = (⟨u.1, hmem⟩ : A.sectionSevenEllipticCentralImage) := Subtype.ext hyu
    exact hxy ▸ hy
  have hleft : (regionInclusion (A.orderFourDiscRegion_subset_centralRegion hr) u :
      ↥A.sectionSevenAffineOrderFourCentralRegion) =
      ⟨(⟨u.1, hmem⟩ : A.sectionSevenEllipticCentralImage).1,
        ⟨⟨u.1, hmem⟩, hheight, rfl⟩⟩ := rfl
  rw [hleft,
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_centralRegionQuotient
      ⟨u.1, hmem⟩ hheight,
    A.quotientToFun_eq_orderFourAffineDiscLiftQuotientInclusion hr
      (A.orderFourAffineRadialEquivChoice hr0 hr)
      (A.orderFourAffineRadialEquivChoice_toFun hr0 hr),
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_discInclusion hr,
    A.toCentralFamily_sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph r]

/-- The explicit order-four affine radial inverse deforms the identity central region to the
inclusion of a smaller affine disc. -/
public theorem orderFourAffineDiscCentral_inverse_deformation
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3) :
    (ContinuousMap.id ↥A.sectionSevenAffineOrderFourCentralRegion).Homotopic
      ((regionInclusion (A.orderFourDiscRegion_subset_centralRegion hr)).comp
        (A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).invFun) := by
  rw [← A.orderFourAffineDiscCentralHomotopyEquiv_toFun hr0 hr]
  exact (A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).right_inv.symm

/-- The common affine band. -/
public abbrev SectionSevenAffineMarkedBand (A : PaperAnalyticData) :=
  (A.sectionSevenActualAffineSplit.allocation.orderThreeSide ∩
    A.sectionSevenActualAffineSplit.allocation.orderFourSide :
      Set A.SectionSevenEllipticInterior)

/-- Reading an order-three central overlap point in the actual filling chart returns its exact
star-collar filling representative. -/
public theorem sectionSevenOrderThreeFillingImageToPiece_symm_overlap
    (A : PaperAnalyticData)
    (u : ↥(A.sectionSevenOrderThreeFillingImage ∩
      A.sectionSevenAffineOrderThreeCentralRegion)) :
    A.sectionSevenOrderThreePieceHomeomorph.symm
        (A.sectionSevenOrderThreeFillingImageToPiece ⟨u.1, u.2.1⟩) =
      A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u) := by
  have hu : u.1 ∈ A.sectionSevenOrderThreeFillingImage := u.2.1
  let v : A.sectionSevenOrderThreeFillingImage := ⟨u.1, hu⟩
  change A.sectionSevenOrderThreePieceHomeomorph.symm
      (A.sectionSevenOrderThreeFillingImageToPiece v) = _
  apply A.sectionSevenOrderThreePieceHomeomorph.injective
  rw [A.sectionSevenOrderThreePieceHomeomorph.apply_symm_apply]
  apply Subtype.ext
  let S := A.openEmbeddingStarData
  let q : S.collarSource 1 := A.orderThreeOverlapCollarHomeomorph u
  let y : A.sectionSevenEllipticCentralImage :=
    ⟨u.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
      A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) u.2.2⟩
  have hstar : A.starToCentral 1 q =
      A.sectionSevenEllipticCentralImageHomeomorph y :=
    A.starToCentral_orderThreeOverlapCollarHomeomorph u
  have hglued : u.1.1 = S.collarSourceToGlued 1 q := by
    calc
      u.1.1 =
          (S.centralToSectionSevenEulerPieceHomeomorph
            (A.sectionSevenEllipticCentralImageHomeomorph y)).1 :=
        (A.centralToSectionSevenEulerPiece_centralImage y).symm
      _ = (S.centralToSectionSevenEulerPieceHomeomorph
            (A.starToCentral 1 q)).1 := by rw [hstar]
      _ = _ := A.centralToSectionSevenEulerPiece_starToCentral 1 q
  have hrelation :
      S.collarSourceToGlued 1 q =
        S.toFourPieceStarGluingData.glueData.toGlueData.ι
          (some (1 : Fin 3)) (S.toFilling 1 q) := by
    change S.toFourPieceStarGluingData.glueData.toGlueData.ι none (S.toCentral 1 q) =
      S.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some (1 : Fin 3)) (S.toFilling 1 q)
    symm
    apply (S.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
      (some (1 : Fin 3)) none (S.toFilling 1 q) (S.toCentral 1 q)).mpr
    exact ⟨S.fillingCollarPoint 1 q, rfl, by
      change ((S.collarEquiv 1).symm (S.fillingCollarPoint 1 q)).1 = S.toCentral 1 q
      rw [S.collarEquiv_symm_toFilling]
      rfl⟩
  have hcoe := Topology.IsEmbedding.toHomeomorph_apply_coe
    (S.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding
      (some (1 : Fin 3))).isEmbedding (S.toFilling 1 q)
  calc
    (A.sectionSevenOrderThreeFillingImageToPiece v).1 = u.1.1 := rfl
    _ = S.collarSourceToGlued 1 q := hglued
    _ = _ := hrelation
    _ = (A.sectionSevenOrderThreePieceHomeomorph (S.toFilling 1 q)).1 := hcoe.symm

/-- The corresponding exact order-four filling representative. -/
public theorem sectionSevenOrderFourFillingImageToPiece_symm_overlap
    (A : PaperAnalyticData)
    (u : ↥(A.sectionSevenOrderFourFillingImage ∩
      A.sectionSevenAffineOrderFourCentralRegion)) :
    A.sectionSevenOrderFourPieceHomeomorph.symm
        (A.sectionSevenOrderFourFillingImageToPiece ⟨u.1, u.2.1⟩) =
      A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u) := by
  have hu : u.1 ∈ A.sectionSevenOrderFourFillingImage := u.2.1
  let v : A.sectionSevenOrderFourFillingImage := ⟨u.1, hu⟩
  change A.sectionSevenOrderFourPieceHomeomorph.symm
      (A.sectionSevenOrderFourFillingImageToPiece v) = _
  apply A.sectionSevenOrderFourPieceHomeomorph.injective
  rw [A.sectionSevenOrderFourPieceHomeomorph.apply_symm_apply]
  apply Subtype.ext
  let S := A.openEmbeddingStarData
  let q : S.collarSource 2 := A.orderFourOverlapCollarHomeomorph u
  let y : A.sectionSevenEllipticCentralImage :=
    ⟨u.1, A.mem_centralImage_of_mem_centralHeightUpperRegion
      A.sectionSevenEllipticCentralHeight (1 / 3 : ℝ) u.2.2⟩
  have hstar : A.starToCentral 2 q =
      A.sectionSevenEllipticCentralImageHomeomorph y :=
    A.starToCentral_orderFourOverlapCollarHomeomorph u
  have hglued : u.1.1 = S.collarSourceToGlued 2 q := by
    calc
      u.1.1 =
          (S.centralToSectionSevenEulerPieceHomeomorph
            (A.sectionSevenEllipticCentralImageHomeomorph y)).1 :=
        (A.centralToSectionSevenEulerPiece_centralImage y).symm
      _ = (S.centralToSectionSevenEulerPieceHomeomorph
            (A.starToCentral 2 q)).1 := by rw [hstar]
      _ = _ := A.centralToSectionSevenEulerPiece_starToCentral 2 q
  have hrelation :
      S.collarSourceToGlued 2 q =
        S.toFourPieceStarGluingData.glueData.toGlueData.ι
          (some (2 : Fin 3)) (S.toFilling 2 q) := by
    change S.toFourPieceStarGluingData.glueData.toGlueData.ι none (S.toCentral 2 q) =
      S.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some (2 : Fin 3)) (S.toFilling 2 q)
    symm
    apply (S.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
      (some (2 : Fin 3)) none (S.toFilling 2 q) (S.toCentral 2 q)).mpr
    exact ⟨S.fillingCollarPoint 2 q, rfl, by
      change ((S.collarEquiv 2).symm (S.fillingCollarPoint 2 q)).1 = S.toCentral 2 q
      rw [S.collarEquiv_symm_toFilling]
      rfl⟩
  have hcoe := Topology.IsEmbedding.toHomeomorph_apply_coe
    (S.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding
      (some (2 : Fin 3))).isEmbedding (S.toFilling 2 q)
  calc
    (A.sectionSevenOrderFourFillingImageToPiece v).1 = u.1.1 := rfl
    _ = S.collarSourceToGlued 2 q := hglued
    _ = _ := hrelation
    _ = (A.sectionSevenOrderFourPieceHomeomorph (S.toFilling 2 q)).1 := hcoe.symm

/-- The common band included in the order-three affine central region. -/
public def sectionSevenAffineBandToOrderThreeCentralRegion (A : PaperAnalyticData) :
    C(A.SectionSevenAffineMarkedBand, ↥A.sectionSevenAffineOrderThreeCentralRegion) where
  toFun x := ⟨x.1, by
    change x.1 ∈ centralHeightLowerRegion A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ)
    obtain ⟨y, hy, hxy⟩ :=
      (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x).2
    exact ⟨y, hy.2, hxy⟩⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The common band included in the order-four affine central region. -/
public def sectionSevenAffineBandToOrderFourCentralRegion (A : PaperAnalyticData) :
    C(A.SectionSevenAffineMarkedBand, ↥A.sectionSevenAffineOrderFourCentralRegion) where
  toFun x := ⟨x.1, by
    change x.1 ∈ centralHeightUpperRegion A.sectionSevenEllipticCentralHeight (1 / 3 : ℝ)
    obtain ⟨y, hy, hxy⟩ :=
      (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x).2
    exact ⟨y, hy.1, hxy⟩⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- A fixed small affine disc contained in the actual order-three star overlap. -/
public noncomputable def sectionSevenAffineOrderThreeMarkedDiscRadius (A : PaperAnalyticData) : ℝ :=
  A.exists_discRegion_subset_orderThreeOverlap.choose

public theorem sectionSevenAffineOrderThreeMarkedDiscRadius_spec (A : PaperAnalyticData) :
    0 < A.sectionSevenAffineOrderThreeMarkedDiscRadius ∧
      A.sectionSevenAffineOrderThreeMarkedDiscRadius ≤ 1 / 3 ∧
      A.sectionSevenAffineOrderThreeDiscRegion
          A.sectionSevenAffineOrderThreeMarkedDiscRadius ⊆
        A.sectionSevenOrderThreeFillingImage ∩
          A.sectionSevenAffineOrderThreeCentralRegion :=
  A.exists_discRegion_subset_orderThreeOverlap.choose_spec

/-- A fixed small affine disc contained in the actual order-four star overlap. -/
public noncomputable def sectionSevenAffineOrderFourMarkedDiscRadius (A : PaperAnalyticData) : ℝ :=
  A.exists_discRegion_subset_orderFourOverlap.choose

public theorem sectionSevenAffineOrderFourMarkedDiscRadius_spec (A : PaperAnalyticData) :
    0 < A.sectionSevenAffineOrderFourMarkedDiscRadius ∧
      A.sectionSevenAffineOrderFourMarkedDiscRadius ≤ 1 / 3 ∧
      A.sectionSevenAffineOrderFourDiscRegion
          A.sectionSevenAffineOrderFourMarkedDiscRadius ⊆
        A.sectionSevenOrderFourFillingImage ∩
          A.sectionSevenAffineOrderFourCentralRegion :=
  A.exists_discRegion_subset_orderFourOverlap.choose_spec

/-- The explicit order-three affine radial inverse, restricted to the common band and then read
as a point of the actual filling image through the proved small-disc inclusion. -/
public noncomputable def sectionSevenAffineOrderThreeDiscFillingEndpoint
    (A : PaperAnalyticData) :
    C(A.SectionSevenAffineMarkedBand, ↥A.sectionSevenOrderThreeFillingImage) :=
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr0 := (A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec).1
  let hr : r ≤ 2 / 3 :=
    (A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec).2.1.trans (by norm_num)
  let hsub := (A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec).2.2
  (⟨fun z : ↥(A.sectionSevenAffineOrderThreeDiscRegion r) ↦
      ⟨z.1, (hsub z.2).1⟩, continuous_subtype_val.subtype_mk _⟩ :
    C(↥(A.sectionSevenAffineOrderThreeDiscRegion r),
      ↥A.sectionSevenOrderThreeFillingImage)).comp
    ((A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
      (A.sectionSevenAffineBandToOrderThreeCentralRegion))

/-- The analogous explicit order-four disc endpoint in the actual filling image. -/
public noncomputable def sectionSevenAffineOrderFourDiscFillingEndpoint
    (A : PaperAnalyticData) :
    C(A.SectionSevenAffineMarkedBand, ↥A.sectionSevenOrderFourFillingImage) :=
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr0 := (A.sectionSevenAffineOrderFourMarkedDiscRadius_spec).1
  let hr : r ≤ 1 - 1 / 3 :=
    (A.sectionSevenAffineOrderFourMarkedDiscRadius_spec).2.1.trans (by norm_num)
  let hsub := (A.sectionSevenAffineOrderFourMarkedDiscRadius_spec).2.2
  (⟨fun z : ↥(A.sectionSevenAffineOrderFourDiscRegion r) ↦
      ⟨z.1, (hsub z.2).1⟩, continuous_subtype_val.subtype_mk _⟩ :
    C(↥(A.sectionSevenAffineOrderFourDiscRegion r),
      ↥A.sectionSevenOrderFourFillingImage)).comp
    ((A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
      (A.sectionSevenAffineBandToOrderFourCentralRegion))

/-- The order-three disc endpoint retaining membership in both the filling and central regions. -/
public noncomputable def sectionSevenAffineOrderThreeDiscOverlapEndpoint
    (A : PaperAnalyticData) :
    C(A.SectionSevenAffineMarkedBand,
      ↥(A.sectionSevenOrderThreeFillingImage ∩
        A.sectionSevenAffineOrderThreeCentralRegion)) :=
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr0 := (A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec).1
  let hr : r ≤ 2 / 3 :=
    (A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec).2.1.trans (by norm_num)
  let hsub := (A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec).2.2
  (⟨fun z : ↥(A.sectionSevenAffineOrderThreeDiscRegion r) ↦
      ⟨z.1, hsub z.2⟩, continuous_subtype_val.subtype_mk _⟩ :
    C(↥(A.sectionSevenAffineOrderThreeDiscRegion r),
      ↥(A.sectionSevenOrderThreeFillingImage ∩
        A.sectionSevenAffineOrderThreeCentralRegion))).comp
    ((A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
      A.sectionSevenAffineBandToOrderThreeCentralRegion)

/-- The order-four endpoint retaining both overlap memberships. -/
public noncomputable def sectionSevenAffineOrderFourDiscOverlapEndpoint
    (A : PaperAnalyticData) :
    C(A.SectionSevenAffineMarkedBand,
      ↥(A.sectionSevenOrderFourFillingImage ∩
        A.sectionSevenAffineOrderFourCentralRegion)) :=
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr0 := (A.sectionSevenAffineOrderFourMarkedDiscRadius_spec).1
  let hr : r ≤ 1 - 1 / 3 :=
    (A.sectionSevenAffineOrderFourMarkedDiscRadius_spec).2.1.trans (by norm_num)
  let hsub := (A.sectionSevenAffineOrderFourMarkedDiscRadius_spec).2.2
  (⟨fun z : ↥(A.sectionSevenAffineOrderFourDiscRegion r) ↦
      ⟨z.1, hsub z.2⟩, continuous_subtype_val.subtype_mk _⟩ :
    C(↥(A.sectionSevenAffineOrderFourDiscRegion r),
      ↥(A.sectionSevenOrderFourFillingImage ∩
        A.sectionSevenAffineOrderFourCentralRegion))).comp
    ((A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
      A.sectionSevenAffineBandToOrderFourCentralRegion)

public theorem sectionSevenAffineOrderThreeDiscOverlapEndpoint_toFilling
    (A : PaperAnalyticData) :
    (IntegralMayerVietoris.interToLeft A.sectionSevenOrderThreeFillingImage
      A.sectionSevenAffineOrderThreeCentralRegion).comp
        A.sectionSevenAffineOrderThreeDiscOverlapEndpoint =
      A.sectionSevenAffineOrderThreeDiscFillingEndpoint := by
  rfl

public theorem sectionSevenAffineOrderFourDiscOverlapEndpoint_toFilling
    (A : PaperAnalyticData) :
    (IntegralMayerVietoris.interToLeft A.sectionSevenOrderFourFillingImage
      A.sectionSevenAffineOrderFourCentralRegion).comp
        A.sectionSevenAffineOrderFourDiscOverlapEndpoint =
      A.sectionSevenAffineOrderFourDiscFillingEndpoint := by
  rfl

/-- The explicit endpoint read in the selected order-three varying filling, with all gluing
homeomorphisms removed. -/
public noncomputable def sectionSevenAffineOrderThreeStarEndpoint (A : PaperAnalyticData) :
    C(A.SectionSevenAffineMarkedBand,
      A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) :=
  (⟨fun u ↦ A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u),
    (A.starToFilling_isOpenEmbedding 1).continuous.comp
      A.orderThreeOverlapCollarHomeomorph.continuous⟩ :
    C(↥(A.sectionSevenOrderThreeFillingImage ∩
      A.sectionSevenAffineOrderThreeCentralRegion),
      A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)).comp
    A.sectionSevenAffineOrderThreeDiscOverlapEndpoint

/-- The corresponding order-four selected-filling endpoint. -/
public noncomputable def sectionSevenAffineOrderFourStarEndpoint (A : PaperAnalyticData) :
    C(A.SectionSevenAffineMarkedBand,
      A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) :=
  (⟨fun u ↦ A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u),
    (A.starToFilling_isOpenEmbedding 2).continuous.comp
      A.orderFourOverlapCollarHomeomorph.continuous⟩ :
    C(↥(A.sectionSevenOrderFourFillingImage ∩
      A.sectionSevenAffineOrderFourCentralRegion),
      A.OrderFourVaryingFilling A.starSeparation.orderFour.radius)).comp
    A.sectionSevenAffineOrderFourDiscOverlapEndpoint

/-- The remaining coordinate calculation with the ambient glued-space homeomorphisms removed. -/
public structure SectionSevenAffineMarkedStarEndpointCompatibility (A : PaperAnalyticData) where
  orderThree :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderThreeStarEndpoint =
      sectionSevenAffineBandOrderThreeMarkedProjection A
  orderFour :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderFourStarEndpoint =
      sectionSevenAffineBandOrderFourMarkedProjection A

/-- The exact remaining coordinate calculation after the band-wide affine radial inverse has
been constructed: the filling radial retraction of each explicit disc endpoint must be the
marked central-fibre projection. -/
public structure SectionSevenAffineMarkedDiscEndpointCompatibility (A : PaperAnalyticData) where
  orderThree :
    (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
      (A.sectionSevenAffineOrderThreeDiscFillingEndpoint)) =
        sectionSevenAffineBandOrderThreeMarkedProjection A
  orderFour :
    (A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
      (A.sectionSevenAffineOrderFourDiscFillingEndpoint)) =
        sectionSevenAffineBandOrderFourMarkedProjection A

/-- The star-coordinate equalities imply the filling-image endpoint equalities. -/
public theorem SectionSevenAffineMarkedStarEndpointCompatibility.toDiscEndpointCompatibility
    {A : PaperAnalyticData} (H : A.SectionSevenAffineMarkedStarEndpointCompatibility) :
    A.SectionSevenAffineMarkedDiscEndpointCompatibility where
  orderThree := by
    apply ContinuousMap.ext
    intro x
    let u := A.sectionSevenAffineOrderThreeDiscOverlapEndpoint x
    have hfill : A.sectionSevenAffineOrderThreeDiscFillingEndpoint x =
        ⟨u.1, u.2.1⟩ := rfl
    change (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
        (A.sectionSevenOrderThreePieceHomeomorph.symm
          (A.sectionSevenOrderThreeFillingImageToPiece
            (A.sectionSevenAffineOrderThreeDiscFillingEndpoint x))) = _
    rw [hfill]
    have hpiece :
        (A.sectionSevenOrderThreePieceHomeomorph.symm
          (A.sectionSevenOrderThreeFillingImageToPiece ⟨u.1, u.2.1⟩) :
            A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) =
          A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u) :=
      A.sectionSevenOrderThreeFillingImageToPiece_symm_overlap u
    rw [hpiece]
    exact congrArg
      (fun f : C(A.SectionSevenAffineMarkedBand,
        OrderThreeReducedCentralFiber A.periods) ↦ f x) H.orderThree
  orderFour := by
    apply ContinuousMap.ext
    intro x
    let u := A.sectionSevenAffineOrderFourDiscOverlapEndpoint x
    have hfill : A.sectionSevenAffineOrderFourDiscFillingEndpoint x =
        ⟨u.1, u.2.1⟩ := rfl
    change (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
        (A.sectionSevenOrderFourPieceHomeomorph.symm
          (A.sectionSevenOrderFourFillingImageToPiece
            (A.sectionSevenAffineOrderFourDiscFillingEndpoint x))) = _
    rw [hfill]
    have hpiece :
        (A.sectionSevenOrderFourPieceHomeomorph.symm
          (A.sectionSevenOrderFourFillingImageToPiece ⟨u.1, u.2.1⟩) :
            A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) =
          A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u) :=
      A.sectionSevenOrderFourFillingImageToPiece_symm_overlap u
    rw [hpiece]
    exact congrArg
      (fun f : C(A.SectionSevenAffineMarkedBand,
        OrderFourReducedCentralFiber A.periods) ↦ f x) H.orderFour

/-- Include the order-three central region in its affine side. -/
public def sectionSevenAffineOrderThreeCentralRegionToSide (A : PaperAnalyticData) :
    C(↥A.sectionSevenAffineOrderThreeCentralRegion,
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide) where
  toFun x := ⟨x.1, Or.inr x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Include the order-four central region in its affine side. -/
public def sectionSevenAffineOrderFourCentralRegionToSide (A : PaperAnalyticData) :
    C(↥A.sectionSevenAffineOrderFourCentralRegion,
      A.sectionSevenActualAffineSplit.allocation.orderFourSide) where
  toFun x := ⟨x.1, Or.inr x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Include the order-three filling image in its affine side. -/
public def sectionSevenAffineOrderThreeFillingImageToSide (A : PaperAnalyticData) :
    C(↥A.sectionSevenOrderThreeFillingImage,
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide) where
  toFun x := ⟨x.1, Or.inl x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Include the order-four filling image in its affine side. -/
public def sectionSevenAffineOrderFourFillingImageToSide (A : PaperAnalyticData) :
    C(↥A.sectionSevenOrderFourFillingImage,
      A.sectionSevenActualAffineSplit.allocation.orderFourSide) where
  toFun x := ⟨x.1, Or.inl x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The explicit affine radial inverse deforms the common-band inclusion to the selected small
disc endpoint, viewed in the order-three filling image. -/
public theorem orderThreeBandInclusion_homotopic_discFillingEndpoint
    (A : PaperAnalyticData) :
    (IntegralMayerVietoris.interToLeft
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide).Homotopic
    ((A.sectionSevenAffineOrderThreeFillingImageToSide).comp
      (A.sectionSevenAffineOrderThreeDiscFillingEndpoint)) := by
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr0 := (A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec).1
  let hr : r ≤ 2 / 3 :=
    (A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec).2.1.trans (by norm_num)
  have h := ContinuousMap.Homotopic.comp
    (.refl A.sectionSevenAffineOrderThreeCentralRegionToSide)
    (ContinuousMap.Homotopic.comp
      (A.orderThreeAffineDiscCentral_inverse_deformation hr0 hr)
      (.refl A.sectionSevenAffineBandToOrderThreeCentralRegion))
  have hleft :
      A.sectionSevenAffineOrderThreeCentralRegionToSide.comp
          A.sectionSevenAffineBandToOrderThreeCentralRegion =
        IntegralMayerVietoris.interToLeft
          A.sectionSevenActualAffineSplit.allocation.orderThreeSide
          A.sectionSevenActualAffineSplit.allocation.orderFourSide := by
    ext x
    rfl
  have hright :
      A.sectionSevenAffineOrderThreeCentralRegionToSide.comp
          ((regionInclusion (A.discRegion_subset_centralRegion hr)).comp
            ((A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
              A.sectionSevenAffineBandToOrderThreeCentralRegion)) =
        A.sectionSevenAffineOrderThreeFillingImageToSide.comp
          A.sectionSevenAffineOrderThreeDiscFillingEndpoint := by
    ext x
    rfl
  simp only [ContinuousMap.id_comp, ContinuousMap.comp_assoc] at h
  rw [hleft, hright] at h
  exact h

/-- The order-four affine radial inverse gives the analogous deformation into its small disc
endpoint in the filling image. -/
public theorem orderFourBandInclusion_homotopic_discFillingEndpoint
    (A : PaperAnalyticData) :
    (IntegralMayerVietoris.interToRight
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide).Homotopic
    ((A.sectionSevenAffineOrderFourFillingImageToSide).comp
      (A.sectionSevenAffineOrderFourDiscFillingEndpoint)) := by
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr0 := (A.sectionSevenAffineOrderFourMarkedDiscRadius_spec).1
  let hr : r ≤ 1 - 1 / 3 :=
    (A.sectionSevenAffineOrderFourMarkedDiscRadius_spec).2.1.trans (by norm_num)
  have h := ContinuousMap.Homotopic.comp
    (.refl A.sectionSevenAffineOrderFourCentralRegionToSide)
    (ContinuousMap.Homotopic.comp
      (A.orderFourAffineDiscCentral_inverse_deformation hr0 hr)
      (.refl A.sectionSevenAffineBandToOrderFourCentralRegion))
  have hleft :
      A.sectionSevenAffineOrderFourCentralRegionToSide.comp
          A.sectionSevenAffineBandToOrderFourCentralRegion =
        IntegralMayerVietoris.interToRight
          A.sectionSevenActualAffineSplit.allocation.orderThreeSide
          A.sectionSevenActualAffineSplit.allocation.orderFourSide := by
    ext x
    rfl
  have hright :
      A.sectionSevenAffineOrderFourCentralRegionToSide.comp
          ((regionInclusion (A.orderFourDiscRegion_subset_centralRegion hr)).comp
            ((A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
              A.sectionSevenAffineBandToOrderFourCentralRegion)) =
        A.sectionSevenAffineOrderFourFillingImageToSide.comp
          A.sectionSevenAffineOrderFourDiscFillingEndpoint := by
    ext x
    rfl
  simp only [ContinuousMap.id_comp, ContinuousMap.comp_assoc] at h
  rw [hleft, hright] at h
  exact h

private theorem orderThreeSideInverse_markedProjection_formula
    (A : PaperAnalyticData) :
    (sectionSevenAffineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp
        (sectionSevenAffineBandOrderThreeMarkedProjection A) =
      (orderThreeOverlapIsHomotopyEquivalence_inclusion
          A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
        ((nestedSubtypeHomeomorph
          A.sectionSevenActualAffineSplit.allocation.orderThreeSide
          A.sectionSevenOrderThreeFillingImage
          A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv
          |>.invFun.comp
            (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.invFun.comp
              (sectionSevenAffineBandOrderThreeMarkedProjection A))) := by
  rfl

private theorem orderFourSideInverse_markedProjection_formula
    (A : PaperAnalyticData) :
    (sectionSevenAffineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp
        (sectionSevenAffineBandOrderFourMarkedProjection A) =
      (orderFourOverlapIsHomotopyEquivalence_inclusion
          A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
        ((nestedSubtypeHomeomorph
          A.sectionSevenActualAffineSplit.allocation.orderFourSide
          A.sectionSevenOrderFourFillingImage
          A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side).toHomotopyEquiv
          |>.invFun.comp
            (A.sectionSevenOrderFourFillingImageHomotopyEquiv.invFun.comp
              (sectionSevenAffineBandOrderFourMarkedProjection A))) := by
  rfl

/-- The two explicit fixed-coordinate endpoint calculations are the only remaining input needed
after the affine radial deformations: filling homotopy-inverse cancellation supplies the desired
side contractions. -/
public theorem SectionSevenAffineMarkedDiscEndpointCompatibility.toSideContractions
    {A : PaperAnalyticData} (H : A.SectionSevenAffineMarkedDiscEndpointCompatibility) :
    A.SectionSevenAffineMarkedBandSideContractions := by
  refine { orderThree := ?_, orderFour := ?_ }
  · let q := A.sectionSevenAffineOrderThreeDiscFillingEndpoint
    let g := A.sectionSevenOrderThreeFillingImageHomotopyEquiv
    let p := sectionSevenAffineBandOrderThreeMarkedProjection A
    have hfill := ContinuousMap.Homotopic.comp g.left_inv (.refl q)
    have hcomp : g.toFun.comp q = p := H.orderThree
    simp only [ContinuousMap.comp_assoc, hcomp] at hfill
    have hside := ContinuousMap.Homotopic.comp
      (.refl A.sectionSevenAffineOrderThreeFillingImageToSide) hfill.symm
    have hendpoint :
        A.sectionSevenAffineOrderThreeFillingImageToSide.comp (g.invFun.comp p) =
          (sectionSevenAffineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp p := by
      dsimp [g, p]
      have hraw :
          A.sectionSevenAffineOrderThreeFillingImageToSide.comp
              (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.invFun.comp
                (sectionSevenAffineBandOrderThreeMarkedProjection A)) =
            (orderThreeOverlapIsHomotopyEquivalence_inclusion
                A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
              ((nestedSubtypeHomeomorph
                A.sectionSevenActualAffineSplit.allocation.orderThreeSide
                A.sectionSevenOrderThreeFillingImage
                A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side)
                |>.toHomotopyEquiv.invFun.comp
                  (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.invFun.comp
                    (sectionSevenAffineBandOrderThreeMarkedProjection A))) := by
        rw [(orderThreeOverlapIsHomotopyEquivalence_inclusion
          A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv_invFun]
        ext x
        rfl
      exact hraw.trans (orderThreeSideInverse_markedProjection_formula A).symm
    simp only [ContinuousMap.id_comp] at hside
    rw [hendpoint] at hside
    exact (A.orderThreeBandInclusion_homotopic_discFillingEndpoint).trans hside
  · let q := A.sectionSevenAffineOrderFourDiscFillingEndpoint
    let g := A.sectionSevenOrderFourFillingImageHomotopyEquiv
    let p := sectionSevenAffineBandOrderFourMarkedProjection A
    have hfill := ContinuousMap.Homotopic.comp g.left_inv (.refl q)
    have hcomp : g.toFun.comp q = p := H.orderFour
    simp only [ContinuousMap.comp_assoc, hcomp] at hfill
    have hside := ContinuousMap.Homotopic.comp
      (.refl A.sectionSevenAffineOrderFourFillingImageToSide) hfill.symm
    have hendpoint :
        A.sectionSevenAffineOrderFourFillingImageToSide.comp (g.invFun.comp p) =
          (sectionSevenAffineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp p := by
      dsimp [g, p]
      have hraw :
          A.sectionSevenAffineOrderFourFillingImageToSide.comp
              (A.sectionSevenOrderFourFillingImageHomotopyEquiv.invFun.comp
                (sectionSevenAffineBandOrderFourMarkedProjection A)) =
            (orderFourOverlapIsHomotopyEquivalence_inclusion
                A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
              ((nestedSubtypeHomeomorph
                A.sectionSevenActualAffineSplit.allocation.orderFourSide
                A.sectionSevenOrderFourFillingImage
                A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side)
                |>.toHomotopyEquiv.invFun.comp
                  (A.sectionSevenOrderFourFillingImageHomotopyEquiv.invFun.comp
                    (sectionSevenAffineBandOrderFourMarkedProjection A))) := by
        rw [(orderFourOverlapIsHomotopyEquivalence_inclusion
          A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv_invFun]
        ext x
        rfl
      exact hraw.trans (orderFourSideInverse_markedProjection_formula A).symm
    simp only [ContinuousMap.id_comp] at hside
    rw [hendpoint] at hside
    exact (A.orderFourBandInclusion_homotopic_discFillingEndpoint).trans hside

/-- Thus the exact two fixed-coordinate endpoint equalities imply the original residual
marked-band package. -/
public theorem markedBandHomotopies_of_discEndpointCompatibility
    (A : PaperAnalyticData) (H : A.SectionSevenAffineMarkedDiscEndpointCompatibility) :
    A.SectionSevenAffineOverlapBandCompatibility :=
  markedBandHomotopies_of_sideContractions A H.toSideContractions

/-- The order-three inverse endpoint in the actual affine side is obtained by transporting the
explicit fixed central point back through the selected varying-filling and open-image
homeomorphisms. -/
public theorem sectionSevenAffineOrderThreeSideInverse_markedProjection
    (A : PaperAnalyticData) :
    (sectionSevenAffineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp
        (sectionSevenAffineBandOrderThreeMarkedProjection A) =
      (orderThreeOverlapIsHomotopyEquivalence_inclusion
          A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
        ((nestedSubtypeHomeomorph
          A.sectionSevenActualAffineSplit.allocation.orderThreeSide
          A.sectionSevenOrderThreeFillingImage
          A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv
          |>.invFun.comp
            (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.invFun.comp
              (sectionSevenAffineBandOrderThreeMarkedProjection A))) := by
  rfl

/-- The corresponding unfolded order-four endpoint. -/
public theorem sectionSevenAffineOrderFourSideInverse_markedProjection
    (A : PaperAnalyticData) :
    (sectionSevenAffineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp
        (sectionSevenAffineBandOrderFourMarkedProjection A) =
      (orderFourOverlapIsHomotopyEquivalence_inclusion
          A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
        ((nestedSubtypeHomeomorph
          A.sectionSevenActualAffineSplit.allocation.orderFourSide
          A.sectionSevenOrderFourFillingImage
          A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side).toHomotopyEquiv
          |>.invFun.comp
            (A.sectionSevenOrderFourFillingImageHomotopyEquiv.invFun.comp
              (sectionSevenAffineBandOrderFourMarkedProjection A))) := by
  rfl

/-- Fully point-set form of the remaining geometry.  The two functions must glue the affine
central-family transport to the cyclic filling contraction continuously across the star collar.
The endpoint equalities are literal equalities of points in the corresponding affine side. -/
public structure SectionSevenAffineMarkedBandGluedHomotopies (A : PaperAnalyticData) where
  orderThreeToFun : unitInterval × A.SectionSevenAffineMarkedBand →
    A.sectionSevenActualAffineSplit.allocation.orderThreeSide
  orderThree_continuous : Continuous orderThreeToFun
  orderThree_zero : ∀ x,
    orderThreeToFun (0, x) =
      IntegralMayerVietoris.interToLeft
        A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenActualAffineSplit.allocation.orderFourSide x
  orderThree_one : ∀ x,
    orderThreeToFun (1, x) =
      (sectionSevenAffineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun
        (sectionSevenAffineBandOrderThreeMarkedProjection A x)
  orderFourToFun : unitInterval × A.SectionSevenAffineMarkedBand →
    A.sectionSevenActualAffineSplit.allocation.orderFourSide
  orderFour_continuous : Continuous orderFourToFun
  orderFour_zero : ∀ x,
    orderFourToFun (0, x) =
      IntegralMayerVietoris.interToRight
        A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenActualAffineSplit.allocation.orderFourSide x
  orderFour_one : ∀ x,
    orderFourToFun (1, x) =
      (sectionSevenAffineOrderFourSideToReducedFiberHomotopyEquiv A).invFun
        (sectionSevenAffineBandOrderFourMarkedProjection A x)

/-- The explicit glued functions and their point-set endpoint formulas supply the exact
side-contraction package of the preceding reduction. -/
public theorem SectionSevenAffineMarkedBandGluedHomotopies.toSideContractions
    {A : PaperAnalyticData} (H : A.SectionSevenAffineMarkedBandGluedHomotopies) :
    A.SectionSevenAffineMarkedBandSideContractions where
  orderThree := ⟨{
    toFun := H.orderThreeToFun
    continuous_toFun := H.orderThree_continuous
    map_zero_left := H.orderThree_zero
    map_one_left := H.orderThree_one }⟩
  orderFour := ⟨{
    toFun := H.orderFourToFun
    continuous_toFun := H.orderFour_continuous
    map_zero_left := H.orderFour_zero
    map_one_left := H.orderFour_one }⟩

/-- Consequently the fully point-set glued homotopies prove the original residual marked-band
assertion. -/
public theorem markedBandHomotopies_of_gluedHomotopies
    (A : PaperAnalyticData) (H : A.SectionSevenAffineMarkedBandGluedHomotopies) :
    A.SectionSevenAffineOverlapBandCompatibility :=
  markedBandHomotopies_of_sideContractions A H.toSideContractions

end SphereSixComplex.Geometry.PaperAnalyticData

end
