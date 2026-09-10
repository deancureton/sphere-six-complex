module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenSmallMarkedDiscWitness
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandHomotopyReduction

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
public noncomputable def affineOrderThreeMarkedFixedCentralPoint
    (A : PaperAnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      (orderThreeRadialActionData A.periods).FillingQuotient) :=
  (orderThreeRadialActionData A.periods).centralInclusion.comp
    (affineBandOrderThreeMarkedProjection A)

/-- The order-four analogue of `affineOrderThreeMarkedFixedCentralPoint`. -/
public noncomputable def affineOrderFourMarkedFixedCentralPoint
    (A : PaperAnalyticData) :
    C((A.actualAffineHeightSplit.allocation.orderThreeSide ∩
        A.actualAffineHeightSplit.allocation.orderFourSide :
          Set A.ellipticInterior),
      (orderFourRadialActionData A.periods).FillingQuotient) :=
  (orderFourRadialActionData A.periods).centralInclusion.comp
    (affineBandOrderFourMarkedProjection A)

/-- Pointwise, the order-three endpoint is the orbit class at the disc centre with the marked
band fibre coordinate. -/
public theorem affineOrderThreeMarkedFixedCentralPoint_apply
    (A : PaperAnalyticData)
    (x : (A.actualAffineHeightSplit.allocation.orderThreeSide ∩
      A.actualAffineHeightSplit.allocation.orderFourSide :
        Set A.ellipticInterior)) :
    affineOrderThreeMarkedFixedCentralPoint A x =
      Quotient.mk _ ((orderThreeRadialActionData A.periods).actionData.center,
        affineBandFiberCoordinate A x) := by
  exact RadialEllipticActionData.centralInclusion_coverProjection_sourceHomeomorph_symm
    (orderThreeRadialActionData A.periods) (affineBandFiberCoordinate A x)

/-- Pointwise, the order-four endpoint is the orbit class at its disc centre with the marked
band coordinate transported to the order-four fixed torus. -/
public theorem affineOrderFourMarkedFixedCentralPoint_apply
    (A : PaperAnalyticData)
    (x : (A.actualAffineHeightSplit.allocation.orderThreeSide ∩
      A.actualAffineHeightSplit.allocation.orderFourSide :
        Set A.ellipticInterior)) :
    affineOrderFourMarkedFixedCentralPoint A x =
      Quotient.mk _ ((orderFourRadialActionData A.periods).actionData.center,
        A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
          (affineBandFiberCoordinate A x)) := by
  exact RadialEllipticActionData.centralInclusion_coverProjection_sourceHomeomorph_symm
    (orderFourRadialActionData A.periods)
      (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
        (affineBandFiberCoordinate A x))

/-- Before transport through the open filling image, the inverse of the selected order-three
radial equivalence is exactly the inverse product-quotient homeomorphism applied to the explicit
fixed central point. -/
public theorem orderThreeSelectedFilling_invFun_markedProjection
    (A : PaperAnalyticData) :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).invFun.comp
        (affineBandOrderThreeMarkedProjection A) =
      (⟨(orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification
          |>.quotientHomeomorph.symm,
        (orderThreeSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification
          |>.quotientHomeomorph.symm.continuous⟩ :
        C((orderThreeRadialActionData A.periods).FillingQuotient,
          A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)).comp
        (affineOrderThreeMarkedFixedCentralPoint A) := by
  rfl

/-- The analogous formula for the selected order-four filling equivalence. -/
public theorem orderFourSelectedFilling_invFun_markedProjection
    (A : PaperAnalyticData) :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).invFun.comp
        (affineBandOrderFourMarkedProjection A) =
      (⟨(orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification
          |>.quotientHomeomorph.symm,
        (orderFourSelectedAffineRadialCompatibility A).toVaryingFillingProductIdentification
          |>.quotientHomeomorph.symm.continuous⟩ :
        C((orderFourRadialActionData A.periods).FillingQuotient,
          A.OrderFourVaryingFilling A.starSeparation.orderFour.radius)).comp
        (affineOrderFourMarkedFixedCentralPoint A) := by
  rfl

/-- The explicit order-three affine radial equivalence between an affine disc region and the
whole order-three central half-plane region.  Unlike selecting a witness from the proposition
`discRegionInclusion_isHomotopyEquivalence`, its inverse retains the real-period formula. -/
public noncomputable def orderThreeAffineDiscCentralHomotopyEquiv
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 2 / 3) :
    ↥(A.affineOrderThreeDiscRegion r) ≃ₕ
      ↥A.affineOrderThreeCentralRegion :=
  (A.affineOrderThreeDiscRegionQuotientHomeomorph r).toHomotopyEquiv |>.trans
    ((A.orderThreeAffineRadialLiftEquiv (s := r / 2) (by linarith) (by linarith) hr)
      |>.quotientHomotopyEquiv
        (A.orderThreeAffineDiscLiftAction_continuous r)
        A.orderThreeAffineHalfPlaneLiftAction_continuous) |>.trans
    A.affineOrderThreeCentralRegionQuotientHomeomorph.symm.toHomotopyEquiv

/-- The forward map of the explicit order-three equivalence is the literal region inclusion. -/
public theorem orderThreeAffineDiscCentralHomotopyEquiv_toFun
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 2 / 3) :
    (A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).toFun =
      regionInclusion (A.discRegion_subset_centralRegion hr) := by
  apply ContinuousMap.ext
  intro x
  apply A.affineOrderThreeCentralRegionQuotientHomeomorph.injective
  change A.affineOrderThreeCentralRegionQuotientHomeomorph
      (A.affineOrderThreeCentralRegionQuotientHomeomorph.symm
        ((A.orderThreeAffineRadialLiftEquiv (s := r / 2)
          (by linarith) (by linarith) hr).quotientToFun
            (A.affineOrderThreeDiscRegionQuotientHomeomorph r x))) = _
  rw [A.affineOrderThreeCentralRegionQuotientHomeomorph.apply_symm_apply]
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
    (ContinuousMap.id ↥A.affineOrderThreeCentralRegion).Homotopic
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
    ↥(A.affineOrderFourDiscRegion r) ≃ₕ
      ↥A.affineOrderFourCentralRegion :=
  (A.affineOrderFourDiscRegionQuotientHomeomorph r).toHomotopyEquiv |>.trans
    ((A.orderFourAffineRadialEquivChoice hr0 hr).quotientHomotopyEquiv
      (A.orderFourAffineDiscLiftAction_continuous r)
      A.orderFourAffineHalfPlaneLiftAction_continuous) |>.trans
    A.affineOrderFourCentralRegionQuotientHomeomorph.symm.toHomotopyEquiv

/-- The forward map of the explicit order-four equivalence is the literal region inclusion. -/
public theorem orderFourAffineDiscCentralHomotopyEquiv_toFun
    (A : PaperAnalyticData) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3) :
    (A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).toFun =
      regionInclusion (A.orderFourDiscRegion_subset_centralRegion hr) := by
  apply ContinuousMap.ext
  intro u
  apply A.affineOrderFourCentralRegionQuotientHomeomorph.injective
  change A.affineOrderFourCentralRegionQuotientHomeomorph
      (A.affineOrderFourCentralRegionQuotientHomeomorph.symm
        ((A.orderFourAffineRadialEquivChoice hr0 hr).quotientToFun
          (A.affineOrderFourDiscRegionQuotientHomeomorph r u))) = _
  rw [A.affineOrderFourCentralRegionQuotientHomeomorph.apply_symm_apply]
  apply A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.injective
  have hmem : u.1 ∈ A.ellipticCentralImage :=
    A.mem_centralImage_of_mem_centralHeightLowerRegion
      (fun z ↦ ‖(A.ellipticCentralCoordinate z).1 - 1‖) r u.2
  have hheight : (1 : ℝ) / 3 <
      A.ellipticCentralHeight ⟨u.1, hmem⟩ := by
    obtain ⟨y, hy, hyu⟩ := A.orderFourDiscRegion_subset_centralRegion hr u.2
    have hxy : y = (⟨u.1, hmem⟩ : A.ellipticCentralImage) := Subtype.ext hyu
    exact hxy ▸ hy
  have hleft : (regionInclusion (A.orderFourDiscRegion_subset_centralRegion hr) u :
      ↥A.affineOrderFourCentralRegion) =
      ⟨(⟨u.1, hmem⟩ : A.ellipticCentralImage).1,
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
    (ContinuousMap.id ↥A.affineOrderFourCentralRegion).Homotopic
      ((regionInclusion (A.orderFourDiscRegion_subset_centralRegion hr)).comp
        (A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).invFun) := by
  rw [← A.orderFourAffineDiscCentralHomotopyEquiv_toFun hr0 hr]
  exact (A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).right_inv.symm

/-- The common affine band. -/
public abbrev affineMarkedBand (A : PaperAnalyticData) :=
  (A.actualAffineHeightSplit.allocation.orderThreeSide ∩
    A.actualAffineHeightSplit.allocation.orderFourSide :
      Set A.ellipticInterior)

/-- Reading an order-three central overlap point in the actual filling chart returns its exact
star-collar filling representative. -/
public theorem orderThreeFillingImageToPiece_symm_overlap
    (A : PaperAnalyticData)
    (u : ↥(A.orderThreeFillingImage ∩
      A.affineOrderThreeCentralRegion)) :
    A.orderThreePieceHomeomorph.symm
        (A.orderThreeFillingImageToPiece ⟨u.1, u.2.1⟩) =
      A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u) := by
  have hu : u.1 ∈ A.orderThreeFillingImage := u.2.1
  let v : A.orderThreeFillingImage := ⟨u.1, hu⟩
  change A.orderThreePieceHomeomorph.symm
      (A.orderThreeFillingImageToPiece v) = _
  apply A.orderThreePieceHomeomorph.injective
  rw [A.orderThreePieceHomeomorph.apply_symm_apply]
  apply Subtype.ext
  let S := A.openEmbeddingStarData
  let q : S.collarSource 1 := A.orderThreeOverlapCollarHomeomorph u
  let y : A.ellipticCentralImage :=
    ⟨u.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
      A.ellipticCentralHeight (2 / 3 : ℝ) u.2.2⟩
  have hstar : A.starToCentral 1 q =
      A.ellipticCentralImageHomeomorph y :=
    A.starToCentral_orderThreeOverlapCollarHomeomorph u
  have hglued : u.1.1 = S.collarSourceToGlued 1 q := by
    calc
      u.1.1 =
          (S.centralToSectionSevenEulerPieceHomeomorph
            (A.ellipticCentralImageHomeomorph y)).1 :=
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
    (A.orderThreeFillingImageToPiece v).1 = u.1.1 := rfl
    _ = S.collarSourceToGlued 1 q := hglued
    _ = _ := hrelation
    _ = (A.orderThreePieceHomeomorph (S.toFilling 1 q)).1 := hcoe.symm

/-- The corresponding exact order-four filling representative. -/
public theorem orderFourFillingImageToPiece_symm_overlap
    (A : PaperAnalyticData)
    (u : ↥(A.orderFourFillingImage ∩
      A.affineOrderFourCentralRegion)) :
    A.orderFourPieceHomeomorph.symm
        (A.orderFourFillingImageToPiece ⟨u.1, u.2.1⟩) =
      A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u) := by
  have hu : u.1 ∈ A.orderFourFillingImage := u.2.1
  let v : A.orderFourFillingImage := ⟨u.1, hu⟩
  change A.orderFourPieceHomeomorph.symm
      (A.orderFourFillingImageToPiece v) = _
  apply A.orderFourPieceHomeomorph.injective
  rw [A.orderFourPieceHomeomorph.apply_symm_apply]
  apply Subtype.ext
  let S := A.openEmbeddingStarData
  let q : S.collarSource 2 := A.orderFourOverlapCollarHomeomorph u
  let y : A.ellipticCentralImage :=
    ⟨u.1, A.mem_centralImage_of_mem_centralHeightUpperRegion
      A.ellipticCentralHeight (1 / 3 : ℝ) u.2.2⟩
  have hstar : A.starToCentral 2 q =
      A.ellipticCentralImageHomeomorph y :=
    A.starToCentral_orderFourOverlapCollarHomeomorph u
  have hglued : u.1.1 = S.collarSourceToGlued 2 q := by
    calc
      u.1.1 =
          (S.centralToSectionSevenEulerPieceHomeomorph
            (A.ellipticCentralImageHomeomorph y)).1 :=
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
    (A.orderFourFillingImageToPiece v).1 = u.1.1 := rfl
    _ = S.collarSourceToGlued 2 q := hglued
    _ = _ := hrelation
    _ = (A.orderFourPieceHomeomorph (S.toFilling 2 q)).1 := hcoe.symm

/-- The common band included in the order-three affine central region. -/
public def affineBandToOrderThreeCentralRegion (A : PaperAnalyticData) :
    C(A.affineMarkedBand, ↥A.affineOrderThreeCentralRegion) where
  toFun x := ⟨x.1, by
    change x.1 ∈ centralHeightLowerRegion A.ellipticCentralHeight (2 / 3 : ℝ)
    obtain ⟨y, hy, hxy⟩ :=
      (A.actualAffineHeightSplit.sidesIntersectionHomeomorph x).2
    exact ⟨y, hy.2, hxy⟩⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The common band included in the order-four affine central region. -/
public def affineBandToOrderFourCentralRegion (A : PaperAnalyticData) :
    C(A.affineMarkedBand, ↥A.affineOrderFourCentralRegion) where
  toFun x := ⟨x.1, by
    change x.1 ∈ centralHeightUpperRegion A.ellipticCentralHeight (1 / 3 : ℝ)
    obtain ⟨y, hy, hxy⟩ :=
      (A.actualAffineHeightSplit.sidesIntersectionHomeomorph x).2
    exact ⟨y, hy.1, hxy⟩⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- A fixed small affine disc contained in the actual order-three star overlap. -/
public noncomputable def affineOrderThreeMarkedDiscRadius (A : PaperAnalyticData) : ℝ :=
  A.exists_small_discRegion_subset_orderThreeOverlap.choose

public theorem affineOrderThreeMarkedDiscRadius_spec (A : PaperAnalyticData) :
    0 < A.affineOrderThreeMarkedDiscRadius ∧
      A.affineOrderThreeMarkedDiscRadius ≤ 1 / 3 ∧
      A.affineOrderThreeDiscRegion
          A.affineOrderThreeMarkedDiscRadius ⊆
        A.orderThreeFillingImage ∩
          A.affineOrderThreeCentralRegion :=
  by
    have h := A.exists_small_discRegion_subset_orderThreeOverlap.choose_spec
    exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- A fixed small affine disc contained in the actual order-four star overlap. -/
public noncomputable def affineOrderFourMarkedDiscRadius (A : PaperAnalyticData) : ℝ :=
  A.exists_small_discRegion_subset_orderFourOverlap.choose

public theorem affineOrderFourMarkedDiscRadius_spec (A : PaperAnalyticData) :
    0 < A.affineOrderFourMarkedDiscRadius ∧
      A.affineOrderFourMarkedDiscRadius ≤ 1 / 3 ∧
      A.affineOrderFourDiscRegion
          A.affineOrderFourMarkedDiscRadius ⊆
        A.orderFourFillingImage ∩
          A.affineOrderFourCentralRegion :=
  by
    have h := A.exists_small_discRegion_subset_orderFourOverlap.choose_spec
    exact ⟨h.1, h.2.1, h.2.2.1⟩

public theorem affineOrderThreeMarkedDiscRadius_cayley (A : PaperAnalyticData)
    (z : UpperHalfPlane)
    (hz : ‖A.modular.sourceCoordinate.coordinate z‖ < A.affineOrderThreeMarkedDiscRadius) :
    ∃ k : SphereSixComplex.TriangleGroup.Delta,
      ‖(SphereSixComplex.Geometry.EllipticCayleyHomeomorph.orderThreeCayleyHomeomorph
        (SphereSixComplex.TriangleGroup.fuchsianSourceAction k • z) : ℂ)‖ <
        A.starSeparation.orderThree.radius / 2 :=
  A.exists_small_discRegion_subset_orderThreeOverlap.choose_spec.2.2.2 z hz

public theorem affineOrderFourMarkedDiscRadius_cayley (A : PaperAnalyticData)
    (z : UpperHalfPlane)
    (hz : ‖A.modular.sourceCoordinate.coordinate z - 1‖ < A.affineOrderFourMarkedDiscRadius) :
    ∃ k : SphereSixComplex.TriangleGroup.Delta,
      ‖(SphereSixComplex.Geometry.EllipticCayleyHomeomorph.orderFourCayleyHomeomorph
        (SphereSixComplex.TriangleGroup.fuchsianSourceAction k • z) : ℂ)‖ <
        A.starSeparation.orderFour.radius / 2 :=
  A.exists_small_discRegion_subset_orderFourOverlap.choose_spec.2.2.2 z hz

/-- The explicit order-three affine radial inverse, restricted to the common band and then read
as a point of the actual filling image through the proved small-disc inclusion. -/
public noncomputable def affineOrderThreeDiscFillingEndpoint
    (A : PaperAnalyticData) :
    C(A.affineMarkedBand, ↥A.orderThreeFillingImage) :=
  let r := A.affineOrderThreeMarkedDiscRadius
  let hr0 := (A.affineOrderThreeMarkedDiscRadius_spec).1
  let hr : r ≤ 2 / 3 :=
    (A.affineOrderThreeMarkedDiscRadius_spec).2.1.trans (by norm_num)
  let hsub := (A.affineOrderThreeMarkedDiscRadius_spec).2.2
  (⟨fun z : ↥(A.affineOrderThreeDiscRegion r) ↦
      ⟨z.1, (hsub z.2).1⟩, continuous_subtype_val.subtype_mk _⟩ :
    C(↥(A.affineOrderThreeDiscRegion r),
      ↥A.orderThreeFillingImage)).comp
    ((A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
      (A.affineBandToOrderThreeCentralRegion))

/-- The analogous explicit order-four disc endpoint in the actual filling image. -/
public noncomputable def affineOrderFourDiscFillingEndpoint
    (A : PaperAnalyticData) :
    C(A.affineMarkedBand, ↥A.orderFourFillingImage) :=
  let r := A.affineOrderFourMarkedDiscRadius
  let hr0 := (A.affineOrderFourMarkedDiscRadius_spec).1
  let hr : r ≤ 1 - 1 / 3 :=
    (A.affineOrderFourMarkedDiscRadius_spec).2.1.trans (by norm_num)
  let hsub := (A.affineOrderFourMarkedDiscRadius_spec).2.2
  (⟨fun z : ↥(A.affineOrderFourDiscRegion r) ↦
      ⟨z.1, (hsub z.2).1⟩, continuous_subtype_val.subtype_mk _⟩ :
    C(↥(A.affineOrderFourDiscRegion r),
      ↥A.orderFourFillingImage)).comp
    ((A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
      (A.affineBandToOrderFourCentralRegion))

/-- The order-three disc endpoint retaining membership in both the filling and central regions. -/
public noncomputable def affineOrderThreeDiscOverlapEndpoint
    (A : PaperAnalyticData) :
    C(A.affineMarkedBand,
      ↥(A.orderThreeFillingImage ∩
        A.affineOrderThreeCentralRegion)) :=
  let r := A.affineOrderThreeMarkedDiscRadius
  let hr0 := (A.affineOrderThreeMarkedDiscRadius_spec).1
  let hr : r ≤ 2 / 3 :=
    (A.affineOrderThreeMarkedDiscRadius_spec).2.1.trans (by norm_num)
  let hsub := (A.affineOrderThreeMarkedDiscRadius_spec).2.2
  (⟨fun z : ↥(A.affineOrderThreeDiscRegion r) ↦
      ⟨z.1, hsub z.2⟩, continuous_subtype_val.subtype_mk _⟩ :
    C(↥(A.affineOrderThreeDiscRegion r),
      ↥(A.orderThreeFillingImage ∩
        A.affineOrderThreeCentralRegion))).comp
    ((A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
      A.affineBandToOrderThreeCentralRegion)

/-- The order-four endpoint retaining both overlap memberships. -/
public noncomputable def affineOrderFourDiscOverlapEndpoint
    (A : PaperAnalyticData) :
    C(A.affineMarkedBand,
      ↥(A.orderFourFillingImage ∩
        A.affineOrderFourCentralRegion)) :=
  let r := A.affineOrderFourMarkedDiscRadius
  let hr0 := (A.affineOrderFourMarkedDiscRadius_spec).1
  let hr : r ≤ 1 - 1 / 3 :=
    (A.affineOrderFourMarkedDiscRadius_spec).2.1.trans (by norm_num)
  let hsub := (A.affineOrderFourMarkedDiscRadius_spec).2.2
  (⟨fun z : ↥(A.affineOrderFourDiscRegion r) ↦
      ⟨z.1, hsub z.2⟩, continuous_subtype_val.subtype_mk _⟩ :
    C(↥(A.affineOrderFourDiscRegion r),
      ↥(A.orderFourFillingImage ∩
        A.affineOrderFourCentralRegion))).comp
    ((A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
      A.affineBandToOrderFourCentralRegion)

public theorem affineOrderThreeDiscOverlapEndpoint_toFilling
    (A : PaperAnalyticData) :
    (IntegralMayerVietoris.interToLeft A.orderThreeFillingImage
      A.affineOrderThreeCentralRegion).comp
        A.affineOrderThreeDiscOverlapEndpoint =
      A.affineOrderThreeDiscFillingEndpoint := by
  rfl

public theorem affineOrderFourDiscOverlapEndpoint_toFilling
    (A : PaperAnalyticData) :
    (IntegralMayerVietoris.interToLeft A.orderFourFillingImage
      A.affineOrderFourCentralRegion).comp
        A.affineOrderFourDiscOverlapEndpoint =
      A.affineOrderFourDiscFillingEndpoint := by
  rfl

/-- The explicit endpoint read in the selected order-three varying filling, with all gluing
homeomorphisms removed. -/
public noncomputable def affineOrderThreeStarEndpoint (A : PaperAnalyticData) :
    C(A.affineMarkedBand,
      A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) :=
  (⟨fun u ↦ A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u),
    (A.starToFilling_isOpenEmbedding 1).continuous.comp
      A.orderThreeOverlapCollarHomeomorph.continuous⟩ :
    C(↥(A.orderThreeFillingImage ∩
      A.affineOrderThreeCentralRegion),
      A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)).comp
    A.affineOrderThreeDiscOverlapEndpoint

/-- The corresponding order-four selected-filling endpoint. -/
public noncomputable def affineOrderFourStarEndpoint (A : PaperAnalyticData) :
    C(A.affineMarkedBand,
      A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) :=
  (⟨fun u ↦ A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u),
    (A.starToFilling_isOpenEmbedding 2).continuous.comp
      A.orderFourOverlapCollarHomeomorph.continuous⟩ :
    C(↥(A.orderFourFillingImage ∩
      A.affineOrderFourCentralRegion),
      A.OrderFourVaryingFilling A.starSeparation.orderFour.radius)).comp
    A.affineOrderFourDiscOverlapEndpoint

/-- The remaining coordinate calculation with the ambient glued-space homeomorphisms removed. -/
public structure AffineMarkedStarEndpointCompatibility (A : PaperAnalyticData) where
  orderThree :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderThreeStarEndpoint =
      affineBandOrderThreeMarkedProjection A
  orderFour :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderFourStarEndpoint =
      affineBandOrderFourMarkedProjection A

/-- The exact remaining coordinate calculation after the band-wide affine radial inverse has
been constructed: the filling radial retraction of each explicit disc endpoint must be the
marked central-fibre projection. -/
public structure AffineMarkedDiscEndpointCompatibility (A : PaperAnalyticData) where
  orderThree :
    (A.orderThreeFillingImageHomotopyEquiv.toFun.comp
      (A.affineOrderThreeDiscFillingEndpoint)) =
        affineBandOrderThreeMarkedProjection A
  orderFour :
    (A.orderFourFillingImageHomotopyEquiv.toFun.comp
      (A.affineOrderFourDiscFillingEndpoint)) =
        affineBandOrderFourMarkedProjection A

/-- The star-coordinate equalities imply the filling-image endpoint equalities. -/
public theorem AffineMarkedStarEndpointCompatibility.toDiscEndpointCompatibility
    {A : PaperAnalyticData} (H : A.AffineMarkedStarEndpointCompatibility) :
    A.AffineMarkedDiscEndpointCompatibility where
  orderThree := by
    apply ContinuousMap.ext
    intro x
    let u := A.affineOrderThreeDiscOverlapEndpoint x
    have hfill : A.affineOrderThreeDiscFillingEndpoint x =
        ⟨u.1, u.2.1⟩ := rfl
    change (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
        (A.orderThreePieceHomeomorph.symm
          (A.orderThreeFillingImageToPiece
            (A.affineOrderThreeDiscFillingEndpoint x))) = _
    rw [hfill]
    have hpiece :
        (A.orderThreePieceHomeomorph.symm
          (A.orderThreeFillingImageToPiece ⟨u.1, u.2.1⟩) :
            A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) =
          A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u) :=
      A.orderThreeFillingImageToPiece_symm_overlap u
    rw [hpiece]
    exact congrArg
      (fun f : C(A.affineMarkedBand,
        OrderThreeReducedCentralFiber A.periods) ↦ f x) H.orderThree
  orderFour := by
    apply ContinuousMap.ext
    intro x
    let u := A.affineOrderFourDiscOverlapEndpoint x
    have hfill : A.affineOrderFourDiscFillingEndpoint x =
        ⟨u.1, u.2.1⟩ := rfl
    change (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
        (A.orderFourPieceHomeomorph.symm
          (A.orderFourFillingImageToPiece
            (A.affineOrderFourDiscFillingEndpoint x))) = _
    rw [hfill]
    have hpiece :
        (A.orderFourPieceHomeomorph.symm
          (A.orderFourFillingImageToPiece ⟨u.1, u.2.1⟩) :
            A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) =
          A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u) :=
      A.orderFourFillingImageToPiece_symm_overlap u
    rw [hpiece]
    exact congrArg
      (fun f : C(A.affineMarkedBand,
        OrderFourReducedCentralFiber A.periods) ↦ f x) H.orderFour

/-- Include the order-three central region in its affine side. -/
public def affineOrderThreeCentralRegionToSide (A : PaperAnalyticData) :
    C(↥A.affineOrderThreeCentralRegion,
      A.actualAffineHeightSplit.allocation.orderThreeSide) where
  toFun x := ⟨x.1, Or.inr x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Include the order-four central region in its affine side. -/
public def affineOrderFourCentralRegionToSide (A : PaperAnalyticData) :
    C(↥A.affineOrderFourCentralRegion,
      A.actualAffineHeightSplit.allocation.orderFourSide) where
  toFun x := ⟨x.1, Or.inr x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Include the order-three filling image in its affine side. -/
public def affineOrderThreeFillingImageToSide (A : PaperAnalyticData) :
    C(↥A.orderThreeFillingImage,
      A.actualAffineHeightSplit.allocation.orderThreeSide) where
  toFun x := ⟨x.1, Or.inl x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Include the order-four filling image in its affine side. -/
public def affineOrderFourFillingImageToSide (A : PaperAnalyticData) :
    C(↥A.orderFourFillingImage,
      A.actualAffineHeightSplit.allocation.orderFourSide) where
  toFun x := ⟨x.1, Or.inl x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The explicit affine radial inverse deforms the common-band inclusion to the selected small
disc endpoint, viewed in the order-three filling image. -/
public theorem orderThreeBandInclusion_homotopic_discFillingEndpoint
    (A : PaperAnalyticData) :
    (IntegralMayerVietoris.interToLeft
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide).Homotopic
    ((A.affineOrderThreeFillingImageToSide).comp
      (A.affineOrderThreeDiscFillingEndpoint)) := by
  let r := A.affineOrderThreeMarkedDiscRadius
  let hr0 := (A.affineOrderThreeMarkedDiscRadius_spec).1
  let hr : r ≤ 2 / 3 :=
    (A.affineOrderThreeMarkedDiscRadius_spec).2.1.trans (by norm_num)
  have h := ContinuousMap.Homotopic.comp
    (.refl A.affineOrderThreeCentralRegionToSide)
    (ContinuousMap.Homotopic.comp
      (A.orderThreeAffineDiscCentral_inverse_deformation hr0 hr)
      (.refl A.affineBandToOrderThreeCentralRegion))
  have hleft :
      A.affineOrderThreeCentralRegionToSide.comp
          A.affineBandToOrderThreeCentralRegion =
        IntegralMayerVietoris.interToLeft
          A.actualAffineHeightSplit.allocation.orderThreeSide
          A.actualAffineHeightSplit.allocation.orderFourSide := by
    ext x
    rfl
  have hright :
      A.affineOrderThreeCentralRegionToSide.comp
          ((regionInclusion (A.discRegion_subset_centralRegion hr)).comp
            ((A.orderThreeAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
              A.affineBandToOrderThreeCentralRegion)) =
        A.affineOrderThreeFillingImageToSide.comp
          A.affineOrderThreeDiscFillingEndpoint := by
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
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide).Homotopic
    ((A.affineOrderFourFillingImageToSide).comp
      (A.affineOrderFourDiscFillingEndpoint)) := by
  let r := A.affineOrderFourMarkedDiscRadius
  let hr0 := (A.affineOrderFourMarkedDiscRadius_spec).1
  let hr : r ≤ 1 - 1 / 3 :=
    (A.affineOrderFourMarkedDiscRadius_spec).2.1.trans (by norm_num)
  have h := ContinuousMap.Homotopic.comp
    (.refl A.affineOrderFourCentralRegionToSide)
    (ContinuousMap.Homotopic.comp
      (A.orderFourAffineDiscCentral_inverse_deformation hr0 hr)
      (.refl A.affineBandToOrderFourCentralRegion))
  have hleft :
      A.affineOrderFourCentralRegionToSide.comp
          A.affineBandToOrderFourCentralRegion =
        IntegralMayerVietoris.interToRight
          A.actualAffineHeightSplit.allocation.orderThreeSide
          A.actualAffineHeightSplit.allocation.orderFourSide := by
    ext x
    rfl
  have hright :
      A.affineOrderFourCentralRegionToSide.comp
          ((regionInclusion (A.orderFourDiscRegion_subset_centralRegion hr)).comp
            ((A.orderFourAffineDiscCentralHomotopyEquiv hr0 hr).invFun.comp
              A.affineBandToOrderFourCentralRegion)) =
        A.affineOrderFourFillingImageToSide.comp
          A.affineOrderFourDiscFillingEndpoint := by
    ext x
    rfl
  simp only [ContinuousMap.id_comp, ContinuousMap.comp_assoc] at h
  rw [hleft, hright] at h
  exact h

private theorem orderThreeSideInverse_markedProjection_formula
    (A : PaperAnalyticData) :
    (affineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp
        (affineBandOrderThreeMarkedProjection A) =
      (orderThreeOverlapIsHomotopyEquivalence_inclusion
          A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
        ((nestedSubtypeHomeomorph
          A.actualAffineHeightSplit.allocation.orderThreeSide
          A.orderThreeFillingImage
          A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv
          |>.invFun.comp
            (A.orderThreeFillingImageHomotopyEquiv.invFun.comp
              (affineBandOrderThreeMarkedProjection A))) := by
  rfl

private theorem orderFourSideInverse_markedProjection_formula
    (A : PaperAnalyticData) :
    (affineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp
        (affineBandOrderFourMarkedProjection A) =
      (orderFourOverlapIsHomotopyEquivalence_inclusion
          A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
        ((nestedSubtypeHomeomorph
          A.actualAffineHeightSplit.allocation.orderFourSide
          A.orderFourFillingImage
          A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv
          |>.invFun.comp
            (A.orderFourFillingImageHomotopyEquiv.invFun.comp
              (affineBandOrderFourMarkedProjection A))) := by
  rfl

/-- The two explicit fixed-coordinate endpoint calculations are the only remaining input needed
after the affine radial deformations: filling homotopy-inverse cancellation supplies the desired
side contractions. -/
public theorem AffineMarkedDiscEndpointCompatibility.toSideContractions
    {A : PaperAnalyticData} (H : A.AffineMarkedDiscEndpointCompatibility) :
    A.AffineMarkedBandSideContractions := by
  refine { orderThree := ?_, orderFour := ?_ }
  · let q := A.affineOrderThreeDiscFillingEndpoint
    let g := A.orderThreeFillingImageHomotopyEquiv
    let p := affineBandOrderThreeMarkedProjection A
    have hfill := ContinuousMap.Homotopic.comp g.left_inv (.refl q)
    have hcomp : g.toFun.comp q = p := H.orderThree
    simp only [ContinuousMap.comp_assoc, hcomp] at hfill
    have hside := ContinuousMap.Homotopic.comp
      (.refl A.affineOrderThreeFillingImageToSide) hfill.symm
    have hendpoint :
        A.affineOrderThreeFillingImageToSide.comp (g.invFun.comp p) =
          (affineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp p := by
      dsimp [g, p]
      have hraw :
          A.affineOrderThreeFillingImageToSide.comp
              (A.orderThreeFillingImageHomotopyEquiv.invFun.comp
                (affineBandOrderThreeMarkedProjection A)) =
            (orderThreeOverlapIsHomotopyEquivalence_inclusion
                A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
              ((nestedSubtypeHomeomorph
                A.actualAffineHeightSplit.allocation.orderThreeSide
                A.orderThreeFillingImage
                A.actualAffineHeightSplit.orderThreeFillingImage_subset_side)
                |>.toHomotopyEquiv.invFun.comp
                  (A.orderThreeFillingImageHomotopyEquiv.invFun.comp
                    (affineBandOrderThreeMarkedProjection A))) := by
        rw [(orderThreeOverlapIsHomotopyEquivalence_inclusion
          A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv_invFun]
        ext x
        rfl
      exact hraw.trans (orderThreeSideInverse_markedProjection_formula A).symm
    simp only [ContinuousMap.id_comp] at hside
    rw [hendpoint] at hside
    exact (A.orderThreeBandInclusion_homotopic_discFillingEndpoint).trans hside
  · let q := A.affineOrderFourDiscFillingEndpoint
    let g := A.orderFourFillingImageHomotopyEquiv
    let p := affineBandOrderFourMarkedProjection A
    have hfill := ContinuousMap.Homotopic.comp g.left_inv (.refl q)
    have hcomp : g.toFun.comp q = p := H.orderFour
    simp only [ContinuousMap.comp_assoc, hcomp] at hfill
    have hside := ContinuousMap.Homotopic.comp
      (.refl A.affineOrderFourFillingImageToSide) hfill.symm
    have hendpoint :
        A.affineOrderFourFillingImageToSide.comp (g.invFun.comp p) =
          (affineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp p := by
      dsimp [g, p]
      have hraw :
          A.affineOrderFourFillingImageToSide.comp
              (A.orderFourFillingImageHomotopyEquiv.invFun.comp
                (affineBandOrderFourMarkedProjection A)) =
            (orderFourOverlapIsHomotopyEquivalence_inclusion
                A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
              ((nestedSubtypeHomeomorph
                A.actualAffineHeightSplit.allocation.orderFourSide
                A.orderFourFillingImage
                A.actualAffineHeightSplit.orderFourFillingImage_subset_side)
                |>.toHomotopyEquiv.invFun.comp
                  (A.orderFourFillingImageHomotopyEquiv.invFun.comp
                    (affineBandOrderFourMarkedProjection A))) := by
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
    (A : PaperAnalyticData) (H : A.AffineMarkedDiscEndpointCompatibility) :
    A.AffineOverlapBandCompatibility :=
  markedBandHomotopies_of_sideContractions A H.toSideContractions

/-- The order-three inverse endpoint in the actual affine side is obtained by transporting the
explicit fixed central point back through the selected varying-filling and open-image
homeomorphisms. -/
public theorem affineOrderThreeSideInverse_markedProjection
    (A : PaperAnalyticData) :
    (affineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp
        (affineBandOrderThreeMarkedProjection A) =
      (orderThreeOverlapIsHomotopyEquivalence_inclusion
          A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
        ((nestedSubtypeHomeomorph
          A.actualAffineHeightSplit.allocation.orderThreeSide
          A.orderThreeFillingImage
          A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv
          |>.invFun.comp
            (A.orderThreeFillingImageHomotopyEquiv.invFun.comp
              (affineBandOrderThreeMarkedProjection A))) := by
  rfl

/-- The corresponding unfolded order-four endpoint. -/
public theorem affineOrderFourSideInverse_markedProjection
    (A : PaperAnalyticData) :
    (affineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp
        (affineBandOrderFourMarkedProjection A) =
      (orderFourOverlapIsHomotopyEquivalence_inclusion
          A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
        ((nestedSubtypeHomeomorph
          A.actualAffineHeightSplit.allocation.orderFourSide
          A.orderFourFillingImage
          A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv
          |>.invFun.comp
            (A.orderFourFillingImageHomotopyEquiv.invFun.comp
              (affineBandOrderFourMarkedProjection A))) := by
  rfl

/-- Fully point-set form of the remaining geometry.  The two functions must glue the affine
central-family transport to the cyclic filling contraction continuously across the star collar.
The endpoint equalities are literal equalities of points in the corresponding affine side. -/
public structure AffineMarkedBandGluedHomotopies (A : PaperAnalyticData) where
  orderThreeToFun : unitInterval × A.affineMarkedBand →
    A.actualAffineHeightSplit.allocation.orderThreeSide
  orderThree_continuous : Continuous orderThreeToFun
  orderThree_zero : ∀ x,
    orderThreeToFun (0, x) =
      IntegralMayerVietoris.interToLeft
        A.actualAffineHeightSplit.allocation.orderThreeSide
        A.actualAffineHeightSplit.allocation.orderFourSide x
  orderThree_one : ∀ x,
    orderThreeToFun (1, x) =
      (affineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun
        (affineBandOrderThreeMarkedProjection A x)
  orderFourToFun : unitInterval × A.affineMarkedBand →
    A.actualAffineHeightSplit.allocation.orderFourSide
  orderFour_continuous : Continuous orderFourToFun
  orderFour_zero : ∀ x,
    orderFourToFun (0, x) =
      IntegralMayerVietoris.interToRight
        A.actualAffineHeightSplit.allocation.orderThreeSide
        A.actualAffineHeightSplit.allocation.orderFourSide x
  orderFour_one : ∀ x,
    orderFourToFun (1, x) =
      (affineOrderFourSideToReducedFiberHomotopyEquiv A).invFun
        (affineBandOrderFourMarkedProjection A x)

/-- The explicit glued functions and their point-set endpoint formulas supply the exact
side-contraction package of the preceding reduction. -/
public theorem AffineMarkedBandGluedHomotopies.toSideContractions
    {A : PaperAnalyticData} (H : A.AffineMarkedBandGluedHomotopies) :
    A.AffineMarkedBandSideContractions where
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
    (A : PaperAnalyticData) (H : A.AffineMarkedBandGluedHomotopies) :
    A.AffineOverlapBandCompatibility :=
  markedBandHomotopies_of_sideContractions A H.toSideContractions

end SphereSixComplex.Geometry.PaperAnalyticData

end
