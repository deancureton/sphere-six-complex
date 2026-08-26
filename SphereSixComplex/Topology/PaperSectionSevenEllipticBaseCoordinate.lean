module

public import SphereSixComplex.Geometry.PaperCentralCompactCore
public import SphereSixComplex.Topology.PaperSectionSevenCentralBandSplit

/-!
# A concrete base split for the Section 7 elliptic interior

The invariant modular coordinate descends from the regular family to its central quotient.  Two
overlapping real half-planes in the twice-punctured affine coordinate line then give the open
central allocation used by the two-disc cover.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- The modular base coordinate is constant on triangle-group orbits of the regular torus
family. -/
public theorem centralFamilyCoordinate_respects
    (x y : RegularTotalSpace A.periods)
    (h : (@MulAction.orbitRel SphereSixComplex.TriangleGroup.Delta _ _
      (regularFamilyDeckAction A.periods)) x y) :
    A.regularCoordinate (regularTotalSpaceBase A.periods x) =
      A.regularCoordinate (regularTotalSpaceBase A.periods y) := by
  let _ := regularFamilyDeckAction A.periods
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, rfl⟩ := h
  apply Subtype.ext
  change A.modular.sourceCoordinate.coordinate
      (regularTotalSpaceBase A.periods (regularFamilyDeckMap A.periods g y)).1 = _
  rw [regularTotalSpaceBase_familyDeckMap]
  exact A.modular.sourceCoordinate.coordinate_invariant g _

/-- The exact affine coordinate on the base of the actual central family. -/
public noncomputable def centralFamilyCoordinate :
    A.CentralFamily → RegularCoordinateBase := by
  letI := regularFamilyDeckAction A.periods
  exact Quotient.lift
    (fun x ↦ A.regularCoordinate (regularTotalSpaceBase A.periods x))
    A.centralFamilyCoordinate_respects

public theorem centralFamilyCoordinate_centralQuotientProjection
    (x : RegularTotalSpace A.periods) :
    A.centralFamilyCoordinate (A.centralQuotientProjection x) =
      A.regularCoordinate (regularTotalSpaceBase A.periods x) :=
  rfl

public theorem centralFamilyCoordinate_continuous :
    Continuous A.centralFamilyCoordinate := by
  let _ := regularFamilyDeckAction A.periods
  apply continuous_quot_lift A.centralFamilyCoordinate_respects
  exact A.regularCoordinate_isLocalHomeomorph.continuous.comp
    (regularTotalSpaceBase_continuous A.periods)

public theorem centralFamilyCoordinate_surjective :
    Function.Surjective A.centralFamilyCoordinate := by
  intro z
  obtain ⟨u, hu⟩ := A.regularCoordinate_surjective z
  let q : RegularTotalSpace A.periods :=
    projection (regularParameterMap A.periods) (u, 0)
  refine ⟨A.centralQuotientProjection q, ?_⟩
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  change A.regularCoordinate u = z
  exact hu

public theorem sectionSevenCentralPiece_subset_ellipticInterior :
    A.SectionSevenEllipticCover.piece 0 ⊆
      A.SectionSevenEllipticCover.stage (2 : Fin 4) := by
  intro x hx
  rw [FourPieceOpenCover.stage]
  exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by decide, hx⟩⟩

/-- Forgetting the elliptic-interior subtype identifies its central image with the central cover
piece. -/
public def sectionSevenEllipticCentralImageToPiece :
    A.sectionSevenEllipticCentralImage ≃ₜ A.SectionSevenEllipticCover.piece 0 where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, A.sectionSevenCentralPiece_subset_ellipticInterior x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The central image inside the elliptic interior is the actual central family. -/
public noncomputable def sectionSevenEllipticCentralImageHomeomorph :
    A.sectionSevenEllipticCentralImage ≃ₜ A.CentralFamily :=
  A.sectionSevenEllipticCentralImageToPiece.trans
    A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.symm

/-- A point of the central image inherits the exact affine base coordinate. -/
public noncomputable def sectionSevenEllipticCentralCoordinate :
    A.sectionSevenEllipticCentralImage → RegularCoordinateBase :=
  fun x ↦ A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph x)

public theorem sectionSevenEllipticCentralCoordinate_continuous :
    Continuous A.sectionSevenEllipticCentralCoordinate :=
  A.centralFamilyCoordinate_continuous.comp
    A.sectionSevenEllipticCentralImageHomeomorph.continuous

/-- The real part of the affine base coordinate supplies the central splitting height. -/
public noncomputable def sectionSevenEllipticCentralHeight :
    A.sectionSevenEllipticCentralImage → ℝ :=
  fun x ↦ (A.sectionSevenEllipticCentralCoordinate x).1.re

public theorem sectionSevenEllipticCentralHeight_continuous :
    Continuous A.sectionSevenEllipticCentralHeight :=
  Complex.continuous_re.comp
    (continuous_subtype_val.comp A.sectionSevenEllipticCentralCoordinate_continuous)

/-- The selected order-three collar lies over the affine neighborhood `re < 1/3`. -/
public theorem orderThreeStarCollar_centralCoordinate_re_lt
    (q : A.starCollarSourceType (1 : Fin 3)) :
    (A.centralFamilyCoordinate (A.starToCentral 1 q)).1.re < 1 / 3 := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = SphereSixComplex.TriangleGroup.fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  change (A.centralFamilyCoordinate
    (orderThreeLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      A.starSeparation.orderThree.sourceData
        (orderThreePuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource
          A.starSeparation.orderThree.radius q))).1.re < 1 / 3
  generalize hQ : orderThreePuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource
      A.starSeparation.orderThree.radius q = Q
  induction Q using Quotient.inductionOn with
  | _ x =>
      rw [orderThreeLinearCollarToPuncturedGlobalFamily_mk]
      change (A.modular.sourceCoordinate.coordinate
        (regularTotalSpaceBase A.periods
          (orderThreeCollarToRegular A.periods hproper
            A.starSeparation.orderThree.sourceData x)).1).re < 1 / 3
      rw [orderThreeCollarToRegular_base A.periods hproper hsource
        A.starSeparation.orderThree.sourceData]
      have hx : ‖(orderThreeCayleyHomeomorph
          (familyTotalSpaceBase A.periods x) : ℂ)‖ <
          A.starSeparation.orderThree.radius := by
        simpa only [orderThreeLinearPuncturedCarrier.eq_def,
          orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderThreeFamilyRadius.eq_def] using x.property.2
      exact (Complex.re_le_norm _).trans_lt
        (A.starSeparation.orderThree_coordinate_bound _ hx)

/-- The selected order-four collar lies over the affine neighborhood `2/3 < re`. -/
public theorem orderFourStarCollar_twoThirds_lt_centralCoordinate_re
    (q : A.starCollarSourceType (2 : Fin 3)) :
    2 / 3 < (A.centralFamilyCoordinate (A.starToCentral 2 q)).1.re := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = SphereSixComplex.TriangleGroup.fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  change 2 / 3 < (A.centralFamilyCoordinate
    (orderFourLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      A.starSeparation.orderFour.sourceData
        (orderFourPuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource
          A.starSeparation.orderFour.radius q))).1.re
  generalize hQ : orderFourPuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource
      A.starSeparation.orderFour.radius q = Q
  induction Q using Quotient.inductionOn with
  | _ x =>
      rw [orderFourLinearCollarToPuncturedGlobalFamily_mk]
      change 2 / 3 < (A.modular.sourceCoordinate.coordinate
        (regularTotalSpaceBase A.periods
          (orderFourCollarToRegular A.periods hproper
            A.starSeparation.orderFour.sourceData x)).1).re
      rw [orderFourCollarToRegular_base A.periods hproper hsource
        A.starSeparation.orderFour.sourceData]
      have hx : ‖(orderFourCayleyHomeomorph
          (familyTotalSpaceBase A.periods x) : ℂ)‖ <
          A.starSeparation.orderFour.radius := by
        simpa only [orderFourLinearPuncturedCarrier.eq_def,
          orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderFourFamilyRadius.eq_def] using x.property.2
      have hbound := A.starSeparation.orderFour_coordinate_bound _ hx
      have hre := Complex.abs_re_le_norm
        (A.modular.sourceCoordinate.coordinate (familyTotalSpaceBase A.periods x) - 1)
      simp only [Complex.sub_re, Complex.one_re] at hre
      have hreLower : -‖A.modular.sourceCoordinate.coordinate
          (familyTotalSpaceBase A.periods x) - 1‖ ≤
          (A.modular.sourceCoordinate.coordinate
            (familyTotalSpaceBase A.periods x)).re - 1 :=
        (abs_le.mp hre).1
      linarith

private theorem sectionSevenEllipticCentralImageHomeomorph_of_collar
    (i : Fin 3) (q : A.starCollarSourceType i)
    (x : A.sectionSevenEllipticCentralImage)
    (hx : A.openEmbeddingStarData.collarSourceToGlued i q = x.1.1) :
    A.sectionSevenEllipticCentralImageHomeomorph x = A.starToCentral i q := by
  apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
  apply Subtype.ext
  let y : A.openEmbeddingStarData.SectionSevenEulerCover.piece 0 := ⟨x.1.1, x.2⟩
  have hxy : A.sectionSevenEllipticCentralImageHomeomorph x =
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.symm y := rfl
  calc
    ↑(A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.sectionSevenEllipticCentralImageHomeomorph x)) = y.1 := by
      rw [hxy]
      exact congrArg Subtype.val
        (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.apply_symm_apply y)
    _ = x.1.1 := rfl
    _ = A.openEmbeddingStarData.collarSourceToGlued i q := hx.symm
    _ = ↑(A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral i q)) := by
      let hι :=
        A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding none
      exact (Topology.IsEmbedding.toHomeomorph_apply_coe
        hι.isEmbedding (A.starToCentral i q)).symm

/-- The only separation facts needed to turn the affine half-plane cut into the actual central
allocation. -/
public structure SectionSevenAffineCentralSeparation : Prop where
  orderThreeFilling_disjoint_upper :
    Disjoint A.sectionSevenOrderThreeFillingImage
      (centralHeightUpperRegion A.sectionSevenEllipticCentralHeight (1 / 3 : ℝ))
  orderFourFilling_disjoint_lower :
    Disjoint A.sectionSevenOrderFourFillingImage
      (centralHeightLowerRegion A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ))

/-- The affine bounds built into the selected elliptic collar radii give the required central
separation. -/
public theorem sectionSevenAffineCentralSeparation :
    A.SectionSevenAffineCentralSeparation := by
  constructor
  · rw [Set.disjoint_left]
    rintro x hx₃ ⟨y, hy, rfl⟩
    have hpair : y.1.1 ∈ A.SectionSevenEllipticCover.piece 0 ∩
        A.SectionSevenEllipticCover.piece 1 := ⟨y.2, hx₃⟩
    have hpair' : y.1.1 ∈
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 2 := by
      simpa [SectionSevenEllipticCover,
        OpenEmbeddingStarData.SectionSevenMayerVietorisCover,
        sectionSevenMayerVietorisOpenCover, sectionSevenMayerVietorisOrder] using hpair
    have hrange : Set.range (A.openEmbeddingStarData.collarSourceToGlued 1) =
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 2 := by
      simpa using A.openEmbeddingStarData.range_collarSourceToGlued 1
    rw [← hrange] at hpair'
    obtain ⟨q, hq⟩ := hpair'
    have hcoord := A.orderThreeStarCollar_centralCoordinate_re_lt q
    have hcentral := sectionSevenEllipticCentralImageHomeomorph_of_collar A 1 q y hq
    change 1 / 3 <
      (A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph y)).1.re at hy
    rw [hcentral] at hy
    linarith
  · rw [Set.disjoint_left]
    rintro x hx₄ ⟨y, hy, rfl⟩
    have hpair : y.1.1 ∈ A.SectionSevenEllipticCover.piece 0 ∩
        A.SectionSevenEllipticCover.piece 2 := ⟨y.2, hx₄⟩
    have hpair' : y.1.1 ∈
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 3 := by
      simpa [SectionSevenEllipticCover,
        OpenEmbeddingStarData.SectionSevenMayerVietorisCover,
        sectionSevenMayerVietorisOpenCover, sectionSevenMayerVietorisOrder] using hpair
    have hrange : Set.range (A.openEmbeddingStarData.collarSourceToGlued 2) =
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 3 := by
      simpa using A.openEmbeddingStarData.range_collarSourceToGlued 2
    rw [← hrange] at hpair'
    obtain ⟨q, hq⟩ := hpair'
    have hcoord := A.orderFourStarCollar_twoThirds_lt_centralCoordinate_re q
    have hcentral := sectionSevenEllipticCentralImageHomeomorph_of_collar A 2 q y hq
    change (A.centralFamilyCoordinate
      (A.sectionSevenEllipticCentralImageHomeomorph y)).1.re < 2 / 3 at hy
    rw [hcentral] at hy
    linarith

/-- The overlapping half-planes `re < 2/3` and `1/3 < re` give the concrete central height
split. -/
public noncomputable def sectionSevenAffineCentralHeightSplit
    (S : A.SectionSevenAffineCentralSeparation) :
    A.SectionSevenCentralHeightSplit where
  height := A.sectionSevenEllipticCentralHeight
  height_continuous := A.sectionSevenEllipticCentralHeight_continuous
  lower := 1 / 3
  upper := 2 / 3
  lower_lt_upper := by norm_num
  orderThreeFilling_disjoint_upper := S.orderThreeFilling_disjoint_upper
  orderFourFilling_disjoint_lower := S.orderFourFilling_disjoint_lower

end SphereSixComplex.Geometry.PaperAnalyticData
