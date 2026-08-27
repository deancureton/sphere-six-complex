module

public import SphereSixComplex.Topology.HomotopySplittingIso
public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularLiftCompletionAssembly
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderThreeOverlapIdentification
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderThreeRadialEquivalence
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourOverlapIdentification
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourRadialEquivalence
public import SphereSixComplex.Geometry.PaperCentralEndCover

/-!
# Interleaving the star collars with the affine discs

The order-three star overlap is *not* an affine disc region: the collar is a Cayley disc and the
affine regions are `lambda`-discs, and the two families of shapes never coincide.  What is true,
and all that the affine completion needs, is that the two families *interleave*.  This file
records the point-set dictionary between the star collars and the affine central regions.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open GlobalTorusFamily TorusFamily
open EquivariantQuotientHomeomorph
open SphereSixComplex.TriangleGroup
open SphereSixComplex.OpenUnionHomotopy
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticAffineGlobalSeparation
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- A collar point sits inside the glued space exactly at its central-family image. -/
public theorem centralToSectionSevenEulerPiece_starToCentral (i : Fin 3)
    (q : A.starCollarSourceType i) :
    (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.starToCentral i q)).1 =
      A.openEmbeddingStarData.collarSourceToGlued i q := by
  let hι := A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding none
  exact (Topology.IsEmbedding.toHomeomorph_apply_coe hι.isEmbedding (A.starToCentral i q))

/-- A central-image point sits inside the glued space at its own underlying point. -/
public theorem centralToSectionSevenEulerPiece_centralImage
    (x : A.sectionSevenEllipticCentralImage) :
    (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
        (A.sectionSevenEllipticCentralImageHomeomorph x)).1 = x.1.1 :=
  congrArg Subtype.val
    (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.apply_symm_apply
      ⟨x.1.1, x.2⟩)

/-- The central-image homeomorphism identifies the collar points of the elliptic interior with
the collar range inside the actual central family. -/
public theorem mem_orderThreeFillingImage_iff_mem_starToCentral_range
    (x : A.sectionSevenEllipticCentralImage) :
    x.1 ∈ A.sectionSevenOrderThreeFillingImage ↔
      A.sectionSevenEllipticCentralImageHomeomorph x ∈ Set.range (A.starToCentral (1 : Fin 3)) := by
  have hrange : Set.range (A.openEmbeddingStarData.collarSourceToGlued 1) =
      (sectionSevenStarOpenCover
        A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
      (sectionSevenStarOpenCover
        A.openEmbeddingStarData.toFourPieceStarGluingData).piece 2 := by
    simpa using A.openEmbeddingStarData.range_collarSourceToGlued 1
  constructor
  · intro hx
    have hpair : x.1.1 ∈ A.SectionSevenEllipticCover.piece 0 ∩
        A.SectionSevenEllipticCover.piece 1 := ⟨x.2, hx⟩
    have hpair' : x.1.1 ∈
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 2 := by
      simpa [SectionSevenEllipticCover,
        OpenEmbeddingStarData.SectionSevenMayerVietorisCover,
        sectionSevenMayerVietorisOpenCover, sectionSevenMayerVietorisOrder] using hpair
    rw [← hrange] at hpair'
    obtain ⟨q, hq⟩ := hpair'
    refine ⟨q, ?_⟩
    apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
    apply Subtype.ext
    rw [A.centralToSectionSevenEulerPiece_starToCentral 1 q,
      A.centralToSectionSevenEulerPiece_centralImage x, hq]
  · rintro ⟨q, hq⟩
    have hglued : A.openEmbeddingStarData.collarSourceToGlued 1 q = x.1.1 := by
      rw [← A.centralToSectionSevenEulerPiece_starToCentral 1 q, hq,
        A.centralToSectionSevenEulerPiece_centralImage x]
    have hmem : x.1.1 ∈ Set.range (A.openEmbeddingStarData.collarSourceToGlued 1) := ⟨q, hglued⟩
    rw [hrange] at hmem
    have hpair : x.1.1 ∈ A.SectionSevenEllipticCover.piece 0 ∩
        A.SectionSevenEllipticCover.piece 1 := by
      simpa [SectionSevenEllipticCover,
        OpenEmbeddingStarData.SectionSevenMayerVietorisCover,
        sectionSevenMayerVietorisOpenCover, sectionSevenMayerVietorisOrder] using hmem
    exact hpair.2


/-- The selected order-three collar lies over the affine disc of radius `1/3`.  This is the norm
form of `orderThreeStarCollar_centralCoordinate_re_lt`. -/
public theorem orderThreeStarCollar_centralCoordinate_norm_lt
    (q : A.starCollarSourceType (1 : Fin 3)) :
    ‖(A.centralFamilyCoordinate (A.starToCentral 1 q)).1‖ < 1 / 3 := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = SphereSixComplex.TriangleGroup.fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  change ‖(A.centralFamilyCoordinate
    (orderThreeLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      A.starSeparation.orderThree.sourceData
        (orderThreePuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource
          A.starSeparation.orderThree.radius q))).1‖ < 1 / 3
  generalize hQ : orderThreePuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource
      A.starSeparation.orderThree.radius q = Q
  induction Q using Quotient.inductionOn with
  | _ x =>
      rw [orderThreeLinearCollarToPuncturedGlobalFamily_mk]
      change ‖A.modular.sourceCoordinate.coordinate
        (regularTotalSpaceBase A.periods
          (orderThreeCollarToRegular A.periods hproper
            A.starSeparation.orderThree.sourceData x)).1‖ < 1 / 3
      rw [orderThreeCollarToRegular_base A.periods hproper hsource
        A.starSeparation.orderThree.sourceData]
      have hx : ‖(orderThreeCayleyHomeomorph
          (familyTotalSpaceBase A.periods x) : ℂ)‖ <
          A.starSeparation.orderThree.radius := by
        simpa only [orderThreeLinearPuncturedCarrier.eq_def,
          orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderThreeFamilyRadius.eq_def] using x.property.2
      exact A.starSeparation.orderThree_coordinate_bound _ hx

/-- Outer interleaving step: the actual order-three star overlap is contained in the affine disc
region of radius `1/3`. -/
public theorem orderThreeOverlap_subset_discRegion :
    A.sectionSevenOrderThreeFillingImage ∩ A.sectionSevenAffineOrderThreeCentralRegion ⊆
      A.sectionSevenAffineOrderThreeDiscRegion (1 / 3) := by
  intro x hx
  have hmem : x ∈ A.sectionSevenEllipticCentralImage :=
    A.mem_centralImage_of_mem_centralHeightLowerRegion
      A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) hx.2
  obtain ⟨q, hq⟩ :=
    (A.mem_orderThreeFillingImage_iff_mem_starToCentral_range ⟨x, hmem⟩).mp hx.1
  refine ⟨⟨x, hmem⟩, ?_, rfl⟩
  show A.sectionSevenEllipticCentralRadius ⟨x, hmem⟩ < 1 / 3
  change ‖(A.centralFamilyCoordinate
    (A.sectionSevenEllipticCentralImageHomeomorph ⟨x, hmem⟩)).1‖ < 1 / 3
  rw [← hq]
  exact A.orderThreeStarCollar_centralCoordinate_norm_lt q

/-- Inner interleaving step: some affine disc region is contained in the actual order-three star
overlap.  This is the exact `lambda`-small implies `Cayley`-small escape statement, supplied by
the central end cover. -/
public theorem exists_discRegion_subset_orderThreeOverlap :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 3 ∧
      A.sectionSevenAffineOrderThreeDiscRegion a ⊆
        A.sectionSevenOrderThreeFillingImage ∩ A.sectionSevenAffineOrderThreeCentralRegion := by
  set s := A.starSeparation.orderThree.radius with hs
  have hspos : 0 < s := A.starSeparation.orderThree.radius_pos
  obtain ⟨δ, hδ, hball⟩ := A.exists_orderThree_coordinate_radius (s / 2) (by positivity)
  refine ⟨min δ (1 / 3), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hnorm : ‖(A.centralFamilyCoordinate
      (A.sectionSevenEllipticCentralImageHomeomorph y)).1‖ < min δ (1 / 3) := hy
  obtain ⟨Q, hQ⟩ := A.centralQuotientProjection_surjective
    (A.sectionSevenEllipticCentralImageHomeomorph y)
  have hcoord : ‖A.modular.sourceCoordinate.coordinate
      (regularTotalSpaceBase A.periods Q).1‖ < δ := by
    have := hnorm.trans_le (min_le_left _ _)
    rwa [← hQ, A.centralFamilyCoordinate_centralQuotientProjection] at this
  obtain ⟨g, hg⟩ := hball (regularTotalSpaceBase A.periods Q).1 hcoord
  obtain ⟨z, hz, -⟩ := A.exists_orderThree_starCollar_of_baseRadius Q g (s / 2) hg
    (by linarith)
  have hrange : A.sectionSevenEllipticCentralImageHomeomorph y ∈
      Set.range (A.starToCentral (1 : Fin 3)) := ⟨z, by rw [hz, hQ]⟩
  refine ⟨(A.mem_orderThreeFillingImage_iff_mem_starToCentral_range y).mpr hrange, ?_⟩
  refine ⟨y, ?_, rfl⟩
  show A.sectionSevenEllipticCentralHeight y < 2 / 3
  have hre : (A.centralFamilyCoordinate
      (A.sectionSevenEllipticCentralImageHomeomorph y)).1.re ≤
      ‖(A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph y)).1‖ :=
    Complex.re_le_norm _
  have hlt := hnorm.trans_le (min_le_right _ _)
  change (A.centralFamilyCoordinate
    (A.sectionSevenEllipticCentralImageHomeomorph y)).1.re < 2 / 3
  linarith


/-- The inclusion of one subset into a larger one, as a bundled continuous map. -/
public def regionInclusion {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s ⊆ t) :
    C(↥s, ↥t) :=
  ⟨fun x ↦ ⟨x.1, h x.2⟩, by fun_prop⟩

/-- Affine disc regions of radius at most `2/3` lie in the order-three central region. -/
public theorem discRegion_subset_centralRegion {r : ℝ} (hr : r ≤ 2 / 3) :
    A.sectionSevenAffineOrderThreeDiscRegion r ⊆
      A.sectionSevenAffineOrderThreeCentralRegion := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  have hnorm : ‖(A.centralFamilyCoordinate
      (A.sectionSevenEllipticCentralImageHomeomorph y)).1‖ < r := hy
  have hre : (A.centralFamilyCoordinate
      (A.sectionSevenEllipticCentralImageHomeomorph y)).1.re ≤
      ‖(A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph y)).1‖ :=
    Complex.re_le_norm _
  show A.sectionSevenEllipticCentralHeight y < 2 / 3
  change (A.centralFamilyCoordinate
    (A.sectionSevenEllipticCentralImageHomeomorph y)).1.re < 2 / 3
  linarith

/-- The affine disc region of any positive radius at most `2/3` includes into the order-three
central region by a homotopy equivalence.  This is the proved lifted radial transport, descended
through the full deck action and transported to the two named region models. -/
public theorem discRegionInclusion_isHomotopyEquivalence {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 2 / 3) :
    IsHomotopyEquivalence
      ((regionInclusion (A.discRegion_subset_centralRegion hr) :
        C(↥(A.sectionSevenAffineOrderThreeDiscRegion r),
          ↥A.sectionSevenAffineOrderThreeCentralRegion)) :
        ↥(A.sectionSevenAffineOrderThreeDiscRegion r) →
          ↥A.sectionSevenAffineOrderThreeCentralRegion) := by
  obtain ⟨E, hE⟩ := A.exists_orderThreeAffineRadialEquiv hr0 hr
  refine E.isHomotopyEquivalence_of_quotient_models _
    (A.sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r)
    A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph ?_
    (A.orderThreeAffineDiscLiftAction_continuous r)
    A.orderThreeAffineHalfPlaneLiftAction_continuous
  funext x
  apply A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.injective
  rw [Function.comp_apply, Function.comp_apply,
    A.quotientToFun_eq_orderThreeAffineDiscLiftQuotientInclusion hr E hE,
    A.toCentralFamily_orderThreeAffineDiscLiftQuotientInclusion hr,
    A.toCentralFamily_sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r,
    A.toCentralFamily_sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph]
  rfl

/-- Nested affine disc regions include into one another by homotopy equivalences. -/
public theorem discRegionInclusion_mono_isHomotopyEquivalence
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb : b ≤ 2 / 3)
    (hsub : A.sectionSevenAffineOrderThreeDiscRegion a ⊆
      A.sectionSevenAffineOrderThreeDiscRegion b) :
    IsHomotopyEquivalence
      ((regionInclusion hsub : C(↥(A.sectionSevenAffineOrderThreeDiscRegion a),
        ↥(A.sectionSevenAffineOrderThreeDiscRegion b))) :
        ↥(A.sectionSevenAffineOrderThreeDiscRegion a) →
          ↥(A.sectionSevenAffineOrderThreeDiscRegion b)) := by
  refine SphereSixComplex.isHomotopyEquivalence_of_comp_left
    (f := regionInclusion hsub)
    (g := regionInclusion (A.discRegion_subset_centralRegion hb)) ?_
    (A.discRegionInclusion_isHomotopyEquivalence (ha0.trans_le hab) hb)
  exact A.discRegionInclusion_isHomotopyEquivalence ha0 (hab.trans hb)

/-- Monotonicity of the affine disc regions. -/
public theorem discRegion_mono {a b : ℝ} (hab : a ≤ b) :
    A.sectionSevenAffineOrderThreeDiscRegion a ⊆
      A.sectionSevenAffineOrderThreeDiscRegion b := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, lt_of_lt_of_le hy hab, rfl⟩

/-- **Interleaving reduction.**  The order-three overlap inclusion is a homotopy equivalence as
soon as the overlap admits a self-homotopy into one small affine disc region sitting inside it.
Every other ingredient — the two long affine radial equivalences and the two interleaving set
inclusions — is proved.

The remaining input `hshrink` is exactly a radial shrinking of the Cayley star collar towards its
elliptic centre; no identification of the collar with an affine disc region is required, and in
particular the false set equality forced by the overlap quotient structures is avoided. -/
public theorem orderThreeOverlapIsHomotopyEquivalence_of_shrink
    {a : ℝ} (ha0 : 0 < a) (ha3 : a ≤ 1 / 3)
    (hsub : A.sectionSevenAffineOrderThreeDiscRegion a ⊆
      A.sectionSevenOrderThreeFillingImage ∩ A.sectionSevenAffineOrderThreeCentralRegion)
    (shrink : C(↥(A.sectionSevenOrderThreeFillingImage ∩
        A.sectionSevenAffineOrderThreeCentralRegion),
      ↥(A.sectionSevenAffineOrderThreeDiscRegion a)))
    (hshrink : (((regionInclusion hsub).comp shrink :
      C(↥(A.sectionSevenOrderThreeFillingImage ∩
          A.sectionSevenAffineOrderThreeCentralRegion),
        ↥(A.sectionSevenOrderThreeFillingImage ∩
          A.sectionSevenAffineOrderThreeCentralRegion)))).Homotopic
      (ContinuousMap.id _)) :
    IsHomotopyEquivalence (interToRight A.sectionSevenOrderThreeFillingImage
      A.sectionSevenAffineOrderThreeCentralRegion).hom := by
  have hOuter : A.sectionSevenOrderThreeFillingImage ∩
      A.sectionSevenAffineOrderThreeCentralRegion ⊆
      A.sectionSevenAffineOrderThreeDiscRegion (1 / 3) :=
    A.orderThreeOverlap_subset_discRegion
  have hgf : IsHomotopyEquivalence
      (((regionInclusion hsub).comp shrink :
        C(↥(A.sectionSevenOrderThreeFillingImage ∩
            A.sectionSevenAffineOrderThreeCentralRegion),
          ↥(A.sectionSevenOrderThreeFillingImage ∩
            A.sectionSevenAffineOrderThreeCentralRegion))) :
        ↥(A.sectionSevenOrderThreeFillingImage ∩
          A.sectionSevenAffineOrderThreeCentralRegion) →
          ↥(A.sectionSevenOrderThreeFillingImage ∩
            A.sectionSevenAffineOrderThreeCentralRegion)) :=
    SphereSixComplex.isHomotopyEquivalence_of_homotopic hshrink
      SphereSixComplex.isHomotopyEquivalence_id
  have hhg : IsHomotopyEquivalence
      ((((regionInclusion hOuter).comp (regionInclusion hsub)) :
        C(↥(A.sectionSevenAffineOrderThreeDiscRegion a),
          ↥(A.sectionSevenAffineOrderThreeDiscRegion (1 / 3)))) :
        ↥(A.sectionSevenAffineOrderThreeDiscRegion a) →
          ↥(A.sectionSevenAffineOrderThreeDiscRegion (1 / 3))) :=
    A.discRegionInclusion_mono_isHomotopyEquivalence ha0 ha3 (by norm_num)
      (A.discRegion_mono ha3)
  have hmid : IsHomotopyEquivalence
      ((regionInclusion hOuter : C(↥(A.sectionSevenOrderThreeFillingImage ∩
          A.sectionSevenAffineOrderThreeCentralRegion),
        ↥(A.sectionSevenAffineOrderThreeDiscRegion (1 / 3)))) :
        ↥(A.sectionSevenOrderThreeFillingImage ∩
          A.sectionSevenAffineOrderThreeCentralRegion) →
          ↥(A.sectionSevenAffineOrderThreeDiscRegion (1 / 3))) :=
    SphereSixComplex.isHomotopyEquivalence_last_of_interleaving
      shrink (regionInclusion hsub) (regionInclusion hOuter) hgf hhg
  exact (A.discRegionInclusion_isHomotopyEquivalence (r := 1 / 3) (by norm_num)
    (by norm_num)).comp hmid


/-! ## The order-four side -/

/-- The order-four affine disc region at `1`, inside the regular central image. -/
public noncomputable def sectionSevenAffineOrderFourDiscRegion (r : ℝ) :
    Set A.SectionSevenEllipticInterior :=
  centralHeightLowerRegion
    (fun z ↦ ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖) r

public theorem orderFourAffineDiscLiftQuotientToCentralFamily_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderFourAffineDiscLiftQuotientToCentralFamily r) :=
  restrictedOrbitQuotientInclusion_isOpenEmbedding _ _ A.regularFamilyDeckAction_continuous

/-- The order-four lifted affine disc quotient is exactly its open image in the central family. -/
public noncomputable def orderFourAffineDiscLiftQuotientHomeomorphRange (r : ℝ) :
    Quotient (orbitRelOf (A.orderFourAffineDiscLiftAction r)) ≃ₜ
      Set.range (A.orderFourAffineDiscLiftQuotientToCentralFamily r) :=
  (A.orderFourAffineDiscLiftQuotientToCentralFamily_isOpenEmbedding r).isEmbedding.toHomeomorph

/-- The order-four affine disc region, expressed as the quotient of its full-deck-action lift. -/
public noncomputable def sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph (r : ℝ) :
    ↥(A.sectionSevenAffineOrderFourDiscRegion r) ≃ₜ
      Quotient (orbitRelOf (A.orderFourAffineDiscLiftAction r)) :=
  (centralHeightLowerRegionHomeomorph A
      (fun z ↦ ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖) r).symm |>.trans
    (A.sectionSevenEllipticCentralImageHomeomorph.subtype fun _ ↦ Iff.rfl) |>.trans
    (Homeomorph.setCongr
      (A.range_orderFourAffineDiscLiftQuotientToCentralFamily r).symm) |>.trans
    (A.orderFourAffineDiscLiftQuotientHomeomorphRange r).symm

public theorem toCentralFamily_orderFourAffineDiscLiftQuotientHomeomorphRange_symm (r : ℝ)
    (c : Set.range (A.orderFourAffineDiscLiftQuotientToCentralFamily r)) :
    A.orderFourAffineDiscLiftQuotientToCentralFamily r
        ((A.orderFourAffineDiscLiftQuotientHomeomorphRange r).symm c) = c.1 :=
  congrArg Subtype.val
    ((A.orderFourAffineDiscLiftQuotientHomeomorphRange r).apply_symm_apply c)

/-- The order-four disc-region quotient model is compatible with the central-family
coordinates. -/
public theorem toCentralFamily_sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph
    (r : ℝ) (x : ↥(A.sectionSevenAffineOrderFourDiscRegion r)) :
    A.orderFourAffineDiscLiftQuotientToCentralFamily r
        (A.sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph r x) =
      A.sectionSevenEllipticCentralImageHomeomorph
        ⟨x.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
          (fun z ↦ ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖) r x.2⟩ := by
  refine (A.toCentralFamily_orderFourAffineDiscLiftQuotientHomeomorphRange_symm r _).trans ?_
  exact congrArg A.sectionSevenEllipticCentralImageHomeomorph
    (Subtype.ext (A.coe_centralHeightLowerRegionHomeomorph_symm
      (fun z ↦ ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖) r x))

/-- Order-four affine disc regions of radius at most `1 - 1/3` lie in the order-four central
region. -/
public theorem orderFourDiscRegion_subset_centralRegion {r : ℝ} (hr : r ≤ 1 - 1 / 3) :
    A.sectionSevenAffineOrderFourDiscRegion r ⊆
      A.sectionSevenAffineOrderFourCentralRegion := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  have hnorm : ‖(A.sectionSevenEllipticCentralCoordinate y).1 - 1‖ < r := hy
  have hre := Complex.abs_re_le_norm ((A.sectionSevenEllipticCentralCoordinate y).1 - 1)
  simp only [Complex.sub_re, Complex.one_re] at hre
  have hlow : -‖(A.sectionSevenEllipticCentralCoordinate y).1 - 1‖ ≤
      (A.sectionSevenEllipticCentralCoordinate y).1.re - 1 := (abs_le.mp hre).1
  show (1 : ℝ) / 3 < A.sectionSevenEllipticCentralHeight y
  change (1 : ℝ) / 3 < (A.sectionSevenEllipticCentralCoordinate y).1.re
  linarith

/-- The order-four disc region includes into the order-four central region by a homotopy
equivalence. -/
public theorem orderFourDiscRegionInclusion_isHomotopyEquivalence
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3) :
    IsHomotopyEquivalence
      ((regionInclusion (A.orderFourDiscRegion_subset_centralRegion hr) :
        C(↥(A.sectionSevenAffineOrderFourDiscRegion r),
          ↥A.sectionSevenAffineOrderFourCentralRegion)) :
        ↥(A.sectionSevenAffineOrderFourDiscRegion r) →
          ↥A.sectionSevenAffineOrderFourCentralRegion) := by
  obtain ⟨E, hE⟩ := A.exists_orderFourAffineRadialEquiv hr0 hr
  refine E.isHomotopyEquivalence_of_quotient_models _
    (A.sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph r)
    A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph ?_
    (A.orderFourAffineDiscLiftAction_continuous r)
    A.orderFourAffineHalfPlaneLiftAction_continuous
  funext u
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
  rw [Function.comp_apply, Function.comp_apply, hleft,
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_centralRegionQuotient
      ⟨u.1, hmem⟩ hheight,
    A.quotientToFun_eq_orderFourAffineDiscLiftQuotientInclusion hr E hE,
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_discInclusion hr,
    A.toCentralFamily_sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph r]

/-- Monotonicity of the order-four affine disc regions. -/
public theorem orderFourDiscRegion_mono {a b : ℝ} (hab : a ≤ b) :
    A.sectionSevenAffineOrderFourDiscRegion a ⊆
      A.sectionSevenAffineOrderFourDiscRegion b := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, lt_of_lt_of_le hy hab, rfl⟩

/-- Nested order-four affine disc regions include into one another by homotopy equivalences. -/
public theorem orderFourDiscRegionInclusion_mono_isHomotopyEquivalence
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 - 1 / 3)
    (hsub : A.sectionSevenAffineOrderFourDiscRegion a ⊆
      A.sectionSevenAffineOrderFourDiscRegion b) :
    IsHomotopyEquivalence
      ((regionInclusion hsub : C(↥(A.sectionSevenAffineOrderFourDiscRegion a),
        ↥(A.sectionSevenAffineOrderFourDiscRegion b))) :
        ↥(A.sectionSevenAffineOrderFourDiscRegion a) →
          ↥(A.sectionSevenAffineOrderFourDiscRegion b)) := by
  refine SphereSixComplex.isHomotopyEquivalence_of_comp_left
    (f := regionInclusion hsub)
    (g := regionInclusion (A.orderFourDiscRegion_subset_centralRegion hb)) ?_
    (A.orderFourDiscRegionInclusion_isHomotopyEquivalence (ha0.trans_le hab) hb)
  exact A.orderFourDiscRegionInclusion_isHomotopyEquivalence ha0 (hab.trans hb)


public theorem mem_centralImage_of_mem_centralHeightUpperRegion
    (height : A.sectionSevenEllipticCentralImage → ℝ) (lower : ℝ)
    {x : A.SectionSevenEllipticInterior}
    (hx : x ∈ centralHeightUpperRegion height lower) :
    x ∈ A.sectionSevenEllipticCentralImage := by
  obtain ⟨y, _, rfl⟩ := hx
  exact y.2

/-- The central-image homeomorphism identifies the order-four collar points of the elliptic
interior with the order-four collar range inside the actual central family. -/
public theorem mem_orderFourFillingImage_iff_mem_starToCentral_range
    (x : A.sectionSevenEllipticCentralImage) :
    x.1 ∈ A.sectionSevenOrderFourFillingImage ↔
      A.sectionSevenEllipticCentralImageHomeomorph x ∈
        Set.range (A.starToCentral (2 : Fin 3)) := by
  have hrange : Set.range (A.openEmbeddingStarData.collarSourceToGlued 2) =
      (sectionSevenStarOpenCover
        A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
      (sectionSevenStarOpenCover
        A.openEmbeddingStarData.toFourPieceStarGluingData).piece 3 := by
    simpa using A.openEmbeddingStarData.range_collarSourceToGlued 2
  constructor
  · intro hx
    have hpair : x.1.1 ∈ A.SectionSevenEllipticCover.piece 0 ∩
        A.SectionSevenEllipticCover.piece 2 := ⟨x.2, hx⟩
    have hpair' : x.1.1 ∈
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 0 ∩
        (sectionSevenStarOpenCover
          A.openEmbeddingStarData.toFourPieceStarGluingData).piece 3 := by
      simpa [SectionSevenEllipticCover,
        OpenEmbeddingStarData.SectionSevenMayerVietorisCover,
        sectionSevenMayerVietorisOpenCover, sectionSevenMayerVietorisOrder] using hpair
    rw [← hrange] at hpair'
    obtain ⟨q, hq⟩ := hpair'
    refine ⟨q, ?_⟩
    apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
    apply Subtype.ext
    rw [A.centralToSectionSevenEulerPiece_starToCentral 2 q,
      A.centralToSectionSevenEulerPiece_centralImage x, hq]
  · rintro ⟨q, hq⟩
    have hglued : A.openEmbeddingStarData.collarSourceToGlued 2 q = x.1.1 := by
      rw [← A.centralToSectionSevenEulerPiece_starToCentral 2 q, hq,
        A.centralToSectionSevenEulerPiece_centralImage x]
    have hmem : x.1.1 ∈ Set.range (A.openEmbeddingStarData.collarSourceToGlued 2) := ⟨q, hglued⟩
    rw [hrange] at hmem
    have hpair : x.1.1 ∈ A.SectionSevenEllipticCover.piece 0 ∩
        A.SectionSevenEllipticCover.piece 2 := by
      simpa [SectionSevenEllipticCover,
        OpenEmbeddingStarData.SectionSevenMayerVietorisCover,
        sectionSevenMayerVietorisOpenCover, sectionSevenMayerVietorisOrder] using hmem
    exact hpair.2

/-- The selected order-four collar lies over the affine disc of radius `1/3` centred at `1`. -/
public theorem orderFourStarCollar_centralCoordinate_norm_lt
    (q : A.starCollarSourceType (2 : Fin 3)) :
    ‖(A.centralFamilyCoordinate (A.starToCentral 2 q)).1 - 1‖ < 1 / 3 := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = SphereSixComplex.TriangleGroup.fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  change ‖(A.centralFamilyCoordinate
    (orderFourLinearCollarToPuncturedGlobalFamily A.periods hproper hsource
      A.starSeparation.orderFour.sourceData
        (orderFourPuncturedCollarQuotientHomeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph hsource
          A.starSeparation.orderFour.radius q))).1 - 1‖ < 1 / 3
  generalize hQ : orderFourPuncturedCollarQuotientHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph hsource
      A.starSeparation.orderFour.radius q = Q
  induction Q using Quotient.inductionOn with
  | _ x =>
      rw [orderFourLinearCollarToPuncturedGlobalFamily_mk]
      change ‖A.modular.sourceCoordinate.coordinate
        (regularTotalSpaceBase A.periods
          (orderFourCollarToRegular A.periods hproper
            A.starSeparation.orderFour.sourceData x)).1 - 1‖ < 1 / 3
      rw [orderFourCollarToRegular_base A.periods hproper hsource
        A.starSeparation.orderFour.sourceData]
      have hx : ‖(orderFourCayleyHomeomorph
          (familyTotalSpaceBase A.periods x) : ℂ)‖ <
          A.starSeparation.orderFour.radius := by
        simpa only [orderFourLinearPuncturedCarrier.eq_def,
          orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderFourFamilyRadius.eq_def] using x.property.2
      exact A.starSeparation.orderFour_coordinate_bound _ hx

/-- Outer interleaving step on the order-four side. -/
public theorem orderFourOverlap_subset_discRegion :
    A.sectionSevenOrderFourFillingImage ∩ A.sectionSevenAffineOrderFourCentralRegion ⊆
      A.sectionSevenAffineOrderFourDiscRegion (1 / 3) := by
  intro x hx
  have hmem : x ∈ A.sectionSevenEllipticCentralImage :=
    A.mem_centralImage_of_mem_centralHeightUpperRegion
      A.sectionSevenEllipticCentralHeight (1 / 3 : ℝ) hx.2
  obtain ⟨q, hq⟩ :=
    (A.mem_orderFourFillingImage_iff_mem_starToCentral_range ⟨x, hmem⟩).mp hx.1
  refine ⟨⟨x, hmem⟩, ?_, rfl⟩
  show ‖(A.sectionSevenEllipticCentralCoordinate ⟨x, hmem⟩).1 - 1‖ < 1 / 3
  change ‖(A.centralFamilyCoordinate
    (A.sectionSevenEllipticCentralImageHomeomorph ⟨x, hmem⟩)).1 - 1‖ < 1 / 3
  rw [← hq]
  exact A.orderFourStarCollar_centralCoordinate_norm_lt q

/-- Inner interleaving step on the order-four side. -/
public theorem exists_discRegion_subset_orderFourOverlap :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 3 ∧
      A.sectionSevenAffineOrderFourDiscRegion a ⊆
        A.sectionSevenOrderFourFillingImage ∩ A.sectionSevenAffineOrderFourCentralRegion := by
  set s := A.starSeparation.orderFour.radius with hs
  have hspos : 0 < s := A.starSeparation.orderFour.radius_pos
  obtain ⟨δ, hδ, hball⟩ := A.exists_orderFour_coordinate_radius (s / 2) (by positivity)
  refine ⟨min δ (1 / 3), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hnorm : ‖(A.centralFamilyCoordinate
      (A.sectionSevenEllipticCentralImageHomeomorph y)).1 - 1‖ < min δ (1 / 3) := hy
  obtain ⟨Q, hQ⟩ := A.centralQuotientProjection_surjective
    (A.sectionSevenEllipticCentralImageHomeomorph y)
  have hcoord : ‖A.modular.sourceCoordinate.coordinate
      (regularTotalSpaceBase A.periods Q).1 - 1‖ < δ := by
    have := hnorm.trans_le (min_le_left _ _)
    rwa [← hQ, A.centralFamilyCoordinate_centralQuotientProjection] at this
  obtain ⟨g, hg⟩ := hball (regularTotalSpaceBase A.periods Q).1 hcoord
  obtain ⟨z, hz, -⟩ := A.exists_orderFour_starCollar_of_baseRadius Q g (s / 2) hg
    (by linarith)
  have hrange : A.sectionSevenEllipticCentralImageHomeomorph y ∈
      Set.range (A.starToCentral (2 : Fin 3)) := ⟨z, by rw [hz, hQ]⟩
  refine ⟨(A.mem_orderFourFillingImage_iff_mem_starToCentral_range y).mpr hrange, ?_⟩
  refine ⟨y, ?_, rfl⟩
  have hlt := hnorm.trans_le (min_le_right _ _)
  have hre := Complex.abs_re_le_norm
    ((A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph y)).1 - 1)
  simp only [Complex.sub_re, Complex.one_re] at hre
  have hlow : -‖(A.centralFamilyCoordinate
      (A.sectionSevenEllipticCentralImageHomeomorph y)).1 - 1‖ ≤
      (A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph y)).1.re - 1 :=
    (abs_le.mp hre).1
  show (1 : ℝ) / 3 < A.sectionSevenEllipticCentralHeight y
  change (1 : ℝ) / 3 <
    (A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph y)).1.re
  linarith

/-- **Interleaving reduction, order-four side.** -/
public theorem orderFourOverlapIsHomotopyEquivalence_of_shrink
    {a : ℝ} (ha0 : 0 < a) (ha3 : a ≤ 1 / 3)
    (hsub : A.sectionSevenAffineOrderFourDiscRegion a ⊆
      A.sectionSevenOrderFourFillingImage ∩ A.sectionSevenAffineOrderFourCentralRegion)
    (shrink : C(↥(A.sectionSevenOrderFourFillingImage ∩
        A.sectionSevenAffineOrderFourCentralRegion),
      ↥(A.sectionSevenAffineOrderFourDiscRegion a)))
    (hshrink : (((regionInclusion hsub).comp shrink :
      C(↥(A.sectionSevenOrderFourFillingImage ∩
          A.sectionSevenAffineOrderFourCentralRegion),
        ↥(A.sectionSevenOrderFourFillingImage ∩
          A.sectionSevenAffineOrderFourCentralRegion)))).Homotopic
      (ContinuousMap.id _)) :
    IsHomotopyEquivalence (interToRight A.sectionSevenOrderFourFillingImage
      A.sectionSevenAffineOrderFourCentralRegion).hom := by
  have hOuter : A.sectionSevenOrderFourFillingImage ∩
      A.sectionSevenAffineOrderFourCentralRegion ⊆
      A.sectionSevenAffineOrderFourDiscRegion (1 / 3) :=
    A.orderFourOverlap_subset_discRegion
  have hgf : IsHomotopyEquivalence
      (((regionInclusion hsub).comp shrink :
        C(↥(A.sectionSevenOrderFourFillingImage ∩
            A.sectionSevenAffineOrderFourCentralRegion),
          ↥(A.sectionSevenOrderFourFillingImage ∩
            A.sectionSevenAffineOrderFourCentralRegion))) :
        ↥(A.sectionSevenOrderFourFillingImage ∩
          A.sectionSevenAffineOrderFourCentralRegion) →
          ↥(A.sectionSevenOrderFourFillingImage ∩
            A.sectionSevenAffineOrderFourCentralRegion)) :=
    SphereSixComplex.isHomotopyEquivalence_of_homotopic hshrink
      SphereSixComplex.isHomotopyEquivalence_id
  have hhg : IsHomotopyEquivalence
      ((((regionInclusion hOuter).comp (regionInclusion hsub)) :
        C(↥(A.sectionSevenAffineOrderFourDiscRegion a),
          ↥(A.sectionSevenAffineOrderFourDiscRegion (1 / 3)))) :
        ↥(A.sectionSevenAffineOrderFourDiscRegion a) →
          ↥(A.sectionSevenAffineOrderFourDiscRegion (1 / 3))) :=
    A.orderFourDiscRegionInclusion_mono_isHomotopyEquivalence ha0 ha3 (by norm_num)
      (A.orderFourDiscRegion_mono ha3)
  have hmid : IsHomotopyEquivalence
      ((regionInclusion hOuter : C(↥(A.sectionSevenOrderFourFillingImage ∩
          A.sectionSevenAffineOrderFourCentralRegion),
        ↥(A.sectionSevenAffineOrderFourDiscRegion (1 / 3)))) :
        ↥(A.sectionSevenOrderFourFillingImage ∩
          A.sectionSevenAffineOrderFourCentralRegion) →
          ↥(A.sectionSevenAffineOrderFourDiscRegion (1 / 3))) :=
    SphereSixComplex.isHomotopyEquivalence_last_of_interleaving
      shrink (regionInclusion hsub) (regionInclusion hOuter) hgf hhg
  exact (A.orderFourDiscRegionInclusion_isHomotopyEquivalence (r := 1 / 3) (by norm_num)
    (by norm_num)).comp hmid

/-! ## The order-three overlap is the order-three star collar

The set-level dictionary is promoted to an explicit homeomorphism.  This is what lets a radial
shrinking of the collar be read as a self-map of the overlap. -/

/-- A central-image point of the order-three filling image already lies in the order-three
central region: the selected collar is trapped in `‖lambda‖ < 1/3`. -/
public theorem mem_orderThreeCentralRegion_of_mem_fillingImage
    (x : A.sectionSevenEllipticCentralImage)
    (hx : x.1 ∈ A.sectionSevenOrderThreeFillingImage) :
    x.1 ∈ A.sectionSevenAffineOrderThreeCentralRegion := by
  obtain ⟨q, hq⟩ := (A.mem_orderThreeFillingImage_iff_mem_starToCentral_range x).mp hx
  refine ⟨x, ?_, rfl⟩
  show A.sectionSevenEllipticCentralHeight x < 2 / 3
  change (A.centralFamilyCoordinate
    (A.sectionSevenEllipticCentralImageHomeomorph x)).1.re < 2 / 3
  rw [← hq]
  have hnorm := A.orderThreeStarCollar_centralCoordinate_norm_lt q
  have hre := Complex.re_le_norm (A.centralFamilyCoordinate (A.starToCentral 1 q)).1
  linarith

/-- The order-three star overlap, as a subspace of the elliptic interior, is exactly the
order-three star collar quotient. -/
public noncomputable def orderThreeOverlapCollarHomeomorph :
    ↥(A.sectionSevenOrderThreeFillingImage ∩
        A.sectionSevenAffineOrderThreeCentralRegion) ≃ₜ
      A.starCollarSourceType (1 : Fin 3) :=
  let e₁ : ↥(A.sectionSevenOrderThreeFillingImage ∩
      A.sectionSevenAffineOrderThreeCentralRegion) ≃ₜ
      {x : A.sectionSevenEllipticCentralImage //
        x.1 ∈ A.sectionSevenOrderThreeFillingImage} :=
    { toFun := fun u ↦ ⟨⟨u.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
        A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) u.2.2⟩, u.2.1⟩
      invFun := fun v ↦ ⟨v.1.1,
        ⟨v.2, A.mem_orderThreeCentralRegion_of_mem_fillingImage v.1 v.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let e₂ := A.sectionSevenEllipticCentralImageHomeomorph.subtype
    A.mem_orderThreeFillingImage_iff_mem_starToCentral_range
  let e₃ := (A.starToCentral_isOpenEmbedding (1 : Fin 3)).isEmbedding.toHomeomorph
  e₁.trans (e₂.trans e₃.symm)

/-- The overlap-to-collar homeomorphism is compatible with the central-family coordinates. -/
public theorem starToCentral_orderThreeOverlapCollarHomeomorph
    (u : ↥(A.sectionSevenOrderThreeFillingImage ∩
      A.sectionSevenAffineOrderThreeCentralRegion)) :
    A.starToCentral 1 (A.orderThreeOverlapCollarHomeomorph u) =
      A.sectionSevenEllipticCentralImageHomeomorph
        ⟨u.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
          A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) u.2.2⟩ := by
  let e₃ := (A.starToCentral_isOpenEmbedding (1 : Fin 3)).isEmbedding.toHomeomorph
  let w : ↥(Set.range (A.starToCentral (1 : Fin 3))) :=
    ⟨A.sectionSevenEllipticCentralImageHomeomorph
        ⟨u.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
          A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) u.2.2⟩,
      (A.mem_orderThreeFillingImage_iff_mem_starToCentral_range _).mp u.2.1⟩
  have hcoe := Topology.IsEmbedding.toHomeomorph_apply_coe
    (A.starToCentral_isOpenEmbedding (1 : Fin 3)).isEmbedding (e₃.symm w)
  show A.starToCentral 1 (e₃.symm w) = _
  exact hcoe.symm.trans (congrArg Subtype.val (e₃.apply_symm_apply w))

/-- The underlying elliptic-interior point of a collar point, through the overlap
identification. -/
public theorem starToCentral_orderThreeOverlapCollarHomeomorph_symm
    (z : A.starCollarSourceType (1 : Fin 3)) :
    A.sectionSevenEllipticCentralImageHomeomorph
        ⟨(A.orderThreeOverlapCollarHomeomorph.symm z).1,
          A.mem_centralImage_of_mem_centralHeightLowerRegion
            A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ)
            (A.orderThreeOverlapCollarHomeomorph.symm z).2.2⟩ =
      A.starToCentral 1 z := by
  have h := A.starToCentral_orderThreeOverlapCollarHomeomorph
    (A.orderThreeOverlapCollarHomeomorph.symm z)
  rw [A.orderThreeOverlapCollarHomeomorph.apply_symm_apply] at h
  exact h.symm

/-- Quantitative form of the collar coordinate bound: a collar point of small Cayley radius has
small affine coordinate. -/
public theorem orderThreeStarCollar_centralCoordinate_norm_lt_of_radius
    {a t : ℝ}
    (ht : ∀ z : UpperHalfPlane, ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < t →
      ‖A.modular.sourceCoordinate.coordinate z‖ < a)
    (z : A.starCollarSourceType (1 : Fin 3))
    (hz : A.starCollarRadius (1 : Fin 3) z < t) :
    ‖(A.centralFamilyCoordinate (A.starToCentral 1 z)).1‖ < a := by
  induction z using Quotient.inductionOn with
  | _ q =>
      let hproper : SourceActionProperlyDiscontinuous
          (U := A.modular.modularParameter.toTriangleUniformization) :=
        sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction
      let qlin := orderThreePuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderThree.radius q
      let qreg := orderThreeCollarToRegular A.periods hproper
        A.starSeparation.orderThree.sourceData qlin
      have hbase : ‖(orderThreeCayleyHomeomorph
          (regularTotalSpaceBase A.periods qreg).1).1‖ =
          orderThreeFamilyRadius A.periods qlin := by
        rw [orderThreeFamilyRadius.eq_def]
        exact congrArg (fun y : UpperHalfPlane ↦ ‖(orderThreeCayleyHomeomorph y).1‖)
          (orderThreeCollarToRegular_base A.periods hproper
            A.modular.modularParameter.toTriangleUniformization_sourceAction
            A.starSeparation.orderThree.sourceData qlin)
      have key : ‖(orderThreeCayleyHomeomorph
          (regularTotalSpaceBase A.periods qreg).1).1‖ =
          A.starCollarRadius (1 : Fin 3) (Quotient.mk _ q) := by
        calc ‖(orderThreeCayleyHomeomorph
              (regularTotalSpaceBase A.periods qreg).1).1‖
            = orderThreeFamilyRadius A.periods qlin := hbase
          _ = orderThreeFamilyRadius A.periods q :=
              orderThreeFamilyRadius_principalGauge A.periods q
          _ = A.starCollarRadius (1 : Fin 3) (Quotient.mk _ q) :=
              (A.orderThreeStarCollarRadius_mk q).symm
      have hgoal : ‖A.modular.sourceCoordinate.coordinate
          (regularTotalSpaceBase A.periods qreg).1‖ < a := by
        refine ht _ ?_
        rw [key]
        exact hz
      rw [A.orderThreeStarToCentral_mk q, A.centralFamilyCoordinate_centralQuotientProjection]
      exact hgoal

/-! ## Radial shrinking of the order-three star collar

The shrink is performed in the order-three real-period product chart, where the disc coordinate
*is* the Cayley radius.  Multiplication of that coordinate by a real factor commutes with the
scalar rotation generating the cyclic action, so the whole homotopy is equivariant and descends
to the collar quotient.  The radial mapping-torus axiom is not used. -/

/-- Radial shrinking of the varying order-three family, read in the product chart. -/
public noncomputable def orderThreeFamilyShrink (s : unitInterval)
    (q : TotalSpace (parameterMap A.periods)) : TotalSpace (parameterMap A.periods) :=
  (orderThreeRealPeriodProductHomeomorph A.periods).symm
    (discRadialHomotopy (s, (orderThreeRealPeriodProductHomeomorph A.periods q).1),
      (orderThreeRealPeriodProductHomeomorph A.periods q).2)

public theorem orderThreeFamilyShrink_continuous :
    Continuous fun z : unitInterval × TotalSpace (parameterMap A.periods) ↦
      A.orderThreeFamilyShrink z.1 z.2 := by
  apply (orderThreeRealPeriodProductHomeomorph A.periods).symm.continuous.comp
  refine Continuous.prodMk ?_ ?_
  · exact discRadialHomotopy_continuous.comp (continuous_fst.prodMk
      ((continuous_fst.comp
        ((orderThreeRealPeriodProductHomeomorph A.periods).continuous.comp continuous_snd))))
  · exact continuous_snd.comp
      ((orderThreeRealPeriodProductHomeomorph A.periods).continuous.comp continuous_snd)

@[simp]
public theorem orderThreeFamilyShrink_zero (q : TotalSpace (parameterMap A.periods)) :
    A.orderThreeFamilyShrink 0 q = q := by
  rw [orderThreeFamilyShrink, discRadialHomotopy_zero]
  exact (orderThreeRealPeriodProductHomeomorph A.periods).symm_apply_apply q

/-- The shrink scales the Cayley radius by the expected real factor. -/
public theorem orderThreeFamilyRadius_familyShrink (s : unitInterval)
    (q : TotalSpace (parameterMap A.periods)) :
    orderThreeFamilyRadius A.periods (A.orderThreeFamilyShrink s q) =
      (1 - (s : ℝ)) * orderThreeFamilyRadius A.periods q := by
  rw [orderThreeFamilyRadius_eq_productNorm, orderThreeFamilyRadius_eq_productNorm,
    orderThreeFamilyShrink, Homeomorph.apply_symm_apply]
  have hval : ((discRadialHomotopy
      (s, (orderThreeRealPeriodProductHomeomorph A.periods q).1) : ComplexUnitDisc) : ℂ) =
      ((1 - (s : ℝ) : ℝ) : ℂ) *
        ((orderThreeRealPeriodProductHomeomorph A.periods q).1 : ℂ) := rfl
  have hs0 : (0 : ℝ) ≤ 1 - (s : ℝ) := by
    have := s.2.2
    linarith
  simp only [hval, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]

/-- The shrink is equivariant for the affine cyclic action on the varying family. -/
public theorem orderThreeFamilyShrink_equivariant (s : unitInterval)
    (g : FiniteCyclic 3) (q : TotalSpace (parameterMap A.periods)) :
    A.orderThreeFamilyShrink s (actionMap (orderThreeAffineFamilyAction A.periods) g q) =
      actionMap (orderThreeAffineFamilyAction A.periods) g (A.orderThreeFamilyShrink s q) := by
  have hP : ∀ y : TotalSpace (parameterMap A.periods),
      orderThreeRealPeriodProductHomeomorph A.periods
          (actionMap (orderThreeAffineFamilyAction A.periods) g y) =
        actionMap
          (SphereSixComplex.Geometry.EllipticFixedPointCriterion.orderThreeActionData
            A.periods).diagonalAction g
          (orderThreeRealPeriodProductHomeomorph A.periods y) :=
    fun y ↦ orderThreeRealPeriodProductHomeomorph_equivariant A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction g y
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  rw [orderThreeFamilyShrink, Homeomorph.apply_symm_apply, hP, hP,
    orderThreeFamilyShrink, Homeomorph.apply_symm_apply]
  exact (orderThreeRadialActionData A.periods).radial_equivariant g s
    (orderThreeRealPeriodProductHomeomorph A.periods q)

/-- The selected order-three collar carrier. -/
public noncomputable abbrev orderThreeCollarCarrier :
    InvariantOpenCarrier (orderThreeAffineFamilyAction A.periods) :=
  orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius

public theorem mem_orderThreeCollarCarrier
    {q : TotalSpace (parameterMap A.periods)} :
    q ∈ A.orderThreeCollarCarrier.carrier ↔
      0 < orderThreeFamilyRadius A.periods q ∧
        orderThreeFamilyRadius A.periods q < A.starSeparation.orderThree.radius :=
  Iff.rfl

/-- A Cayley radius small enough to force a prescribed affine coordinate bound. -/
public theorem exists_orderThreeCayleyRadius_coordinate_lt {a : ℝ} (ha : 0 < a) :
    ∃ t : ℝ, 0 < t ∧ ∀ z : UpperHalfPlane,
      ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < t →
        ‖A.modular.sourceCoordinate.coordinate z‖ < a := by
  have hopen : IsOpen {z : UpperHalfPlane |
      ‖A.modular.sourceCoordinate.coordinate z‖ < a} :=
    isOpen_lt (continuous_norm.comp
      A.modular.sourceCoordinate.coordinate_holomorphic.continuous) continuous_const
  have hmem : SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint ∈
      {z : UpperHalfPlane | ‖A.modular.sourceCoordinate.coordinate z‖ < a} := by
    show ‖A.modular.sourceCoordinate.coordinate
      SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint‖ < a
    rw [A.modular.sourceCoordinate.coordinate_at_one]
    simpa using ha
  obtain ⟨t, ht, -, hsub⟩ :=
    exists_cayleyRadius_subset SphereSixComplex.TriangleGroup.fuchsianOneFixedPoint hopen hmem
  exact ⟨t, ht, fun z hz ↦ hsub z hz⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end
