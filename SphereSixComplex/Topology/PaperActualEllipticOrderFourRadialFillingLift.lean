module

public import SphereSixComplex.Topology.PaperActualAffineFillingCoverModelsProof

/-!
# The canonical radial lift for the actual order-four elliptic filling

The real-period gauge converts the constant vector coordinate on the radial mapping-torus cover
to the moving period coordinate used by the analytic filling.  This is the order-four analogue
of the already constructed order-three lift.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
open SphereSixComplex.CyclicAngularFundamentalDomain

variable (A : PaperAnalyticData)

/-- Inclusion of the actual order-four overlap into its filling piece is the original star
collar-to-filling map in the canonical source and target coordinates. -/
public theorem orderFourCollarToActualOverlap_toPiece
    (x : A.openEmbeddingStarData.collarSource 2) :
    A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
        (A.orderFourCollarToActualOverlapHomeomorph x) =
      A.orderFourFillingToActualPieceHomeomorph (A.starToFilling 2 x) := by
  apply Subtype.ext
  change
    A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      none (A.openEmbeddingStarData.toCentral 2 x) =
    A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      (some 2) (A.openEmbeddingStarData.toFilling 2 x)
  symm
  apply (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
    (some 2) none (A.openEmbeddingStarData.toFilling 2 x)
      (A.openEmbeddingStarData.toCentral 2 x)).mpr
  exact ⟨A.openEmbeddingStarData.fillingCollarPoint 2 x, rfl, by
    change ((A.openEmbeddingStarData.collarEquiv 2).symm
      (A.openEmbeddingStarData.fillingCollarPoint 2 x)).1 =
        A.openEmbeddingStarData.toCentral 2 x
    rw [A.openEmbeddingStarData.collarEquiv_symm_toFilling]
    rfl⟩

/-- The explicit order-four lift from radial universal-cover coordinates to the vector-bundle
cover of the filling. -/
public noncomputable def orderFourActualEllipticRadialFillingLift :
    C(OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace),
      ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace) where
  toFun q :=
    let u := angularCover (T := ComplexTwoSpace) 4
      A.starSeparation.orderFour.radius_lt_one.le q
    (⟨u.1.1, u.2.2⟩,
      (fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (orderFourCayleyHomeomorph.symm u.1.1, u.1.2)).2)
  continuous_toFun := by
    let hangular := continuous_angularCover (T := ComplexTwoSpace) 4
      A.starSeparation.orderFour.radius_lt_one.le
    let d : OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace) →
        ComplexDiscBall A.starSeparation.orderFour.radius := fun q =>
      let u := angularCover (T := ComplexTwoSpace) 4
        A.starSeparation.orderFour.radius_lt_one.le q
      ⟨u.1.1, u.2.2⟩
    have hd : Continuous d :=
      Continuous.subtype_mk
        ((continuous_subtype_val.comp hangular).fst) _
    let v : OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace) → UpperHalfPlane × ComplexTwoSpace := fun q =>
      let u := angularCover (T := ComplexTwoSpace) 4
        A.starSeparation.orderFour.radius_lt_one.le q
      (orderFourCayleyHomeomorph.symm u.1.1, u.1.2)
    have hv : Continuous v :=
      (orderFourCayleyHomeomorph.symm.continuous.comp
        ((continuous_subtype_val.comp hangular).fst)).prodMk
          ((continuous_subtype_val.comp hangular).snd)
    have hmoving : Continuous (fun q =>
        (fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo (v q)).2) :=
      continuous_snd.comp
        ((fixedToMovingCover_continuous A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).comp hv)
    exact hd.prodMk hmoving

@[simp]
public theorem orderFourActualEllipticRadialFillingLift_fst
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    (A.orderFourActualEllipticRadialFillingLift q).1.1 =
      (angularCover (T := ComplexTwoSpace) 4
        A.starSeparation.orderFour.radius_lt_one.le q).1.1 :=
  rfl

@[simp]
public theorem orderFourActualEllipticRadialFillingLift_snd
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    (A.orderFourActualEllipticRadialFillingLift q).2 =
      (fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (orderFourCayleyHomeomorph.symm
          (angularCover (T := ComplexTwoSpace) 4
            A.starSeparation.orderFour.radius_lt_one.le q).1.1,
          (angularCover (T := ComplexTwoSpace) 4
            A.starSeparation.orderFour.radius_lt_one.le q).1.2)).2 :=
  rfl

/-- In the fixed real-period product chart, the explicit lift is exactly the angular cover and
the original vector-cover coordinate. -/
public theorem orderFourFillingProductMap_actualEllipticRadialFillingLift
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    orderFourFillingProductMap A A.starSeparation.orderFour.radius
        (A.orderFourFillingCoverMap A.starSeparation.orderFour.radius
          (A.orderFourActualEllipticRadialFillingLift q)) =
      ((angularCover (T := ComplexTwoSpace) 4
          A.starSeparation.orderFour.radius_lt_one.le q).1.1,
        Quotient.mk _ q.2.2) := by
  rw [orderFourFillingProductMap]
  rw [orderFourFillingCoverMap.eq_def]
  rw [orderFourRealPeriodProductHomeomorph_mk]
  rw [A.orderFourActualEllipticRadialFillingLift_fst,
    A.orderFourActualEllipticRadialFillingLift_snd]
  rw [orderFourCayleyHomeomorph.apply_symm_apply]
  let u := angularCover (T := ComplexTwoSpace) 4
    A.starSeparation.orderFour.radius_lt_one.le q
  let p : UpperHalfPlane × ComplexTwoSpace :=
    (orderFourCayleyHomeomorph.symm u.1.1, u.1.2)
  have hp : (orderFourCayleyHomeomorph.symm u.1.1,
      (fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo p).2) =
      fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo p := by
    apply Prod.ext <;> rfl
  change (u.1.1, Quotient.mk _ (movingToFixedCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo
      (orderFourCayleyHomeomorph.symm u.1.1,
        (fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo p).2)).2) =
    (u.1.1, Quotient.mk _ q.2.2)
  rw [hp, movingToFixedCover_fixedToMovingCover]
  rfl

/-- The angular quotient homeomorphism sends the explicit angular lift to the affine
mapping-torus projection of the same real/vector coordinate. -/
public theorem orderFourAngularQuotientHomeomorph_apply
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    let D := orderFourCyclicPuncturedProductData A.periods
      A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one
    let w : OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × A.orderFourTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
    EstablishedCyclicAngularFundamentalDomain.quotientHomeomorphRadialMappingTorus D
        CyclicAngularFundamentalDomain.orderFourMultiplier_eq_standardMultiplier
        (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w) =
      (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2) := by
  dsimp only
  let D := orderFourCyclicPuncturedProductData A.periods
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  let w : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × A.orderFourTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
  let hgen := CyclicAngularFundamentalDomain.isStandardGenerator_of_multiplier_eq
    D.action D.clutching D.multiplier D.multiplier_norm
      CyclicAngularFundamentalDomain.orderFourMultiplier_eq_standardMultiplier
      D.generator_formula
  let hf := isQuotientMap_angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl
    D.action_continuous
  let hg := isQuotientMap_radialTorusMap
    (r := A.starSeparation.orderFour.radius) D.clutching
  let heq := angularQuotientMap_eq_iff D.action D.clutching D.radius_lt_one.le D.carrier
    rfl hgen
  change ((Homeomorph.refl (OpenRadialInterval A.starSeparation.orderFour.radius)).prodCongr
      (realMappingTorusHomeomorph _))
    (CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps
      hf hg heq
      (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w)) = _
  have happly : CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps hf hg heq
      (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w) =
      radialTorusMap D.clutching w :=
    (heq _ _).mp
      (Function.surjInv_eq hf.surjective
        (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w))
  rw [happly]
  rfl

/-- The explicit order-four radial lift commutes with the collar inclusion into the actual
filling piece. -/
public theorem orderFourActualEllipticRadialFillingLift_commutes
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
        (A.orderFourActualEllipticBoundaryProjection q) =
      A.orderFourActualEllipticFillingProjection
        (A.orderFourActualEllipticRadialFillingLift q) := by
  rw [orderFourActualEllipticBoundaryProjection]
  rw [orderFourActualEllipticFillingProjection]
  let x : A.openEmbeddingStarData.collarSource 2 :=
    A.orderFourCollarRadialMappingTorusHomeomorph.symm
      (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2)
  change A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
      (A.orderFourCollarToActualOverlapHomeomorph x) =
    A.orderFourFillingToActualPieceHomeomorph
      (A.orderFourActualFillingCoverProjection A.starSeparation.orderFour.radius
        (A.orderFourActualEllipticRadialFillingLift q))
  rw [A.orderFourCollarToActualOverlap_toPiece x]
  apply congrArg A.orderFourFillingToActualPieceHomeomorph
  let xq : A.starCollarSourceType 2 :=
    A.orderFourCollarRadialMappingTorusHomeomorph.symm
      (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2)
  change A.starToFilling 2 xq =
    A.orderFourActualFillingCoverProjection A.starSeparation.orderFour.radius
      (A.orderFourActualEllipticRadialFillingLift q)
  let D := orderFourCyclicPuncturedProductData A.periods
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  let e := orderFourPuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one
  let hprod := EquivariantQuotientHomeomorph.restrictedOrbitQuotientHomeomorph e
  let hang := EstablishedCyclicAngularFundamentalDomain.quotientHomeomorphRadialMappingTorus D
    CyclicAngularFundamentalDomain.orderFourMultiplier_eq_standardMultiplier
  let w : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × A.orderFourTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
  have hxprod : hprod xq =
      angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w := by
    apply hang.injective
    change A.orderFourCollarRadialMappingTorusHomeomorph xq =
      hang (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w)
    rw [show A.orderFourCollarRadialMappingTorusHomeomorph xq =
        (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2) from
      A.orderFourCollarRadialMappingTorusHomeomorph.apply_symm_apply _,
      A.orderFourAngularQuotientHomeomorph_apply q]
  have hxx : xq = hprod.symm
      (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w) := by
    rw [← hxprod]
    exact (hprod.symm_apply_apply xq).symm
  rw [hxx]
  let y : D.carrier.carrier :=
    (Homeomorph.setCongr (show D.carrier.carrier =
      puncturedProduct A.orderFourTorus A.starSeparation.orderFour.radius from rfl)).symm
      (angularCover (T := A.orderFourTorus) 4 D.radius_lt_one.le w)
  let s := e.toHomeomorph.symm y
  have hinv : hprod.symm
      (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w) =
      Quotient.mk _ s := by
    apply hprod.injective
    rw [hprod.apply_symm_apply]
    change Quotient.mk _ y = hprod (Quotient.mk _ s)
    rw [EquivariantQuotientHomeomorph.restrictedOrbitQuotientHomeomorph_mk]
    rw [show e.toHomeomorph s = y from e.toHomeomorph.apply_symm_apply y]
  rw [hinv]
  change A.orderFourPuncturedCollarToFilling A.starSeparation.orderFour.radius
      (Quotient.mk _ s) =
    A.orderFourActualFillingCoverProjection A.starSeparation.orderFour.radius
      (A.orderFourActualEllipticRadialFillingLift q)
  rw [A.orderFourPuncturedCollarToFilling_mk]
  rw [orderFourActualFillingCoverProjection]
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply (orderFourRealPeriodProductHomeomorph A.periods).injective
  change (e.toHomeomorph s).1 =
    orderFourFillingProductMap A A.starSeparation.orderFour.radius
      (A.orderFourFillingCoverMap A.starSeparation.orderFour.radius
        (A.orderFourActualEllipticRadialFillingLift q))
  rw [show e.toHomeomorph s = y from e.toHomeomorph.apply_symm_apply y]
  rw [A.orderFourFillingProductMap_actualEllipticRadialFillingLift q]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData
