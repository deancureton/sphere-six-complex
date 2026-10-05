module

public import SphereSixComplex.Paper.Geometry.PaperOpenEmbeddingStar
public import SphereSixComplex.Prerequisites.Topology.DiscRadialTopology
public import SphereSixComplex.Prerequisites.Topology.FreeLoopHomology

@[expose] public section
noncomputable section
open scoped ContinuousMap
open SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree

namespace SphereSixComplex.Geometry.EllipticDiscCircle

theorem loopHomologyClass_disc_prod_eq_zero
    {T Y : Type} [TopologicalSpace T] [TopologicalSpace Y]
    {b : ComplexUnitDisc} (p : Path b b) (t : T)
    (f : C(ComplexUnitDisc × T, Y)) :
    loopHomologyClass ((p.prod (Path.refl t)).map f.continuous) = 0 := by
  let H : ContinuousMap.Homotopy
      ((p.prod (Path.refl t)).map f.continuous).toContinuousMap
      (Path.refl (f (ComplexUnitDisc.center, t))).toContinuousMap :=
    { toFun := fun q ↦ f (ComplexDisc.radialHomotopy (q.1, p q.2), t)
      continuous_toFun := f.continuous.comp
        ((ComplexDisc.continuous_radialHomotopy.comp
          (continuous_fst.prodMk (p.continuous.comp continuous_snd))).prodMk continuous_const)
      map_zero_left := by intro s; simp
      map_one_left := by intro s; simp }
  have h := loopHomologyClass_eq_of_freeHomotopy
    ((p.prod (Path.refl t)).map f.continuous)
    (Path.refl (f (ComplexUnitDisc.center, t))) H (by
      intro s
      change f (ComplexDisc.radialHomotopy (s, p 0), t) =
        f (ComplexDisc.radialHomotopy (s, p 1), t)
      rw [p.source, p.target])
  exact h.trans (loopHomologyClass_refl _)

open AnalyticData ComplexTorus

def discBallScale {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    C(ComplexUnitDisc, ComplexDiscBall r) where
  toFun w :=
    let hw : ‖(r : ℂ) * (w : ℂ)‖ < r := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
      simpa using mul_lt_mul_of_pos_left w.property hr
    ⟨⟨(r : ℂ) * (w : ℂ), hw.trans hr1⟩, hw⟩
  continuous_toFun :=
    (continuous_const.mul continuous_subtype_val).subtype_mk _ |>.subtype_mk _

def orderThreeDisc (A : AnalyticData) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    C(ComplexUnitDisc, A.OrderThreeVaryingFilling r) := by
  let _ := A.orderThreeFillingAction r
  exact ⟨fun w ↦ Quotient.mk _ (A.orderThreeFillingCoverMap r (discBallScale hr hr1 w, 0)),
    continuous_quot_mk.comp ((A.orderThreeFillingCoverMap_continuous r).comp
      ((discBallScale hr hr1).continuous.prodMk continuous_const))⟩

def orderFourDisc (A : AnalyticData) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    C(ComplexUnitDisc, A.OrderFourVaryingFilling r) := by
  let _ := A.orderFourFillingAction r
  exact ⟨fun w ↦ Quotient.mk _ (A.orderFourFillingCoverMap r (discBallScale hr hr1 w, 0)),
    continuous_quot_mk.comp ((A.orderFourFillingCoverMap_continuous r).comp
      ((discBallScale hr hr1).continuous.prodMk continuous_const))⟩

theorem loopHomologyClass_disc_map_eq_zero
    {Y : Type} [TopologicalSpace Y] {b : ComplexUnitDisc}
    (p : Path b b) (f : C(ComplexUnitDisc, Y)) :
    loopHomologyClass (p.map f.continuous) = 0 := by
  exact loopHomologyClass_disc_prod_eq_zero p ()
    ⟨fun q ↦ f q.1, f.continuous.comp continuous_fst⟩




open EllipticLogarithmicGauge EllipticVaryingFamilyQuotient
open AnalyticTorusFamily TorusFamily EllipticCayleyHomeomorph EllipticWholeFiberCompactCover

def orderThreePuncturedDiscPoint (A : AnalyticData) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : ComplexUnitDisc) (hw : (w : ℂ) ≠ 0) :
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier :=
  ⟨(A.orderThreeFillingCoverMap r (discBallScale hr hr1 w, 0)).val, by
    constructor
    · change 0 < orderThreeFamilyRadius A.periods
        (Quotient.mk _ (orderThreeCayleyHomeomorph.symm (discBallScale hr hr1 w).val, 0))
      rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk,
        orderThreeCayleyHomeomorph.apply_symm_apply]
      change 0 < ‖(r : ℂ) * (w : ℂ)‖
      exact norm_pos_iff.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hw)
    · exact (A.orderThreeFillingCoverMap r (discBallScale hr hr1 w, 0)).property⟩

theorem orderThreeDisc_eq_collar (A : AnalyticData) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : ComplexUnitDisc) (hw : (w : ℂ) ≠ 0) :
    orderThreeDisc A hr hr1 w = A.orderThreePuncturedCollarToFilling r
      (Quotient.mk _ (orderThreePuncturedDiscPoint A hr hr1 w hw)) := by
  rw [A.orderThreePuncturedCollarToFilling_mk]
  rfl

def orderFourPuncturedDiscPoint (A : AnalyticData) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : ComplexUnitDisc) (hw : (w : ℂ) ≠ 0) :
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier :=
  ⟨(A.orderFourFillingCoverMap r (discBallScale hr hr1 w, 0)).val, by
    constructor
    · change 0 < orderFourFamilyRadius A.periods
        (Quotient.mk _ (orderFourCayleyHomeomorph.symm (discBallScale hr hr1 w).val, 0))
      rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk,
        orderFourCayleyHomeomorph.apply_symm_apply]
      change 0 < ‖(r : ℂ) * (w : ℂ)‖
      exact norm_pos_iff.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hw)
    · exact (A.orderFourFillingCoverMap r (discBallScale hr hr1 w, 0)).property⟩

theorem orderFourDisc_eq_collar (A : AnalyticData) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : ComplexUnitDisc) (hw : (w : ℂ) ≠ 0) :
    orderFourDisc A hr hr1 w = A.orderFourPuncturedCollarToFilling r
      (Quotient.mk _ (orderFourPuncturedDiscPoint A hr hr1 w hw)) := by
  rw [A.orderFourPuncturedCollarToFilling_mk]
  rfl

def centralInclusion (A : AnalyticData) :
    C(A.CentralFamily, GluedSpace A.openEmbeddingStarData.toFourPieceStarGluingData.glueData) :=
  ⟨A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι none,
    (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding _).continuous⟩

def orderThreeDiscToStar (A : AnalyticData) :
    C(ComplexUnitDisc,
      GluedSpace A.openEmbeddingStarData.toFourPieceStarGluingData.glueData) :=
  ⟨fun w ↦ A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      (some 1) (orderThreeDisc A A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one w),
    (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding _).continuous.comp
      (orderThreeDisc A A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one).continuous⟩

theorem orderThreeDiscToStar_eq_central (A : AnalyticData)
    (w : ComplexUnitDisc) (hw : (w : ℂ) ≠ 0) :
    orderThreeDiscToStar A w = centralInclusion A
      (A.orderThreePuncturedCollarToCentralFamily A.starSeparation.orderThree.sourceData
        (Quotient.mk _ (orderThreePuncturedDiscPoint A
          A.starSeparation.orderThree.radius_pos A.starSeparation.orderThree.radius_lt_one w hw))) := by
  let S := A.openEmbeddingStarData
  let q : S.collarSource 1 := Quotient.mk _ (orderThreePuncturedDiscPoint A
    A.starSeparation.orderThree.radius_pos A.starSeparation.orderThree.radius_lt_one w hw)
  change S.toFourPieceStarGluingData.glueData.toGlueData.ι (some 1)
    (orderThreeDisc A _ _ w) =
      S.toFourPieceStarGluingData.glueData.toGlueData.ι none (S.toCentral 1 q)
  rw [orderThreeDisc_eq_collar A _ _ w hw]
  apply (S.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
    (some 1) none (S.toFilling 1 q) (S.toCentral 1 q)).mpr
  exact ⟨S.fillingCollarPoint 1 q, rfl, by
    change ((S.collarEquiv 1).symm (S.fillingCollarPoint 1 q)).val = S.toCentral 1 q
    rw [S.collarEquiv_symm_toFilling]
    rfl⟩

theorem orderThreeDiscToStar_loop_eq_zero (A : AnalyticData)
    {b : ComplexUnitDisc} (p : Path b b) :
    loopHomologyClass (p.map (orderThreeDiscToStar A).continuous) = 0 :=
  loopHomologyClass_disc_map_eq_zero p (orderThreeDiscToStar A)

def orderFourDiscToStar (A : AnalyticData) :
    C(ComplexUnitDisc,
      GluedSpace A.openEmbeddingStarData.toFourPieceStarGluingData.glueData) :=
  ⟨fun w ↦ A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      (some 2) (orderFourDisc A A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one w),
    (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding _).continuous.comp
      (orderFourDisc A A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one).continuous⟩

theorem orderFourDiscToStar_eq_central (A : AnalyticData)
    (w : ComplexUnitDisc) (hw : (w : ℂ) ≠ 0) :
    orderFourDiscToStar A w = centralInclusion A
      (A.orderFourPuncturedCollarToCentralFamily A.starSeparation.orderFour.sourceData
        (Quotient.mk _ (orderFourPuncturedDiscPoint A
          A.starSeparation.orderFour.radius_pos A.starSeparation.orderFour.radius_lt_one w hw))) := by
  let S := A.openEmbeddingStarData
  let q : S.collarSource 2 := Quotient.mk _ (orderFourPuncturedDiscPoint A
    A.starSeparation.orderFour.radius_pos A.starSeparation.orderFour.radius_lt_one w hw)
  change S.toFourPieceStarGluingData.glueData.toGlueData.ι (some 2)
    (orderFourDisc A _ _ w) =
      S.toFourPieceStarGluingData.glueData.toGlueData.ι none (S.toCentral 2 q)
  rw [orderFourDisc_eq_collar A _ _ w hw]
  apply (S.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
    (some 2) none (S.toFilling 2 q) (S.toCentral 2 q)).mpr
  exact ⟨S.fillingCollarPoint 2 q, rfl, by
    change ((S.collarEquiv 2).symm (S.fillingCollarPoint 2 q)).val = S.toCentral 2 q
    rw [S.collarEquiv_symm_toFilling]
    rfl⟩

theorem orderFourDiscToStar_loop_eq_zero (A : AnalyticData)
    {b : ComplexUnitDisc} (p : Path b b) :
    loopHomologyClass (p.map (orderFourDiscToStar A).continuous) = 0 :=
  loopHomologyClass_disc_map_eq_zero p (orderFourDiscToStar A)

end SphereSixComplex.Geometry.EllipticDiscCircle
