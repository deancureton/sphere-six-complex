module
public import SphereSixComplex.Paper.Topology.StarFirstHomology
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryQuotientCovering
public import SphereSixComplex.Paper.Topology.PaperActualVanKampenCover
public import SphereSixComplex.Paper.Topology.ActualEllipticFourthInteriorTranslation
public import SphereSixComplex.Paper.Topology.CuspFillingPhaseCircle
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover
public import SphereSixComplex.Paper.Topology.PaperSectionSevenFinalDegreeZero
@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open GlobalTorusFamily CuspCollar ComplexTorus TorusFamily
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open CuspPeriodExpansion
public theorem centralFourthTranslation_additiveCusp (A : AnalyticData) (t : ℝ) (s : ℂ)
    (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) (v : ComplexTwoSpace) :
    A.centralFourthTranslation ((t : UnitAddCircle),
      additiveCuspCoverToGlobal A.starCuspWitness ⟨(v,s),hs⟩) =
    additiveCuspCoverToGlobal A.starCuspWitness ⟨(v + Pi.single 1 (t : ℂ),s),hs⟩ := by
  simp only [additiveCuspCoverToGlobal_eq_quotientProjections]
  change invariantPeriodCircleTranslation A.periods _ _ _ = _
  rw [invariantPeriodCircleTranslation_real]
  change invariantPeriodRealTranslation A.periods _ _
    (t, Quotient.mk _ (Quotient.mk _ _)) = _
  rw [invariantPeriodRealTranslation_mk, regularPeriodTranslation_mk]
  apply congrArg A.centralQuotientProjection
  apply congrArg (projection (regularParameterMap A.periods))
  apply Prod.ext
  · rfl
  · change t • periodVector _ ![0,0,0,1] + v = v + Pi.single 1 (t : ℂ)
    ext i
    fin_cases i <;> simp [periodVector, periodMatrix, Matrix.vecHead, Matrix.vecTail, add_comm]
public def starFourthCuspInclusion (A : AnalyticData) :
    C(A.openEmbeddingStarData.filling 0, A.VanKampenSpace) :=
  ⟨A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι (some 0),
    (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_isOpenEmbedding _).continuous⟩

public def starFourthCentralInclusion (A : AnalyticData) : C(A.CentralFamily, A.VanKampenSpace) :=
  ⟨fun q ↦ (A.fourthTranslationCentralInclusion q).1,
    continuous_subtype_val.comp A.fourthTranslationCentralInclusion.continuous⟩

public theorem starFourth_glue (A : AnalyticData)
    (q : A.openEmbeddingStarData.collarSource 0) :
    A.starFourthCentralInclusion (A.starToCentral 0 q) =
      A.starFourthCuspInclusion (A.starToFilling 0 q) := by
  have h := (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.glue_condition_apply
    none (some 0) (A.openEmbeddingStarData.centralCollarPoint 0 q)).symm
  change _ = A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι (some 0)
    ((A.openEmbeddingStarData.collarEquiv 0)
      (A.openEmbeddingStarData.centralCollarPoint 0 q)).1 at h
  rw [OpenEmbeddingStarData.collarEquiv, Homeomorph.trans_apply,
    ← A.openEmbeddingStarData.toCentralCollarHomeomorph_apply,
    Homeomorph.symm_apply_apply, A.openEmbeddingStarData.toFillingCollarHomeomorph_apply] at h
  rw [A.openEmbeddingStarData.toCentralCollarHomeomorph_apply] at h
  exact h

public theorem starFourth_additive_glue (A : AnalyticData) (s : ℂ)
    (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) (v : ComplexTwoSpace) :
    A.starFourthCentralInclusion (additiveCuspCoverToGlobal A.starCuspWitness ⟨(v,s),hs⟩) =
    A.starFourthCuspInclusion (puncturedLocalCuspToFilling A.starCuspWitness
      (actualCuspCollarPeriodPoint A.starCuspWitness hs v)) := by
  have h := A.starFourth_glue (additiveCuspBoundaryProjection A.starCuspWitness ⟨(v,s),hs⟩)
  change A.starFourthCentralInclusion (puncturedLocalCuspQuotientMap A.starCuspWitness
    (additiveCuspBoundaryProjection _ _)) = _ at h
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection] at h
  exact h

public theorem starFourth_additive_collar (A : AnalyticData) (t : ℝ) (s : ℂ)
    (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius) (v : ComplexTwoSpace) :
    A.starFourthCentralInclusion (A.centralFourthTranslation ((t : UnitAddCircle),
      additiveCuspCoverToGlobal A.starCuspWitness ⟨(v,s),hs⟩)) =
    A.starFourthCuspInclusion (cuspFillingPeriodCircle A.starCuspWitness 1
      ((t : UnitAddCircle),puncturedLocalCuspToFilling A.starCuspWitness
        (actualCuspCollarPeriodPoint A.starCuspWitness hs v))) := by
  exact (congrArg A.starFourthCentralInclusion
    (A.centralFourthTranslation_additiveCusp t s hs v)).trans
    ((A.starFourth_additive_glue s hs _).trans
      (congrArg A.starFourthCuspInclusion
        (cuspFillingPeriodCircle_periodPoint A.starCuspWitness 1 t s hs v)).symm)

public theorem starFourth_collar (A : AnalyticData) (z : UnitAddCircle)
    (q : A.openEmbeddingStarData.collarSource 0) :
    A.starFourthCentralInclusion (A.centralFourthTranslation (z,A.starToCentral 0 q)) =
      A.starFourthCuspInclusion (cuspFillingPeriodCircle A.starCuspWitness 1
        (z,A.starToFilling 0 q)) := by
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨⟨⟨v,s⟩,hs⟩,rfl⟩ :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap A.starCuspWitness).surjective q
  change A.starFourthCentralInclusion (A.centralFourthTranslation ((t : UnitAddCircle),
    puncturedLocalCuspQuotientMap A.starCuspWitness
      (additiveCuspBoundaryProjection _ ⟨(v,s),hs⟩))) = _
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection]
  exact A.starFourth_additive_collar t s hs v

public def starFourthCuspChart (A : AnalyticData) :
    (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3) ≃ₜ
      A.openEmbeddingStarData.filling 0 :=
  (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0).symm

public def starFourthPatchSet (A : AnalyticData) :
    Fin 2 → Set (UnitAddCircle × A.VanKampenSpace) :=
  ![Prod.snd ⁻¹' A.ellipticInterior,
    Prod.snd ⁻¹' A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3]

public def starFourthPatch (A : AnalyticData) :
    (i : Fin 2) → C(A.starFourthPatchSet i, A.VanKampenSpace) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun i ↦ Fin.elim0 i))
  · exact ⟨fun p ↦ (A.ellipticFourthTranslation (p.1.1,⟨p.1.2,p.2⟩)).1,
      continuous_subtype_val.comp (A.ellipticFourthTranslation.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _)))⟩
  · exact A.starFourthCuspInclusion.comp ((cuspFillingPeriodCircle A.starCuspWitness 1).comp
      ⟨fun p ↦ (p.1.1,A.starFourthCuspChart ⟨p.1.2,p.2⟩),
        (continuous_fst.comp continuous_subtype_val).prodMk
          (A.starFourthCuspChart.continuous.comp
            ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩)

public theorem starFourth_overlap (A : AnalyticData) (x : UnitAddCircle × A.VanKampenSpace)
    (h0 : x ∈ A.starFourthPatchSet 0) (h1 : x ∈ A.starFourthPatchSet 1) :
    A.starFourthPatch 0 ⟨x,h0⟩ = A.starFourthPatch 1 ⟨x,h1⟩ := by
  obtain ⟨q,hq⟩ := A.cuspCollarToSectionSevenFinalOverlapHomeomorph.surjective ⟨x.2,h0,h1⟩
  have hc : A.starFourthCentralInclusion (A.starToCentral 0 q) = x.2 := congrArg Subtype.val hq
  have hf : A.starFourthCuspInclusion (A.starToFilling 0 q) = x.2 :=
    (A.starFourth_glue q).symm.trans hc
  have he : (⟨x.2,h0⟩ : A.ellipticInterior) =
      A.fourthTranslationCentralInclusion (A.starToCentral 0 q) :=
    Subtype.ext hc.symm
  have hchart : A.starFourthCuspChart ⟨x.2,h1⟩ = A.starToFilling 0 q := by
    apply A.starFourthCuspChart.symm.injective
    rw [Homeomorph.symm_apply_apply]
    apply Subtype.ext
    exact hf.symm
  change (A.ellipticFourthTranslation (x.1,⟨x.2,h0⟩)).1 =
    A.starFourthCuspInclusion (cuspFillingPeriodCircle A.starCuspWitness 1
      (x.1,A.starFourthCuspChart ⟨x.2,h1⟩))
  rw [he, hchart, A.ellipticFourthTranslation_central]
  exact A.starFourth_collar x.1 q

public theorem starFourthPatch_compatible (A : AnalyticData)
    (i j : Fin 2) (x : UnitAddCircle × A.VanKampenSpace)
    (hi : x ∈ A.starFourthPatchSet i) (hj : x ∈ A.starFourthPatchSet j) :
    A.starFourthPatch i ⟨x,hi⟩ = A.starFourthPatch j ⟨x,hj⟩ := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact A.starFourth_overlap x hi hj
  · exact (A.starFourth_overlap x hj hi).symm
  · rfl

public theorem starFourthPatchSet_isOpen (A : AnalyticData) (i : Fin 2) :
    IsOpen (A.starFourthPatchSet i) := by
  fin_cases i
  · exact (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.isOpen_stage 2).preimage
      continuous_snd
  · exact (A.openEmbeddingStarData.sectionSevenMayerVietorisCover.isOpen_piece 3).preimage
      continuous_snd

public theorem starFourthPatchSet_nhds (A : AnalyticData) (x : UnitAddCircle × A.VanKampenSpace) :
    ∃ i, A.starFourthPatchSet i ∈ nhds x := by
  have hx : x.2 ∈ A.ellipticInterior ∪
      A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3 := by
    change x.2 ∈ A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage 2 ∪ _
    have hu := A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage_union_next (2 : Fin 3)
    change A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage 2 ∪
      A.openEmbeddingStarData.sectionSevenMayerVietorisCover.piece 3 = _ at hu
    rw [hu]
    change x.2 ∈ A.openEmbeddingStarData.sectionSevenMayerVietorisCover.stage ⟨3,by decide⟩
    rw [FourPieceOpenCover.stage_last]
    trivial
  rcases hx with h | h
  · exact ⟨0,(A.starFourthPatchSet_isOpen 0).mem_nhds h⟩
  · exact ⟨1,(A.starFourthPatchSet_isOpen 1).mem_nhds h⟩

public def starFourthTranslation (A : AnalyticData) :
    C(UnitAddCircle × A.VanKampenSpace, A.VanKampenSpace) :=
  ContinuousMap.liftCover A.starFourthPatchSet A.starFourthPatch
    A.starFourthPatch_compatible A.starFourthPatchSet_nhds

public theorem starFourthTranslation_elliptic (A : AnalyticData)
    (z : UnitAddCircle) (q : A.ellipticInterior) :
    A.starFourthTranslation (z,q.1) = (A.ellipticFourthTranslation (z,q)).1 :=
  ContinuousMap.liftCover_coe (S := A.starFourthPatchSet) (φ := A.starFourthPatch)
    (hφ := A.starFourthPatch_compatible) (hS := A.starFourthPatchSet_nhds)
    (i := 0) ⟨(z,q.1),q.2⟩

open AlgebraicTopology SphereSixComplex.Topology CircleProductIdentityMappingTorus

public theorem ellipticFourthHomologySweep_toStar_eq_zero (A : AnalyticData)
    (x : IntegralSingularHomology 1 A.ellipticInterior) :
    integralSingularHomologyMap 2 A.ellipticInteriorInclusion
      (integralSingularHomologyMap 2 A.ellipticFourthTranslation
        (normalizedCircleCross 1 x)) = 0 := by
  let f : C(UnitAddCircle × A.ellipticInterior, UnitAddCircle × A.VanKampenSpace) :=
    ⟨fun p ↦ (p.1,p.2.1),continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)⟩
  have hz : integralSingularHomologyMap 2 f (normalizedCircleCross 1 x) = 0 := by
    apply circleProductClass_ext 1
    · let _ := A.star_homologyOne_subsingleton
      exact Subsingleton.elim _ _
    · rw [map_zero, integralSingularHomologyMap_comp_wang]
      change integralSingularHomologyMap 2
        (A.ellipticInteriorInclusion.comp productFiberProjection) (normalizedCircleCross 1 x) = 0
      rw [← integralSingularHomologyMap_comp_wang, normalizedCircleCross_projection, map_zero]
  have he : A.ellipticInteriorInclusion.comp A.ellipticFourthTranslation =
      A.starFourthTranslation.comp f := by
    ext p
    exact (A.starFourthTranslation_elliptic p.1 p.2).symm
  rw [integralSingularHomologyMap_comp_wang, he,
    ← integralSingularHomologyMap_comp_wang, hz, map_zero]

end SphereSixComplex.Geometry.AnalyticData
