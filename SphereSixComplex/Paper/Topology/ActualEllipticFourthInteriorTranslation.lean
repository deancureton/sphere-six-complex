module
public import SphereSixComplex.Paper.Topology.ActualEllipticFourthCollarCompatibility
public import SphereSixComplex.Paper.Topology.PaperSectionSevenEllipticBaseCoordinate
public import SphereSixComplex.Paper.Topology.PaperSectionSevenStarIntersections

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData

public def fourthTranslationCentralInclusion (A : PaperAnalyticData) :
    C(A.CentralFamily, A.ellipticInterior) :=
  ⟨fun q ↦ (A.ellipticCentralImageHomeomorph.symm q).1,
    continuous_subtype_val.comp A.ellipticCentralImageHomeomorph.symm.continuous⟩

public def fourthTranslationThreeChart (A : PaperAnalyticData) :
    A.orderThreeFillingImage ≃ₜ A.openEmbeddingStarData.filling 1 :=
  A.orderThreeFillingImageToPiece.trans A.orderThreePieceHomeomorph.symm

public def fourthTranslationFourChart (A : PaperAnalyticData) :
    A.orderFourFillingImage ≃ₜ A.openEmbeddingStarData.filling 2 :=
  A.orderFourFillingImageToPiece.trans A.orderFourPieceHomeomorph.symm

public def fourthTranslationThreeInclusion (A : PaperAnalyticData) :
    C(A.openEmbeddingStarData.filling 1, A.ellipticInterior) :=
  ⟨fun q ↦ (A.fourthTranslationThreeChart.symm q).1,
    continuous_subtype_val.comp A.fourthTranslationThreeChart.symm.continuous⟩

public def fourthTranslationFourInclusion (A : PaperAnalyticData) :
    C(A.openEmbeddingStarData.filling 2, A.ellipticInterior) :=
  ⟨fun q ↦ (A.fourthTranslationFourChart.symm q).1,
    continuous_subtype_val.comp A.fourthTranslationFourChart.symm.continuous⟩

public theorem fourthTranslationCentralInclusion_coe (A : PaperAnalyticData) (q : A.CentralFamily) :
    (A.fourthTranslationCentralInclusion q).1 =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι none q := rfl

public theorem fourthTranslationThreeInclusion_coe (A : PaperAnalyticData)
    (q : A.openEmbeddingStarData.filling 1) :
    (A.fourthTranslationThreeInclusion q).1 =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι (some 1) q := rfl

public theorem fourthTranslationFourInclusion_coe (A : PaperAnalyticData)
    (q : A.openEmbeddingStarData.filling 2) :
    (A.fourthTranslationFourInclusion q).1 =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι (some 2) q := rfl

public theorem fourthTranslationThree_glue (A : PaperAnalyticData)
    (q : A.openEmbeddingStarData.collarSource 1) :
    A.fourthTranslationCentralInclusion (A.starToCentral 1 q) =
      A.fourthTranslationThreeInclusion (A.starToFilling 1 q) := by
  apply Subtype.ext
  have h := (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.glue_condition_apply
    none (some 1) (A.openEmbeddingStarData.centralCollarPoint 1 q)).symm
  change _ = A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι (some 1)
    ((A.openEmbeddingStarData.collarEquiv 1) (A.openEmbeddingStarData.centralCollarPoint 1 q)).1 at h
  rw [OpenEmbeddingStarData.collarEquiv, Homeomorph.trans_apply,
    ← A.openEmbeddingStarData.toCentralCollarHomeomorph_apply,
    Homeomorph.symm_apply_apply, A.openEmbeddingStarData.toFillingCollarHomeomorph_apply] at h
  rw [A.openEmbeddingStarData.toCentralCollarHomeomorph_apply] at h

  exact h

public theorem fourthTranslationFour_glue (A : PaperAnalyticData)
    (q : A.openEmbeddingStarData.collarSource 2) :
    A.fourthTranslationCentralInclusion (A.starToCentral 2 q) =
      A.fourthTranslationFourInclusion (A.starToFilling 2 q) := by
  apply Subtype.ext
  have h := (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.glue_condition_apply
    none (some 2) (A.openEmbeddingStarData.centralCollarPoint 2 q)).symm
  change _ = A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι (some 2)
    ((A.openEmbeddingStarData.collarEquiv 2) (A.openEmbeddingStarData.centralCollarPoint 2 q)).1 at h
  rw [OpenEmbeddingStarData.collarEquiv, Homeomorph.trans_apply,
    ← A.openEmbeddingStarData.toCentralCollarHomeomorph_apply,
    Homeomorph.symm_apply_apply, A.openEmbeddingStarData.toFillingCollarHomeomorph_apply] at h
  rw [A.openEmbeddingStarData.toCentralCollarHomeomorph_apply] at h

  exact h

public theorem fourthTranslationThree_collar (A : PaperAnalyticData) (z : UnitAddCircle)
    (q : A.openEmbeddingStarData.collarSource 1) :
    A.fourthTranslationCentralInclusion (A.centralFourthTranslation (z,A.starToCentral 1 q)) =
      A.fourthTranslationThreeInclusion (A.actualOrderThreeFourthTranslation (z,A.starToFilling 1 q)) := by
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
  induction q using Quotient.inductionOn with
  | _ q =>
    rw [A.orderThreeFourthCollarSource_central, A.orderThreeFourthCollarSource_filling]
    exact A.fourthTranslationThree_glue _

public theorem fourthTranslationFour_collar (A : PaperAnalyticData) (z : UnitAddCircle)
    (q : A.openEmbeddingStarData.collarSource 2) :
    A.fourthTranslationCentralInclusion (A.centralFourthTranslation (z,A.starToCentral 2 q)) =
      A.fourthTranslationFourInclusion (A.actualOrderFourFourthTranslation (z,A.starToFilling 2 q)) := by
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
  induction q using Quotient.inductionOn with
  | _ q =>
    rw [A.orderFourFourthCollarSource_central, A.orderFourFourthCollarSource_filling]
    exact A.fourthTranslationFour_glue _

public theorem fourthTranslationCentralInclusion_injective (A : PaperAnalyticData) :
    Function.Injective A.fourthTranslationCentralInclusion :=
  Subtype.val_injective.comp A.ellipticCentralImageHomeomorph.symm.injective

public theorem fourthTranslationThreeInclusion_injective (A : PaperAnalyticData) :
    Function.Injective A.fourthTranslationThreeInclusion :=
  Subtype.val_injective.comp A.fourthTranslationThreeChart.symm.injective

public theorem fourthTranslationFourInclusion_injective (A : PaperAnalyticData) :
    Function.Injective A.fourthTranslationFourInclusion :=
  Subtype.val_injective.comp A.fourthTranslationFourChart.symm.injective

public theorem fourthTranslationThree_overlap (A : PaperAnalyticData) (z : UnitAddCircle)
    (x : A.ellipticInterior) (h0 : x ∈ A.ellipticCentralImage)
    (h1 : x ∈ A.orderThreeFillingImage) :
    A.fourthTranslationCentralInclusion (A.centralFourthTranslation
      (z,A.ellipticCentralImageHomeomorph ⟨x,h0⟩)) =
    A.fourthTranslationThreeInclusion (A.actualOrderThreeFourthTranslation
      (z,A.fourthTranslationThreeChart ⟨x,h1⟩)) := by
  have hm : x.1 ∈ Set.range (A.openEmbeddingStarData.collarSourceToGlued 1) := by
    rw [A.openEmbeddingStarData.range_collarSourceToGlued]
    exact ⟨h0,h1⟩
  obtain ⟨q,hq⟩ := hm
  have hq0 : A.fourthTranslationCentralInclusion (A.starToCentral 1 q) = x :=
    Subtype.ext hq
  have he0 : A.ellipticCentralImageHomeomorph ⟨x,h0⟩ = A.starToCentral 1 q := by
    apply A.fourthTranslationCentralInclusion_injective
    exact (congrArg Subtype.val (A.ellipticCentralImageHomeomorph.symm_apply_apply
      ⟨x,h0⟩)).trans hq0.symm
  have he1 : A.fourthTranslationThreeChart ⟨x,h1⟩ = A.starToFilling 1 q := by
    apply A.fourthTranslationThreeInclusion_injective
    exact (congrArg Subtype.val (A.fourthTranslationThreeChart.symm_apply_apply
      ⟨x,h1⟩)).trans (hq0.symm.trans (A.fourthTranslationThree_glue q))
  rw [he0,he1]
  exact A.fourthTranslationThree_collar z q

public theorem fourthTranslationFour_overlap (A : PaperAnalyticData) (z : UnitAddCircle)
    (x : A.ellipticInterior) (h0 : x ∈ A.ellipticCentralImage)
    (h1 : x ∈ A.orderFourFillingImage) :
    A.fourthTranslationCentralInclusion (A.centralFourthTranslation
      (z,A.ellipticCentralImageHomeomorph ⟨x,h0⟩)) =
    A.fourthTranslationFourInclusion (A.actualOrderFourFourthTranslation
      (z,A.fourthTranslationFourChart ⟨x,h1⟩)) := by
  have hm : x.1 ∈ Set.range (A.openEmbeddingStarData.collarSourceToGlued 2) := by
    rw [A.openEmbeddingStarData.range_collarSourceToGlued]
    exact ⟨h0,h1⟩
  obtain ⟨q,hq⟩ := hm
  have hq0 : A.fourthTranslationCentralInclusion (A.starToCentral 2 q) = x :=
    Subtype.ext hq
  have he0 : A.ellipticCentralImageHomeomorph ⟨x,h0⟩ = A.starToCentral 2 q := by
    apply A.fourthTranslationCentralInclusion_injective
    exact (congrArg Subtype.val (A.ellipticCentralImageHomeomorph.symm_apply_apply
      ⟨x,h0⟩)).trans hq0.symm
  have he1 : A.fourthTranslationFourChart ⟨x,h1⟩ = A.starToFilling 2 q := by
    apply A.fourthTranslationFourInclusion_injective
    exact (congrArg Subtype.val (A.fourthTranslationFourChart.symm_apply_apply
      ⟨x,h1⟩)).trans (hq0.symm.trans (A.fourthTranslationFour_glue q))
  rw [he0,he1]
  exact A.fourthTranslationFour_collar z q

public def fourthTranslationPatchSet (A : PaperAnalyticData) :
    Fin 3 → Set (UnitAddCircle × A.ellipticInterior) :=
  ![Prod.snd ⁻¹' A.ellipticCentralImage,
    Prod.snd ⁻¹' A.orderThreeFillingImage,
    Prod.snd ⁻¹' A.orderFourFillingImage]

public def fourthTranslationPatch (A : PaperAnalyticData) :
    (i : Fin 3) → C(A.fourthTranslationPatchSet i, A.ellipticInterior) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i ↦ Fin.elim0 i)))
  · exact A.fourthTranslationCentralInclusion.comp (A.centralFourthTranslation.comp
      ⟨fun p ↦ (p.1.1,A.ellipticCentralImageHomeomorph ⟨p.1.2,p.2⟩),
        (continuous_fst.comp continuous_subtype_val).prodMk
          (A.ellipticCentralImageHomeomorph.continuous.comp
            ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩)
  · exact A.fourthTranslationThreeInclusion.comp (A.actualOrderThreeFourthTranslation.comp
      ⟨fun p ↦ (p.1.1,A.fourthTranslationThreeChart ⟨p.1.2,p.2⟩),
        (continuous_fst.comp continuous_subtype_val).prodMk
          (A.fourthTranslationThreeChart.continuous.comp
            ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩)
  · exact A.fourthTranslationFourInclusion.comp (A.actualOrderFourFourthTranslation.comp
      ⟨fun p ↦ (p.1.1,A.fourthTranslationFourChart ⟨p.1.2,p.2⟩),
        (continuous_fst.comp continuous_subtype_val).prodMk
          (A.fourthTranslationFourChart.continuous.comp
            ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩)

public theorem fourthTranslation_fillings_disjoint (A : PaperAnalyticData)
    (x : A.ellipticInterior)
    (h1 : x ∈ A.orderThreeFillingImage)
    (h2 : x ∈ A.orderFourFillingImage) : False := by
  have h : x.1 ∈ (sectionSevenStarOpenCover
      A.openEmbeddingStarData.toFourPieceStarGluingData).piece (1 : Fin 3).succ ∩
      (sectionSevenStarOpenCover
      A.openEmbeddingStarData.toFourPieceStarGluingData).piece (2 : Fin 3).succ := ⟨h1,h2⟩
  rw [A.openEmbeddingStarData.fillingPiece_inter_fillingPiece (by decide)] at h
  exact h

public theorem fourthTranslationPatch_compatible (A : PaperAnalyticData)
    (i j : Fin 3) (x : UnitAddCircle × A.ellipticInterior)
    (hi : x ∈ A.fourthTranslationPatchSet i)
    (hj : x ∈ A.fourthTranslationPatchSet j) :
    A.fourthTranslationPatch i ⟨x,hi⟩ = A.fourthTranslationPatch j ⟨x,hj⟩ := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact A.fourthTranslationThree_overlap x.1 x.2 hi hj
  · exact A.fourthTranslationFour_overlap x.1 x.2 hi hj
  · exact (A.fourthTranslationThree_overlap x.1 x.2 hj hi).symm
  · rfl
  · exact (A.fourthTranslation_fillings_disjoint x.2 hi hj).elim
  · exact (A.fourthTranslationFour_overlap x.1 x.2 hj hi).symm
  · exact (A.fourthTranslation_fillings_disjoint x.2 hj hi).elim
  · rfl

public theorem fourthTranslationPatchSet_isOpen (A : PaperAnalyticData) (i : Fin 3) :
    IsOpen (A.fourthTranslationPatchSet i) := by
  fin_cases i
  · exact A.ellipticCentralImage_isOpen.preimage continuous_snd
  · exact A.orderThreeFillingImage_isOpen.preimage continuous_snd
  · exact A.orderFourFillingImage_isOpen.preimage continuous_snd

public theorem fourthTranslationPatchSet_nhds (A : PaperAnalyticData)
    (x : UnitAddCircle × A.ellipticInterior) :
    ∃ i, A.fourthTranslationPatchSet i ∈ nhds x := by
  have hx : x.2 ∈ A.ellipticCentralImage ∪
      A.orderThreeFillingImage ∪ A.orderFourFillingImage := by
    rw [A.ellipticCentral_union_fillings]
    trivial
  rcases hx with (h | h) | h
  · exact ⟨0,(A.fourthTranslationPatchSet_isOpen 0).mem_nhds h⟩
  · exact ⟨1,(A.fourthTranslationPatchSet_isOpen 1).mem_nhds h⟩
  · exact ⟨2,(A.fourthTranslationPatchSet_isOpen 2).mem_nhds h⟩

public def ellipticFourthTranslation (A : PaperAnalyticData) :
    C(UnitAddCircle × A.ellipticInterior, A.ellipticInterior) :=
  ContinuousMap.liftCover (A.fourthTranslationPatchSet) (A.fourthTranslationPatch)
    (A.fourthTranslationPatch_compatible) (A.fourthTranslationPatchSet_nhds)

public theorem ellipticFourthTranslation_central (A : PaperAnalyticData)
    (z : UnitAddCircle) (q : A.CentralFamily) :
    A.ellipticFourthTranslation (z,A.fourthTranslationCentralInclusion q) =
      A.fourthTranslationCentralInclusion (A.centralFourthTranslation (z,q)) := by
  have h := ContinuousMap.liftCover_coe
    (S := A.fourthTranslationPatchSet) (φ := A.fourthTranslationPatch)
    (hφ := A.fourthTranslationPatch_compatible) (hS := A.fourthTranslationPatchSet_nhds)
    (i := 0) ⟨(z,A.fourthTranslationCentralInclusion q),
      (A.ellipticCentralImageHomeomorph.symm q).property⟩
  change A.ellipticFourthTranslation (z,A.fourthTranslationCentralInclusion q) =
    A.fourthTranslationCentralInclusion (A.centralFourthTranslation
      (z,A.ellipticCentralImageHomeomorph (A.ellipticCentralImageHomeomorph.symm q))) at h
  simpa only [Homeomorph.apply_symm_apply] using h

public theorem ellipticFourthTranslation_three (A : PaperAnalyticData)
    (z : UnitAddCircle) (q : A.openEmbeddingStarData.filling 1) :
    A.ellipticFourthTranslation (z,A.fourthTranslationThreeInclusion q) =
      A.fourthTranslationThreeInclusion (A.actualOrderThreeFourthTranslation (z,q)) := by
  have h := ContinuousMap.liftCover_coe
    (S := A.fourthTranslationPatchSet) (φ := A.fourthTranslationPatch)
    (hφ := A.fourthTranslationPatch_compatible) (hS := A.fourthTranslationPatchSet_nhds)
    (i := 1) ⟨(z,A.fourthTranslationThreeInclusion q),
      (A.fourthTranslationThreeChart.symm q).property⟩
  change A.ellipticFourthTranslation (z,A.fourthTranslationThreeInclusion q) =
    A.fourthTranslationThreeInclusion (A.actualOrderThreeFourthTranslation
      (z,A.fourthTranslationThreeChart (A.fourthTranslationThreeChart.symm q))) at h
  simpa only [Homeomorph.apply_symm_apply] using h

public theorem ellipticFourthTranslation_four (A : PaperAnalyticData)
    (z : UnitAddCircle) (q : A.openEmbeddingStarData.filling 2) :
    A.ellipticFourthTranslation (z,A.fourthTranslationFourInclusion q) =
      A.fourthTranslationFourInclusion (A.actualOrderFourFourthTranslation (z,q)) := by
  have h := ContinuousMap.liftCover_coe
    (S := A.fourthTranslationPatchSet) (φ := A.fourthTranslationPatch)
    (hφ := A.fourthTranslationPatch_compatible) (hS := A.fourthTranslationPatchSet_nhds)
    (i := 2) ⟨(z,A.fourthTranslationFourInclusion q),
      (A.fourthTranslationFourChart.symm q).property⟩
  change A.ellipticFourthTranslation (z,A.fourthTranslationFourInclusion q) =
    A.fourthTranslationFourInclusion (A.actualOrderFourFourthTranslation
      (z,A.fourthTranslationFourChart (A.fourthTranslationFourChart.symm q))) at h
  simpa only [Homeomorph.apply_symm_apply] using h

end SphereSixComplex.Geometry.PaperAnalyticData
