module

public import SphereSixComplex.Topology.SectionSevenMayerVietorisEuler

/-!
# The top-degree vanishing needed by the Section 7 Euler calculation

`SectionSevenStageTopDegreeVanishing` asks that the three intermediate Mayer--Vietoris unions of
the star cover carry no seventh integral homology; it is what makes the degree-six truncated Euler
additivity applicable at each gluing step.

This module discharges it from the exact sequence: if two open pieces have no seventh homology and
their overlap has no sixth homology, the union has no seventh homology, because the connecting map
lands in a trivial group and the sum map has trivial source. Chaining that through the three
stages, and using that the local finiteness data already gives the four pieces no homology above
degree six, leaves a single geometric statement — that each collar source has no sixth homology,
which is the expected dimension count for a five-dimensional collar.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

/-- If two open pieces have no seventh homology and their overlap has no sixth homology, then
their union has no seventh homology. -/
public theorem subsingleton_homology_seven_union
    {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hA7 : Subsingleton (IntegralSingularHomology 7 A))
    (hB7 : Subsingleton (IntegralSingularHomology 7 B))
    (hAB6 : Subsingleton (IntegralSingularHomology 6 (A ∩ B : Set X))) :
    Subsingleton (IntegralSingularHomology 7 (A ∪ B : Set X)) := by
  obtain ⟨boundary, hexact⟩ := establishedIntegralMayerVietorisExactSequence A B hA hB
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : IntegralSingularHomology 7 (A ∪ B : Set X), z = 0 := by
    intro z
    have hz : boundary 6 z = 0 := Subsingleton.elim _ _
    obtain ⟨w, hw⟩ := (hexact 6).1 z |>.mp hz
    rw [← hw]
    have hw1 : w.1 = 0 := Subsingleton.elim _ _
    have hw2 : w.2 = 0 := Subsingleton.elim _ _
    show IntegralMayerVietoris.sumMap A B 7 w = 0
    rw [show w = 0 from Prod.ext hw1 hw2, map_zero]
  rw [key x, key y]

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

/-- Transport of degree-`k` homology vanishing along a homeomorphism. -/
public theorem subsingleton_homology_of_homeomorph {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (k : ℕ) (e : Y ≃ₜ Z) (h : Subsingleton (IntegralSingularHomology k Y)) :
    Subsingleton (IntegralSingularHomology k Z) :=
  ⟨fun x y => (integralSingularHomologyEquiv k e).symm.injective (Subsingleton.elim _ _)⟩

/-- The three intermediate unions have no seventh homology as soon as the four pieces have none
and the three collar sources have no sixth homology. -/
public theorem sectionSevenStageTopDegreeVanishing_of_collar
    (hcentral : Subsingleton (IntegralSingularHomology 7 A.central))
    (hfilling : ∀ i, Subsingleton (IntegralSingularHomology 7 (A.filling i)))
    (hcollar : ∀ i, Subsingleton (IntegralSingularHomology 6 (A.collarSource i))) :
    A.SectionSevenStageTopDegreeVanishing := by
  classical
  set C := A.SectionSevenEulerCover with hC
  have hpiece0 : Subsingleton (IntegralSingularHomology 7 (C.piece 0)) :=
    subsingleton_homology_of_homeomorph 7 A.centralToSectionSevenEulerPieceHomeomorph hcentral
  have hpieceSucc : ∀ i : Fin 3, Subsingleton (IntegralSingularHomology 7 (C.piece i.succ)) :=
    fun i => subsingleton_homology_of_homeomorph 7
      (A.fillingToSectionSevenEulerPieceHomeomorph i) (hfilling i)
  have hoverlap : ∀ i : Fin 3, Subsingleton (IntegralSingularHomology 6
      (C.stage i.castSucc ∩ C.piece i.succ : Set (GluedSpace A.toFourPieceStarGluingData.glueData))) :=
    fun i => subsingleton_homology_of_homeomorph 6
      (A.collarToMayerVietorisOverlapHomeomorph i) (hcollar i)
  have hstage : ∀ r : Fin 4, Subsingleton (IntegralSingularHomology 7 (C.stage r)) := by
    intro r
    induction r using Fin.induction with
    | zero =>
        refine subsingleton_homology_of_homeomorph 7
          (Homeomorph.setCongr A.sectionSevenEulerStage_zero.symm) hpiece0
    | succ i ih =>
        have hunion : Subsingleton (IntegralSingularHomology 7
            ((C.stage i.castSucc ∪ C.piece i.succ :
              Set (GluedSpace A.toFourPieceStarGluingData.glueData)))) :=
          subsingleton_homology_seven_union _ _ (C.isOpen_stage i.castSucc)
            (C.isOpen_piece i.succ) ih (hpieceSucc i) (hoverlap i)
        exact subsingleton_homology_of_homeomorph 7
          (A.sectionSevenEulerStageNextHomeomorph i) hunion
  intro r
  exact subsingleton_homology_seven_union _ _ (C.isOpen_stage r.castSucc)
    (C.isOpen_piece r.succ) (hstage r.castSucc) (hpieceSucc r) (hoverlap r)

/-- The form consumed by the Section 7 assembly: the local finiteness data already supplies the
degree-seven vanishing of the four pieces, so only the collars' sixth homology is left. -/
public theorem sectionSevenStageTopDegreeVanishing_of_localFinite
    (hcentral : IntegralHomologyFiniteSix A.central)
    (hfilling : ∀ i, IntegralHomologyFiniteSix (A.filling i))
    (hcollar : ∀ i, Subsingleton (IntegralSingularHomology 6 (A.collarSource i))) :
    A.SectionSevenStageTopDegreeVanishing :=
  A.sectionSevenStageTopDegreeVanishing_of_collar
    (hcentral.homologyAboveDimension 7 (by norm_num))
    (fun i => (hfilling i).homologyAboveDimension 7 (by norm_num)) hcollar

end OpenEmbeddingStarData

end SphereSixComplex

end

end
