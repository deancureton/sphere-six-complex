module

public import SphereSixComplex.Geometry.PaperLocalCuspFillingConnected
public import SphereSixComplex.Geometry.PaperOpenEmbeddingStarNonempty
public import SphereSixComplex.Geometry.PaperStarComplexStructures
public import SphereSixComplex.Topology.ConnectedMayerVietorisDegreeZero
public import SphereSixComplex.Topology.SectionSevenMayerVietorisEuler
public import SphereSixComplex.Topology.SectionSevenMayerVietorisHomologyAssembly

/-!
# The final degree-zero Mayer--Vietoris map of the analytic star

The central family and all three filling pieces are path-connected because they are connected
complex manifolds.  Hence the penultimate stage and the final cusp piece are path-connected.
The remaining geometric input is stated exactly: path-connectedness of the punctured cusp collar.
Its homeomorphism with the actual final overlap then gives canonical augmentation bases in which
the final degree-zero Mayer--Vietoris map is `x ↦ (x, -x)`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The canonical conversion from one integer coordinate to a `Fin 1`-indexed vector. -/
public noncomputable def integerToFinOneAddEquiv : ℤ ≃+ (Fin 1 → ℤ) where
  toFun z := fun _ ↦ z
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by funext i; fin_cases i; rfl
  map_add' _ _ := rfl

/-- The canonical conversion from an integer pair to a `Fin 2`-indexed vector. -/
public noncomputable def integerPairToFinTwoAddEquiv : (ℤ × ℤ) ≃+ (Fin 2 → ℤ) where
  toFun z := ![z.1, z.2]
  invFun f := (f 0, f 1)
  left_inv z := by rcases z with ⟨x, y⟩; rfl
  right_inv f := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl

namespace Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The central source of the analytic star is path-connected. -/
public theorem starCentral_pathConnected : PathConnectedSpace A.CentralFamily := by
  let _ := A.starCentralCharts
  let _ : ConnectedSpace A.CentralFamily := A.centralFamily_connected
  let _ : LocallyPathConnectedSpace A.CentralFamily :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel A.CentralFamily
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- Every filling source of the analytic star is path-connected. -/
public theorem starFilling_pathConnected (i : Fin 3) :
    PathConnectedSpace (A.starFillingType i) := by
  let _ := A.starFillingCharts i
  let _ : ConnectedSpace (A.starFillingType i) := A.starFilling_connected i
  let _ : LocallyPathConnectedSpace (A.starFillingType i) :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel (A.starFillingType i)
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- The penultimate Mayer--Vietoris stage is the union of the central, order-three, and
order-four pieces. -/
public theorem sectionSevenFinalStage_eq_threePieceUnion :
    (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) =
      (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 0 ∪
      (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 1 ∪
      (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2 := by
  ext x
  simp only [FourPieceOpenCover.stage, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    fin_cases i <;> simp_all
  · rintro ((hx | hx) | hx)
    · exact ⟨0, by omega, hx⟩
    · exact ⟨1, by omega, hx⟩
    · exact ⟨2, by omega, hx⟩

/-- The penultimate Mayer--Vietoris stage of the analytic star is path-connected. -/
public theorem sectionSevenFinalStage_pathConnected :
    PathConnectedSpace
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) := by
  let _ : PathConnectedSpace A.CentralFamily := A.starCentral_pathConnected
  let _ : PathConnectedSpace (A.starFillingType 1) := A.starFilling_pathConnected 1
  let _ : PathConnectedSpace (A.starFillingType 2) := A.starFilling_pathConnected 2
  let _ : PathConnectedSpace A.openEmbeddingStarData.central := by
    change PathConnectedSpace A.CentralFamily
    exact A.starCentral_pathConnected
  let _ : PathConnectedSpace (A.openEmbeddingStarData.filling 1) := by
    change PathConnectedSpace (A.starFillingType 1)
    exact A.starFilling_pathConnected 1
  let _ : PathConnectedSpace (A.openEmbeddingStarData.filling 2) := by
    change PathConnectedSpace (A.starFillingType 2)
    exact A.starFilling_pathConnected 2
  let _ : PathConnectedSpace
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 0) :=
    pathConnectedSpace_of_homeomorph
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
  let _ : PathConnectedSpace
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 1) :=
    pathConnectedSpace_of_homeomorph
      (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 1)
  let _ : PathConnectedSpace
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2) :=
    pathConnectedSpace_of_homeomorph
      (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 2)
  have hPieceZero :
      IsPathConnected
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 0) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hPieceOne :
      IsPathConnected
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 1) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hPieceTwo :
      IsPathConnected
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hZeroOne :
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 0 ∩
        (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 1).Nonempty := by
    let _ : Nonempty (A.openEmbeddingStarData.collarSource 1) :=
      A.openEmbeddingStarData_collarSource_nonempty 1
    have h := Set.range_nonempty
      (A.openEmbeddingStarData.collarSourceToGlued (1 : Fin 3))
    rw [A.openEmbeddingStarData.range_collarSourceToGlued 1] at h
    exact h
  have hZeroTwo :
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 0 ∩
        (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2).Nonempty := by
    let _ : Nonempty (A.openEmbeddingStarData.collarSource 2) :=
      A.openEmbeddingStarData_collarSource_nonempty 2
    have h := Set.range_nonempty
      (A.openEmbeddingStarData.collarSourceToGlued (2 : Fin 3))
    rw [A.openEmbeddingStarData.range_collarSourceToGlued 2] at h
    exact h
  have hZeroOnePath :
      IsPathConnected
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 0 ∪
          (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 1) :=
    hPieceZero.union hPieceOne hZeroOne
  have hUnionInterTwo :
      (((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 0 ∪
          (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 1) ∩
        (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 2).Nonempty := by
    obtain ⟨x, hxzero, hxtwo⟩ := hZeroTwo
    exact ⟨x, Or.inl hxzero, hxtwo⟩
  apply isPathConnected_iff_pathConnectedSpace.mp
  rw [A.sectionSevenFinalStage_eq_threePieceUnion]
  exact hZeroOnePath.union hPieceTwo hUnionInterTwo

/-- The last piece in the paper's Mayer--Vietoris order is the cusp filling and is
path-connected. -/
public theorem sectionSevenFinalCuspPiece_pathConnected :
    PathConnectedSpace
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) := by
  let _ : PathConnectedSpace (A.starFillingType 0) := A.starFilling_pathConnected 0
  let _ : PathConnectedSpace (A.openEmbeddingStarData.filling 0) := by
    change PathConnectedSpace (A.starFillingType 0)
    exact A.starFilling_pathConnected 0
  exact pathConnectedSpace_of_homeomorph
    (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)

/-- The actual final overlap is exactly the central--cusp intersection. -/
public theorem sectionSevenFinalOverlap_eq_centralCuspIntersection :
    (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
      (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 =
      (A.openEmbeddingStarData.SectionSevenEulerCover).piece 0 ∩
        (A.openEmbeddingStarData.SectionSevenEulerCover).piece 1 := by
  ext x
  constructor
  · rintro ⟨hxstage, hxcusp⟩
    rw [FourPieceOpenCover.stage] at hxstage
    simp only [mem_iUnion] at hxstage
    obtain ⟨i, hi, hxi⟩ := hxstage
    fin_cases i
    · exact ⟨hxi, hxcusp⟩
    · have hbad :
          x ∈ (A.openEmbeddingStarData.SectionSevenEulerCover).piece 2 ∩
            (A.openEmbeddingStarData.SectionSevenEulerCover).piece 1 := ⟨hxi, hxcusp⟩
      have hempty :
          (A.openEmbeddingStarData.SectionSevenEulerCover).piece 2 ∩
            (A.openEmbeddingStarData.SectionSevenEulerCover).piece 1 = ∅ := by
        simpa using A.openEmbeddingStarData.fillingPiece_inter_fillingPiece
          (i := 1) (j := 0) (by decide)
      rw [hempty] at hbad
      exact hbad.elim
    · have hbad :
          x ∈ (A.openEmbeddingStarData.SectionSevenEulerCover).piece 3 ∩
            (A.openEmbeddingStarData.SectionSevenEulerCover).piece 1 := ⟨hxi, hxcusp⟩
      have hempty :
          (A.openEmbeddingStarData.SectionSevenEulerCover).piece 3 ∩
            (A.openEmbeddingStarData.SectionSevenEulerCover).piece 1 = ∅ := by
        simpa using A.openEmbeddingStarData.fillingPiece_inter_fillingPiece
          (i := 2) (j := 0) (by decide)
      rw [hempty] at hbad
      exact hbad.elim
    · change (3 : Fin 4) ≤ 2 at hi
      omega
  · rintro ⟨hxcentral, hxcusp⟩
    refine ⟨?_, hxcusp⟩
    rw [FourPieceOpenCover.stage]
    exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by omega, hxcentral⟩⟩

/-- The punctured cusp collar is homeomorphic to the actual final overlap. -/
public noncomputable def cuspCollarToSectionSevenFinalOverlapHomeomorph :
    A.openEmbeddingStarData.collarSource 0 ≃ₜ
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) :=
  (A.openEmbeddingStarData.collarToMayerVietorisOverlapHomeomorph 0).trans
    (Homeomorph.setCongr (by
      change
        (A.openEmbeddingStarData.SectionSevenEulerCover).stage 0 ∩
            (A.openEmbeddingStarData.SectionSevenEulerCover).piece 1 =
          (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage 2 ∩
            (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3
      rw [A.openEmbeddingStarData.sectionSevenEulerStage_zero]
      exact (A.sectionSevenFinalOverlap_eq_centralCuspIntersection).symm))

/-- Path-connectedness of the punctured cusp collar transports to the actual final overlap. -/
public theorem sectionSevenFinalOverlap_pathConnected
    (hCuspCollar : PathConnectedSpace (A.openEmbeddingStarData.collarSource 0)) :
    PathConnectedSpace
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) := by
  let _ := hCuspCollar
  exact pathConnectedSpace_of_homeomorph
    A.cuspCollarToSectionSevenFinalOverlapHomeomorph

/-- The canonical augmentation basis on the actual final overlap. -/
public noncomputable def sectionSevenFinalZeroSource
    (hCuspCollar : PathConnectedSpace (A.openEmbeddingStarData.collarSource 0)) :
    IntegralSingularHomology 0
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+ (Fin 1 → ℤ) := by
  let _ := A.sectionSevenFinalOverlap_pathConnected hCuspCollar
  exact (pathConnectedIntegralHomologyZeroEquivInteger _).trans integerToFinOneAddEquiv

/-- The product of the canonical augmentation bases on the two final sides. -/
public noncomputable def sectionSevenFinalZeroTarget :
    (IntegralSingularHomology 0
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)) ×
      IntegralSingularHomology 0
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3)) ≃+
      (Fin 2 → ℤ) := by
  let _ := A.sectionSevenFinalStage_pathConnected
  let _ := A.sectionSevenFinalCuspPiece_pathConnected
  exact ((pathConnectedIntegralHomologyZeroEquivInteger _).prodCongr
    (pathConnectedIntegralHomologyZeroEquivInteger _)).trans integerPairToFinTwoAddEquiv

/-- In the canonical augmentation bases, the actual final degree-zero difference map is the
displayed `Fin 1 → Fin 2` antidiagonal. -/
public theorem sectionSevenFinalZero_comm
    (hCuspCollar : PathConnectedSpace (A.openEmbeddingStarData.collarSource 0))
    (x : IntegralSingularHomology 0
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace)) :
    A.sectionSevenFinalZeroTarget
        (IntegralMayerVietoris.differenceMap
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
          ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) 0 x) =
      sectionSevenMayerVietorisFinalZeroHom
        (A.sectionSevenFinalZeroSource hCuspCollar x) := by
  let _ := A.sectionSevenFinalStage_pathConnected
  let _ := A.sectionSevenFinalCuspPiece_pathConnected
  let _ := A.sectionSevenFinalOverlap_pathConnected hCuspCollar
  have hnormal :=
    IntegralMayerVietoris.differenceMap_zero_apply_normalForm
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
      ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) x
  funext i
  fin_cases i
  · simpa [sectionSevenFinalZeroTarget, sectionSevenFinalZeroSource,
      integerPairToFinTwoAddEquiv, integerToFinOneAddEquiv,
      sectionSevenMayerVietorisFinalZeroHom] using congrArg Prod.fst hnormal
  · simpa [sectionSevenFinalZeroTarget, sectionSevenFinalZeroSource,
      integerPairToFinTwoAddEquiv, integerToFinOneAddEquiv,
      sectionSevenMayerVietorisFinalZeroHom] using congrArg Prod.snd hnormal

/-- The actual final degree-zero Mayer--Vietoris difference map is injective; no chosen homology
basis or compatibility square is an input. -/
public theorem sectionSevenFinalDifferenceZero_injective
    (hCuspCollar : PathConnectedSpace (A.openEmbeddingStarData.collarSource 0)) :
    Function.Injective
      (IntegralMayerVietoris.differenceMap
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3) 0) := by
  let _ := A.sectionSevenFinalStage_pathConnected
  let _ := A.sectionSevenFinalCuspPiece_pathConnected
  let _ := A.sectionSevenFinalOverlap_pathConnected hCuspCollar
  exact IntegralMayerVietoris.differenceMap_zero_injective _ _

end Geometry.PaperAnalyticData

end SphereSixComplex
