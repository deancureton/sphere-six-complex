module

public import SphereSixComplex.Topology.ConcreteVanKampen
public import SphereSixComplex.Topology.PaperEllipticCollarFundamentalDomain
public import SphereSixComplex.Topology.PaperSectionSevenFinalDegreeZero
public import Mathlib.Analysis.Convex.PathConnected

/-!
# The actual four-piece van Kampen cover

The open images of the central family and the three filling pieces form the paper's geometric
van Kampen cover.  The elliptic overlaps are path-connected through their radial mapping-torus
models; the cusp overlap is handled by the additive cusp cover.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology
open scoped FundamentalGroupoid

namespace SphereSixComplex

/-- A positive open radial interval is path-connected. -/
public theorem openRadialInterval_pathConnected (r : ℝ) (hr : 0 < r) :
    PathConnectedSpace (OpenRadialInterval r) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  change IsPathConnected (Set.Ioo 0 r)
  exact ((convex_Ioo (𝕜 := ℝ) 0 r).isPathConnected
    ⟨r / 2, half_pos hr, half_lt_self hr⟩)

/-- The mapping torus of a self-homeomorphism of a path-connected space is path-connected. -/
public theorem circleMappingTorus_pathConnected
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F] (e : F ≃ₜ F) :
    PathConnectedSpace (CircleMappingTorus e) := by
  let _ : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (𝕜 := ℝ) 0 1).isPathConnected ⟨0, by simp⟩)
  let _ : PathConnectedSpace (Unit × unitInterval × F) := inferInstance
  change PathConnectedSpace
    (Quotient (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ e)))
  infer_instance

namespace Geometry.PaperAnalyticData

open AnalyticTorusFamily EllipticFamilySpecialization

variable (A : PaperAnalyticData)

/-- The actual order-three collar source is path-connected. -/
public theorem starOrderThreeCollarSource_pathConnected :
    PathConnectedSpace (A.openEmbeddingStarData.collarSource 1) := by
  let _ : PathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius) :=
    openRadialInterval_pathConnected _ A.starSeparation.orderThree.radius_pos
  let _ : PathConnectedSpace
      (AdditiveTorus
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1) := inferInstance
  let _ : PathConnectedSpace
      (CircleMappingTorus (orderThreeAffineClutchingHomeomorph A.periods)) :=
    circleMappingTorus_pathConnected _
  let _ : PathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        CircleMappingTorus (orderThreeAffineClutchingHomeomorph A.periods)) := inferInstance
  exact pathConnectedSpace_of_homeomorph A.orderThreeCollarRadialMappingTorusHomeomorph.symm

/-- The actual order-four collar source is path-connected. -/
public theorem starOrderFourCollarSource_pathConnected :
    PathConnectedSpace (A.openEmbeddingStarData.collarSource 2) := by
  let _ : PathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius) :=
    openRadialInterval_pathConnected _ A.starSeparation.orderFour.radius_pos
  let _ : PathConnectedSpace
      (AdditiveTorus
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1) := inferInstance
  let _ : PathConnectedSpace
      (CircleMappingTorus (orderFourAffineClutchingHomeomorph A.periods)) :=
    circleMappingTorus_pathConnected _
  let _ : PathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        CircleMappingTorus (orderFourAffineClutchingHomeomorph A.periods)) := inferInstance
  exact pathConnectedSpace_of_homeomorph A.orderFourCollarRadialMappingTorusHomeomorph.symm

/-- All three actual collar sources are path-connected. -/
public theorem starCollarSource_pathConnected (i : Fin 3) :
    PathConnectedSpace (A.openEmbeddingStarData.collarSource i) := by
  fin_cases i
  · exact A.starCuspCollarSource_pathConnected
  · exact A.starOrderThreeCollarSource_pathConnected
  · exact A.starOrderFourCollarSource_pathConnected

/-- The glued space underlying the actual analytic star. -/
public abbrev VanKampenSpace :=
  GluedSpace A.openEmbeddingStarData.toFourPieceStarGluingData.glueData

/-- The canonical four open images of the actual analytic star. -/
public noncomputable abbrev VanKampenOpenCover :=
  sectionSevenStarOpenCover A.openEmbeddingStarData.toFourPieceStarGluingData

/-- The canonical central and filling images, with concrete connector paths in the central
piece, form the exact four-piece cover consumed by the finite van Kampen diagram. -/
public noncomputable def actualVanKampenFourPieceCover :
    Topology.PaperVanKampenFourPieceCover
      (A.openEmbeddingStarData.collarSourceToGlued 0
        (Classical.choice (A.starCollarSourceType_nonempty 0))) := by
  let S := A.openEmbeddingStarData
  let C := VanKampenOpenCover A
  let s₀ : S.collarSource 0 := Classical.choice (A.starCollarSourceType_nonempty 0)
  let s₁ : S.collarSource 1 := Classical.choice (A.starCollarSourceType_nonempty 1)
  let s₂ : S.collarSource 2 := Classical.choice (A.starCollarSourceType_nonempty 2)
  let p₀ : VanKampenSpace A := S.collarSourceToGlued 0 s₀
  let p₁ : VanKampenSpace A := S.collarSourceToGlued 1 s₁
  let p₂ : VanKampenSpace A := S.collarSourceToGlued 2 s₂
  have hp₀ : p₀ ∈ C.piece 0 ∩ C.piece 1 := by
    have h : p₀ ∈ Set.range (S.collarSourceToGlued 0) := ⟨s₀, rfl⟩
    rw [S.range_collarSourceToGlued 0] at h
    simpa [C, VanKampenOpenCover] using h
  have hp₁ : p₁ ∈ C.piece 0 ∩ C.piece 2 := by
    have h : p₁ ∈ Set.range (S.collarSourceToGlued 1) := ⟨s₁, rfl⟩
    rw [S.range_collarSourceToGlued 1] at h
    simpa [C, VanKampenOpenCover] using h
  have hp₂ : p₂ ∈ C.piece 0 ∩ C.piece 3 := by
    have h : p₂ ∈ Set.range (S.collarSourceToGlued 2) := ⟨s₂, rfl⟩
    rw [S.range_collarSourceToGlued 2] at h
    simpa [C, VanKampenOpenCover] using h
  let _ : PathConnectedSpace A.CentralFamily := A.starCentral_pathConnected
  let _ : PathConnectedSpace S.central := A.starCentral_pathConnected
  let _ : PathConnectedSpace (C.piece 0) :=
    pathConnectedSpace_of_homeomorph S.centralToSectionSevenEulerPieceHomeomorph
  have hcore : IsPathConnected (C.piece 0) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hjoin₁ : JoinedIn (C.piece 0) p₀ p₁ := hcore.joinedIn p₀ hp₀.1 p₁ hp₁.1
  have hjoin₂ : JoinedIn (C.piece 0) p₀ p₂ := hcore.joinedIn p₀ hp₀.1 p₂ hp₂.1
  let connector₁ : Path p₀ p₁ := Classical.choose hjoin₁
  let connector₂ : Path p₀ p₂ := Classical.choose hjoin₂
  let _ (i : Fin 3) : PathConnectedSpace (S.filling i) := A.starFilling_pathConnected i
  let _ (i : Fin 3) : PathConnectedSpace (C.piece i.succ) :=
    pathConnectedSpace_of_homeomorph (S.fillingToSectionSevenEulerPieceHomeomorph i)
  have hfilling (i : Fin 3) : IsPathConnected (C.piece i.succ) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  let _ (i : Fin 3) : PathConnectedSpace (S.collarSource i) :=
    A.starCollarSource_pathConnected i
  have hoverlap (i : Fin 3) : IsPathConnected (C.piece 0 ∩ C.piece i.succ) := by
    let _ : PathConnectedSpace
        (finiteCoverIntersection C.piece {0, i.succ}) :=
      pathConnectedSpace_of_homeomorph (S.centralFillingIntersectionHomeomorph i)
    rw [show C.piece 0 ∩ C.piece i.succ = finiteCoverIntersection C.piece {0, i.succ} by
      ext x
      simp [finiteCoverIntersection, and_comm]]
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  refine
    { core := C.piece 0
      cusp := C.piece 1
      ellipticThree := C.piece 2
      ellipticFour := C.piece 3
      core_isOpen := C.isOpen_piece 0
      cusp_isOpen := C.isOpen_piece 1
      ellipticThree_isOpen := C.isOpen_piece 2
      ellipticFour_isOpen := C.isOpen_piece 3
      covers := ?_
      cusp_disjoint_ellipticThree := ?_
      cusp_disjoint_ellipticFour := ?_
      ellipticThree_disjoint_ellipticFour := ?_
      core_pathConnected := hcore
      cusp_pathConnected := hfilling 0
      ellipticThree_pathConnected := hfilling 1
      ellipticFour_pathConnected := hfilling 2
      cusp_overlap_pathConnected := hoverlap 0
      ellipticThree_overlap_pathConnected := hoverlap 1
      ellipticFour_overlap_pathConnected := hoverlap 2
      base_mem_core := hp₀.1
      cuspPoint := p₀
      cuspPoint_mem := hp₀
      cuspConnector := Path.refl p₀
      cuspConnector_mem := fun _ ↦ hp₀.1
      ellipticThreePoint := p₁
      ellipticThreePoint_mem := hp₁
      ellipticThreeConnector := connector₁
      ellipticThreeConnector_mem := Classical.choose_spec hjoin₁
      ellipticFourPoint := p₂
      ellipticFourPoint_mem := hp₂
      ellipticFourConnector := connector₂
      ellipticFourConnector_mem := Classical.choose_spec hjoin₂ }
  · rw [← C.covers]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (((hx | hx) | hx) | hx)
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
      · exact ⟨2, hx⟩
      · exact ⟨3, hx⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
  · rw [Set.disjoint_iff_inter_eq_empty]
    exact S.fillingPiece_inter_fillingPiece (i := 0) (j := 1) (by decide)
  · rw [Set.disjoint_iff_inter_eq_empty]
    exact S.fillingPiece_inter_fillingPiece (i := 0) (j := 2) (by decide)
  · rw [Set.disjoint_iff_inter_eq_empty]
    exact S.fillingPiece_inter_fillingPiece (i := 1) (j := 2) (by decide)

/-- The fundamental groupoid of the actual glued space is the colimit of the four actual pieces
and their pairwise intersections. -/
public theorem actualPairwiseVanKampenCocone_isColimit :
    let D := A.actualVanKampenFourPieceCover
    Nonempty
      (IsColimit
        ((πₒ (TopCat.of A.VanKampenSpace)).mapCocone
          (CategoryTheory.Pairwise.cocone D.opens))) := by
  exact A.actualVanKampenFourPieceCover.pairwiseVanKampenCocone_isColimit

end Geometry.PaperAnalyticData

end SphereSixComplex

end
