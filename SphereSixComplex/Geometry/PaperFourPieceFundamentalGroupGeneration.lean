module

public import SphereSixComplex.Geometry.PaperGluingData
public import SphereSixComplex.Topology.OpenCoverFundamentalGroup

/-!
# Fundamental-group generation for the paper's four-piece carrier

The van Kampen basepoint lies in both the central piece and the cusp filling, but in neither
elliptic filling.  Accordingly, this file absorbs the cusp filling into the root of a rooted
star cover and leaves the two elliptic fillings as its disjoint leaves.  The resulting theorem
is a direct specialization of compact loop subdivision to the actual glued carrier.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open SphereSixComplex.Topology

namespace SphereSixComplex

/-- The image of the central family in the paper's glued carrier. -/
public def paperVanKampenCentralPieceImage : Set PaperGluedCarrier :=
  Set.range (paperFourPieceStar.glueData.toGlueData.ι none)

/-- The image of the cusp filling in the paper's glued carrier. -/
public def paperVanKampenCuspPieceImage : Set PaperGluedCarrier :=
  Set.range (paperFourPieceStar.glueData.toGlueData.ι (some 0))

/-- The root of the paper star cover: central family together with the cusp filling. -/
public def paperVanKampenRootPieceImage : Set PaperGluedCarrier :=
  paperVanKampenCentralPieceImage ∪ paperVanKampenCuspPieceImage

/-- The two remaining leaves of the rooted paper star are the order-three and order-four
fillings. -/
public def paperVanKampenEllipticPieceImage (i : Fin 2) : Set PaperGluedCarrier :=
  Set.range (paperFourPieceStar.glueData.toGlueData.ι (some i.succ))

/-- The global van Kampen basepoint also has a representative in the cusp filling. -/
public theorem paperVanKampenBasepoint_mem_cuspPieceImage :
    paperVanKampenBasepoint ∈ paperVanKampenCuspPieceImage := by
  let z := Classical.choice (paperFourPieceStar_nonemptyCentralCollar 0)
  change ∃ y,
    paperFourPieceStar.glueData.toGlueData.ι (some 0) y =
      paperFourPieceStar.glueData.toGlueData.ι none z.1
  refine ⟨(paperFourPieceStar.collarEquiv 0 z).1, ?_⟩
  exact ((paperFourPieceStar.ι_none_eq_ι_some_iff_mem_collarPairRange 0 z.1
    (paperFourPieceStar.collarEquiv 0 z).1).mpr ⟨z, rfl⟩).symm

/-- The central image is path connected. -/
public theorem paperVanKampenCentralPieceImage_isPathConnected :
    IsPathConnected paperVanKampenCentralPieceImage := by
  let _ : PathConnectedSpace (paperFourPieceStar.glueData.U none) :=
    paperFourPieceStar_pathConnectedPiece none
  exact isPathConnected_range
    (paperFourPieceStar.glueData.ι_isOpenEmbedding none).continuous

/-- The cusp-filling image is path connected. -/
public theorem paperVanKampenCuspPieceImage_isPathConnected :
    IsPathConnected paperVanKampenCuspPieceImage := by
  let _ : PathConnectedSpace (paperFourPieceStar.glueData.U (some 0)) :=
    paperFourPieceStar_pathConnectedPiece (some 0)
  exact isPathConnected_range
    (paperFourPieceStar.glueData.ι_isOpenEmbedding (some 0)).continuous

/-- The central--cusp overlap is the image of the nonempty path-connected cusp collar. -/
public theorem paperVanKampenCentral_inter_cusp_isPathConnected :
    IsPathConnected
      (paperVanKampenCentralPieceImage ∩ paperVanKampenCuspPieceImage) := by
  rw [paperVanKampenCentralPieceImage, paperVanKampenCuspPieceImage,
    paperFourPieceStar.range_ι_none_inter_range_ι_some]
  exact @isPathConnected_range (paperFourPieceStar.centralCollar 0)
    PaperGluedCarrier inferInstance inferInstance
    (paperFourPieceStar_pathConnectedCentralCollar 0) _
    ((paperFourPieceStar.glueData.ι_isOpenEmbedding none).continuous.comp
      continuous_subtype_val)

/-- Root loops and elliptic-filling loops, whiskered through the central--cusp root, generate
the fundamental group of the actual four-piece glued carrier. -/
public theorem paperVanKampenRootedStarLoopClasses_generate :
    Subgroup.closure
        (rootedStarCoverLoopClasses paperVanKampenRootPieceImage
          paperVanKampenEllipticPieceImage paperVanKampenBasepoint) = ⊤ := by
  apply rootedStarCoverLoopClasses_generate
  · exact (paperFourPieceStar.glueData.ι_isOpenEmbedding none).isOpen_range.union
      (paperFourPieceStar.glueData.ι_isOpenEmbedding (some 0)).isOpen_range
  · intro i
    exact (paperFourPieceStar.glueData.ι_isOpenEmbedding (some i.succ)).isOpen_range
  · intro p _
    obtain ⟨j, x, hx⟩ := paperFourPieceStar.glueData.ι_jointly_surjective p
    cases j with
    | none => exact Or.inl (Or.inl ⟨x, hx⟩)
    | some j =>
        fin_cases j
        · exact Or.inl (Or.inr ⟨x, hx⟩)
        · exact Or.inr (Set.mem_iUnion.2 ⟨0, ⟨x, hx⟩⟩)
        · exact Or.inr (Set.mem_iUnion.2 ⟨1, ⟨x, hx⟩⟩)
  · exact Or.inl ⟨paperVanKampenCentralPoint, rfl⟩
  · intro i hi
    obtain ⟨y, hy⟩ := hi
    have hcentral : paperVanKampenCentralPoint ∈
        paperFourPieceStar.centralCollar i.succ := by
      apply (paperFourPieceStar.exists_ι_none_eq_ι_some_iff_mem_centralCollar
        i.succ paperVanKampenCentralPoint).mp
      exact ⟨y, hy.symm⟩
    have hcusp : paperVanKampenCentralPoint ∈
        paperFourPieceStar.centralCollar 0 :=
      (Classical.choice (paperFourPieceStar_nonemptyCentralCollar 0)).2
    have hdisjoint : Disjoint (paperFourPieceStar.centralCollar 0)
        (paperFourPieceStar.centralCollar i.succ) :=
      paperFourPieceStar.centralCollar_disjoint (by
        intro h
        have hval := congrArg Fin.val h
        simp at hval)
    have hbot : paperVanKampenCentralPoint ∈
        (⊥ : Opens paperFourPieceStar.central) :=
      hdisjoint.le_bot ⟨hcusp, hcentral⟩
    have hempty : paperVanKampenCentralPoint ∈
        (∅ : Set paperFourPieceStar.central) := hbot
    exact hempty
  · have hcentral : IsPathConnected paperVanKampenCentralPieceImage := by
      let _ : PathConnectedSpace (paperFourPieceStar.glueData.U none) :=
        paperFourPieceStar_pathConnectedPiece none
      exact isPathConnected_range
        (paperFourPieceStar.glueData.ι_isOpenEmbedding none).continuous
    have hcusp : IsPathConnected paperVanKampenCuspPieceImage := by
      let _ : PathConnectedSpace (paperFourPieceStar.glueData.U (some 0)) :=
        paperFourPieceStar_pathConnectedPiece (some 0)
      exact isPathConnected_range
        (paperFourPieceStar.glueData.ι_isOpenEmbedding (some 0)).continuous
    have hinter :
        (paperVanKampenCentralPieceImage ∩ paperVanKampenCuspPieceImage).Nonempty := by
      rw [paperVanKampenCentralPieceImage, paperVanKampenCuspPieceImage,
        paperFourPieceStar.range_ι_none_inter_range_ι_some]
      let z := Classical.choice (paperFourPieceStar_nonemptyCentralCollar 0)
      exact ⟨_, z, rfl⟩
    exact hcentral.union hcusp hinter
  · intro i
    let _ : PathConnectedSpace
        (paperFourPieceStar.glueData.U (some i.succ)) :=
      paperFourPieceStar_pathConnectedPiece (some i.succ)
    exact isPathConnected_range
      (paperFourPieceStar.glueData.ι_isOpenEmbedding (some i.succ)).continuous
  · intro i
    have hdisjoint : Disjoint paperVanKampenCuspPieceImage
        (paperVanKampenEllipticPieceImage i) :=
      paperFourPieceStar.disjoint_range_ι_some_of_ne (by
        intro h
        have hval := congrArg Fin.val h
        simp at hval)
    have heq :
        paperVanKampenRootPieceImage ∩ paperVanKampenEllipticPieceImage i =
          paperVanKampenCentralPieceImage ∩ paperVanKampenEllipticPieceImage i := by
      ext p
      constructor
      · rintro ⟨hp | hp, hi⟩
        · exact ⟨hp, hi⟩
        · exact (Set.disjoint_left.1 hdisjoint hp hi).elim
      · rintro ⟨hp, hi⟩
        exact ⟨Or.inl hp, hi⟩
    rw [heq, paperVanKampenCentralPieceImage, paperVanKampenEllipticPieceImage,
      paperFourPieceStar.range_ι_none_inter_range_ι_some]
    exact @isPathConnected_range
      (paperFourPieceStar.centralCollar i.succ) PaperGluedCarrier
      inferInstance inferInstance
      (paperFourPieceStar_pathConnectedCentralCollar i.succ) _
      ((paperFourPieceStar.glueData.ι_isOpenEmbedding none).continuous.comp
        continuous_subtype_val)
  · intro i j hij
    exact paperFourPieceStar.disjoint_range_ι_some_of_ne
      (fun h ↦ hij (Fin.succ_injective 2 h))

/-- Elliptic-filling loop classes transported to the global basepoint along a path in the
central--cusp root. -/
public def paperVanKampenEllipticWhiskeredLoopClasses :
    Set (FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint) :=
  {g | ∃ (i : Fin 2) (x : PaperGluedCarrier),
    x ∈ paperVanKampenRootPieceImage ∩ paperVanKampenEllipticPieceImage i ∧
      ∃ (W : Path paperVanKampenBasepoint x) (L : Path x x),
        Set.range W ⊆ paperVanKampenRootPieceImage ∧
          Set.range L ⊆ paperVanKampenEllipticPieceImage i ∧
            openCoverLoopClass (W.trans (L.trans W.symm)) = g}

/-- The four individual piece-loop families used after splitting the central--cusp root. -/
public def paperVanKampenFourPieceLoopClasses :
    Set (FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint) :=
  binaryOpenCoverLoopClasses paperVanKampenCentralPieceImage
      paperVanKampenCuspPieceImage paperVanKampenBasepoint ∪
    paperVanKampenEllipticWhiskeredLoopClasses

/-- Loops in the four individual piece images generate the actual carrier fundamental group.
Unlike the rooted statement, the central--cusp union no longer appears as an indivisible source
of generators: every root loop has been subdivided into central and cusp loops. -/
public theorem paperVanKampenFourPieceLoopClasses_generate :
    Subgroup.closure paperVanKampenFourPieceLoopClasses = ⊤ := by
  let H : Subgroup (FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint) :=
    Subgroup.closure paperVanKampenFourPieceLoopClasses
  apply top_unique
  rw [← paperVanKampenRootedStarLoopClasses_generate]
  apply (Subgroup.closure_le _).2
  intro g hg
  rcases hg with hg | hg
  · obtain ⟨L, hL, rfl⟩ := hg
    have hmember := binaryOpenCoverLoopClass_mem_closure
      paperVanKampenCentralPieceImage paperVanKampenCuspPieceImage
      paperVanKampenBasepoint
      (paperFourPieceStar.glueData.ι_isOpenEmbedding none).isOpen_range
      (paperFourPieceStar.glueData.ι_isOpenEmbedding (some 0)).isOpen_range
      ⟨paperVanKampenCentralPoint, rfl⟩
      paperVanKampenBasepoint_mem_cuspPieceImage
      paperVanKampenCentralPieceImage_isPathConnected
      paperVanKampenCuspPieceImage_isPathConnected
      paperVanKampenCentral_inter_cusp_isPathConnected L (by
        simpa [paperVanKampenRootPieceImage] using hL)
    exact Subgroup.closure_mono Set.subset_union_left hmember
  · apply Subgroup.subset_closure
    exact Or.inr hg


end SphereSixComplex

end
