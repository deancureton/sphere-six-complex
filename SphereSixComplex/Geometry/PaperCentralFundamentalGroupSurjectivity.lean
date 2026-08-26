module

public import SphereSixComplex.Geometry.PaperFourPieceFundamentalGroupGeneration
public import SphereSixComplex.Geometry.PaperEllipticFundamentalGroupSurjectivity
public import SphereSixComplex.Geometry.PaperCuspFundamentalGroupSurjectivity

/-!
# Surjectivity from the central family to the four-piece paper carrier

Each filling is attached along an open collar whose map to that filling is surjective on
fundamental groups.  Combining those three local statements with the actual four-piece open-cover
generation theorem shows that the central family already carries every loop class in the glued
carrier.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open SphereSixComplex.Topology
open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge

namespace SphereSixComplex

public abbrev PaperA := Geometry.establishedPaperAnalyticData

/-- The common collar source included into the central family. -/
public noncomputable def paperStarCollarToCentral (i : Fin 3) :
    C(PaperA.starCollarSourceType i, PaperA.CentralFamily) :=
  ⟨PaperA.starToCentral i, (PaperA.starToCentral_isOpenEmbedding i).continuous⟩

/-- The common collar source included into its filling. -/
public noncomputable def paperStarCollarToFilling (i : Fin 3) :
    C(PaperA.starCollarSourceType i, PaperA.starFillingType i) :=
  ⟨PaperA.starToFilling i, (PaperA.starToFilling_isOpenEmbedding i).continuous⟩

/-- Include one of the three fillings into the glued carrier. -/
public noncomputable def paperStarFillingToCarrier (i : Fin 3) :
    C(PaperA.starFillingType i, PaperGluedCarrier) :=
  ⟨paperFourPieceStar.glueData.toGlueData.ι (some i),
    (paperFourPieceStar.glueData.ι_isOpenEmbedding (some i)).continuous⟩

/-- The central and filling representatives of a common-source collar point have the same image
in the glued carrier. -/
public theorem paperStarCollar_glue (i : Fin 3) (q : PaperA.starCollarSourceType i) :
    paperVanKampenCentralToCarrier (paperStarCollarToCentral i q) =
      paperStarFillingToCarrier i (paperStarCollarToFilling i q) := by
  exact OpenEmbeddingStarData.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
    PaperA.openEmbeddingStarData i q

/-- All three chosen collar-to-filling maps are surjective on fundamental groups at every
basepoint. -/
public theorem paperStarCollarToFilling_fundamentalGroup_surjective
    (i : Fin 3) (q : PaperA.starCollarSourceType i) :
    Function.Surjective (FundamentalGroup.map (paperStarCollarToFilling i) q) := by
  fin_cases i
  · exact puncturedLocalCuspToFilling_fundamentalGroup_surjective_at
      PaperA.starCuspWitness q
  · exact PaperA.orderThreePuncturedCollarToFilling_fundamentalGroup_surjective_at
      PaperA.starSeparation.orderThree.radius_pos
      PaperA.starSeparation.orderThree.radius_lt_one q
  · exact PaperA.orderFourPuncturedCollarToFilling_fundamentalGroup_surjective_at
      PaperA.starSeparation.orderFour.radius_pos
      PaperA.starSeparation.orderFour.radius_lt_one q

/-- The two ways of mapping a collar fundamental-group class into the glued carrier agree. -/
public theorem paperStarCollar_fundamentalGroup_glue
    (i : Fin 3) (q : PaperA.starCollarSourceType i)
    (v : FundamentalGroup (PaperA.starCollarSourceType i) q) :
    FundamentalGroup.map paperVanKampenCentralToCarrier
        (paperStarCollarToCentral i q)
        (FundamentalGroup.map (paperStarCollarToCentral i) q v) =
      FundamentalGroup.mapOfEq (paperStarFillingToCarrier i)
        (paperStarCollar_glue i q).symm
        (FundamentalGroup.map (paperStarCollarToFilling i) q v) := by
  induction v using Quotient.ind with
  | _ P =>
      rw [FundamentalGroup.mapOfEq_apply]
      change Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk P)
            (paperStarCollarToCentral i)) paperVanKampenCentralToCarrier =
        (Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk P)
            (paperStarCollarToFilling i)) (paperStarFillingToCarrier i)).cast
              (paperStarCollar_glue i q) (paperStarCollar_glue i q)
      rw [← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_cast]
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      exact paperStarCollar_glue i (P t)

/-- A loop in a filling, based at a collar point and transported to the global basepoint along a
central path, comes from the fundamental group of the central family. -/
public theorem paperStarFilling_whiskeredLoopClass_mem_central_range
    (i : Fin 3) (q : PaperA.starCollarSourceType i)
    (W : Path paperVanKampenCentralPoint (paperStarCollarToCentral i q))
    (L : Path
      (paperVanKampenCentralToCarrier (paperStarCollarToCentral i q))
      (paperVanKampenCentralToCarrier (paperStarCollarToCentral i q)))
    (hL : Set.range L ⊆ Set.range (paperStarFillingToCarrier i)) :
    whiskeredLoopClass (W.map paperVanKampenCentralToCarrier.continuous) L ∈
      (FundamentalGroup.map paperVanKampenCentralToCarrier
        paperVanKampenCentralPoint).range := by
  obtain ⟨u, hu⟩ :=
    openEmbedding_loopClass_mem_fundamentalGroupMapOfEq_range
      (paperStarFillingToCarrier i)
      (paperFourPieceStar.glueData.ι_isOpenEmbedding (some i))
      (paperStarCollarToFilling i q)
      (paperVanKampenCentralToCarrier (paperStarCollarToCentral i q))
      (paperStarCollar_glue i q).symm L hL
  obtain ⟨v, hv⟩ :=
    paperStarCollarToFilling_fundamentalGroup_surjective i q u
  induction v using Quotient.ind with
  | _ P =>
      have hlocal :
          pathLoopClass
              (((P.map (paperStarCollarToCentral i).continuous).map
                paperVanKampenCentralToCarrier.continuous)) =
            pathLoopClass L := by
        calc
          pathLoopClass
              (((P.map (paperStarCollarToCentral i).continuous).map
                paperVanKampenCentralToCarrier.continuous)) =
              FundamentalGroup.map paperVanKampenCentralToCarrier
                (paperStarCollarToCentral i q)
                (FundamentalGroup.map (paperStarCollarToCentral i) q
                  (pathLoopClass P)) := by
            rfl
          _ = FundamentalGroup.mapOfEq (paperStarFillingToCarrier i)
                (paperStarCollar_glue i q).symm
                (FundamentalGroup.map (paperStarCollarToFilling i) q
                  (pathLoopClass P)) :=
            paperStarCollar_fundamentalGroup_glue i q (pathLoopClass P)
          _ = FundamentalGroup.mapOfEq (paperStarFillingToCarrier i)
                (paperStarCollar_glue i q).symm u := by
            exact congrArg
              (FundamentalGroup.mapOfEq (paperStarFillingToCarrier i)
                (paperStarCollar_glue i q).symm) hv
          _ = pathLoopClass L := hu
      let WG : Path paperVanKampenBasepoint
          (paperVanKampenCentralToCarrier (paperStarCollarToCentral i q)) :=
        W.map paperVanKampenCentralToCarrier.continuous
      have htransport := congrArg
        (FundamentalGroup.fundamentalGroupMulEquivOfPath WG).symm hlocal
      rw [fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass,
        fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass] at htransport
      refine ⟨whiskeredLoopClass W
        (P.map (paperStarCollarToCentral i).continuous), ?_⟩
      have hmap := mapOfEq_whiskeredLoopClass
        paperVanKampenCentralToCarrier rfl rfl W
          (P.map (paperStarCollarToCentral i).continuous)
      have hmap' :
          FundamentalGroup.mapOfEq paperVanKampenCentralToCarrier rfl
              (whiskeredLoopClass W
                (P.map (paperStarCollarToCentral i).continuous)) =
            whiskeredLoopClass
              (W.map paperVanKampenCentralToCarrier.continuous)
              ((P.map (paperStarCollarToCentral i).continuous).map
                paperVanKampenCentralToCarrier.continuous) := by
        simpa using hmap
      calc
        FundamentalGroup.map paperVanKampenCentralToCarrier
            paperVanKampenCentralPoint
            (whiskeredLoopClass W
              (P.map (paperStarCollarToCentral i).continuous)) =
            FundamentalGroup.mapOfEq paperVanKampenCentralToCarrier rfl
              (whiskeredLoopClass W
                (P.map (paperStarCollarToCentral i).continuous)) := by
          rw [FundamentalGroup.mapOfEq_apply]
          rfl
        _ = whiskeredLoopClass
            (W.map paperVanKampenCentralToCarrier.continuous) L := by
          dsimp only [WG] at htransport
          exact hmap'.trans htransport

/-- The concrete central family is path connected. -/
public noncomputable instance paperCentralFamily_pathConnectedSpace :
    PathConnectedSpace PaperA.CentralFamily := by
  change PathConnectedSpace (paperFourPieceStar.glueData.U none)
  exact paperFourPieceStar_pathConnectedPiece none

/-- A chosen path in the central family from the global basepoint representative to a collar
point. -/
public noncomputable def paperCentralPathToCollar (i : Fin 3)
    (q : PaperA.starCollarSourceType i) :
    Path paperVanKampenCentralPoint (paperStarCollarToCentral i q) :=
  PathConnectedSpace.somePath _ _

/-- The subgroup of global loop classes coming from the central family. -/
public noncomputable def paperCentralFundamentalGroupRange :
    Subgroup (FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint) :=
  (FundamentalGroup.map paperVanKampenCentralToCarrier
    paperVanKampenCentralPoint).range

/-- A based loop contained in the central-piece image belongs to the central subgroup. -/
public theorem paperCentralPiece_loopClass_mem_central_range
    (L : Path paperVanKampenBasepoint paperVanKampenBasepoint)
    (hL : Set.range L ⊆ paperVanKampenCentralPieceImage) :
    openCoverLoopClass L ∈ paperCentralFundamentalGroupRange := by
  exact openEmbedding_loopClass_mem_fundamentalGroupMap_range
    paperVanKampenCentralToCarrier
    (paperFourPieceStar.glueData.ι_isOpenEmbedding none)
    paperVanKampenCentralPoint L hL

/-- Every point in a central--filling overlap has a representative in the common collar source. -/
public theorem exists_paperStarCollarSource_of_mem_intersection
    (i : Fin 3) (x : PaperGluedCarrier)
    (hx : x ∈ paperVanKampenCentralPieceImage ∩
      Set.range (paperStarFillingToCarrier i)) :
    ∃ q : PaperA.starCollarSourceType i,
      paperVanKampenCentralToCarrier (paperStarCollarToCentral i q) = x := by
  change x ∈
    Set.range (paperFourPieceStar.glueData.toGlueData.ι none) ∩
      Set.range (paperFourPieceStar.glueData.toGlueData.ι (some i)) at hx
  rw [paperFourPieceStar.range_ι_none_inter_range_ι_some] at hx
  obtain ⟨z, hz⟩ := hx
  obtain ⟨q, hq⟩ := z.2
  change PaperA.starToCentral i q = z.1 at hq
  refine ⟨q, ?_⟩
  change paperFourPieceStar.glueData.toGlueData.ι none
      (PaperA.starToCentral i q) = x
  exact (congrArg (paperFourPieceStar.glueData.toGlueData.ι none) hq).trans hz

/-- A loop in the cusp filling based at the global cusp-collar point belongs to the central
subgroup. -/
public theorem paperCuspPiece_loopClass_mem_central_range
    (L : Path paperVanKampenBasepoint paperVanKampenBasepoint)
    (hL : Set.range L ⊆ paperVanKampenCuspPieceImage) :
    openCoverLoopClass L ∈ paperCentralFundamentalGroupRange := by
  have hbinter : paperVanKampenBasepoint ∈
      paperVanKampenCentralPieceImage ∩
        Set.range (paperStarFillingToCarrier 0) := by
    constructor
    · exact ⟨paperVanKampenCentralPoint, rfl⟩
    · exact paperVanKampenBasepoint_mem_cuspPieceImage
  obtain ⟨q, hq⟩ :=
    exists_paperStarCollarSource_of_mem_intersection 0
      paperVanKampenBasepoint hbinter
  let W := paperCentralPathToCollar 0 q
  let WG : Path paperVanKampenBasepoint paperVanKampenBasepoint :=
    (W.map paperVanKampenCentralToCarrier.continuous).cast rfl hq.symm
  let Lq : Path
      (paperVanKampenCentralToCarrier (paperStarCollarToCentral 0 q))
      (paperVanKampenCentralToCarrier (paperStarCollarToCentral 0 q)) :=
    L.cast hq hq
  have hLq : Set.range Lq ⊆ Set.range (paperStarFillingToCarrier 0) := by
    change Set.range Lq ⊆ paperVanKampenCuspPieceImage
    intro y hy
    obtain ⟨t, rfl⟩ := hy
    exact hL ⟨t, rfl⟩
  have hwhiskered :
      whiskeredLoopClass
          (W.map paperVanKampenCentralToCarrier.continuous) Lq ∈
        paperCentralFundamentalGroupRange :=
    paperStarFilling_whiskeredLoopClass_mem_central_range 0 q W Lq hLq
  have hWG : pathLoopClass WG ∈ paperCentralFundamentalGroupRange := by
    apply paperCentralPiece_loopClass_mem_central_range WG
    intro y hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨W t, rfl⟩
  have hconj := whiskeredLoopClass_eq_conjugate_cast
    (W.map paperVanKampenCentralToCarrier.continuous) Lq hq
  change whiskeredLoopClass
      (W.map paperVanKampenCentralToCarrier.continuous) Lq =
    (pathLoopClass WG)⁻¹ *
      pathLoopClass (Lq.cast hq.symm hq.symm) * pathLoopClass WG at hconj
  have hrhs :
      (pathLoopClass WG)⁻¹ *
          pathLoopClass (Lq.cast hq.symm hq.symm) * pathLoopClass WG ∈
        paperCentralFundamentalGroupRange := by
    rw [← hconj]
    exact hwhiskered
  have hmiddle := paperCentralFundamentalGroupRange.mul_mem
    (paperCentralFundamentalGroupRange.mul_mem hWG hrhs)
    (paperCentralFundamentalGroupRange.inv_mem hWG)
  have hcast : Lq.cast hq.symm hq.symm = L := by
    apply Path.ext
    funext t
    rfl
  change pathLoopClass L ∈ paperCentralFundamentalGroupRange
  simpa only [mul_assoc, mul_inv_cancel, mul_inv_cancel_left, mul_one, one_mul,
    hcast] using hmiddle

/-- Every generator contributed by one of the two members of the central--cusp binary cover lies
in the central subgroup. -/
public theorem paperBinaryOpenCoverLoopClass_mem_central_range
    {g : FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint}
    (hg : g ∈ binaryOpenCoverLoopClasses paperVanKampenCentralPieceImage
      paperVanKampenCuspPieceImage paperVanKampenBasepoint) :
    g ∈ paperCentralFundamentalGroupRange := by
  obtain ⟨L, hL, rfl⟩ := hg
  rcases hL with hcentral | hcusp
  · exact paperCentralPiece_loopClass_mem_central_range L hcentral
  · exact paperCuspPiece_loopClass_mem_central_range L hcusp

/-- Every based loop contained in the central--cusp root belongs to the central subgroup. -/
public theorem paperRootPiece_loopClass_mem_central_range
    (L : Path paperVanKampenBasepoint paperVanKampenBasepoint)
    (hL : Set.range L ⊆ paperVanKampenRootPieceImage) :
    openCoverLoopClass L ∈ paperCentralFundamentalGroupRange := by
  have hclosure := binaryOpenCoverLoopClass_mem_closure
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
  exact ((Subgroup.closure_le paperCentralFundamentalGroupRange).2 fun _ h ↦
    paperBinaryOpenCoverLoopClass_mem_central_range h) hclosure

/-- An elliptic-filling loop, transported through the root as in the rooted-star generating
family, belongs to the central subgroup. -/
public theorem paperEllipticWhiskeredLoopClass_mem_central_range
    (i : Fin 2) (x : PaperGluedCarrier)
    (hx : x ∈ paperVanKampenRootPieceImage ∩
      paperVanKampenEllipticPieceImage i)
    (W : Path paperVanKampenBasepoint x) (L : Path x x)
    (hW : Set.range W ⊆ paperVanKampenRootPieceImage)
    (hL : Set.range L ⊆ paperVanKampenEllipticPieceImage i) :
    whiskeredLoopClass W L ∈ paperCentralFundamentalGroupRange := by
  have hcentral : x ∈ paperVanKampenCentralPieceImage := by
    rcases hx.1 with hcentral | hcusp
    · exact hcentral
    · exfalso
      have hne : (0 : Fin 3) ≠ i.succ := by
        exact (Fin.succ_ne_zero i).symm
      have hd := paperFourPieceStar.disjoint_range_ι_some_of_ne hne
      apply Set.disjoint_left.1 hd hcusp
      exact hx.2
  have hxFilling : x ∈ Set.range (paperStarFillingToCarrier i.succ) := by
    rcases hx.2 with ⟨y, hy⟩
    exact ⟨y, hy⟩
  have hinter : x ∈ paperVanKampenCentralPieceImage ∩
      Set.range (paperStarFillingToCarrier i.succ) := ⟨hcentral, hxFilling⟩
  obtain ⟨q, hq⟩ :=
    exists_paperStarCollarSource_of_mem_intersection i.succ x hinter
  let Wc := paperCentralPathToCollar i.succ q
  let W₀ : Path paperVanKampenBasepoint x :=
    (Wc.map paperVanKampenCentralToCarrier.continuous).cast rfl hq.symm
  let Lq : Path
      (paperVanKampenCentralToCarrier (paperStarCollarToCentral i.succ q))
      (paperVanKampenCentralToCarrier (paperStarCollarToCentral i.succ q)) :=
    L.cast hq hq
  have hLq : Set.range Lq ⊆ Set.range (paperStarFillingToCarrier i.succ) := by
    change Set.range Lq ⊆ paperVanKampenEllipticPieceImage i
    intro y hy
    obtain ⟨t, rfl⟩ := hy
    exact hL ⟨t, rfl⟩
  have hlocal :
      whiskeredLoopClass
          (Wc.map paperVanKampenCentralToCarrier.continuous) Lq ∈
        paperCentralFundamentalGroupRange :=
    paperStarFilling_whiskeredLoopClass_mem_central_range
      i.succ q Wc Lq hLq
  have hlocal₀ : whiskeredLoopClass W₀ L ∈
      paperCentralFundamentalGroupRange := by
    have heq : whiskeredLoopClass
        (Wc.map paperVanKampenCentralToCarrier.continuous) Lq =
          whiskeredLoopClass W₀ L := by
      unfold whiskeredLoopClass pathLoopClass
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      rfl
    rwa [← heq]
  let R : Path paperVanKampenBasepoint paperVanKampenBasepoint :=
    W.trans W₀.symm
  have hRrange : Set.range R ⊆ paperVanKampenRootPieceImage := by
    rw [show Set.range R = Set.range W ∪ Set.range W₀ by
      simp [R, Path.trans_range, Path.symm_range]]
    apply Set.union_subset hW
    intro y hy
    obtain ⟨t, rfl⟩ := hy
    exact Or.inl ⟨Wc t, rfl⟩
  have hR : pathLoopClass R ∈ paperCentralFundamentalGroupRange :=
    paperRootPiece_loopClass_mem_central_range R hRrange
  have hchange := whiskeredLoopClass_change_whisker W W₀ L
  change whiskeredLoopClass W L =
    (pathLoopClass R)⁻¹ * whiskeredLoopClass W₀ L * pathLoopClass R at hchange
  rw [hchange]
  exact paperCentralFundamentalGroupRange.mul_mem
    (paperCentralFundamentalGroupRange.mul_mem
      (paperCentralFundamentalGroupRange.inv_mem hR) hlocal₀) hR

/-- Every member of the actual four-piece van Kampen generating family is carried by the
central family. -/
public theorem paperVanKampenFourPieceLoopClass_mem_central_range
    {g : FundamentalGroup PaperGluedCarrier paperVanKampenBasepoint}
    (hg : g ∈ paperVanKampenFourPieceLoopClasses) :
    g ∈ paperCentralFundamentalGroupRange := by
  rcases hg with hbinary | helliptic
  · exact paperBinaryOpenCoverLoopClass_mem_central_range hbinary
  · obtain ⟨i, x, hx, W, L, hW, hL, rfl⟩ := helliptic
    exact paperEllipticWhiskeredLoopClass_mem_central_range i x hx W L hW hL

/-- The image of the central-family fundamental group is the whole fundamental group of the
actual four-piece glued carrier. -/
public theorem paperCentralFundamentalGroupRange_eq_top :
    paperCentralFundamentalGroupRange = ⊤ := by
  apply top_unique
  rw [← paperVanKampenFourPieceLoopClasses_generate]
  exact (Subgroup.closure_le paperCentralFundamentalGroupRange).2
    (fun _ hg ↦ paperVanKampenFourPieceLoopClass_mem_central_range hg)

/-- The actual core-to-four-piece-carrier map is surjective on fundamental groups. -/
public theorem actualCoreFundamentalGroupMap_surjective :
    Function.Surjective
      (FundamentalGroup.map paperVanKampenCentralToCarrier
        paperVanKampenCentralPoint) := by
  intro g
  have hg : g ∈ paperCentralFundamentalGroupRange := by
    rw [paperCentralFundamentalGroupRange_eq_top]
    trivial
  exact hg

end SphereSixComplex

end
