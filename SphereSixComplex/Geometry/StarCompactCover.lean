module

public import SphereSixComplex.Geometry.ClosedRelationGluing
public import SphereSixComplex.Geometry.OpenEmbeddingStarGluing

/-!
# Compact covers for four-piece star gluings

A star gluing can be compact even when none of its four open pieces is compact.  This file packages
the exact pointwise condition needed to replace a point outside a chosen compact subset by an
identified collar point lying in the chosen compact subset of the adjacent piece.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex

noncomputable section

namespace FourPieceStarGluingData

variable (A : FourPieceStarGluingData)

/-- Compact subsets of the four pieces which cover every point, possibly after transporting that
point across one of the three collar identifications. -/
public structure CompactCoverData where
  centralSubset : Set A.central
  fillingSubset : ∀ i, Set (A.filling i)
  centralSubset_isCompact : IsCompact centralSubset
  fillingSubset_isCompact : ∀ i, IsCompact (fillingSubset i)
  central_covers : ∀ x : A.central, x ∈ centralSubset ∨
    ∃ (i : Fin 3) (z : A.centralCollar i), z.1 = x ∧
      (A.collarEquiv i z).1 ∈ fillingSubset i
  filling_covers : ∀ (i : Fin 3) (y : A.filling i), y ∈ fillingSubset i ∨
    ∃ z : A.fillingCollar i, z.1 = y ∧
      ((A.collarEquiv i).symm z).1 ∈ centralSubset

namespace CompactCoverData

variable {A : FourPieceStarGluingData} (C : A.CompactCoverData)

/-- The central and filling compact subsets as one family indexed by the gluing pieces. -/
@[expose] public def compactSubset : ∀ j, Set (A.glueData.U j)
  | none => C.centralSubset
  | some i => C.fillingSubset i

/-- Every member of the indexed family is compact. -/
public theorem compactSubset_isCompact : ∀ j, IsCompact (C.compactSubset j)
  | none => C.centralSubset_isCompact
  | some i => C.fillingSubset_isCompact i

/-- The canonical images of the selected compact subsets cover the star gluing. -/
public theorem compactSubset_covers :
    (Set.univ : Set (GluedSpace A.glueData)) =
      ⋃ j, A.glueData.toGlueData.ι j '' C.compactSubset j := by
  ext q
  constructor
  · intro _
    obtain ⟨j, x, rfl⟩ := A.glueData.ι_jointly_surjective q
    cases j with
    | none =>
        rcases C.central_covers x with hx | ⟨i, z, hzx, hz⟩
        · exact Set.mem_iUnion.mpr ⟨none, x, hx, rfl⟩
        · refine Set.mem_iUnion.mpr ⟨some i, (A.collarEquiv i z).1, hz, ?_⟩
          rw [← hzx]
          exact A.glueData.glue_condition_apply none (some i) z
    | some i =>
        rcases C.filling_covers i x with hx | ⟨z, hzx, hz⟩
        · exact Set.mem_iUnion.mpr ⟨some i, x, hx, rfl⟩
        · refine Set.mem_iUnion.mpr ⟨none, ((A.collarEquiv i).symm z).1, hz, ?_⟩
          rw [← hzx]
          have hglue :
              A.glueData.toGlueData.ι none ((A.collarEquiv i).symm z).1 =
                A.glueData.toGlueData.ι (some i)
                  (A.collarEquiv i ((A.collarEquiv i).symm z)).1 :=
            (A.glueData.glue_condition_apply none (some i)
              ((A.collarEquiv i).symm z)).symm
          rw [(A.collarEquiv i).apply_symm_apply] at hglue
          exact hglue
  · exact fun _ ↦ Set.mem_univ q

include C

/-- Pointwise collar coverage by compact subpieces makes the star gluing compact. -/
public theorem compactSpace : CompactSpace (GluedSpace A.glueData) :=
  let _ : Finite A.glueData.J := by
    change Finite (Option (Fin 3))
    infer_instance
  compactSpace_gluedSpace_of_compact_cover A.glueData (compactSubset C)
    (compactSubset_isCompact C) (compactSubset_covers C)

/-- Add closedness of every pairwise relation component to obtain the exact completion data for the
star gluing. -/
public def toGluingCompletionData
    (hclosed : ∀ i j, IsClosed (glueRelComponent A.glueData i j)) :
    GluingCompletionData A.glueData where
  relComponent_closed := hclosed
  compactSubset := compactSubset C
  compactSubset_isCompact := compactSubset_isCompact C
  compactSubset_covers := compactSubset_covers C

end CompactCoverData

end FourPieceStarGluingData

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

/-- Compact-cover data stated directly on a common-source open-embedding star.  The witnesses say
that a point outside its piece's selected compact subset has the same common collar source as a
point in the selected compact subset of the adjacent piece. -/
public structure CompactCoverData where
  centralSubset : Set A.central
  fillingSubset : ∀ i, Set (A.filling i)
  centralSubset_isCompact : IsCompact centralSubset
  fillingSubset_isCompact : ∀ i, IsCompact (fillingSubset i)
  central_covers : ∀ x : A.central, x ∈ centralSubset ∨
    ∃ (i : Fin 3) (z : A.collarSource i), A.toCentral i z = x ∧
      A.toFilling i z ∈ fillingSubset i
  filling_covers : ∀ (i : Fin 3) (y : A.filling i), y ∈ fillingSubset i ∨
    ∃ z : A.collarSource i, A.toFilling i z = y ∧
      A.toCentral i z ∈ centralSubset

namespace CompactCoverData

variable {A : OpenEmbeddingStarData} (C : A.CompactCoverData)

/-- Common-source coverage gives collar-homeomorphism coverage for the associated four-piece
star. -/
public def toFourPieceCompactCoverData :
    A.toFourPieceStarGluingData.CompactCoverData where
  centralSubset := C.centralSubset
  fillingSubset := C.fillingSubset
  centralSubset_isCompact := C.centralSubset_isCompact
  fillingSubset_isCompact := C.fillingSubset_isCompact
  central_covers := by
    intro x
    rcases C.central_covers x with hx | ⟨i, z, hzx, hz⟩
    · exact Or.inl hx
    · refine Or.inr ⟨i, A.centralCollarPoint i z, hzx, ?_⟩
      exact show (A.collarEquiv i (A.centralCollarPoint i z)).1 ∈ C.fillingSubset i by
        rw [A.collarEquiv_toCentral]
        exact hz
  filling_covers := by
    intro i y
    rcases C.filling_covers i y with hy | ⟨z, hzy, hz⟩
    · exact Or.inl hy
    · refine Or.inr ⟨A.fillingCollarPoint i z, hzy, ?_⟩
      exact show ((A.collarEquiv i).symm (A.fillingCollarPoint i z)).1 ∈
          C.centralSubset by
        rw [A.collarEquiv_symm_toFilling]
        exact hz

include C

/-- The selected common-source compact-cover data makes the associated gluing compact. -/
public theorem compactSpace :
    CompactSpace (GluedSpace A.toFourPieceStarGluingData.glueData) :=
  FourPieceStarGluingData.CompactCoverData.compactSpace
    (toFourPieceCompactCoverData C)

/-- Common-source compact coverage and closed pairwise relation components give the exact gluing
completion data. -/
public def toGluingCompletionData
    (hclosed : ∀ i j, IsClosed
      (glueRelComponent A.toFourPieceStarGluingData.glueData i j)) :
    GluingCompletionData A.toFourPieceStarGluingData.glueData :=
  FourPieceStarGluingData.CompactCoverData.toGluingCompletionData
    (toFourPieceCompactCoverData C) hclosed

end CompactCoverData

end OpenEmbeddingStarData

end

end SphereSixComplex
