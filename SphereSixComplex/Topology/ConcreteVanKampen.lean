module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen
public import SphereSixComplex.Topology.VanKampenGeometry

/-!
# The concrete four-piece van Kampen diagram

Thomas Zhu's fundamental-groupoid form of Seifert--van Kampen says that the fundamental
groupoid functor is a cosheaf.  This file instantiates that general theorem for the four open
pieces retained by `PaperVanKampenFourPieceCover`.  In particular, the resulting finite diagram
contains precisely the four pieces and their pairwise intersections.

This is the space-level van Kampen theorem used by the paper.  Computing the local fundamental
groupoids and their maps on the named meridians is a separate, paper-specific step.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped FundamentalGroupoid

noncomputable section

namespace SphereSixComplex.Topology
namespace PaperVanKampenFourPieceCover

/-- Names for the four open pieces in the paper's star-shaped cover. -/
public inductive Piece where
  | core
  | cusp
  | ellipticThree
  | ellipticFour
  deriving DecidableEq

/-- Explicit finite enumeration of the four paper pieces. -/
public instance : Fintype Piece where
  elems := {.core, .cusp, .ellipticThree, .ellipticFour}
  complete x := by cases x <;> simp

/-- The four sets in `PaperVanKampenFourPieceCover`, bundled as open subspaces. -/
public def opens {Y : Type*} [TopologicalSpace Y] {base : Y}
    (D : PaperVanKampenFourPieceCover base) :
    Piece → Opens (TopCat.of Y)
  | .core => ⟨D.core, D.core_isOpen⟩
  | .cusp => ⟨D.cusp, D.cusp_isOpen⟩
  | .ellipticThree => ⟨D.ellipticThree, D.ellipticThree_isOpen⟩
  | .ellipticFour => ⟨D.ellipticFour, D.ellipticFour_isOpen⟩

/-- The indexed family of four opens covers the whole ambient space. -/
public theorem iSup_opens_eq_top {Y : Type*} [TopologicalSpace Y] {base : Y}
    (D : PaperVanKampenFourPieceCover base) :
    iSup D.opens = ⊤ := by
  apply top_unique
  intro y _
  rw [Opens.mem_iSup]
  have hy : y ∈ D.core ∪ D.cusp ∪ D.ellipticThree ∪ D.ellipticFour := by
    rw [D.covers]
    exact Set.mem_univ y
  rcases hy with ((hy | hy) | hy) | hy
  · exact ⟨.core, hy⟩
  · exact ⟨.cusp, hy⟩
  · exact ⟨.ellipticThree, hy⟩
  · exact ⟨.ellipticFour, hy⟩

/-- Seifert--van Kampen over the category of all opens subordinate to one of the paper's four
pieces. -/
public theorem opensLeVanKampenCocone_isColimit
    {Y : Type*} [TopologicalSpace Y] {base : Y}
    (D : PaperVanKampenFourPieceCover base) :
    Nonempty
      (IsColimit
        ((πₒ (TopCat.of Y)).mapCocone
          (TopCat.Presheaf.SheafCondition.opensLeCoverCocone D.opens))) := by
  have hsheaf :=
    FundamentalGroupoid.isSheaf_op_opensToGrpd (X := TopCat.of Y)
  rcases hsheaf.isSheafOpensLeCover D.opens with ⟨h⟩
  let e :
      (((πₒ (TopCat.of Y)).mapCocone
        (TopCat.Presheaf.SheafCondition.opensLeCoverCocone D.opens)).op) ≅
          ((πₒ (TopCat.of Y)).op.mapCone
            (TopCat.Presheaf.SheafCondition.opensLeCoverCocone D.opens).op) :=
    Functor.mapCoconeOp
      (G := πₒ (TopCat.of Y))
      (t := TopCat.Presheaf.SheafCondition.opensLeCoverCocone D.opens)
  exact ⟨isColimitOfOp ((IsLimit.equivIsoLimit e).symm h)⟩

/-- Seifert--van Kampen for the finite diagram consisting of the four paper pieces and all their
pairwise intersections. -/
public theorem pairwiseVanKampenCocone_isColimit
    {Y : Type*} [TopologicalSpace Y] {base : Y}
    (D : PaperVanKampenFourPieceCover base) :
    Nonempty
      (IsColimit
        ((πₒ (TopCat.of Y)).mapCocone
          (CategoryTheory.Pairwise.cocone D.opens))) := by
  have hsheaf :=
    FundamentalGroupoid.isSheaf_op_opensToGrpd (X := TopCat.of Y)
  rcases hsheaf.isSheafPairwiseIntersections D.opens with ⟨h⟩
  let e :
      (((πₒ (TopCat.of Y)).mapCocone
        (CategoryTheory.Pairwise.cocone D.opens)).op) ≅
          ((πₒ (TopCat.of Y)).op.mapCone
            (CategoryTheory.Pairwise.cocone D.opens).op) :=
    Functor.mapCoconeOp
      (G := πₒ (TopCat.of Y)) (t := CategoryTheory.Pairwise.cocone D.opens)
  exact ⟨isColimitOfOp ((IsLimit.equivIsoLimit e).symm h)⟩

/-- The apex of the finite pairwise-intersection diagram is the fundamental groupoid of the
whole covered open subspace. -/
public theorem pairwiseVanKampenCocone_pt
    {Y : Type*} [TopologicalSpace Y] {base : Y}
    (D : PaperVanKampenFourPieceCover base) :
    (((πₒ (TopCat.of Y)).mapCocone
      (CategoryTheory.Pairwise.cocone D.opens))).pt =
        (πₒ (TopCat.of Y)).obj ⊤ := by
  change
    (πₒ (TopCat.of Y)).obj (iSup D.opens) =
      (πₒ (TopCat.of Y)).obj ⊤
  rw [D.iSup_opens_eq_top]

end PaperVanKampenFourPieceCover
end SphereSixComplex.Topology
