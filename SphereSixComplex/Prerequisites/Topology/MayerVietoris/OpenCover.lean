module

public import SphereSixComplex.Prerequisites.Topology.MayerVietoris.IntegralSequence

namespace SphereSixComplex

/-- The integral singular-homology Mayer--Vietoris sequence for two open subsets, with difference
map `(i_*, -j_*)` and sum map `k_* + l_*` as defined in `IntegralMayerVietoris`. -/
public theorem IntegralMayerVietoris.exact_sequence_of_isOpen
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) :
    IntegralMayerVietoris.ExactSequence A B :=
  BinaryOpenCover.integralMayerVietorisExactSequence_of_isOpen A B hA hB

/-- If two open pieces have no seventh homology and their overlap has no sixth homology, then
their union has no seventh homology. -/
public theorem subsingleton_homology_seven_union
    {X : Type} [TopologicalSpace X] (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hA7 : Subsingleton (IntegralSingularHomology 7 A))
    (hB7 : Subsingleton (IntegralSingularHomology 7 B))
    (hAB6 : Subsingleton (IntegralSingularHomology 6 (A ∩ B : Set X))) :
    Subsingleton (IntegralSingularHomology 7 (A ∪ B : Set X)) := by
  obtain ⟨boundary, hexact⟩ := IntegralMayerVietoris.exact_sequence_of_isOpen A B hA hB
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

/-- The established binary theorem supplies exactness at each stage of an ordered four-piece open
cover. -/
public theorem FourPieceOpenCover.mayerVietoris_exact
    {X : Type} [TopologicalSpace X] (C : FourPieceOpenCover X) :
    FourPieceMayerVietorisExactness C := by
  intro r
  exact IntegralMayerVietoris.exact_sequence_of_isOpen _ _
    (C.isOpen_stage r.castSucc) (C.isOpen_piece r.succ)

end SphereSixComplex
