module

public import SphereSixComplex.Topology.EstablishedMayerVietoris
public import SphereSixComplex.Topology.PaperSectionSevenMayerVietoris
public import SphereSixComplex.Topology.SectionSevenChainModel
public import SphereSixComplex.Topology.SectionSevenMayerVietorisGradedAlgebra
public import SphereSixComplex.Topology.SingularExcision

/-!
# Homology-level Mayer--Vietoris assembly for Section 7

The paper computes with homology groups and Mayer--Vietoris maps.  This file records the exact
basis-identification contract for those maps on the actual star cover, ordered as in the paper:
central family, order-three filling, order-four filling, then cusp filling.  The contract contains
no field describing the homology of the final glued space.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Matrix Set

namespace SphereSixComplex

/-- Reorder the star as central, order three, order four, cusp. -/
public def sectionSevenMayerVietorisOrder : Fin 4 → Fin 4 :=
  ![0, 2, 3, 1]

public theorem sectionSevenMayerVietorisOrder_surjective :
    Function.Surjective sectionSevenMayerVietorisOrder := by
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- The actual four-piece star cover in the order used by the Mayer--Vietoris calculation. -/
public noncomputable def sectionSevenMayerVietorisOpenCover (A : OpenEmbeddingStarData) :
    FourPieceOpenCover (GluedSpace A.toFourPieceStarGluingData.glueData) where
  piece i := (sectionSevenStarOpenCover A.toFourPieceStarGluingData).piece
    (sectionSevenMayerVietorisOrder i)
  isOpen_piece i := (sectionSevenStarOpenCover
    A.toFourPieceStarGluingData).isOpen_piece (sectionSevenMayerVietorisOrder i)
  covers := by
    rw [← (sectionSevenStarOpenCover A.toFourPieceStarGluingData).covers]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨sectionSevenMayerVietorisOrder i, hi⟩
    · rintro ⟨j, hj⟩
      obtain ⟨i, rfl⟩ := sectionSevenMayerVietorisOrder_surjective j
      exact ⟨i, hj⟩

/-- The normalized final degree-two map: identity on the four central coordinates, then the
unit maps from the two generators of `K₂`. -/
public def sectionSevenMayerVietorisFinalTwoMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0,  0;
     0, 1, 0, 0, 0,  0;
     0, 0, 1, 0, 0,  0;
     0, 0, 0, 1, 0,  0;
     0, 0, 0, 0, 1,  0;
     0, 0, 0, 0, 0, -1]

/-- The normalized final degree-two homomorphism. -/
public def sectionSevenMayerVietorisFinalTwoHom : (Fin 6 → ℤ) →+ (Fin 6 → ℤ) :=
  (Matrix.mulVecLin sectionSevenMayerVietorisFinalTwoMatrix).toAddHom

public theorem sectionSevenMayerVietorisFinalTwoHom_involutive (x : Fin 6 → ℤ) :
    sectionSevenMayerVietorisFinalTwoHom
      (sectionSevenMayerVietorisFinalTwoHom x) = x := by
  funext i
  fin_cases i <;>
    simp [sectionSevenMayerVietorisFinalTwoHom, sectionSevenMayerVietorisFinalTwoMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

public theorem sectionSevenMayerVietorisFinalTwoHom_bijective :
    Function.Bijective sectionSevenMayerVietorisFinalTwoHom := by
  constructor
  · intro x y h
    have h' := congrArg sectionSevenMayerVietorisFinalTwoHom h
    simpa only [sectionSevenMayerVietorisFinalTwoHom_involutive] using h'
  · intro y
    exact ⟨sectionSevenMayerVietorisFinalTwoHom y,
      sectionSevenMayerVietorisFinalTwoHom_involutive y⟩

/-- The connected degree-zero difference map. -/
public def sectionSevenMayerVietorisFinalZeroHom : (Fin 1 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![x 0, -x 0]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    abel

public theorem sectionSevenMayerVietorisFinalZeroHom_injective :
    Function.Injective sectionSevenMayerVietorisFinalZeroHom := by
  intro x y h
  funext i
  fin_cases i
  simpa [sectionSevenMayerVietorisFinalZeroHom] using congrFun h 0

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

public abbrev SectionSevenMayerVietorisSpace :=
  GluedSpace A.toFourPieceStarGluingData.glueData

public abbrev SectionSevenMayerVietorisCover :=
  sectionSevenMayerVietorisOpenCover A

/-- Homology-level identifications for the source-stated Mayer--Vietoris calculation.  The local
and partial-stage families expose all comparison objects; the final three map squares are the
only fields used to derive low-degree vanishing. -/
public structure SectionSevenMayerVietorisHomologyAssembly where
  /-- Degreewise models for the four actual open pieces. -/
  pieceModel : Fin 4 → ℕ → AddCommGrpCat
  /-- The chosen homology basis for every actual open piece. -/
  pieceEquiv : ∀ i k,
    IntegralSingularHomology k ((SectionSevenMayerVietorisCover A).piece i) ≃+
      pieceModel i k
  /-- Degreewise models for the three actual collar sources. -/
  collarModel : Fin 3 → ℕ → AddCommGrpCat
  /-- The chosen homology basis for every collar source. -/
  collarEquiv : ∀ i k, IntegralSingularHomology k (A.collarSource i) ≃+ collarModel i k
  /-- Degreewise models for the three proper prefix stages. -/
  stageModel : Fin 3 → ℕ → AddCommGrpCat
  /-- The chosen homology basis for every proper prefix stage. -/
  stageEquiv : ∀ r k,
    IntegralSingularHomology k
      ((SectionSevenMayerVietorisCover A).stage r.castSucc) ≃+ stageModel r k
  /-- The degree-one basis on the order-four collar in the interior union. -/
  interiorOneSource :
    IntegralSingularHomology 1
      ((SectionSevenMayerVietorisCover A).stage (1 : Fin 4) ∩
        (SectionSevenMayerVietorisCover A).piece 2 :
          Set (SectionSevenMayerVietorisSpace A)) ≃+ (Fin 4 → ℤ)
  /-- The degree-one basis on the two sides of the interior union. -/
  interiorOneTarget :
    (IntegralSingularHomology 1
        ((SectionSevenMayerVietorisCover A).stage (1 : Fin 4)) ×
      IntegralSingularHomology 1
        ((SectionSevenMayerVietorisCover A).piece 2)) ≃+ (Fin 4 → ℤ)
  /-- The actual interior degree-one map is the displayed `α₁`. -/
  interiorOne_comm : ∀ x,
    interiorOneTarget (IntegralMayerVietoris.differenceMap
      ((SectionSevenMayerVietorisCover A).stage (1 : Fin 4))
        ((SectionSevenMayerVietorisCover A).piece 2) 1 x) =
      alphaOneMatrix.mulVec (interiorOneSource x)
  /-- The degree-two basis on the order-four collar in the interior union. -/
  interiorTwoSource :
    IntegralSingularHomology 2
      ((SectionSevenMayerVietorisCover A).stage (1 : Fin 4) ∩
        (SectionSevenMayerVietorisCover A).piece 2 :
          Set (SectionSevenMayerVietorisSpace A)) ≃+ (Fin 6 → ℤ)
  /-- The degree-two basis on the two sides of the interior union. -/
  interiorTwoTarget :
    (IntegralSingularHomology 2
        ((SectionSevenMayerVietorisCover A).stage (1 : Fin 4)) ×
      IntegralSingularHomology 2
        ((SectionSevenMayerVietorisCover A).piece 2)) ≃+ (Fin 4 → ℤ)
  /-- The actual interior degree-two map is the displayed `α₂`. -/
  interiorTwo_comm : ∀ x,
    interiorTwoTarget (IntegralMayerVietoris.differenceMap
      ((SectionSevenMayerVietorisCover A).stage (1 : Fin 4))
        ((SectionSevenMayerVietorisCover A).piece 2) 2 x) =
      alphaTwoMatrix.mulVec (interiorTwoSource x)
  /-- The degree-zero basis on the final overlap. -/
  finalZeroSource :
    IntegralSingularHomology 0
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4) ∩
        (SectionSevenMayerVietorisCover A).piece 3 :
          Set (SectionSevenMayerVietorisSpace A)) ≃+ (Fin 1 → ℤ)
  /-- The degree-zero basis on the two final sides. -/
  finalZeroTarget :
    (IntegralSingularHomology 0
        ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4)) ×
      IntegralSingularHomology 0
        ((SectionSevenMayerVietorisCover A).piece 3)) ≃+ (Fin 2 → ℤ)
  /-- The actual final degree-zero map is the connected difference map. -/
  finalZero_comm : ∀ x,
    finalZeroTarget (IntegralMayerVietoris.differenceMap
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4))
        ((SectionSevenMayerVietorisCover A).piece 3) 0 x) =
      sectionSevenMayerVietorisFinalZeroHom (finalZeroSource x)
  /-- The degree-one basis on the final overlap. -/
  finalOneSource :
    IntegralSingularHomology 1
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4) ∩
        (SectionSevenMayerVietorisCover A).piece 3 :
          Set (SectionSevenMayerVietorisSpace A)) ≃+ (Fin 3 → ℤ)
  /-- The degree-one basis on the two final sides. -/
  finalOneTarget :
    (IntegralSingularHomology 1
        ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4)) ×
      IntegralSingularHomology 1
        ((SectionSevenMayerVietorisCover A).piece 3)) ≃+ (Fin 3 → ℤ)
  /-- The actual final degree-one map is the verified unit presentation. -/
  finalOne_comm : ∀ x,
    finalOneTarget (IntegralMayerVietoris.differenceMap
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4))
        ((SectionSevenMayerVietorisCover A).piece 3) 1 x) =
      sectionSevenFirstBoundaryHom (finalOneSource x)
  /-- The degree-two basis on the final overlap. -/
  finalTwoSource :
    IntegralSingularHomology 2
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4) ∩
        (SectionSevenMayerVietorisCover A).piece 3 :
          Set (SectionSevenMayerVietorisSpace A)) ≃+ (Fin 6 → ℤ)
  /-- The degree-two basis on the two final sides. -/
  finalTwoTarget :
    (IntegralSingularHomology 2
        ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4)) ×
      IntegralSingularHomology 2
        ((SectionSevenMayerVietorisCover A).piece 3)) ≃+ (Fin 6 → ℤ)
  /-- The actual final degree-two map is the normalized source-stated attachment map. -/
  finalTwo_comm : ∀ x,
    finalTwoTarget (IntegralMayerVietoris.differenceMap
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4))
        ((SectionSevenMayerVietorisCover A).piece 3) 2 x) =
      sectionSevenMayerVietorisFinalTwoHom (finalTwoSource x)

namespace SectionSevenMayerVietorisHomologyAssembly

variable {A : OpenEmbeddingStarData}

private theorem injective_of_equiv_comm
    {S T S' T' : Type} [AddCommGroup S] [AddCommGroup T]
    [AddCommGroup S'] [AddCommGroup T']
    (eS : S ≃+ S') (eT : T ≃+ T') (f : S →+ T) (g : S' →+ T')
    (hcomm : ∀ x, eT (f x) = g (eS x)) (hg : Function.Injective g) :
    Function.Injective f := by
  intro x y hxy
  apply eS.injective
  apply hg
  rw [← hcomm, ← hcomm, hxy]

private theorem surjective_of_equiv_comm
    {S T S' T' : Type} [AddCommGroup S] [AddCommGroup T]
    [AddCommGroup S'] [AddCommGroup T']
    (eS : S ≃+ S') (eT : T ≃+ T') (f : S →+ T) (g : S' →+ T')
    (hcomm : ∀ x, eT (f x) = g (eS x)) (hg : Function.Surjective g) :
    Function.Surjective f := by
  intro y
  obtain ⟨x', hx'⟩ := hg (eT y)
  refine ⟨eS.symm x', ?_⟩
  apply eT.injective
  rw [hcomm, eS.apply_symm_apply, hx']

public theorem finalDifferenceZero_injective
    (H : A.SectionSevenMayerVietorisHomologyAssembly) :
    Function.Injective (IntegralMayerVietoris.differenceMap
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4))
        ((SectionSevenMayerVietorisCover A).piece 3) 0) :=
  injective_of_equiv_comm H.finalZeroSource H.finalZeroTarget _ _ H.finalZero_comm
    sectionSevenMayerVietorisFinalZeroHom_injective

public theorem finalDifferenceOne_bijective
    (H : A.SectionSevenMayerVietorisHomologyAssembly) :
    Function.Bijective (IntegralMayerVietoris.differenceMap
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4))
        ((SectionSevenMayerVietorisCover A).piece 3) 1) :=
  ⟨injective_of_equiv_comm H.finalOneSource H.finalOneTarget _ _ H.finalOne_comm
      sectionSevenFirstBoundary_bijective.injective,
    surjective_of_equiv_comm H.finalOneSource H.finalOneTarget _ _ H.finalOne_comm
      sectionSevenFirstBoundary_bijective.surjective⟩

public theorem finalDifferenceTwo_bijective
    (H : A.SectionSevenMayerVietorisHomologyAssembly) :
    Function.Bijective (IntegralMayerVietoris.differenceMap
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4))
        ((SectionSevenMayerVietorisCover A).piece 3) 2) :=
  ⟨injective_of_equiv_comm H.finalTwoSource H.finalTwoTarget _ _ H.finalTwo_comm
      sectionSevenMayerVietorisFinalTwoHom_bijective.injective,
    surjective_of_equiv_comm H.finalTwoSource H.finalTwoTarget _ _ H.finalTwo_comm
      sectionSevenMayerVietorisFinalTwoHom_bijective.surjective⟩

private theorem unionHomology_subsingleton_of_exact
    {Y : Type} [TopologicalSpace Y] (U V : Set Y)
    (h : IntegralMayerVietoris.ExactSequence U V) (k : ℕ)
    (hNext : Function.Surjective (IntegralMayerVietoris.differenceMap U V (k + 1)))
    (hThis : Function.Injective (IntegralMayerVietoris.differenceMap U V k)) :
    Subsingleton (IntegralSingularHomology (k + 1) (U ∪ V : Set Y)) := by
  obtain ⟨boundary, hExact⟩ := h
  constructor
  intro x y
  suffices ∀ z : IntegralSingularHomology (k + 1) (U ∪ V : Set Y), z = 0 by
    rw [this x, this y]
  intro z
  have hsumZero : ∀ w, IntegralMayerVietoris.sumMap U V (k + 1) w = 0 := by
    intro w
    have hwRange : w ∈ Set.range (IntegralMayerVietoris.differenceMap U V (k + 1)) := by
      obtain ⟨v, rfl⟩ := hNext w
      exact ⟨v, rfl⟩
    exact (hExact (k + 1)).2.2 w |>.mpr hwRange
  have hBoundaryZero : boundary k z = 0 := by
    apply hThis
    have hzRange : boundary k z ∈ Set.range (boundary k) := ⟨z, rfl⟩
    simpa using ((hExact k).2.1 (boundary k z) |>.mpr hzRange)
  have hzRange : z ∈ Set.range (IntegralMayerVietoris.sumMap U V (k + 1)) :=
    (hExact k).1 z |>.mp hBoundaryZero
  obtain ⟨w, rfl⟩ := hzRange
  exact hsumZero w

public theorem finalUnionHomologyOne_subsingleton
    (H : A.SectionSevenMayerVietorisHomologyAssembly) :
    Subsingleton (IntegralSingularHomology 1
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4) ∪
        (SectionSevenMayerVietorisCover A).piece 3 :
          Set (SectionSevenMayerVietorisSpace A))) :=
  unionHomology_subsingleton_of_exact _ _
    (establishedFourPieceMayerVietorisExactness (SectionSevenMayerVietorisCover A) 2) 0
    H.finalDifferenceOne_bijective.surjective H.finalDifferenceZero_injective

public theorem finalUnionHomologyTwo_subsingleton
    (H : A.SectionSevenMayerVietorisHomologyAssembly) :
    Subsingleton (IntegralSingularHomology 2
      ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4) ∪
        (SectionSevenMayerVietorisCover A).piece 3 :
          Set (SectionSevenMayerVietorisSpace A))) :=
  unionHomology_subsingleton_of_exact _ _
    (establishedFourPieceMayerVietorisExactness (SectionSevenMayerVietorisCover A) 2) 1
    H.finalDifferenceTwo_bijective.surjective H.finalDifferenceOne_bijective.injective

public theorem final_union_eq_univ :
    (SectionSevenMayerVietorisCover A).stage (2 : Fin 4) ∪
      (SectionSevenMayerVietorisCover A).piece 3 = Set.univ := by
  calc
    _ = (SectionSevenMayerVietorisCover A).stage (2 : Fin 3).succ := by
      simpa using
        (SectionSevenMayerVietorisCover A).stage_union_next (2 : Fin 3)
    _ = Set.univ := (SectionSevenMayerVietorisCover A).stage_last

public noncomputable def finalUnionHomeomorph :
    ((SectionSevenMayerVietorisCover A).stage (2 : Fin 4) ∪
      (SectionSevenMayerVietorisCover A).piece 3 :
        Set (SectionSevenMayerVietorisSpace A)) ≃ₜ SectionSevenMayerVietorisSpace A :=
  topologicalSubsetHomeomorphOfEqUniv _ _ final_union_eq_univ

public theorem homologyOne_subsingleton
    (H : A.SectionSevenMayerVietorisHomologyAssembly) :
    Subsingleton (IntegralSingularHomology 1 (SectionSevenMayerVietorisSpace A)) := by
  let _ := H.finalUnionHomologyOne_subsingleton
  let e := integralSingularHomologyEquiv 1 (finalUnionHomeomorph (A := A))
  exact ⟨fun x y ↦ e.symm.injective (Subsingleton.elim _ _)⟩

public theorem homologyTwo_subsingleton
    (H : A.SectionSevenMayerVietorisHomologyAssembly) :
    Subsingleton (IntegralSingularHomology 2 (SectionSevenMayerVietorisSpace A)) := by
  let _ := H.finalUnionHomologyTwo_subsingleton
  let e := integralSingularHomologyEquiv 2 (finalUnionHomeomorph (A := A))
  exact ⟨fun x y ↦ e.symm.injective (Subsingleton.elim _ _)⟩

end SectionSevenMayerVietorisHomologyAssembly

end OpenEmbeddingStarData

end SphereSixComplex
