module

public import SphereSixComplex.Geometry.FourPieceStarGluing

/-!
# Four-piece stars from common collar sources

The analytic construction naturally supplies each attaching collar as one space with open
embeddings into the central family and the corresponding filling.  This module converts those
maps into the open-subspace homeomorphisms required by `FourPieceStarGluingData`.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex

noncomputable section

/-- Three common collar sources, each openly embedded in the central piece and one filling. -/
public structure OpenEmbeddingStarData where
  central : TopCat
  filling : Fin 3 → TopCat
  collarSource : Fin 3 → TopCat
  toCentral : ∀ i, collarSource i ⟶ central
  toFilling : ∀ i, collarSource i ⟶ filling i
  toCentral_isOpenEmbedding : ∀ i, IsOpenEmbedding (toCentral i)
  toFilling_isOpenEmbedding : ∀ i, IsOpenEmbedding (toFilling i)
  centralRange_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (toCentral i)) (Set.range (toCentral j))

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

/-- The image of the `i`th common collar source in the central piece. -/
public def centralCollar (i : Fin 3) : Opens A.central :=
  ⟨Set.range (A.toCentral i), (A.toCentral_isOpenEmbedding i).isOpen_range⟩

/-- The image of the `i`th common collar source in its filling piece. -/
public def fillingCollar (i : Fin 3) : Opens (A.filling i) :=
  ⟨Set.range (A.toFilling i), (A.toFilling_isOpenEmbedding i).isOpen_range⟩

/-- A point of a common collar source, viewed in its central image. -/
public def centralCollarPoint (i : Fin 3) (x : A.collarSource i) : A.centralCollar i :=
  ⟨A.toCentral i x, by
    change ∃ y, A.toCentral i y = A.toCentral i x
    exact ⟨x, rfl⟩⟩

/-- A point of a common collar source, viewed in its filling image. -/
public def fillingCollarPoint (i : Fin 3) (x : A.collarSource i) : A.fillingCollar i :=
  ⟨A.toFilling i x, by
    change ∃ y, A.toFilling i y = A.toFilling i x
    exact ⟨x, rfl⟩⟩

/-- The central collar image, identified with its common source. -/
public noncomputable def toCentralCollarHomeomorph (i : Fin 3) :
    A.collarSource i ≃ₜ A.centralCollar i := by
  change A.collarSource i ≃ₜ Set.range (A.toCentral i)
  exact (A.toCentral_isOpenEmbedding i).isEmbedding.toHomeomorph

/-- The filling collar image, identified with its common source. -/
public noncomputable def toFillingCollarHomeomorph (i : Fin 3) :
    A.collarSource i ≃ₜ A.fillingCollar i := by
  change A.collarSource i ≃ₜ Set.range (A.toFilling i)
  exact (A.toFilling_isOpenEmbedding i).isEmbedding.toHomeomorph

@[simp]
public theorem toCentralCollarHomeomorph_apply (i : Fin 3) (x : A.collarSource i) :
    A.toCentralCollarHomeomorph i x = A.centralCollarPoint i x := by
  apply Subtype.ext
  change ↑((A.toCentral_isOpenEmbedding i).isEmbedding.toHomeomorph x) = A.toCentral i x
  exact Topology.IsEmbedding.toHomeomorph_apply_coe
    (A.toCentral_isOpenEmbedding i).isEmbedding x

@[simp]
public theorem toFillingCollarHomeomorph_apply (i : Fin 3) (x : A.collarSource i) :
    A.toFillingCollarHomeomorph i x = A.fillingCollarPoint i x := by
  apply Subtype.ext
  change ↑((A.toFilling_isOpenEmbedding i).isEmbedding.toHomeomorph x) = A.toFilling i x
  exact Topology.IsEmbedding.toHomeomorph_apply_coe
    (A.toFilling_isOpenEmbedding i).isEmbedding x

/-- The collar homeomorphism obtained by identifying both images with their common source. -/
public noncomputable def collarEquiv (i : Fin 3) :
    A.centralCollar i ≃ₜ A.fillingCollar i :=
  (A.toCentralCollarHomeomorph i).symm.trans (A.toFillingCollarHomeomorph i)

/-- Common-source open embeddings canonically determine a four-piece star gluing. -/
public noncomputable def toFourPieceStarGluingData : FourPieceStarGluingData where
  central := A.central
  filling := A.filling
  centralCollar := A.centralCollar
  fillingCollar := A.fillingCollar
  collarEquiv := A.collarEquiv
  centralCollar_disjoint := by
    intro i j hij
    exact Opens.coe_disjoint.mp (A.centralRange_disjoint hij)

@[simp]
public theorem collarEquiv_toCentral (i : Fin 3) (x : A.collarSource i) :
    A.collarEquiv i (A.centralCollarPoint i x) = A.fillingCollarPoint i x := by
  change A.toFillingCollarHomeomorph i
      ((A.toCentralCollarHomeomorph i).symm (A.centralCollarPoint i x)) = _
  have hx : (A.toCentralCollarHomeomorph i).symm (A.centralCollarPoint i x) = x := by
    rw [← A.toCentralCollarHomeomorph_apply i x]
    exact (A.toCentralCollarHomeomorph i).symm_apply_apply x
  rw [hx]
  exact A.toFillingCollarHomeomorph_apply i x

@[simp]
public theorem collarEquiv_symm_toFilling (i : Fin 3) (x : A.collarSource i) :
    (A.collarEquiv i).symm (A.fillingCollarPoint i x) = A.centralCollarPoint i x := by
  change A.toCentralCollarHomeomorph i
      ((A.toFillingCollarHomeomorph i).symm (A.fillingCollarPoint i x)) = _
  have hx : (A.toFillingCollarHomeomorph i).symm (A.fillingCollarPoint i x) = x := by
    rw [← A.toFillingCollarHomeomorph_apply i x]
    exact (A.toFillingCollarHomeomorph i).symm_apply_apply x
  rw [hx]
  exact A.toCentralCollarHomeomorph_apply i x

end OpenEmbeddingStarData

end

end SphereSixComplex
