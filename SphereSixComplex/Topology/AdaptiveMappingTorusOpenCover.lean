module

public import SphereSixComplex.Topology.WangHomologyPresentationProof

/-!
# An adaptive open cover of a finite-bouquet mapping torus

This file constructs a two-set cover whose overlap bands can be made arbitrarily narrow around
the quarter and three-quarter points of the cylinder coordinate.
-/

namespace SphereSixComplex

open scoped Classical

section Bands

/-- A neighbourhood of the identified cylinder ends, with transition width controlled by `ε`. -/
public def adaptiveVertexBand (ε : ℝ) : Set unitInterval :=
  {t | (t : ℝ) < 1 / 4 + ε ∨ 3 / 4 - ε < (t : ℝ)}

/-- A neighbourhood of the middle of the cylinder, with transition width controlled by `ε`. -/
public def adaptiveEdgeBand (ε : ℝ) : Set unitInterval :=
  {t | 1 / 4 - ε < (t : ℝ) ∧ (t : ℝ) < 3 / 4 + ε}

/-- The two transition intervals in the adaptive cover. -/
public def adaptiveOverlapBand (ε : ℝ) : Set unitInterval :=
  {t |
    (1 / 4 - ε < (t : ℝ) ∧ (t : ℝ) < 1 / 4 + ε) ∨
      (3 / 4 - ε < (t : ℝ) ∧ (t : ℝ) < 3 / 4 + ε)}

public theorem isOpen_adaptiveVertexBand (ε : ℝ) : IsOpen (adaptiveVertexBand ε) :=
  (isOpen_lt continuous_subtype_val continuous_const).union
    (isOpen_lt continuous_const continuous_subtype_val)

public theorem isOpen_adaptiveEdgeBand (ε : ℝ) : IsOpen (adaptiveEdgeBand ε) :=
  (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

public theorem isOpen_adaptiveOverlapBand (ε : ℝ) : IsOpen (adaptiveOverlapBand ε) :=
  ((isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)).union
    ((isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const))

public theorem adaptiveVertexBand_ends {ε : ℝ} (hε : 0 < ε) :
    (0 : unitInterval) ∈ adaptiveVertexBand ε ↔
      (1 : unitInterval) ∈ adaptiveVertexBand ε := by
  constructor
  · intro _
    right
    norm_num
    linarith
  · intro _
    left
    norm_num
    linarith

public theorem adaptiveEdgeBand_ends {ε : ℝ} (hε : ε < 1 / 4) :
    (0 : unitInterval) ∈ adaptiveEdgeBand ε ↔
      (1 : unitInterval) ∈ adaptiveEdgeBand ε := by
  constructor
  · rintro ⟨h, -⟩
    norm_num at h
    linarith
  · rintro ⟨-, h⟩
    norm_num at h
    linarith

/-- Positive transition width makes the adaptive bands cover the cylinder. -/
public theorem adaptiveVertexBand_union_adaptiveEdgeBand {ε : ℝ} (hε : 0 < ε) :
    adaptiveVertexBand ε ∪ adaptiveEdgeBand ε = Set.univ := by
  ext t
  constructor
  · intro _
    trivial
  · intro _
    rcases lt_or_ge (t : ℝ) (1 / 4 + ε) with h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_or_ge (3 / 4 - ε : ℝ) (t : ℝ) with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨by linarith, by linarith⟩

/-- The intersection of the adaptive bands is exactly the two transition intervals. -/
public theorem adaptiveVertexBand_inter_adaptiveEdgeBand (ε : ℝ) :
    adaptiveVertexBand ε ∩ adaptiveEdgeBand ε = adaptiveOverlapBand ε := by
  ext t
  constructor
  · rintro ⟨hvertex, hedge⟩
    rcases hvertex with hlow | hhigh
    · exact Or.inl ⟨hedge.1, hlow⟩
    · exact Or.inr ⟨hhigh, hedge.2⟩
  · rintro (hlow | hhigh)
    · exact ⟨Or.inl hlow.2, ⟨hlow.1, by linarith⟩⟩
    · exact ⟨Or.inr hhigh.1, ⟨by linarith, hhigh.2⟩⟩

public theorem uQuarter_mem_adaptiveOverlapBand {ε : ℝ} (hε : 0 < ε) :
    uQuarter ∈ adaptiveOverlapBand ε := by
  left
  change 1 / 4 - ε < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < 1 / 4 + ε
  constructor <;> linarith

public theorem uThreeQuarters_mem_adaptiveOverlapBand {ε : ℝ} (hε : 0 < ε) :
    uThreeQuarters ∈ adaptiveOverlapBand ε := by
  right
  change 3 / 4 - ε < (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) < 3 / 4 + ε
  constructor <;> linarith

end Bands

section Pieces

variable {ι F : Type} [TopologicalSpace F]

/-- The saturated mapping-torus piece over the adaptive end band. -/
public def adaptiveVertexPiece (φ : ι → F ≃ₜ F) (ε : ℝ) :
    Set (FiniteBouquetMappingTorus φ) :=
  bouquetPiece φ (adaptiveVertexBand ε)

/-- The saturated mapping-torus piece over the adaptive middle band. -/
public def adaptiveEdgePiece (φ : ι → F ≃ₜ F) (ε : ℝ) :
    Set (FiniteBouquetMappingTorus φ) :=
  bouquetPiece φ (adaptiveEdgeBand ε)

public theorem isOpen_adaptiveVertexPiece [TopologicalSpace ι]
    (φ : ι → F ≃ₜ F) {ε : ℝ} (hε : 0 < ε) :
    IsOpen (adaptiveVertexPiece φ ε) :=
  isOpen_bouquetPiece φ (isOpen_adaptiveVertexBand ε) (adaptiveVertexBand_ends hε)

public theorem isOpen_adaptiveEdgePiece [TopologicalSpace ι]
    (φ : ι → F ≃ₜ F) {ε : ℝ} (hε : ε < 1 / 4) :
    IsOpen (adaptiveEdgePiece φ ε) :=
  isOpen_bouquetPiece φ (isOpen_adaptiveEdgeBand ε) (adaptiveEdgeBand_ends hε)

/-- The adaptive pieces cover the finite-bouquet mapping torus. -/
public theorem adaptiveVertexPiece_union_adaptiveEdgePiece
    (φ : ι → F ≃ₜ F) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) :
    adaptiveVertexPiece φ ε ∪ adaptiveEdgePiece φ ε = Set.univ := by
  rw [adaptiveVertexPiece, adaptiveEdgePiece,
    bouquetPiece_union φ (adaptiveVertexBand_ends hε) (adaptiveEdgeBand_ends hε'),
    adaptiveVertexBand_union_adaptiveEdgeBand hε, bouquetPiece_univ]

/-- The overlap of the adaptive pieces is saturated over the two transition intervals. -/
public theorem adaptiveVertexPiece_inter_adaptiveEdgePiece
    (φ : ι → F ≃ₜ F) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) :
    adaptiveVertexPiece φ ε ∩ adaptiveEdgePiece φ ε =
      bouquetPiece φ (adaptiveOverlapBand ε) := by
  rw [adaptiveVertexPiece, adaptiveEdgePiece,
    bouquetPiece_inter φ (adaptiveVertexBand_ends hε) (adaptiveEdgeBand_ends hε'),
    adaptiveVertexBand_inter_adaptiveEdgeBand]

variable [TopologicalSpace ι]

/-- The adaptive end piece as an open subset. -/
public def adaptiveCoverVertexOpen (φ : ι → F ≃ₜ F) (ε : ℝ) (hε : 0 < ε) :
    TopologicalSpace.Opens (TopCat.of (FiniteBouquetMappingTorus φ)) where
  carrier := adaptiveVertexPiece φ ε
  is_open' := isOpen_adaptiveVertexPiece φ hε

/-- The adaptive middle piece as an open subset. -/
public def adaptiveCoverEdgeOpen (φ : ι → F ≃ₜ F) (ε : ℝ) (hε : ε < 1 / 4) :
    TopologicalSpace.Opens (TopCat.of (FiniteBouquetMappingTorus φ)) where
  carrier := adaptiveEdgePiece φ ε
  is_open' := isOpen_adaptiveEdgePiece φ hε

/-- The adaptive opens form a binary open cover. -/
public theorem adaptiveCoverOpen (φ : ι → F ≃ₜ F) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 4) :
    adaptiveCoverVertexOpen φ ε hε ⊔ adaptiveCoverEdgeOpen φ ε hε' = ⊤ := by
  ext x
  change x ∈ adaptiveVertexPiece φ ε ∪ adaptiveEdgePiece φ ε ↔ x ∈ Set.univ
  rw [adaptiveVertexPiece_union_adaptiveEdgePiece φ hε hε']

end Pieces

end SphereSixComplex
