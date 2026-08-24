module

public import SphereSixComplex.Geometry.ClosedRelationGluing
public import SphereSixComplex.Geometry.OpenEmbeddingStarGluing

/-!
# Closed relations for an open-embedding star

For a four-piece star built from common collar sources, every off-diagonal relation component
is the image of the corresponding paired collar map.  Thus the only geometric closedness input
is closedness of these three images; properness of each paired map is a sufficient condition.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex

noncomputable section

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

/-- The two collar embeddings, regarded as one map into the product of the adjacent pieces. -/
public def collarPairMap (i : Fin 3) :
    A.collarSource i → A.central × A.filling i :=
  fun x ↦ (A.toCentral i x, A.toFilling i x)

/-- The central-to-filling relation component is exactly the image of the paired collar map. -/
public theorem glueRelComponent_none_some (i : Fin 3) :
    glueRelComponent A.toFourPieceStarGluingData.glueData none (some i) =
      Set.range (A.collarPairMap i) := by
  rw [show glueRelComponent A.toFourPieceStarGluingData.glueData none (some i) =
      {p | ∃ x : A.centralCollar i,
        x.1 = p.1 ∧ (A.collarEquiv i x).1 = p.2} by rfl]
  ext p
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨z, hz⟩ := x.2
    have hzx : A.centralCollarPoint i z = x := Subtype.ext hz
    refine ⟨z, Prod.ext ?_ ?_⟩
    · exact hz.trans hx
    · change A.toFilling i z = p.2
      rw [← hy, ← hzx, A.collarEquiv_toCentral]
      rfl
  · rintro ⟨z, rfl⟩
    refine ⟨A.centralCollarPoint i z, ?_, ?_⟩
    · unfold centralCollarPoint collarPairMap
      rfl
    · change (A.collarEquiv i (A.centralCollarPoint i z)).1 = A.toFilling i z
      rw [A.collarEquiv_toCentral]
      rfl

/-- The reverse relation component is the image of the same paired map with coordinates swapped. -/
public theorem glueRelComponent_some_none (i : Fin 3) :
    glueRelComponent A.toFourPieceStarGluingData.glueData (some i) none =
      Set.range (fun x : A.collarSource i ↦ (A.toFilling i x, A.toCentral i x)) := by
  rw [show glueRelComponent A.toFourPieceStarGluingData.glueData (some i) none =
      {p | ∃ x : A.fillingCollar i,
        x.1 = p.1 ∧ ((A.collarEquiv i).symm x).1 = p.2} by rfl]
  ext p
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨z, hz⟩ := x.2
    have hzx : A.fillingCollarPoint i z = x := Subtype.ext hz
    refine ⟨z, Prod.ext ?_ ?_⟩
    · exact hz.trans hx
    · change A.toCentral i z = p.2
      rw [← hy, ← hzx, A.collarEquiv_symm_toFilling]
      rfl
  · rintro ⟨z, rfl⟩
    refine ⟨A.fillingCollarPoint i z, ?_, ?_⟩
    · unfold fillingCollarPoint
      rfl
    · change ((A.collarEquiv i).symm (A.fillingCollarPoint i z)).1 = A.toCentral i z
      rw [A.collarEquiv_symm_toFilling]
      rfl

/-- Closed images of the three paired collar maps are the exact off-diagonal closedness data. -/
public structure ClosedCollarPairData : Prop where
  isClosed_range : ∀ i, IsClosed (Set.range (A.collarPairMap i))

/-- Proper paired collar maps have closed images. -/
public theorem closedCollarPairData_of_isProperMap
    (h : ∀ i, IsProperMap (A.collarPairMap i)) :
    A.ClosedCollarPairData :=
  ⟨fun i ↦ (h i).isClosed_range⟩

private theorem isClosed_reverseRange (i : Fin 3)
    (h : IsClosed (Set.range (A.collarPairMap i))) :
    IsClosed (Set.range (fun x : A.collarSource i ↦
      (A.toFilling i x, A.toCentral i x))) := by
  rw [show Set.range (fun x : A.collarSource i ↦
        (A.toFilling i x, A.toCentral i x)) =
      Prod.swap ⁻¹' Set.range (A.collarPairMap i) by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Prod.ext (congrArg Prod.snd hx) (congrArg Prod.fst hx)⟩]
  exact h.preimage continuous_swap

end OpenEmbeddingStarData

/-- A self-relation component is the diagonal of its piece. -/
public theorem glueRelComponent_self (D : TopCat.GlueData) (i : D.J) :
    glueRelComponent D i i = {p | p.1 = p.2} := by
  ext p
  unfold glueRelComponent
  change D.Rel ⟨i, p.1⟩ ⟨i, p.2⟩ ↔ p.1 = p.2
  rw [← D.ι_eq_iff_rel]
  constructor
  · intro h
    exact D.ι_injective i h
  · intro h
    exact congrArg (D.toGlueData.ι i) h

/-- A self-relation component of a Hausdorff piece is closed. -/
public theorem glueRelComponent_self_isClosed (D : TopCat.GlueData) (i : D.J)
    [T2Space (D.U i)] : IsClosed (glueRelComponent D i i) := by
  rw [glueRelComponent_self]
  exact isClosed_eq continuous_fst continuous_snd

/-- Distinct filling pieces of a four-piece star have no direct relation component. -/
public theorem glueRelComponent_distinct_fillings
    (B : FourPieceStarGluingData) {i j : Fin 3} (hij : i ≠ j) :
    glueRelComponent B.glueData (some i) (some j) = ∅ := by
  ext p
  unfold glueRelComponent
  constructor
  · rintro ⟨x, -, -⟩
    simpa [FourPieceStarGluingData.overlap, hij] using x.2
  · simp

namespace OpenEmbeddingStarData.ClosedCollarPairData

variable {A : OpenEmbeddingStarData} (C : A.ClosedCollarPairData)

include C

/-- Closed paired collar images, together with Hausdorff pieces, close every fixed-pair
component of the four-piece relation. -/
public theorem relComponent_isClosed
    [T2Space A.central] [∀ i, T2Space (A.filling i)] :
    ∀ i j, IsClosed
      (glueRelComponent A.toFourPieceStarGluingData.glueData i j) := by
  change ∀ i j : Option (Fin 3), IsClosed
    (glueRelComponent A.toFourPieceStarGluingData.glueData i j)
  intro i j
  cases i with
  | none =>
      cases j with
      | none =>
          let D := A.toFourPieceStarGluingData.glueData
          let ni : D.J := none
          let _ : T2Space (D.U ni) := by
            change T2Space A.central
            infer_instance
          exact glueRelComponent_self_isClosed D ni
      | some j =>
          rw [A.glueRelComponent_none_some]
          exact OpenEmbeddingStarData.ClosedCollarPairData.isClosed_range C j
  | some i =>
      cases j with
      | none =>
          rw [A.glueRelComponent_some_none]
          exact A.isClosed_reverseRange i
            (OpenEmbeddingStarData.ClosedCollarPairData.isClosed_range C i)
      | some j =>
          by_cases hij : i = j
          · subst j
            let D := A.toFourPieceStarGluingData.glueData
            let si : D.J := some i
            let _ : T2Space (D.U si) := by
              change T2Space (A.filling i)
              infer_instance
            exact glueRelComponent_self_isClosed D si
          · rw [glueRelComponent_distinct_fillings _ hij]
            exact isClosed_empty

/-- The closed paired collar criterion makes the four-piece gluing Hausdorff. -/
public theorem t2Space
    [T2Space A.central] [∀ i, T2Space (A.filling i)] :
    T2Space (GluedSpace A.toFourPieceStarGluingData.glueData) := by
  let _ : Finite A.toFourPieceStarGluingData.glueData.J := by
    change Finite (Option (Fin 3))
    infer_instance
  exact t2Space_gluedSpace_of_closed_components _ (relComponent_isClosed C)

end OpenEmbeddingStarData.ClosedCollarPairData

end

end SphereSixComplex
